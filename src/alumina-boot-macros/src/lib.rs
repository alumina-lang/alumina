#[macro_use]
extern crate quote;
#[macro_use]
extern crate syn;

extern crate proc_macro;

use std::path::{Path, PathBuf};

use proc_macro::{Span, TokenStream};
use quote::ToTokens;
use std::io::Read;
use syn::{spanned::Spanned, DeriveInput, Lifetime};

fn hash_file(path: &Path) -> std::io::Result<blake3::Hash> {
    let mut hasher = blake3::Hasher::new();
    let mut file = std::fs::File::open(path)?;

    // could just read the whole file into memory, but mono.rs is like 220 kB
    let mut buffer = [0; 65536];
    loop {
        match file.read(&mut buffer) {
            Ok(0) => break,
            Ok(n) => {
                hasher.update(&buffer[..n]);
            }
            Err(ref e) if e.kind() == std::io::ErrorKind::Interrupted => continue,
            Err(e) => return Err(e),
        }
    }

    Ok(hasher.finalize())
}

#[proc_macro]
pub fn sources_hash(input: TokenStream) -> TokenStream {
    parse_macro_input!(input as syn::parse::Nothing);

    // Calculate a compound hash of all the .rs files in CARGO_MANIFEST_DIR. NB: this is not env!() macro,
    // as that would give the manifest directory of this crate (alumina-boot-macros) rather than the crate
    // that is using the macro.
    let crate_directory =
        PathBuf::from(std::env::var_os("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR not set"));

    let mut hashes: Vec<_> = walkdir::WalkDir::new(crate_directory)
        .into_iter()
        .map(|e| e.expect("failed to walk directory"))
        .filter(|entry| {
            entry.file_type().is_file() && entry.path().extension() == Some("rs".as_ref())
        })
        .map(|entry| hash_file(entry.path()).expect("failed to hash file"))
        .collect();

    hashes.sort_by(|a, b| a.as_bytes().cmp(b.as_bytes()));

    let mut hasher = blake3::Hasher::new();
    for hash in hashes {
        hasher.update(hash.as_bytes());
    }

    let result = syn::LitByteStr::new(hasher.finalize().as_bytes(), Span::call_site().into());

    TokenStream::from(result.into_token_stream())
}

/// Procedural macro for deriving the AstSerializable trait.
#[proc_macro_derive(AstSerializable)]
pub fn ast_serializable(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let lifetime = input
        .generics
        .lifetimes()
        .map(|l| l.lifetime.clone())
        .next()
        .unwrap_or(Lifetime::new("'ast", input.span()));

    let ident = input.ident.clone();
    let generics = input.generics.clone();
    let module_path: syn::Path = syn::parse_quote!(crate::ast::serialization);

    let (ser_body, deser_body) = match &input.data {
        syn::Data::Enum(e) => {
            let mut serialize_match_arms: Vec<quote::__private::TokenStream> = Vec::new();
            let mut deserialize_match_arms = Vec::new();

            for (variant_index, variant) in e.variants.iter().enumerate() {
                // Panic if we have more than 256 variants
                let variant_index: u8 = variant_index.try_into().expect("too many variants");

                let serialize_fields = variant.fields.iter().enumerate()
                    .map(|(i, f)| {
                        let field = format_ident!("__f_{}", i);
                        let ty = &f.ty;
                        quote! {
                            <#ty as #module_path::AstSerializable<#lifetime>>::serialize(#field, serializer)?;
                        }
                    });

                let deserialize_fields = variant.fields.iter()
                    .map(|f| {
                        let ty = &f.ty;
                        quote! {
                            <#ty as #module_path::AstSerializable<#lifetime>>::deserialize(deserializer)?
                        }
                    });

                let fields = (0..variant.fields.len()).map(|i| format_ident!("__f_{}", i));

                let var_ident = &variant.ident;
                if variant.fields.is_empty() {
                    serialize_match_arms.push(quote! {
                        #ident::#var_ident => {
                            serializer.write_u8(#variant_index)?;
                        },
                    });

                    deserialize_match_arms.push(quote! {
                        #variant_index => #ident::#var_ident,
                    });
                } else {
                    serialize_match_arms.push(quote! {
                        #ident::#var_ident(#(#fields,)*) => {
                            serializer.write_u8(#variant_index)?;
                            #(#serialize_fields)*
                        },
                    });
                    deserialize_match_arms.push(quote! {
                        #variant_index => #ident::#var_ident(#(#deserialize_fields,)*),
                    });
                }
            }

            let ser_body = quote! {
                match self {
                    #(#serialize_match_arms)*
                }

                Ok(())
            };
            let deser_body = quote! {
                let ret = match deserializer.read_u8()? {
                    #(#deserialize_match_arms)*
                    _ => unreachable!()
                };

                Ok(ret)
            };
            (ser_body, deser_body)
        }
        syn::Data::Struct(r#struct) => {
            let mut tuple_struct = false;

            let serialize_fields = r#struct.fields.iter().enumerate()
                .map(|(i, f)| {
                    let ty = &f.ty;
                    if let Some(field) = &f.ident {
                        quote! {
                            <#ty as #module_path::AstSerializable<#lifetime>>::serialize(&self.#field, serializer)?;
                        }
                    } else {
                        let index = syn::Index::from(i);
                        tuple_struct = true;

                        quote! {
                            <#ty as #module_path::AstSerializable<#lifetime>>::serialize(&self.#index, serializer)?;
                        }
                    }
                });

            let deserialize_fields = r#struct.fields.iter()
                .map(|f| {
                    let ty = &f.ty;
                    if let Some(field) = &f.ident {
                        quote! {
                            #field: <#ty as #module_path::AstSerializable<#lifetime>>::deserialize(deserializer)?
                        }
                    } else {
                        quote! {
                            <#ty as #module_path::AstSerializable<#lifetime>>::deserialize(deserializer)?
                        }
                    }
                });

            let ser_body = quote! {
                #(#serialize_fields)*
                Ok(())
            };

            let deser_body = if tuple_struct {
                quote! { Ok(#ident (#(#deserialize_fields,)*)) }
            } else {
                quote! { Ok(#ident { #(#deserialize_fields,)* })}
            };

            (ser_body, deser_body)
        }
        syn::Data::Union(_) => panic!("unions are not supported"),
    };

    TokenStream::from(quote! {
        impl<#lifetime> #module_path::AstSerializable<#lifetime> for #ident #generics {
            fn serialize<W: ::std::io::Write>(
                &self,
                serializer: &mut #module_path::AstSerializer<#lifetime, W>
            ) -> #module_path::Result<()> {
                #ser_body
            }

            fn deserialize<R: ::std::io::Read>(
                deserializer: &mut #module_path::AstDeserializer<#lifetime, R>
            ) -> #module_path::Result<Self> {
                #deser_body
            }
        }
    })
}
