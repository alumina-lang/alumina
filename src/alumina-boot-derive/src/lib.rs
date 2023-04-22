#[macro_use]
extern crate quote;
#[macro_use]
extern crate syn;

extern crate proc_macro;

use std::sync::Arc;

use proc_macro::{Span, TokenStream};
use syn::{spanned::Spanned, DeriveInput, Lifetime};

#[proc_macro_derive(AstSerializable)]
pub fn alumina_serdes(input: TokenStream) -> TokenStream {
    // Parse the input tokens into a syntax tree
    let input = parse_macro_input!(input as DeriveInput);
    // Build the output, possibly using quasi-quotation

    let lifetime = input
        .generics
        .lifetimes()
        .map(|l| l.lifetime.clone())
        .next()
        .unwrap_or(Lifetime::new("'lif", input.span()));

    let ident = input.ident.clone();
    let generics = input.generics.clone();

    let (ser_body, deser_body) = match &input.data {
        syn::Data::Enum(e) => {
            let mut ser_match_arms: Vec<quote::__private::TokenStream> = Vec::new();
            let mut deser_match_arms = Vec::new();

            for (variant_index, variant) in e.variants.iter().enumerate() {
                // Panic if we have more than 255 variants
                let variant_index: u8 = variant_index.try_into().unwrap();

                let sers = variant.fields.iter().enumerate()
                    .map(|(i, f)| {
                        let field = format_ident!("__f_{}", i);
                        let ty = &f.ty;
                        quote! {
                            <#ty as crate::serdes::AstSerializable<#lifetime>>::serialize(#field, serializer)?;
                        }
                    });

                let desers = variant.fields.iter().enumerate()
                    .map(|(i, f)| {
                        let ty = &f.ty;
                        quote! {
                            <#ty as crate::serdes::AstSerializable<#lifetime>>::deserialize(deserializer)?
                        }
                    });

                let fields = (0..variant.fields.len())
                    .map(|i| {
                        format_ident!("__f_{}", i)
                    });

                let var_ident = &variant.ident;
                if variant.fields.len() == 0 {
                    ser_match_arms.push(quote! {
                        #ident::#var_ident => {
                            serializer.write_u8(#variant_index)?;
                        },
                    });

                    deser_match_arms.push(quote! {
                        #variant_index => #ident::#var_ident,
                    });
                } else {
                    ser_match_arms.push(quote! {
                        #ident::#var_ident(#(#fields,)*) => {
                            serializer.write_u8(#variant_index)?;
                            #(#sers)*
                        },
                    });
                    deser_match_arms.push(quote! {
                        #variant_index => #ident::#var_ident(#(#desers,)*),
                    });
                }
            }

            let ser_body = quote! {
                match self {
                    #(#ser_match_arms)*
                }

                Ok(())
            };
            let deser_body = quote! {
                let ret = match deserializer.read_u8()? {
                    #(#deser_match_arms)*
                    _ => unreachable!()
                };

                Ok(ret)
            };
            (ser_body, deser_body)
        }
        syn::Data::Struct(r#struct) => {
            let sers = r#struct.fields.iter().enumerate()
                .map(|(i, f)| {
                    let field = &f.ident;
                    let ty = &f.ty;
                    quote! {
                        <#ty as crate::serdes::AstSerializable<#lifetime>>::serialize(&self.#field, serializer)?;
                    }
                });

            let desers = r#struct.fields.iter().enumerate()
                .map(|(i, f)| {
                    let field = &f.ident;
                    let ty = &f.ty;
                    quote! {
                        #field: <#ty as crate::serdes::AstSerializable<#lifetime>>::deserialize(deserializer)?
                    }
                });

            let ser_body = quote! {
                #(#sers)*
                Ok(())
            };

            let deser_body = quote! {
                Ok(#ident {
                    #(#desers,)*
                })
            };

            (ser_body, deser_body)
        }
        syn::Data::Union(_) => todo!(),
    };

    let expanded = quote! {
        impl<#lifetime> crate::serdes::AstSerializable<#lifetime> for #ident #generics {
            fn serialize<S: crate::serdes::AstSerializer<#lifetime>>(&self, serializer: &mut S) -> crate::serdes::Result<()> {
                #ser_body
            }

            fn deserialize<D: crate::serdes::AstDeserializer<#lifetime>>(deserializer: &mut D) -> crate::serdes::Result<Self> {
                #deser_body
            }

        }
    };

    // Hand the output tokens back to the compiler
    TokenStream::from(expanded)
}
