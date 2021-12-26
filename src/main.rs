#![feature(bool_to_option)]
#![feature(never_type)]
#![feature(backtrace)]

mod ast;
mod codegen;
mod common;
mod compiler;
mod diagnostics;
mod intrinsics;
mod ir;
mod name_resolution;
mod parser;
mod utils;
mod visitors;

use compiler::Compiler;
use compiler::SourceFile;
use diagnostics::DiagnosticContext;
use std::path::PathBuf;

fn main() {
    let diag_context = DiagnosticContext::new();
    let mut compiler = Compiler::new(diag_context.clone());
    let files = vec![
        SourceFile {
            filename: PathBuf::from("./stdlib/lib.alu"),
            path: "::std".to_string(),
        },
        SourceFile {
            filename: PathBuf::from("./stdlib/result.alu"),
            path: "::std::result".to_string(),
        },
        SourceFile {
            filename: PathBuf::from("./stdlib/random.alu"),
            path: "::std::random".to_string(),
        },
        SourceFile {
            filename: PathBuf::from("./stdlib/_prelude.alu"),
            path: "".to_string(),
        },
        SourceFile {
            filename: PathBuf::from("./stdlib/collections.alu"),
            path: "::std::collections".to_string(),
        },
        SourceFile {
            filename: PathBuf::from("./stdlib/impl/xxhash.alu"),
            path: "::std::hash::xxhash".to_string(),
        },
        SourceFile {
            filename: PathBuf::from("./examples/minimal.alu"),
            path: "::hello_world".to_string(),
        },
    ];

    match compiler.compile(files) {
        Ok(program) => {
            diag_context.print_error_report().unwrap();
            println!("{}", program);
        }
        Err(e) => {
            diag_context.add_from_error(e).unwrap();
            diag_context.print_error_report().unwrap();
            std::process::exit(1);
        }
    }
}
