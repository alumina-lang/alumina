#![feature(backtrace)]
#![feature(assert_matches)]
#![feature(bool_to_option)]
#![feature(never_type)]

mod ast;
mod codegen;
mod common;
mod compiler;
mod intrinsics;
mod ir;
mod name_resolution;
mod parser;
mod utils;
mod visitors;

use compiler::Compiler;
use compiler::SourceFile;
use std::path::PathBuf;

fn main() {
    let mut compiler = Compiler::new(vec![
        SourceFile {
            filename: PathBuf::from("./stdlib/lib.alu"),
            path: "std".to_string(),
        },
        SourceFile {
            filename: PathBuf::from("./examples/minimal.alu"),
            path: "hello_world".to_string(),
        },
    ]);

    match compiler.compile() {
        Ok(program) => {
            println!("{}", program);
        }
        Err(e) => {
            compiler.print_error_report(e).unwrap();
            std::process::exit(1);
        }
    }
}
