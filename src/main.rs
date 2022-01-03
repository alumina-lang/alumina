#![feature(bool_to_option)]
#![feature(never_type)]
#![feature(backtrace)]
#![feature(core_intrinsics)]

mod ast;
mod codegen;
mod common;
mod compiler;
mod diagnostics;
mod global_ctx;
mod intrinsics;
mod ir;
mod name_resolution;
mod parser;
mod utils;
mod visitors;

use clap::Parser;
use common::AluminaError;
use compiler::Compiler;
use compiler::SourceFile;
use diagnostics::DiagnosticContext;
use global_ctx::GlobalCtx;
use std::collections::HashMap;
use std::error::Error;
use std::fs::FileType;
use std::path::PathBuf;
use walkdir::WalkDir;

/// Parse a single key-value pair
fn parse_key_val<T, U>(s: &str) -> Result<(T, U), Box<dyn Error + Send + Sync + 'static>>
where
    T: std::str::FromStr,
    T::Err: Error + Send + Sync + 'static,
    U: std::str::FromStr,
    U::Err: Error + Send + Sync + 'static,
{
    let pos = s
        .find('=')
        .ok_or_else(|| format!("invalid KEY=value: no `=` found in `{}`", s))?;
    Ok((s[..pos].parse()?, s[pos + 1..].parse()?))
}

#[derive(Parser, Debug)]
#[clap(about, version, author)]
struct Args {
    /// Output filename (defaults to stdout)
    #[clap(short, long)]
    output: Option<String>,

    /// Path to the standard library
    #[clap(long)]
    sysroot: PathBuf,

    /// Modules to compile (use 'module::name=filename.alu' syntax)
    #[clap(parse(try_from_str = parse_key_val))]
    modules: Vec<(String, PathBuf)>,
}

fn get_sysroot(args: &Args) -> Result<Vec<SourceFile>, AluminaError> {
    let mut result = Vec::new();

    for maybe_entry in WalkDir::new(args.sysroot.clone())
        .follow_links(true)
        .into_iter()
    {
        use std::fmt::Write;
        let entry = maybe_entry?;
        if entry.file_type().is_dir() {
            continue;
        }

        let filename = entry.file_name().to_string_lossy();
        if !filename.ends_with(".alu") {
            continue;
        }

        let path_segments: Vec<_> = entry
            .path()
            .strip_prefix(args.sysroot.clone())
            .unwrap()
            .iter()
            .map(|s| s.to_string_lossy())
            .collect();

        let mut module_path = String::new();
        for (index, segment) in path_segments.iter().enumerate() {
            if index < path_segments.len() - 1 {
                write!(module_path, "::{}", segment).unwrap();
            } else {
                let module_name = segment.strip_suffix(".alu").unwrap();
                if module_name != "_root" {
                    write!(module_path, "::{}", module_name).unwrap();
                }
            }
        }
        if module_path.is_empty() {
            module_path.push_str("::");
        }
        result.push(SourceFile {
            filename: entry.into_path(),
            path: module_path,
        });
    }

    Ok(result)
}

fn main() {
    let args = Args::parse();

    let global_ctx = GlobalCtx::new();
    let mut compiler = Compiler::new(global_ctx.clone());

    let mut files = get_sysroot(&args).unwrap();
    for (path, filename) in &args.modules {
        files.push(SourceFile {
            filename: filename.clone(),
            path: path.clone(),
        });
    }

    match compiler.compile(files) {
        Ok(program) => {
            let diag_ctx = global_ctx.diag();
            diag_ctx.print_error_report().unwrap();
            match args.output {
                Some(filename) => std::fs::write(filename, program).unwrap(),
                None => {
                    print!("{}", program);
                }
            }
        }
        Err(e) => {
            let diag_ctx = global_ctx.diag();
            diag_ctx.add_from_error(e).unwrap();
            diag_ctx.print_error_report().unwrap();
            std::process::exit(1);
        }
    }
}
