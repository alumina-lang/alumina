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
use common::CodeError;
use compiler::Compiler;
use compiler::SourceFile;

use global_ctx::GlobalCtx;
use global_ctx::OutputType;

use std::error::Error;

use std::path::PathBuf;
use std::time::Instant;
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

fn parse_key_maybe_val<T, U>(
    s: &str,
) -> Result<(T, Option<U>), Box<dyn Error + Send + Sync + 'static>>
where
    T: std::str::FromStr,
    T::Err: Error + Send + Sync + 'static,
    U: std::str::FromStr,
    U::Err: Error + Send + Sync + 'static,
{
    if let Some(pos) = s.find('=') {
        Ok((s[..pos].parse()?, Some(s[pos + 1..].parse()?)))
    } else {
        Ok((s.parse()?, None))
    }
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

    /// Modules to compile (use 'module::name=filename.alu' syntax). If output type is executable,
    /// main function is exepcted in the last module.
    #[clap(parse(try_from_str = parse_key_val))]
    modules: Vec<(String, PathBuf)>,

    /// Compile in debug mode
    #[clap(long, short)]
    debug: bool,

    /// Collect timings
    #[clap(long)]
    timings: bool,

    /// Whether a library should be output
    #[clap(long)]
    library: bool,

    /// Conditional compilation options
    #[clap(long, parse(try_from_str = parse_key_maybe_val), multiple_occurrences(true))]
    cfg: Vec<(String, Option<String>)>,
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

#[test]
fn test_1() {
    panic!("oops")
}

#[test]
fn test_2_with_long_nae() {}

#[test]
fn test_3() {
    std::thread::sleep(std::time::Duration::from_millis(100));
}

fn main() {
    let start_time = Instant::now();
    let args = Args::parse();

    let output_type = if args.library {
        OutputType::Library
    } else {
        OutputType::Executable
    };

    let mut global_ctx = GlobalCtx::new(output_type);
    let mut compiler = Compiler::new(global_ctx.clone());

    let mut files = get_sysroot(&args).unwrap();
    for (path, filename) in &args.modules {
        files.push(SourceFile {
            filename: filename.clone(),
            path: path.clone(),
        });
    }

    for (key, value) in args.cfg {
        if let Some(value) = value {
            global_ctx.add_cfg(key, value)
        } else {
            global_ctx.add_flag(key)
        }
    }

    if args.debug {
        global_ctx.add_flag("debug");
    }

    match compiler.compile(files, start_time) {
        Ok(program) => {
            let diag_ctx = global_ctx.diag();
            if args.timings {
                for (stage, duration) in compiler.timings() {
                    diag_ctx.add_note(CodeError::freeform(format!(
                        "compiler timings: stage {:?} took {}ms",
                        stage,
                        duration.as_millis()
                    )));
                }
            }
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
