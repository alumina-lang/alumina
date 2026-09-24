# Alumina Programming Language

Alumina is an imperative, general-purpose, statically typed, compiled system programming language.

Non-exhaustive list of distinguishing features:

- Module system and 2-pass compilation (no header files and forward declarations needed)
- Generics (duck-typed, similar to C++ templates but without SFINAE), protocols and mixins
  - Specialization is possible with `when` expressions
  - Opt-in dynamic polymorphism with dynamic dispatch ([`dyn` pointers](./examples/dyn.alu))
- Limited operator overloading (via `Equatable` and `Comparable` protocols)
- Block expressions
- Anonymous functions (including closures)
- Richer type system:
  - strong enums,
  - array slices,
  - named function types,
  - tuples,
  - first-class 0-sized types (unit/void, 0-sized arrays, structs with no fields, ...),
  - never type
- Hygienic expression macros
- [Stackful coroutines](./examples/coroutines.alu)
- [Compile-time constant evaluation](./examples/constants.alu) (including loops, function calls, etc.)
- [Unified call syntax](https://en.wikipedia.org/wiki/Uniform_Function_Call_Syntax) for functions and macros in scope
- [Defer expressions](./examples/defer_and_move.alu)
- [Compile-time reflection and meta-programming](./examples/reflection.alu)

Alumina is heavily inspired by Rust, especially in terms of syntax and standard library API. Unlike Rust, however, Alumina is not memory-safe and it requires manual memory management.

# Quick links

- [Language guide](./docs/lang_guide.md)
- [Library documentation](https://docs.alumina-lang.net)
- [Online compiler playground](https://play.alumina-lang.net)

# Motivating example

<!-- github, add syntax highlighting for Alumina pls -->
```rust
struct Stack<T> {
   data: &mut [T],
   len: usize,
}

impl Stack<T> {
   use std::mem::slice;

   fn new() -> Stack<T> {
      with_capacity(0)
   }

   fn with_capacity(capacity: usize) -> Stack<T> {
      Stack {
         data: slice::alloc(capacity),
         len: 0,
      }
   }

   fn reserve(self: &mut Stack<T>, additional: usize) {
      use std::cmp::max;

      if self.len + additional > self.data.len() {
         self.data = self.data.realloc(max(
            self.data.len() * 2,
            self.len + additional
         ));
      }
   }

   fn push(self: &mut Stack<T>, value: T) {
      self.reserve(1);
      self.data[self.len] = value;
      self.len += 1;
   }

   fn pop(self: &mut Stack<T>) -> T {
      self.len -= 1;
      self.data[self.len]
   }

   fn is_empty(self: &Stack<T>) -> bool {
      self.len == 0
   }

   fn free(self: &mut Stack<T>) {
      self.data.free();
   }
}

fn main() {
   let v: Stack<&[u8]> = Stack::new();
   defer v.free();

   v.push("Stack.\n");
   v.push("a ");
   v.push("am ");
   v.push("I ");

   while !v.is_empty() {
       print!("{}", v.pop());
   }
}
```

# Status

Bootstrap Alumina compiler ([`alumina-boot`](./src/alumina-boot)) is written in Rust and is actively developed. It compiles to ugly C11 code with GCC extensions (works on Clang too).

Finished:

- Lexical analysis and parser (using Tree-Sitter)
- Scope/name resolution
- Type support
- Lowering parse tree into AST (desugaring, macro expansion, ...)
- Lowering AST into IR (with monomorphization, type checking and semantic analysis)
- Basic optimizations (ZST elision, dead code elimination)
- Codegen to C11
- A full-featured [standard library](https://docs.alumina-lang.net/std)
    - [heap-allocating collections](https://docs.alumina-lang.net/std/collections) (vector, hashmap, hashset, deque)
    - [iterator combinators](https://docs.alumina-lang.net/std/iter)
    - [string functions and formatting](https://docs.alumina-lang.net/std/string)
    - [spawning processes](https://docs.alumina-lang.net/std/process)
    - [standard, file and pipe I/O](https://docs.alumina-lang.net/std/io)
    - [multithreading](https://docs.alumina-lang.net/std/thread)
    - [synchronization primitives and atomics](https://docs.alumina-lang.net/std/sync)
    - [basic filesystem operations](https://docs.alumina-lang.net/std/fs)
    - [TCP/IP sockets](https://docs.alumina-lang.net/std/net)
    - [random number generation](https://docs.alumina-lang.net/std/random)
    - [unit testing framework](https://docs.alumina-lang.net/test)
    - [reflection](https://docs.alumina-lang.net/std/typing)

To be done:

- Standard library is only usable on Unixes (tested on x86_64/aarch64/riscv64 Linux, macOS and Android)
- Compiler driver (something like Rust's `cargo`)
- A good story for third-party libraries (something like `crates.io` maybe?)
- Various rough edges, bugs and missing features

Full list of missing features, open questions, bugs and ideas for the future is in [MISSING.md](./MISSING.md)

# Try it out

Don't want to install anything? Try https://play.alumina-lang.net, an online compiler playground.

You can do it with Podman/Docker:

```bash
# With Podman
alias alumina-boot='podman run -v $(pwd):/workspace ghcr.io/alumina-lang/alumina-boot:latest'
# With Docker
alias alumina-boot='docker run -u $(id -u ${USER}):$(id -g ${USER}) -v $(pwd):/workspace ghcr.io/alumina-lang/alumina-boot:latest'

alumina-boot hello_world=./examples/hello_world.alu -o hello.c
cc hello.c -o hello
./hello
```

Otherwise, follow the instructions to build it from source.

## Prerequisites

The compiler, `aluminac`, is written in Alumina and generates native code with LLVM. It is bootstrapped with `alumina-boot`, the original compiler written in Rust. Supported platforms are Linux (x86_64 and aarch64) and macOS (arm64). To build it, you need:

  - A C compiler (GCC or Clang) and Make
  - A Rust toolchain (`rustup install stable`), for `alumina-boot`
  - LLVM 22 (e.g. `apt install llvm-22-dev` from [apt.llvm.org](https://apt.llvm.org), or `brew install llvm`). If `llvm-config-22` is not on your `PATH`, pass `LLVM_CONFIG=/path/to/llvm-config` to `make`.
  - Node.js and Tree-sitter CLI (`npm install -g tree-sitter-cli` or `cargo install tree-sitter-cli`)
  - Tree-sitter runtime library (`libtree-sitter.a`/`libtree-sitter.so`):
   ```bash
   git clone https://github.com/tree-sitter/tree-sitter
   cd tree-sitter
   make
   sudo make install
   # sudo ldconfig
   ```
  - Python 3, to run the tests

## Building

To build the compiler, run:

```
make
```

This builds `alumina-boot`, bootstraps `aluminac` with it and leaves `./aluminac` (a link to `build/debug/aluminac`; use `make RELEASE=1` for an optimized build). Now you are able to compile Alumina code, e.g.

```
./aluminac --sysroot ./sysroot hello_world=./examples/hello_world.alu -o hello_world
./hello_world
```

Add `--test` to build the unit test runner instead (the `main()` function is replaced by it), and `--cfg threading` (linking with `-lpthread`) for multithreading:

```
./aluminac --sysroot ./sysroot --cfg threading --link-args -lpthread threading=./examples/threading.alu -o threading
./threading
```

## Debugging

Compile with `-g` for debug information (DWARF; on macOS aluminac also runs `dsymutil`). Debuggers see Alumina's names: functions by their paths (`main::geometry::Square::area`, `std::collections::vector::Vector::push<i32>`), types as they are written (`&[u8]`, `(i32, bool)`, `std::option::Option<i32>`), in backtraces, breakpoints (`b main::add`) and expressions. `tools/lldb/alumina-lldb` is lldb with formatters for the standard library's types:

```
(&[u8]) name = "hello"
(std::collections::vector::Vector<i32>) v = len=2 { [0] = 10, [1] = 20 }
(std::option::Option<i32>) some = some(7)
(std::collections::hashmap::HashMap<i32, &[u8], std::hash::xxhash::Xxh64>) m = len=1 { [0] = (1, "one") }
```

(or load them in any lldb with `command script import tools/lldb/alumina_lldb.py`; that also lets `step` enter the standard library, which lldb skips by default because C++'s is also `std::`).

`make install` installs `aluminac`, `alumina-lldb` and the standard library into `PREFIX` (`/usr/local` by default); set `ALUMINA_SYSROOT` to `$PREFIX/share/alumina` to use it without `--sysroot`.

`alumina-boot` alone (it compiles Alumina to C) can be built with `make boot`.

# Contributing

Issues, pull requests, and feature requests are most welcome. Standard library is covered with tests, and there are also documentation tests (all examples from the standard library are compiled and executed as test cases).

To run all the tests (the compiler's, the standard library's, the language's and the documentation's):

```shell
make test
```

or a part of them, e.g. `make test-std` (the standard library), `make test-docs` (the documentation) or `make test-debuginfo` (programs run in lldb, which it needs: `lldb-22` or `lldb`, or `LLDB=<path>`). `make check` runs everything CI does, including the bootstrap check (the compiler, compiled by itself, compiles itself to the same code).

Standard library contributions are especially welcome! Ideas for contribution:

- Better / more performant algorithms and collections (sorting, HashMap, ...)
- Port the standard library to other platforms (e.g. Windows) or libc implementations
- Unix domain socket support
- More test cases and documentation / example code for existing functionality

## Projects using Alumina

Needless to say, a great way to contribute to the project is to just use Alumina for your own programs and libraries. Submit a PR and add your project to the list:

- [timestamped](http://github.com/tibordp/timestamped) - A utility to record and replay the output of a program with timestamps.

