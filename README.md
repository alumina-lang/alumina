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

- Standard library is only usable on Unixes (tested on Linux, macOS and Android)
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

To compile `alumina-boot` compiler from source, these prerequisites are needed:

  - A C compiler (GCC or Clang) and Make
  - A Rust toolchain (`rustup install stable`)
  - Node.js and Tree-sitter CLI (`npm install -g tree-sitter-cli` or `cargo install tree-sitter-cli`)

Additionally, to compile the tools, such as `alumina-doc`, these prerequisites are needed:

  - Tree-sitter runtime library (`libtree-sitter.a`/`libtree-sitter.so`):
   ```bash
   git clone https://github.com/tree-sitter/tree-sitter
   cd tree-sitter
   make
   sudo make install
   # sudo ldconfig
   ```
  - [`libbacktrace`](https://github.com/ianlancetaylor/libbacktrace/) is an optional dependency for nice stack backtraces on panics. If disabled, pass `STD_BACKTRACE=1` when building `aluminac` to use the libc's backtrace function instead.
   ```bash
   git clone https://github.com/ianlancetaylor/libbacktrace
   cd libbacktrace
   ./configure
   make
   sudo make install
   ```

## Building

To compile `alumina-boot` compiler from source, run:
```
make alumina-boot
```

Now you are able to compile Alumina code, e.g.

```
./alumina-boot --sysroot ./sysroot hello_world=./examples/hello_world.alu -o hello_world.c
cc hello_world.c -o hello_world
./hello_world
```

If you wish to run the tests, simply add `--cfg test`. In this case the `main()` function will be replaced by the test runner.

```
./alumina-boot --sysroot ./sysroot hello_world=./examples/hello_world.alu -o hello_world_test.c
cc hello_world_test.c -o hello_world_test
./hello_world_test
```

If you wish to compile with multithreading enabled, add `--cfg threading` and link with `libpthread`.

```
./alumina-boot --cfg threading --sysroot ./sysroot hello_world=./examples/threading.alu -o threading.c
cc threading.c -o threading -lpthread
./threading
```


To compile the self-hosted compiler, run:
```
make aluminac
```

See the [language guide](./docs/lang_guide.md), assorted [examples](./examples), [standard library](./sysroot) for a tour of the language.


# Contributing

Issues, pull requests, and feature requests are most welcome. Standard library is covered with tests, and there are also documentation tests (all examples from the standard library are compiled and executed as test cases).

To run the standard library tests

```shell
make test-std
```

To run the documentation tests

```shell
make test-docs
```

Standard library contributions are especially welcome! Ideas for contribution:

- Better / more performant algorithms and collections (sorting, HashMap, ...)
- Port the standard library to other platforms (e.g. Windows) or libc implementations (on Linux only glibc is supported, musl would be very nice to have)
- Unix domain socket support
- More test cases and documentation / example code for existing functionality

## Projects using Alumina

Needless to say, a great way to contribute to the project is to just use Alumina for your own programs and libraries. Submit a PR and add your project to the list:

- [timestamped](http://github.com/tibordp/timestamped) - A utility to record and replay the output of a program with timestamps.

