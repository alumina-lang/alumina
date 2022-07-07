# The Alumina Programming Language

Alumina is a general-purpose programming language.

Non-exhaustive list of distinguishing features:

- Module system and 2-pass compilation (no header files and forward declarations needed)
- Generics, protocols and mixins (duck-typed, similar to C++ template but without overloading/SFINAE)
  - Specialization is possible with [`when` expressions](./examples/when_expression.alu)
  - Opt-in dynamic polymorphism with dynamic dispatch ([`dyn` pointers](./examples/dyn.alu))
- [Unified call syntax](https://en.wikipedia.org/wiki/Uniform_Function_Call_Syntax) for functions in scope
- Limited operator overloading (via `Equatable` and `Comparable` protocols)
- Block expressions
- Anonymous functions (including closures)
- Richer type system:
  - strong enums,
  - array slices,
  - tuples,
  - first-class 0-sized types (unit/void, function types, 0-sized arrays, structs with no fields, ...),
  - never type
- Hygenic expression macros
- Go-style [defer expressions](./examples/defer_and_move.alu)

Alumina is heavily inspired by Rust, especially in terms of syntax and standard library API. Unlike Rust, however, Alumina is not memory-safe and it requires manual memory management.

# Quick links

- [Online compiler playground](https://play.alumina-lang.net)
- [Library documentation](https://docs.alumina-lang.net)

# Motivating example

<!-- github, add syntax highlighting for Alumina pls -->
```rust
struct Stack<T> {
    data: &mut [T],
    length: usize,
}

impl Stack {
    use std::mem::{alloc, realloc};

    fn new<T>() -> Stack<T> {
        with_capacity(0)
    }

    fn with_capacity<T>(capacity: usize) -> Stack<T> {
        Stack {
            data: alloc::<T>(capacity),
            length: 0,
        }
    }

    fn reserve<T>(self: &mut Stack<T>, new_capacity: usize) {
        if self.data.len < new_capacity {
            self.data = self.data.realloc(new_capacity);
        }
    }

    fn push<T>(self: &mut Stack<T>, value: T) {
        use std::cmp::max;

        if self.length == self.data.len {
            self.reserve(max(self.data.len, 1) * 2);
        }

        self.data[self.length] = value;
        self.length += 1;
    }

    fn pop<T>(self: &mut Stack<T>) -> T {
        self.length -= 1;
        self.data[self.length]
    }

    fn empty<T>(self: &Stack<T>) -> bool {
        self.length == 0
    }

    fn free<T>(self: &mut Stack<T>) {
        use std::mem::free;
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

    while !v.empty() {
        print!("{}", v.pop());
    }
}
```

# Status

Bootstrap Alumina compiler ([`alumina-boot`](./src/alumina-boot)) is written in Rust and is currently actively developed. It compiles to ugly C11 code with GCC extensions (works on Clang too). It is currently at a point where it can be considered a functional compiler, but it is not by any means stable, reliable or complete.

Finished:

- Lexical analysis and parser (using Tree-Sitter)
- Scope/name resolution
- Type support
- Lowering parse tree into AST (desugaring, macro expansion, ...)
- Lowering AST into IR (with monomorphization, type checking and semantic analysis)
- Codegen to C11
- A reasonable chunk of standard library
    - collections (vector, hashmap, hashset)
    - iterator combinators
    - string functions and formatting
    - spawning processes
    - standard, file and pipe I/O
    - multithreading
    - atomics
    - basic synchronization primitives
    - basic filesystem operations
    - TCP/IP sockets
    - random number generation
    - unit testing

To be done:

- Standard library is only usable on Unixes (tested on Linux, macOS and Android)
- Probably a lot of bugs and miscompilations
- Better error messages and warnings. Currently they are not terrible, but not great either.
- Language and library reference and other documentation

A self-hosted compiler ([`aluminac`](./src/aluminac)) is also being written. It is in very early stages (is only able to parse source at the moment). It will eventually have a LLVM backend.

Full list of missing features, open questions, bugs and ideas for the future in [MISSING.md](./MISSING.md)

# Try it out

Just want to try it out? You can do it with Podman/Docker:

```bash
# With Podman
alias alumina-boot='podman run -v $(pwd):/workspace ghcr.io/tibordp/alumina-boot:latest'
# With Docker
alias alumina-boot='docker run -u $(id -u ${USER}):$(id -g ${USER}) -v $(pwd):/workspace ghcr.io/tibordp/alumina-boot:latest'

alumina-boot hello_world=./examples/hello_world.alu -o hello.c
cc hello.c -o hello
./hello
```

Otherwise, follow the instructions to build it from source.

## Prerequisites

To compile `alumina-boot` compiler from source, these prerequisites are needed:

  - A C compiler (GCC or Clang) and Make
  - A Rust toolchain (`rustup install stable`)
  - Node.js and Tree-sitter CLI (`npm install -g tree-sitter-cli`)

Additionally, to compile `aluminac`, these prerequisites are needed:

  - LLVM 13 shared libraries and headers (`llvm-13-dev`)
  - Tree-sitter runtime library (`libtree-sitter.a`/`libtree-sitter.so`):

```bash
git clone https://github.com/tree-sitter/tree-sitter
cd tree-sitter
make
sudo make install
# sudo ldconfig
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

See [examples](./examples), [standard library](./sysroot) and the [self-hosted compiler](./src/aluminac) for a tour of the language.

# Contributing

Issues, pull requests, and feature requests are most welcome. Standard library is somewhat covered with tests, and there are also regression tests that run all the examples in the `examples` folders. These tests are run with

```
make test
```

If the snapshot need to be updated, run

```
make test-fix
```

Standard library contrinutions are especially welcome!
