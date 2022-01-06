# The Alumina Programming Language

Alumina is a general-purpose programming language. 

Non-exhaustive list of distinguishing features:

- Module system and 2-pass compilation (no header files and forward declarations needed)
- Generics, protocols and mixins (duck-typed, similar to C++ template but without overloading/SFINAE)
  - Specialization is possible with [`when` expressions](./examples/when_expression.alu)
- [Unified call syntax](https://en.wikipedia.org/wiki/Uniform_Function_Call_Syntax) for functions in scope
- Limited operator overloading (via `Equatable` and `Comparable` protocols)
- Block expressions
- Lambdas (static only, closures are not supported)
- Richer type system:
  - strong enums,
  - array slices,
  - tuples,
  - first-class 0-sized types (unit/void, function types, 0-sized arrays, structs with no fields, ...),
  - never type
- Hygenic expression macros
- Const evaluation (very limited at the moment)
- Go-style defer expressions

Alumina is heavily inspired by Rust, especially in terms of syntax and standard library API. Unlike Rust, however, Alumina is not memory-safe and it requires manual memory management.

# Motivating example

<!-- github, add syntax highlighting for Alumina pls -->
```rust
struct Stack<T> {
    data: &mut [T],
    length: usize,
}

impl Stack {
    use std::mem::{alloc, realloc, copy_to};

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
        use std::math::max;

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

Bootstrap Alumina compiler ([`alumina-boot`](./aluminac)) is written in Rust and is currently actively developed. It compiles to ugly C11 code with GCC extensions. It is currently at a point where it can be considered a functional compiler, but it is not by any means stable, reliable or complete.

Finished:

- Lexical analysis and parser (using Tree-Sitter)
- Scope/name resolution
- Type support
- Lowering parse tree into AST (desugaring, macro expansion, ...)
- Lowering AST into IR (with monomorphization, type checking and semantic analysis)
- Codegen to C

TBD:

- Standard library is only usable on Linux-like targets
- Probably a lot of bugs and miscompilations

A self-hosted compiler ([`aluminac`](./aluminac)) is also being written. It is in very early stages (is only able to parse source at the moment). It will eventually have a LLVM backend.

Full list of missing features, open questions, bugs and ideas for the future in [MISSING.md](./MISSING.md)

# Try it out

## Prerequisites

To compile `alumina-boot` compiler from source, these prerequisites are needed:
  
  - A C compiler (GCC/clang)
  - Nightly Rust toolchain (`rustup install nightly`)
  - Tree-sitter CLI (`npm install -g tree-sitter-cli`)

Additionally, to compile `aluminac`, Tree-sitter runtime library (`libtree-sitter.a`/`libtree-sitter.so`) is needed:

```bash
https://github.com/tree-sitter/tree-sitter
cd tree-sitter
make
sudo make install
```

## Building
  
To compile `alumina-boot` compiler from source, run:
```
make alumina-boot
```

Now you are able to compile Aluimina code, e.g.

```
./build/alumina-boot --sysroot ./stdlib hello_world=./examples/hello_world.alu -o hello_world.c
cc hello_world.c -o hello_world
./hello_world
```

To compile the self-hosted compiler, run:
```
make alumina-boot
```

See [examples](./examples), [standard library](./stdlib) and the [self-hosted compiler](./aluminac) for a tour of the language, documentation is TBD.

# Contributing

Issues, pull requests, and feature requests are most welcome. There is not a good test suite at the moment, but there are regression tests that run all the examples in the `examples` folders. These tests are run with 

```
make test
```

If the snapshot need to be updated, run 

```
make test-fix
```

