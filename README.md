# The Alumina Programming Language

Alumina is a programming language. 

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

## Motivating example

<!-- totally not rust lmao -->
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

## Status

Bootstrap Alumina compiler (`alumina-boot`) is written in Rust and is currently actively developed. It compiles to ugly C11 code with GCC extensions. It is currently at a point where it can be considered a functional compiler, but it is not by any means stable or complete.

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

Full list of missing features, open questions, bugs and ideas for the future in [MISSING.md](./MISSING.md)

After the compiler is reliable enough, Alumina will be written as a self-hosted compiler with a LLVM backend (as this has always been my dream).


## Try it out

To compile `alumina-boot` compiler from source, these prerequisites are needed:
  
  - Nightly Rust toolchain (`rustup install nightly`)
  - Tree-sitter CLI (`npm install -g tree-sitter-cli`)

Then, run `cargo +nightly install --path .` to build and install the compiler. 

To compile and run a simple program, try:

```
alumina-boot --sysroot ./stdlib hello_world=./examples/hello_world.alu -o hello_world.c
cc hello_world.c -o hello_world
./hello_world
```

See [examples](./examples) and [standard library](./stdlib) for a tour of the language, 
documentation is TBD.
