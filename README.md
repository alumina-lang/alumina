# Alumina

Alumina is a C-like programming language with a Rust-like syntax.

It has the following conveniences over C:

- Generics (duck-typed, similar to C++ templates, but without specializations)
- [Unified call syntax](https://en.wikipedia.org/wiki/Uniform_Function_Call_Syntax) for functions in scope
- Block expressions, lambdas (stateless only, closures are not supported)
- Module system, namespaces and 2-pass compilation (no header files and forward declarations needed)
- Richer type system: strong enums, array slices, tuples, 0-sized types, never type.
- Const evaluation (very limited at the moment)
- Go-style defer expressions

Alumina can be thought of as Go without a garbage collector and runtime. Unlike C++, Rust and D is not a RAII language and requires manual memory management and is not memory-safe.

## Motivating example

<!-- totally not rust lmao -->
```rust
struct vector<T> {
    data: &mut [T],
    length: usize,
}

impl vector {
    use std::mem::{slice, alloc, copy_to};

    fn new<T>() -> vector<T> {
        with_capacity(0)
    }

    fn with_capacity<T>(capacity: usize) -> vector<T> {
        vector {
            data: alloc::<T>(capacity),
            length: 0,
        }
    }

    fn reserve<T>(self: &mut vector<T>, new_capacity: usize) {
        if self.data.len < new_capacity {
            self.data = {
                let new_data = alloc::<T>(new_capacity);
                self.data.copy_to(new_data.ptr);
                self.free();
                new_data
            };
        }
    }

    fn push<T>(self: &mut vector<T>, value: T) {
        use std::math::max;

        if self.length == self.data.len {
            self.reserve(max(self.data.len, 1) * 2);
        }

        self.data[self.length] = value;
        self.length += 1;
    }

    fn pop<T>(self: &mut vector<T>) -> T {
        let value = self.data[self.length - 1];
        self.length -= 1;
        value
    }

    fn empty<T>(self: &vector<T>) -> bool {
        self.length == 0
    }

    fn free<T>(self: &mut vector<T>) {
        use std::mem::free;
        self.data.free();
    }
}

use std::io::print;

#[export]
fn main() {
    let v: vector<&[u8]> = vector::new();
    defer v.free();
    
    v.push("vector.\n");
    v.push("a ");
    v.push("am ");
    v.push("I ");

    while !v.empty() {
        print(v.pop());
    }
}
```

## Status 

Bootstrap Alumina compiler is written in Rust and is currently actively developed. It compiles to freestanding C11 code with GCC extensions.

Finished:
- Lexical analysis and parser (using Tree-Sitter)
- Scope/name resolution
- Type support
- Lowering parse tree into AST (desugaring)
- Lowering AST into IR (with monomorphization, type checking and semantic analysis)
- Codegen to C

TBD:
- Stdlib is very barebones
- Probably a lot of bugs and miscompilations
- Better error reporting & diagnostics
- Compiler interface
- Code cleanup, it's a big mess so far

Full list of missing features, bugs and ideas for the future in [MISSING.md](./MISSING.md) 

After the compiler is somewhat functional, Alumina will be written as a self-hosted compiler with a LLVM backend (as this has always been my dream).


