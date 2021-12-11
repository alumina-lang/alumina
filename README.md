# Alumina

Alumina is a C-like programming language with Rust-like syntax.

It has the following conveniences over C:

- Generics (duck-typed, similar to C++ templates, but without specializations)
- [Unified call syntax](https://en.wikipedia.org/wiki/Uniform_Function_Call_Syntax) for functions in scope
- Block expressions, lambdas (stateless only, closures are not supported)
- Module system, namespaces and 2-pass compilation (no header files and forward declarations needed)
- Richer type system: strong enums, slices, tuples, unit and never types. Also some type inference (though not full Hindley-Milner)

Alumina can be thought of as Go without a garbage collector and runtime. Unlike C++, Rust and D is not a RAII language and requires manual memory management and is not memory-safe.

## Motivating example

<!-- totally not rust lmao -->
```rust
struct vector<T> {
    data: &mut [T],
    length: usize,
}

impl vector {
    use std::mem::{slice, alloc, copy_to, free};

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
                self.data.free();
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

    fn destroy<T>(self: &mut vector<T>) {
        self.data.free();
    }
}


#[export]
fn main() {
    let v: vector<u8> = vector::new();
    v.push(1);
    v.destroy();
}
```

## Status 

Bootstrap Alumina compiler is written in Rust and is currently actively developed. It will compile to C code.

Finished:
- Lexical analysis and parser (using Tree-Sitter)
- Scope/name resolution
- Basic type support
- Lowering parse tree into AST (desugaring)
- Lowering AST into IR (with type checking and semantic analysis)
- Codegen with C

TBD:
- Better error reporting & diagnostics
- Compiler driver for multi-file compilation
- All the other housekeeping stuff

Full list of missing features, bugs and ideas for the future in [MISSING.md](./MISSING.md) 

After the compiler is somewhat functional, Alumina will be written as a self-hosted compiler with a LLVM backend (as this has always been my dream).


