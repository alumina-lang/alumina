# Alumina

Alumina is a C-like programming language with Rust-like syntax.

It has the following conveniences over C:

- Generics (duck-typed, similar to C++ templates, but without specializations)
- [Unified call syntax](https://en.wikipedia.org/wiki/Uniform_Function_Call_Syntax) for functions in scope
- Lambdas (stateless only, closures are not supported)
- Module system, namespaces and 2-pass compilation (no header files and forward declarations needed)
- Block expressions
- Richer type system: strong enums, slices, tuples, unit and never types. Also some type inference (though not full Hindley-Milner)

Alumina can be thought of as Go without a garbage collector and runtime. Unlike C++, Rust and D is not a RAII language and requires manual memory management and is not memory-safe.

## Motivating example

```rust
mod alloc {
    extern fn malloc(size: usize) -> &();
    extern fn free(ptr: &());
}

struct vector<T> {
    data: &T,
    length: usize,
    capacity: usize,
}

impl vector {
    use super::alloc::{malloc, free as free_};

    fn new<T>() -> vector<T> {
        with_capacity::<T>(0)
    }

    fn with_capacity<T>(capacity: usize) -> vector<T> {
        vector<T> {
            data: malloc(sizeof::<T>() * capacity) as &T,
            length: 0,
            capacity: capacity,
        }
    }

    fn push<T>(self: &vector<T>, value: T) {
        if self.length == self.capacity {
            let new_capacity = if self.capacity == 0 { 
                1
            } else {
                self.capacity * 2
            };

            let new_ptr = malloc(sizeof::<T>() * new_capacity) as &T;
            memcpy(new_ptr, self.data, self.length);
            free_(self.data);
            self.data = new_ptr;
            self.capacity = new_capacity;
        }

        self.data[self.length] = value;
        self.length += 1;
    }

    fn index<T>(self: &vector<T>, index: usize) -> &T {
        self.data + index
    }

    fn free<T>(self: &vector<T>) {
        free_(self.data);
    }
}

fn main() {
    let v = vector::new::<u8>();
    v.push(1);
    v.free();
}
```

## Status 

Bootstrap Alumina compiler is written in Rust and is currently actively developed. It will compile to C code.

Finished:
- Lexical analysis and parser (using Tree-Sitter)
- Scope/name resolution
- Basic type support
- Lowering parse tree into AST (desugaring)

TBD:
- Lowering AST into IR (with type checking and semantic analysis)
- Better error reporting
- Debug information (spans)
- Codegen with C
- Compiler driver for multi-file compilation

After the compiler is somewhat functional, Alumina will be written as a self-hosted compiler with a LLVM backend (as this has always been my dream).


