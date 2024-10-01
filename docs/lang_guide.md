# Alumina language guide <!-- omit from toc -->

This is a short guide of the notable features of the Alumina programming language. It is not a complete reference, but it should be enough to get you started. See also the [standard library documentation](https://docs.alumina-lang.net) and the examples in the [examples folder](../examples/).

With regards to syntax, the language is very similar to Rust and in terms of semantics it is very similar to C. Generics are similar to C++ templates, except there is no overloading or template specialization. When in doubt, referring to those languages is the best way to go.

- [Modules](#modules)
  - [Name resolution](#name-resolution)
- [Functions](#functions)
  - [Generic functions](#generic-functions)
  - [Foreign functions](#foreign-functions)
  - [Coroutines](#coroutines)
    - [Implementation details](#implementation-details)
  - [Other function attributes](#other-function-attributes)
- [Constants](#constants)
- [Statics](#statics)
  - [Generic statics and constants](#generic-statics-and-constants)
  - [Thread-local statics](#thread-local-statics)
- [Types](#types)
  - [Fixed-size arrays](#fixed-size-arrays)
  - [Tuples](#tuples)
  - [Type aliases](#type-aliases)
  - [Structs and unions](#structs-and-unions)
  - [Enums](#enums)
  - [Impl blocks](#impl-blocks)
  - [Type attributes](#type-attributes)
  - [Slices](#slices)
  - [What about strings?](#what-about-strings)
  - [Zero-sized types](#zero-sized-types)
    - [Layout implications of zero-sized types](#layout-implications-of-zero-sized-types)
- [Macros](#macros)
- [Statements and expressions](#statements-and-expressions)
  - [Variables](#variables)
  - [Loops](#loops)
  - [Auto-ref and rvalue promotion](#auto-ref-and-rvalue-promotion)
  - [Function calls](#function-calls)
  - [Try expression](#try-expression)
  - [Switch expressions](#switch-expressions)
  - [Defer expressions](#defer-expressions)
  - [Anonymous functions and closures](#anonymous-functions-and-closures)
- [Protocols and mixins](#protocols-and-mixins)
- [Other topics](#other-topics)
  - [String formatting](#string-formatting)
  - [Type coercion](#type-coercion)
  - [Conditional compilation](#conditional-compilation)
  - [`typeof` type](#typeof-type)
  - [Reflection and specialization](#reflection-and-specialization)
  - [Unit testing](#unit-testing)
  - [Dyn pointers](#dyn-pointers)
  - [Operator overloading](#operator-overloading)
- [Miscellaneous](#miscellaneous)
  - [Lints (warnings)](#lints-warnings)
  - [Style conventions](#style-conventions)


# Modules

Alumina programs are organized into so-called *modules* (`mod` keyword), which serve as a grouping of related items and prevent name clashes. Modules can be nested and form a tree structure.

Alumina does not have a notion of visibility (public / private declarations) and always compiles the whole program as one unit. Therefore, modules are more like namespaces.

For example

```rust
mod math {
    const ZERO = 0;

    mod regular {
        const PI = 3.14159;
    }

    mod indiana {
        // https://en.wikipedia.org/wiki/Indiana_Pi_Bill
        const PI = 3.2;
    }
}

mod demo {
    fn print() {
        println!("ZERO: {}", math::ZERO);
        println!("PI: {}", math::regular::PI);
        println!("PI (in Indiana): {}", math::indiana::PI);
    }
}
```

There is a convention that the directory structure follows the module structure, for example the above example could equivalently be split into multiple files. Currently the compiler does not enforce this and any file can represent a module at any location.

```
.
├── math/
│     ├── regular.alu
│     └── indiana.alu
├─  math.alu
└── demo.alu
```

```rust
// math.alu
const ZERO = 0;
```

```rust
// regular.alu
const PI = 3.14159;
```

```rust
// indiana.alu
const PI = 3.2;
```

```rust
// demo.alu
fn print() {
    println!("ZERO: {}", math::ZERO);
    println!("PI: {}", math::regular::PI);
    println!("PI (in Indiana): {}", math::indiana::PI);
}
```

## Name resolution

Alumina is a two-pass compiler, all items are collected first and all names are resolved in the second pass. That means that items can be defined in any order. This is not true for so-called linear scopes (basically function bodies). Items defined in function bodies must precede their use within the same function.

Within the same non-linear scope names must be unique (even if they are of different kinds). In linear scopes a later definition of a name shadows the previous one.

```rust
mod sample {
    struct Foo {}
    fn Foo() {} // error: duplicate name `Foo`
}
```

```rust
fn main() {
    fn foo() -> i32 {
        1
    }

    fn foo() -> i32 {
        2
    }

    println!("{}", foo()); // prints 2

    let a = 1;
    let a = 2;

    println!("{}", a); // prints 2
}
```

Items that are declared within a module or any enclosing modules can be used directly without needing to qualify the full path,
for example:

```rust
const QUUX = 1;

mod foo {
    const BAR = 2;
    mod bar {
        const BAZ = BAR + QUUX;

        // Equivalently `const BAZ = foo::BAR + QUUX`
        // but both are valid.
    }
}
```

The items in sibling or child modules can be referred to using a relative or fully qualified path, or they can be imported.

```rust
mod foo {
    mod bar {
        const BAR = 1;
    }

    use bar::BAR;
    const BAZ = BAR + BAR;
}

use foo::{BAZ, bar::BAR};
const QUUX = BAZ + BAR;

// Equivalently `const QUUX = foo::BAZ + foo::bar::BAR`
```

Items defined in inner modules have higher precedence than items defined in outer modules, meaning that a module can shadow items in parent modules.

```rust
const BAR = 1;

mod foo {
    const BAR = 2;

    const QUUX = BAR; // = 2
}
```

There are a small number of items from the standard library that are available in every module, such as `Option` and `assert`. See [std::prelude](https://docs.alumina-lang.net/std/prelude) for the full list. If they are shadowed by a local definition, they are still accessible using the fully qualified path (e.g. `::assert`)

# Functions

Functions are defined using the `fn` keyword. The return type can be omitted if the return type is `()`.

```rust
fn add(x: i32, y: i32) -> i32 {
    x + y
}

fn print() {
    println!("{}", add(1, 2));
}
```

The entrypoint to the program is the `main` function, which can appear in any module in the program. Main function can optionally accept a single argument of type `&[&[u8]]` (program arguments) and return an `i32` (exit code). The following examples are all valid:

```rust
fn main() {
    println!("Hello, world!");
}
```

```rust
fn main() -> i32 {
    42
}
```

```rust
fn main(args: &[&[]]) -> i32 {
    if args.len() > 1 {
        for arg in args[1..] {
            println!("{}", arg);
        }
        0
    } else {
        eprintln!("usage: {} <arg>...", args[0]);
        1
    }
}
```


## Generic functions

Generic functions are defined using the `<...>` syntax.

```rust
fn add<T>(x: T, y: T) -> T {
    x + y
}
```

The body of generic function is not type-checked until the function is monomorphized with concrete types as arguments. See [protocols and mixins](#protocols-and-mixins) for a way to constrain the type arguments to only ones meaningful for the function.

Function bodies can contain other item definitions (e.g. nested functions, constants, types, etc.) and they are local to the function.

```rust
fn main() {
    const IAN = 1;

    struct Bar {
        bar: i32,
    }

    type Age = Bar;

    fn sav() -> Age {
        Bar { bar: IAN }
    }

    sav();
}
```

## Foreign functions

Functions have internal linkage by default (are `static` in C terminology). When compiling a library, the function can be exported using the `#[export]` attribute. The names of exported functions will not be mangled and can appear in any module in the program.

```rust
// lib.alu
#[export]
fn add(x: i32, y: i32) -> i32 {
    x + y
}
```

```c
// main.c
extern int32_t add(int32_t x, int32_t y);

int main() {
    printf("%d\n", add(1, 2));
}
```

Similarly, Alumina can use foreign functions with the `extern "ABI"` syntax. Only C ABI with standard calling convention for the target platform is supported art the moment.

```c
// lib.c
int add(int x, int y) {
    return x + y;
}
```

```rust
// main.alu
extern "C" fn add(x: libc::c_int, y: libc::c_int) -> libc::c_int;

fn main() {
    println!("{}", add(1, 2));
}
```


## Coroutines

Coroutines are a functions that can suspend their execution and resume later, while also sending and receiving values from the outside. They are defined using the `fn*` keyword. The return type of a coroutine is `Coroutine<YieldT, RecvT>`, where `YieldT` is the type of values that the coroutine can yield and `RecvT` is the type of values that the coroutine can receive.

A special case of a coroutine is a so-called generator, which only yields values (`RecvT` is `()`). Generators can be used as iterators (e.g. in for loops) and are a convenient way to implement lazy sequences.

```rust
fn* fibonacci() -> Coroutine<i32> {
    let a = 0;
    let b = 1;

    loop {
        yield a;
        let tmp = a;
        a = b;
        b = tmp + b;
    }
}
```

Coroutine instance is created by simply calling the coroutine function.

```rust
fn main() {
    let gen = fibonacci();
    defer gen.close();

    for val in gen.take(10) {
        println!("{}", val);
    }
}
```

Coroutines allocate memory on the heap to store the state of the coroutine and need to be freed when they are no longer needed. See [Coroutine](https://docs.alumina-lang.net/std/runtime/Generator.html) for more details.

### Implementation details

Coroutines are currently implemented using stackful coroutines using [minicoro](https://github.com/edubart/minicoro) library. The stack size of a coroutine is fixed at 64KB. It requires the `minicoro` library to be linked in the final binary. Default stack size is set to 56 kB, which can be controlled by compile flags of the `minicoro` library.

For CPU-bound code, coroutines that context-switch often are roughly an order of magnitude slower than hand-crafted iterators, but they can be significantly faster than using an external thread (which offers similar ergonomics). The following table shows the results of a simple benchmark that calculates the sum of 10 million random numbers with a fixed seed (numbers are generated in the iterator/coroutine/thread, and summed outside of it).


| Test case                               | Time (ms) |
|-----------------------------------------|----------:|
| iterators                               |       17  |
| coroutines                              |      325  |
| two threads (with a rendezvous channel) |   22,264  |


## Other function attributes

- `#[inline]`, `#[inline(always)]` and `#[inline(never)]` control the inlining behavior of the function.
- `#[cold]` marks the function as unlikely to be called. Any branch that leads to the function call is marked as unlikely to be taken. Usually used on error handling functions to to optimize for the happy path with regards to branch prediction.
- `#[link_name("name")]` allows to specify the name of the function in the generated object file. This is useful for linking to C libraries that use non-standard naming conventions.
- `#[location("file/name.alu", line)]` allows to override the location of the function in the debug information and compile errors. This is useful for functions that are generated by macros or other code generation tools.
- `#[tuple_args]` allows to the function to receive its arguments as a tuple. When the function is generic, this is a way to implement variadic functions in Alumina. The function's calling convention is not affected by this attribute, so the function can still be called with a normal argument list even from foreign code. See also [`invoke method`](https://docs.alumina-lang.net/std/builtins/callable.html#item.invoke) for the converse (call any function with a tuple of arguments).

    ```rust
    use std::builtins::Tuple;
    use std::hash::DefaultHash;

    #[tuple_args]
    fn contrived_add(args: (i32, i32)) -> i32 {
        args.0 + args.1
    }

    add(1, 2);

    #[tuple_args]
    fn quick_hash<T: Tuple>(args: T) -> u64 {
        let hasher = DefaultHash::new();
        args.hash(&hasher); // tuples implement Hashable
        hasher.finish()
    }

    quick_hash(1);
    quick_hash(1, "hello");
    quick_hash(1, "hello", ());
    ```

# Constants

Constants are defined using the `const` keyword. Constants are evaluated at compile time and can be used in any constant context (such as for enum values, other constants and lengths of fixed-size arrays).

```rust
const FOO = 1;
const BAR: u64 = 1;
const QUUX: usize = (1 + BAR) as usize;

let arr: [u32; QUUX];
```

Constant evaluation supports many of the language features, including variable assignments, loops, conditionals, function calls, etc. Functions do not have to be specifically marked as `const` or `constexpr` in order to use them in constant expressions. The following are not supported:

- foreign function calls, including `libc` functions
- coroutines
- inline assembly and most other compiler intrinsics
- type punning (via `transmute`, `union` or pointer casts)
    - exception: transmuting integers of same size and floating point numbers to integers and back is supported
- pointer arithmetic between pointers of different provenance
  ```rust
  const _ = {
        let a: [u8; 10];
        let b: [u8; 10];

        let diff1 = &a[7] - &a[3]; // this is allowed
        let diff2 = &a[7] - &b[3]; // but this is not
  }
  ```
- converting between pointers and integers
- all operations[^1] that would cause undefined behavior at runtime (out of bounds array access, signed overflow, division by zero, reaching `std::unreachable()`, etc.)
  - uninitialized memory is not forbidden - a constant is allowed e.g. to evaluate to a struct with an uninitialized field, but if the uninitialized value is used for computation during constant evaluation itself, this will result in a compile-time error.
    ```rust
    struct Maybe<T> { just: bool, val: T }

    const _: Maybe<i32> = {
        let x: i32;
        x = x + 1;                     // this is not allowed
        Maybe { just: false, val: x }  // but this is
    };
    ```

Call to `std::runtime::in_const_context` function evaluates to `true` during constant evaluation and `false` during code generation. This can be used to make functions const-compatible (e.g. by using an implementation not relying on foreign functions).

There are also limits on how complex a constant expression can be. The compiler will reject constant expressions that are too complex to evaluate at compile time. The current hard-coded limits are 100000 steps and a maximum recursion depth of 100 per constant expression.

[^1]: If you can produce UB during const-eval, please file a bug.

# Statics

Statics (also known as global variables) are defined using the `static` keyword. If the static does not have an initializer, it will be initialized to all-zero byte pattern. Initializers run before the `main` function at runtime and can perform arbitrary operations. If a static is unused in `main` or other exported functions, the initializer is not guaranteed to run.

Order of initialization is the topological order of the dependency graph of all static initializers. If there is a cycle, the program will fail to compile. Order of initialization between disjoint components of the dependency graph is unspecified.


```rust
static FOO: i32; // = 0
static BAR: u64 = 1;
static SUM_OF_FIRST_10_SQUARES: u64 = {
    let sum = 0u64;
    for i in 1u64..=10 {
        sum += i * i;
    }
    sum
}
```

Like functions, statics can be exported using the `#[export]`. The names of exported statics will not be mangled and can appear in any module in the program.

```rust
// lib.alu
#[export]
static FOO: i32 = 1;
```

```c
// main.c
extern int32_t FOO;

int main() {
    printf("%d\n", FOO);
}
```

And for extern statics that are linked into the program

```c
// lib.c
int FOO = 1;
```

```rust
/// main.alu
extern "C" static FOO: libc::c_int;

fn main() {
    println!("{}", FOO);
}
```

## Generic statics and constants

Statics and constants can be generic. This is seldom needed, but can be useful to create associated variables for a family of generic types or functions. Each combination of type parameters is monomorphized to a distinct variable. Generic statics cannot be `extern`.

```rust
const TYPE_SIZE<T>: usize = std::mem::size_of::<T>();

static CACHE<T, F>: Option<T>; // zero initialized

fn memoized<T, F: Fn() -> T>(f: F) -> T {
    if CACHE::<T, F>.is_some() {
        CACHE::<T, F>.unwrap()
    } else {
        let value = f();
        CACHE::<T, F> = Option::some(value);
        value
    }
}

fn rand() -> u32 {
    std::random::thread_rng().next_u32()
}

fn main() {
    // Prints the same value twice
    println!("{}", memoized(rand));
    println!("{}", memoized(rand));
}
```

## Thread-local statics

When compiled with multi-threading enabled (`--cfg threading`), statics can be made thread-local using the `#[thread_local]` attribute. That way each thread can have an independent copy of the variable. When threading is disabled, the attribute has no effect.

```rust
#[thread_local] static FOO: i32;

use std::thread::spawn;

fn main() {
    let t = spawn(|| {
        FOO = 2;
    });

    t.join().unwrap();
    println!("{}", FOO); // = 0
}
```

# Types

Alumina's type system consists of the following types:

- primitive numeric types (e.g. [`u8`](https://docs.alumina-lang.net/std/builtins/u8.html), [`u16`](https://docs.alumina-lang.net/std/builtins/u16.html), [`f64`](https://docs.alumina-lang.net/std/builtins/f64.html), ...)
- [boolean type](https://docs.alumina-lang.net/std/builtins/bool.html) (`bool`)
- [unit/void type](https://docs.alumina-lang.net/std/builtins/void.html) (`void` or `()`)
- pointers (e.g. `&i32`, `&mut i32`)
- tuples (e.g. `(i32, f64)`, `(i32, i32, i32)`)
- fixed-size arrays (e.g. `[i32; 3]`, `[i32; 10]`)
- [never type](https://docs.alumina-lang.net/std/builtins/never.html) (`!`)
- function pointers (e.g. `fn(i32) -> i32`)
- named types (can have `impl` blocks)
    - structs (`struct Foo { x: i32, y: i32 }`)
    - enums (`enum Foo { A, B, C }`)
    - unions (`union Foo { x: i32, y: i32 }`)
- "named function" types, a family of unit types, each containing a specific function

There is also a special syntax for two kinds of types that are not technically built into the compiler, but are defined in the standard library:

- [slices](#slices) (`&[i32]`, `&mut i32`)
- [dynamic dispatch pointers](#dyn-pointers) (`&dyn Protocol`)

[Protocols](#protocols-and-mixins), constants and statics themselves are also technically types (can be used as type arguments and reflection), but they are not valid types for values.

```rust
const foo: i32 = 1;

let a: foo; // a is zero-sized. This is valid, but not at all useful.
```


## Fixed-size arrays

```rust
let a: [i32; 3] = [1, 2, 3];
let b: [i32; 0] = [];
let b: [(); 2] = [(), ()];
```

Unlike in C, fixed-size arrays do not decay to pointers and can be passed by value like any other type. Depending on ABI, this can also mean that small arrays can be passed in registers, so do not hesitate to use them where it makes sense.

```rust
fn print_ipv4_addr(addr: [u8; 4]) {
    // ...
}

fn print_ipv4_addr(a: u8, b: u8, c: u8, d: u8) {
    // ...
}
```

## Tuples

Tuples are fixed-size collections of values of different types. They are defined using parentheses and a comma-separated list of types. Under the hood, tuples are just structs with unnamed fields.

```rust
let t: (i32, f64, bool) = (1, 2.0, true);
```

Tuples can be indexed using the dot syntax. The index can either be an integer literal or a constant expression (in which case it needs parentheses).

```rust
let x = t.0;
let y = t.1;
let z = t.(1 + 1);
```

Tuples can be unpacked (splatted) into another tuple using the `...` syntax.

```rust
let t = (1, 2, 3);
let q = (0, t..., 4);

// q = (0, 1, 2, 3, 4)
```

Tuples can be sliced using the range index syntax. The range index needs to be a constant expression. This is mostly useful for generic meta-programming (e.g. to handle the first element and recurse on the rest).

```rust
let t = (1, 2, 3, 4, 5);
let s = t.(1..3);

// s = (2, 3)
```


## Type aliases

```rust
type Int32 = i32;

let x: Int32 = 1;
```

Type aliases can be generic, for example:

```rust
struct Set<T> {}
type Set<T> = Map<T, ()>;
```

There are a small number of generic type aliases (called type operators) built in to the language. See [std::builtins](https://docs.alumina-lang.net/std/builtins) for the full list.

## Structs and unions

```rust
struct Point3D {
    x: f64,
    y: f64,
    z: f64,
}

union StringOrInt {
    string: [u8; 100]
    int: i32
}
```

Values of struct or union type can be created using a struct expression.

```rust
let p = Point3D { x: 1.0, y: 2.0, z: 3.0 };
let s = StringOrInt { int: 1337 };
```

Structs and unions can be generic, for example:

```rust
struct Point<T> {
    x: T,
    y: T,
}
```

## Enums

Enums are types that can take on one of a finite number of values.

```rust
enum Color {
    Red,
    Green,
    Blue,
}
```

Enum members can optionally have associated values. They must be constant expressions (see [Constants](#constants)) of an integer type. The underlying type of the enum is determined by the value of the first member and defaults to `i32` if no values are specified.

The underlying value of an enum member can be retrieved by casting.

```rust
enum Boolean {
    False = 0u8,
    True = 1u8,
}

fn to_std(v: Boolean) -> bool {
    switch v {
        Boolean::True => true,
        Boolean::False => false,
        _ => unreachable!(),
    }
}

assert_eq!(Boolean::True as u8, 1);
```

Enums cannot be generic, but are otherwise first-class types and can have their own `impl` blocks.

## Impl blocks

Named types can have associated methods (most commonly constructors and methods). They are defined using the `impl` blocks.

```rust
struct Point {
    x: f64,
    y: f64,
}

impl Point {
    fn distance_from_origin(self: &Point) -> f64 {
        (self.x * self.x + self.y * self.y).sqrt()
    }
}

fn main() {
    let p = Point { x: 1.0, y: 2.0 };
    println!("{}", p.distance_from_origin());

    // Also valid:
    // println!("{}", Point::distance_from_origin(&p));
}
```

Note that associated functions are only loosely bound to their types. They can be thought as modules whose items are automatically imported in scope. Associated functions can be generic, for example:

```rust
struct Point<T> {
    x: T,
    y: T,
}

impl Point {
    fn distance_from_origin<T>(self: &Point<T>) -> T {
        (self.x * self.x + self.y * self.y).sqrt()
    }
}
```

When a type is generic, it is often the case that most methods will be generic with the same type parameters and maybe additional ones. For this reason, the common type parameters can be placed on the `impl` block itself. This is just a syntactic shortcut and does not change the nature of the associated functions.

```rust
struct Point<T> {
    x: T,
    y: T,
}

impl Point<T> {
    fn rotate_180deg(self: &Point<T>) -> Point<T> {
        Point { x: -self.x, y: -self.y }
    }

    fn distance_from_origin(self: &Point<T>) -> T {
        (self.x * self.x + self.y * self.y).sqrt()
    }
}

let point = Point { x: 1.0, y: 2.0 };

let rotated = Point::rotate_180deg::<f64>(&point);
// Not `Point::<f64>::rotate_180deg(&point);`
```

## Type attributes

Named types can have attributes.

- `#[align(n)]` specifies the minimum alignment of the type. Alignment must be a power of two.
- `#[packed]` on a struct specifies that the type should be packed (no padding between fields).
- `#[transparent]` on structs and unions with a single field specifies that the type should be treated as if it were the type of the field from the ABI perspective. This is useful for newtypes.
- `#[diag::must_use]` on a struct or enum specifies that the type must be used in some way. Currently this is used in the standard library on `Result` types to ensure that the user does not forget to handle errors. Raises a warning if the value is not used.

## Slices

Slices are "fat" pointers representing a contiguous sequence of elements in memory. They consist of the pointer to the first element and the length of the sequence. Slices can be either mutable (`&mut [T]`) or const (`&[T]`).

Slices can be created in various ways, most commonly by coercion from arrays, dynamic memory allocation or from a raw pointer.

```rust
let t1: &[i32] = &[1, 2, 3];
let t2: &mut [u8] = std::mem::slice::alloc(1024);

println!("{}", t2.len()); // 1024
```

Slices can be indexed like arrays and also sliced using the range index syntax.

```rust
let t: &[i32] = &[1, 2, 3, 4, 5];
let e = t[0]; // 1
let s = t[1..3]; // [2, 3]
```

The syntax for slices (`&[T]`) implies that it is a kind of pointer to some `[T]` type. Unlike Rust, this is **NOT** the case in Alumina and `[T]` is simply invalid syntax. Under the hood slices are [just a struct](https://docs.alumina-lang.net/std/mem/slice.html) with a pointer to the first element and a length. They are commonly passed around by value, as they already contain a pointer inside.

Collection types that are a backed by contiguous memory (e.g. [`Vector`](https://docs.alumina-lang.net/std/collections/Vector.html)) can be indexed directly without converting to a slice first. See [`AsSlice`](https://docs.alumina-lang.net/std/mem/AsSlice.html) and [`AsSliceMut`](https://docs.alumina-lang.net/std/mem/AsSliceMut.html) for more details.

```rust
use std::collections::Vector;

let v = Vector::from_slice(&[1, 2, 3, 4, 5]);

v[0] = v[4];
```

## What about strings?

Alumina does not have a native string type. String literals in the source code are converted to const slices of bytes (`&[u8]`). They are not guaranteed to be zero-terminated. See [`ffi` module](https://docs.alumina-lang.net/std/ffi/) for utilities needed when interacting with C APIs.

[Standard string functions](https://docs.alumina-lang.net/std/string) are generally not Unicode-aware, unless explicitly marked as such. However, if the source code contains non-ASCII characters in string literals, they will be represented as UTF-8 bytes. String literals are not required to be valid UTF-8 (such strings have to use character escapes though, as the source code itself has to be valid UTF-8).


## Zero-sized types

Alumina has first-class support for zero-sized types. The most common one is `()` (a.k.a. `void`), but there are others:

- Zero-length arrays (`[T; 0]`)
- Arrays any length with zero-sized elements (`[(); 1337]`)
- Tuples of zero-sized types (e.g. `((), ((), (((()))), ())`)
- Structs and unions with no fields (`struct Foo {}`)
- Structs and unions with only zero-sized fields (`struct Foo { a: (), b: () }`)
- Named function types (see below)
- Never type (`!`)

During compilation all memory loads and stores of zero-sized values are optimized away. This can be a powerful mechanism in generic context. An example from the standard library is the [`HashSet<T>` type](https://docs.alumina-lang.net/std/collections/HashSet.html), which is just a wrapper around a [`HashMap<T, ()>`](https://docs.alumina-lang.net/std/collections/HashMap.html). As the value type parameter is zero-sized, it incurs no space overhead and the optimizer can remove all loads and stores of the value.

Most zero-sized types are unit types (they contain only a single value). An exception to this is the never type, which is an empty / uninhabited type since having a value of this type would mean that an expression that was supposed to never return actually returned.

Named function types are a family of unit types, each only containing the specific function. This can be used for tricks like this:

```rust
use std::builtins::NamedFunction;

fn hello() {
    println!("Hello");
}

fn invoke<F: NamedFunction + Fn()>() {
    let f = std::util::unit::<F>(); // `unit` produces the only value of a unit type out of thin air
    f();
}

// We can pass hello as a type parameter rather than as a value
invoke::<hello>();
```

### Layout implications of zero-sized types

When zero-sized types are used in aggregates, such as structs, unions and tuples, their layout is usually equivalent to as if the ZST field was not present at all. However, if a ZST has alignment greater than 1, it can affect the layout of the aggregate.

Common ZSTs such as `()` and function types all have alignment of 1. The following are the exception

- `[T; 0]` has the same alignment as `T` (e.g. `[u8; 0]` has alignment of 1, but `[u64; 0]` has alignment of 8)
- Any struct or union with a `#[align(X)]` attribute where X > 1 (e.g `#[align(8)] struct Empty {}`)
- Any zero-sized composite (struct, union, array, tuple) that contains some of the above

```rust
use std::mem::{size_of, align_of};

assert_eq!(size_of::<[u64; 0]>(), 0);
assert_eq!(align_of::<[u64; 0]>(), 8);

struct S1 { b: [u64; 0] }

assert_eq!(size_of::<S1>(), 0);
assert_eq!(align_of::<S1>(), 8);

struct S2 { a: u8, b: [u64; 0] }

assert_eq!(size_of::<S2>(), 8); // size has to be a multiple of alignment, so padding is added
assert_eq!(align_of::<S2>(), 8);
```

# Macros

Alumina supports expression macros that are usually used to encapsulate code that affects the program flow on the caller side. They are invoked like functions, but with the `!` suffix.

```rust
macro error_check!($cond) {
    let cond = $cond; // Prevent multiple evaluation
    if cond == -1 {
        return *libc::__errno_location();
    } else {
        cond
    }
}

fn open_and_close_file(filename: &libc::c_char) -> libc::c_int {
    let fd = error_check!(libc::open("/dev/null", libc::O_RDONLY));

    error_check!(libc::close(fd));

    0
}
```

Macros are hygienic, meaning that they cannot refer to items not accessible in the scope of the macro definition or declare new named items that would be accessible outside the macro. They can however, for example, access local variables if they are defined in a linear scope after the appropriate `let` binding.

```rust
fn main() {
    let counter = 0;

    macro inc() {
        counter += 1;
    }

    inc!();
    println!("{}", counter); // 1
    inc!();
    println!("{}", counter); // 2
    inc!();
    println!("{}", counter); // 3
}
```

Macros can be invoked as a function or with the universal call syntax (like it was a method of the first argument).

```rust
macro add($a, $b) {
    $a + $b
}

// The following are equivalent:
add!(1, 2);
1.add!(2);
```

Macros can be variadic (accept an arbitrary number of arguments). The extra arguments can be unpacked into expressions with `$...` postfix operator where this is meaningful: function arguments, tuple expressions and array expressions as well as as statements.

```rust
macro make_array($a...) {
    [$a$...]
}

let arr = make_array!(1, 2, 3);
```

The placeholder during unpacking can also be in a subexpression.

```rust
macro u128_tuple($a...) {
    (($a as u128)$...)
}

assert_eq!(
    u128_tuple!(1u8, 2u16, 3u32, 4u64),
    (1u128, 2u128, 3u128, 4u128)
);
```

As macros operate on the AST level, they are not quite first-class citizens, however, a "reference to a macro" can be passed as a parameter to another macro.

```rust
macro echo($arg) {
    println!("{}", $arg);
}

macro foreach($f, $arg...) {
    $f!($arg)$...;
}

// 1
// 2
// 3
foreach!(
    echo, // macro "pointer"
    1,
    2,
    3
);
```

# Statements and expressions

In Alumina "everything is an expression" (except statements that introduce new named items, such as `let` bindings or named type definitions). For example, one can write

```rust
fn foo() {
    let a = loop { if 1 > 0 { break 10; } }; // a = 10
    let b = if true { 1 } else { 2 }; // b = 1
    let c = (b = 3); // c = ()
    let d = {
        println!("foo");
        println!("bar");
        3
    }; // d = 3
}
```

Alumina has the following types of expressions

- unit/void expression (`()`)
- literals (`1`, `"foo"`, `true`, `false`, `null`, ...)
- block expressions: `{ statements; ret }`
- function calls ( `expr(arg1, arg2)` )
- field expressions (`expr.field`)
- array/slice index expressions (`expr[0]`)
- try operator (`expr?`)
- unary operations (`-expr`, `~expr`)
- casts (`expr as typ`)
- type checks (`expr is typ`)
- multiplication and division (`lhs * rhs`, `lhs / rhs`),
- addition and subtraction (`lhs + rhs`, `lhs - rhs`)
- bitwise shift (`expr << n`, `expr >> n`)
- bitwise AND (`lhs & rhs`),
- bitwise XOR: (`lhs ^ rhs`),
- bitwise OR: (`lhs | rhs`)
- comparison: (`lhs == rhs`, `lhs < rhs`, ...),
- boolean AND: (`lhs && rhs`)
- boolean OR: (`lhs || rhs`)
- address-of (reference) and dereference (dereference) (`&expr`, `*expr`)
- [range expressions](https://docs.alumina-lang.net/std/range) (`lower..upper`, `lower..=upper`)
- tuple index expressions (`expr.0`, `expr.1`, ..., `expr.(1 + 2)`)
- tuple range index expressions (`expr.(0..2)`, `expr.(1..=2)`, `expr.(..2)`, `expr.(1..)`, `expr.(..)`)
- assignment (`lhs = rhs`, `lhs += rhs`, ...),
- closure: `|args| body`
- loops: (`loop { ... }`, `while cond { ... }`, `for x in range { ... }`)
- static for loop: `for const x in 0..10 { ... }`
- struct expressions: `Point { x: 1, y: 2 }`
- tuple expressions: `(1, 2)`
- array expressions: `[1, 2, 3]`
- if: `if cond { body } else { body }`
- when expressions: `when cond { body } else { body }`
- switch: `switch expr { ... }`
- [defer](#defer-expressions): `defer expr`
- return: `return expr`
- yield: `yield expr`
- break: `break expr`
- continue: `continue`

The binary operations should be familiar to C programmers and follow mostly the same rules, except for the following:

- For arithmetic operations the left-hand side and right-hand side must have the same type. There is no automatic promotion to `int`.
- Similarly, boolean operations only work on `bool` values rather than all integers with 0 as false and all other integers as true.
- Assignment expression evaluates to `()` (void) rather than the value of the assignment

## Variables

Variables are declared with a `let` statement. If declaration is combined with initialization, the type can be omitted, but can also be specified for clarity or when the type of the initializer expression is ambiguous. Variables are always mutable (there is no `let mut` like in Rust).

```rust
let a: i32;
let b = 5;
let c: i32 = 5;
```

If the initializer returns a tuple, it can be unpacked using the `let` statement.

```rust
let (x, y) = (1, 2);
let (x, y): (i32, i32) = (1, 2); // with type annotation
```

## Loops

The most basic loop is the unconditional (infinite) loop

```rust
loop {
    println!("Hello, world!");
}
```

Loop can be broken out of using a `break` expression. Break expressions can optionally take a value which will be used as the value of the whole loop expression.

```rust
use std::random::thread_rng;
let small_number = loop {
    let val = thread_rng().next_float();
    if val < 0.001 {
        break val
    }
}
```

Other types of loops are the `while` loop and the `for` loop

```rust
let i = 0;
while i < 10 {
    i += 1;
}
```

`for` loops are used with iterable types, such as slices and [ranges](https://docs.alumina-lang.net/std/range). See the [std::iter](https://docs.alumina-lang.net/std/iter) module for more information on iterators.

```rust
for i in 0..10 {
    println!("{}", i);
}

for w in ["hello", "world"] {
    println!("{}", w);
}
```

`for i in iterable { body; }` is syntactic sugar for the following loop:

```rust
let tmp1 = iterable.iter();
loop {
    let tmp2 = tmp1.next();
    if tmp2.is_some() {
        let i = tmp2.unwrap();
        body;
    } else {
        break;
    }
}
```

If the iterator returns a tuple, it can be unpacked in the for expression, for example

```rust
let elems = [(1, 2), (2, 3), (3, 4)];
for (x, y) in elems {
    println!("{} {}", x, y);
}
```

## Auto-ref and rvalue promotion

Field access and method calls do not require explicit dereferencing if the operand is a pointer (or multiple pointer).

```rust
struct Foo { bar: i32 }

impl Foo {
    fn by_value(self: Foo) { print!("hey"); }
    fn by_ptr(self: &Foo) { print!("hey"); }
    fn by_pptr(self: &&Foo) { print!("hey"); }
    fn by_ppptr(self: &&&Foo) { print!("hey"); }
}

let foo = Foo { bar: 10 };
let foo_p = &foo;
let foo_pp = &foo_p;
let foo_ppp = &foo_pp;

println!("{}", foo.bar);
println!("{}", foo_p.bar);
println!("{}", foo_pp.bar);
println!("{}", foo_ppp.bar);

foo_ppp.by_ppptr();
foo_ppp.by_pptr();
foo_ppp.by_ptr();
foo_ppp.by_value();

/* ... */
```

Alumina allows a reference to be taken of any expression, including rvalues. If the referencee is an rvalue, the expression will be promoted to a temporary variable that is valid for the duration of the enclosing function (not block!).

```rust
let one_ptr = &(1 + 1);
let two_ptr = &(2 + 2);
let three = *one_ptr + *two_ptr;
```

That allows the above example to work in the other direction too.

```rust
/* ... */

foo.by_value();
foo.by_ptr();
foo.by_pptr();
foo.by_ppptr();
```

## Function calls

Alumina supports unified function call syntax for functions in scope. That means that any free function can be called as if it were a method of the first argument with the remaining arguments as arguments. Auto-ref is used in the same manner, so the type of the first argument in the signature can be a (multiple) pointer of the callee or vice versa.

```rust
fn add_one(x: i32) -> i32 {
    x + 1
}

fn add_one_by_ref(x: &i32) -> i32 {
    *x + 1
}

fn main() {
    println!("{}", 1.add_one());
    println!("{}", 10.add_one_by_ref());
}
```

Generic functions are called with the so-called "turbo-fish" syntax when the type parameters need to be explicitly specified.

```rust
fn cast<T, U>(t: T) -> U {
    t as U
}

let a = cast::<i32, i64>(1);
let b: i64 = cast(1); // Turbofish not necessary as the types are inferred
```

## Try expression

Try operator is a postfix operator that is used in order to short-circuit the current function if the expression represents an error or a missing value in some sense. It is most commonly used with the [Result](https://docs.alumina-lang.net/std/result/) and [Option](https://docs.alumina-lang.net/std/option) types.

Under the hood, it simply de-sugars to the `try` macro invocation. The following are equivalent:

```rust
let a = Option::some(1);

a?;
try!(a);
```

This works in any scope by default since `try` is an item in [the prelude](https://docs.alumina-lang.net/std/prelude). A custom `try` macro can also be provided which will work when `?` expression is used.

```rust
macro try($a) {
    panic!("No. Try not. Do... or do not. There is no try.");
}

let a = "hello world";
a?; // panics
```

## Switch expressions

Switch expressions are syntactic sugar for an if-else chain.

```rust
let a = 5;
let b = switch a + 1 {
    1 => "one",
    2 => "two",
    3 => "three",
    _ => "many",
};
```

Is equivalent to
```rust
let a = 5;

let tmp = a + 1; // evaluated only once
let b = if tmp == 1 {
    "one"
} else if tmp == 2 {
    "two"
} else if tmp == 3 {
    "three"
} else {
    "many"
};
```

## Defer expressions

Defer expressions are used to delay the evaluation of an expression until the end of the current function (not scope/block!)

```rust
fn main() {
    defer println!("world!");
    println!("Hello, ");
}
// prints "Hello, world!"
```

`defer` expressions will execute in reverse order of declaration (not execution) and will execute only a single time (not safe to use in loops). They are primarily meant as a convenient way to clean up resources (e.g. free memory, close files) when a function returns can return early.


## Anonymous functions and closures

Syntax for anonymous functions is `|args| -> ret { body }`. If the return type is void, it can be omitted, but the braces are always required.

```rust
let a = |x: i32| -> i32 { x + 1 };
let b = |x: i32| { println!("You are {} years old", x); };
```

Closures can be created by specifying the variables that are captured by the closure explicitly. They can either be captured by reference or by value.

```rust
// Capture by value (copy)
let a = 5;
let b = |=a, x: i32| -> i32 { a + x };

println!("{}", b(10)); // 15
```

```rust
// Capture by reference
let a = 5;
let b = |&a, x: i32| { a += x; };

b(10);
println!("{}", a); // 15
```

Anonymous function expressions have an unnameable type, but non-closures can be coerced to function pointers. Closures cannot be, so the functions accepting closures as parameters will usually have to be generic.

```rust
fn accepts_fn(f: fn(i32) -> i32) {
    println!("{}", f(10));
}

accepts_fn(|x: i32| -> i32 { x + 1 });
```

```rust
fn accepts_closure<F>(f: F) {
    println!("{}", f(10));
}

let increment = 1;
accepts_closure(|=increment, x: i32| -> i32 { x + increment });
```

# Protocols and mixins

Protocols can be used to constrain the type parameters in generic items. Their main purpose is make the requirements of generic items more explicit, have better compile error messages and as an aid to type inference. Protocols are also the basis for mixins and `dyn` pointers (virtual dispatch).

They are similar to [C++ concepts](https://en.cppreference.com/w/cpp/language/constraints), though much more limited.

Protocols are defined with `protocol` keyword and the list of function signatures that types must implement. Protocols can be generic and by convention the first type parameter is `Self`, referring to the type that implements the protocol.

```rust
protocol Additive<Self> {
    fn zero() -> Self;
    fn add(self: Self, other: Self) -> Self;
    fn sub(self: Self, other: Self) -> Self;
}
```

There is no annotation needed on the types for them to satisfy a protocol. If they have the methods with appropriate signatures, they match. Items' generic type parameters can be constrained to those that implement the protocol.

```rust
struct FancyInt {
    inner: i32
}

impl FancyInt {
    fn new(inner: i32) -> FancyInt {
        FancyInt { inner: inner }
    }

    fn zero() -> FancyInt {
        new(0)
    }

    fn add(self: FancyInt, other: FancyInt) -> FancyInt {
        new(self.inner + other.inner)
    }

    fn sub(self: FancyInt, other: FancyInt) -> FancyInt {
        new(self.inner - other.inner)
    }
}

fn sum<T: Additive<T>>(slice: &[T]) -> T {
    let mut result = T::zero();
    for item in slice {
        result = result.add(item);
    }
    result
}

let s = sum(&[FancyInt::new(1), FancyInt::new(2), FancyInt::new(3)]);

println!("{}", s.inner); // 6
```

Protocols can provide so-called default implementations. They can be used on the types with the `mixin` keyword, but types are also free to implement them in a custom way. Directly implemented methods have precedence over ones provided by the protocol.

```rust
protocol Random<Self> {
    fn next_u32(self: &mut Self) -> u32;

    fn next_u64(self: &mut Self) -> u64 {
        (self.next_u32() as u64) << 32 | (self.next_u32() as u64)
    }

    fn next_u128(self: &mut Self) -> u128 {
        (self.next_u64() as u128) << 64 | (self.next_u64() as u128)
    }
}

struct XkcdRandom {}

impl XkcdRandom {
    fn next_u32(self: &mut XkcdRandom) -> u32 {
        4  // chosen by fair dice roll.
           // guaranteed to be random.
    }

    mixin Random<XkcdRandom>;
}

use std::fmt::hex;

let x = XkcdRandom {};

println!("0x{}", x.next_u64().hex()); // 0x400000004
println!("0x{}", x.next_u128().hex()); // 0x4000000040000000400000004
```

Protocol methods are usually not generic themselves, the type parameters come from the enclosing protocol. If the protocol contains generic methods, it can only be used as a mixin and not as a generic bound.

There are a number of protocols that are built-in to the language. For the full list see [`std::builtins` module](https://docs.alumina-lang.net/std/builtins/). Multiple protocol bounds can be specified by separating them with `+` and negated with `!`.

```rust
use std::builtins::{Primitive, ZeroSized};

/// Return the number of elements that can fit into
/// a buffer of `size` bytes.
///
/// Not meaningful for zero-sized types.
fn buffer_capacity<T: Primitive + !ZeroSized>(size: usize) -> usize {
    // TODO: take alignment into account
    size / size_of::<T>()
}

println!("{}", buffer_capacity::<u32>(16)); // 4
```

[`Callable` protocol](https://docs.alumina-lang.net/std/builtins/Callable.html) that matches function-like objects with a given signature can also be used with the special syntax `Fn(Args) -> Ret` that resembles function pointers. The following two are equivalent:

```rust
use std::builtins::Callable;

fn call1<T, F: Callable<(T), T>>(f: F, x: T) -> T {
    f(x)
}

fn call2<T, F: Fn(T) -> T>(f: F, x: T) -> T {
    f(x)
}
```

Protocols can have constraints themselves. This is a common pattern to achieve protocol "inheritance", for example [`Comparable`](https://docs.alumina-lang.net/std/cmp/Comparable.html) requires that the type satisfies the [`Equatable`](https://docs.alumina-lang.net/std/cmp/Equatable.html) protocol.

```rust
protocol Foo<Self> {
    fn foo() -> Self;
}

protocol Bar<Self: Foo<Self>> {
    fn bar() -> Self;
}
```


# Other topics

## String formatting

Alumina has a built-in string formatting macro [`format_args!`](https://docs.alumina-lang.net/std/fmt/format_args.html) that can be used to format strings using a template (format string) and arguments at compile time. It is usually not used directly, but rather through a variety of other convenience macros defined in the standard library, such as

- [`print!`](https://docs.alumina-lang.net/std/fmt/print.html) and [`println!`](https://docs.alumina-lang.net/std/fmt/println.html) for printing to stdout
- [`eprint!`](https://docs.alumina-lang.net/std/fmt/eprint.html) and [`eprintln!`](https://docs.alumina-lang.net/std/fmt/eprintln.html) for printing to stderr
- [`write!`](https://docs.alumina-lang.net/std/fmt/write.html) and [`writeln!`](https://docs.alumina-lang.net/std/fmt/writeln.html) for writing into a custom "formatter" (e.g. a stream or a file)
- [`format!`](https://docs.alumina-lang.net/std/fmt/format.html) (allocating) and [`format_in!`](https://docs.alumina-lang.net/std/fmt/format_in.html) (non-allocating) for constructing string buffers

```rust
println!("Hello, {}! You are {} years old.", "Alice", 20);
let s = format!("Hello, {}! You are {} years old.", "Bob", 35);
defer s.free()

eprintln!("{}", s);
```

The format string has to be a constant string literal with `{}` placeholders where the arguments should be inserted. The arguments can be any expression that implements the [`std::fmt::Formattable`](https://docs.alumina-lang.net/std/fmt/Formattable.html) protocol. For example, to make a custom type formattable, you can implement the `Formattable` protocol for it:

```rust
struct Point3D {
    x: i32,
    y: i32,
    z: i32
}

impl Point3D {
    use std::fmt::{Formatter, Result, write};

    fn fmt<F: Formatter<F>>(self: &Point3D, f: &mut F) -> Result {
        write!(f, "({}, {}, {})", self.x, self.y, self.z)
    }
}

println!("You are at {}", Point3D { x: 1, y: 2, z: 3 }); // "You are at (1, 2, 3)"
```

`{}` is the only placeholder that is supported. The standard way to customize the display of an argument is with wrapper/adapter types, for example to format the number as hexadecimal:

```rust
use std::fmt::hex;

println!("The number is {}", 0xdeadbeef.hex());
```

There is a built-in adapter [debug](https://docs.alumina-lang.net/std/builtins/fmt.html#item.debug) that can print most values without them needing to implement the `Formattable` protocol. This is useful for debugging and logging, but may not always be the canonical or most user-friendly output.

```rust
use std::fmt::debug;

struct Point3D {
    x: i32,
    y: i32,
    z: i32
}

println!("{}", Point3D { x: 1, y: 2, z: 3 }.debug()); // "Point3D { x: 1, y: 2, z: 3 }"
```

## Type coercion

Values of certain types can be coerced to other types without requiring an explicit conversion or cast.

- Named functions to function pointers
- Mutable pointers to const pointers (`&mut T` to `&T`)
- Mutable slices to const slices (`&mut [T]` to `&[T]`)
- Pointers to fixed-size arrays to slices (`&[T; N]` to `&[T]` and `&mut [T; N]` to `&mut [T]`)
- Mutable `dyn` pointers to const `dyn` pointers (`&mut dyn Protocol` to `&dyn Protocol`)
- Never type (`!`) to any other type

For example

```rust
let a: [i32; 5] = [1,2,3,4,5]
let b: &[i32] = &a;
```

## Conditional compilation

Items with the `#[cfg(...)]` will only be compiled when the compiler is invoked with the specified configuration, for example:

```rust
#[cfg(target_os = "linux")]
fn main() {
    println!("Hello, Linux!");
}

#[cfg(target_os = "macos")]
fn main() {
    println!("Hello, MacOS!");
}

#[cfg(target_os = "windows")]
fn main() {
    compile_fail!("Not yet :) Stay tuned!")
}
```

Conditions can be combined using the `all`, `any`, and `not` specifiers.
```rust
#[cfg(all(any(target_os = "linux", target_os = "macos"), not(target_arch = "x86_64")))]
fn main() {
    println!("Hello, fellow MacOS or Linux user not using an x86_64 architecture!");
}
```

`#[cfg(...)]` attributes can be used on any items as well as on multiple items without having to repeat the condition for each item.

```rust
#[cfg(any(target_os = "linux", target_os = "macos", target_os = "android"))]
{
    const POSIX: bool = true;
    const WINDOWS: bool = false;
}
```

They can also be used on statements

```rust
fn fill_with_random_bytes(buf: &mut [u8]) {
    #[cfg(any(target_os = "linux", target_os = "android"))]
    libc::getrandom(&buf[0], buf.len(), 0);

    #[cfg(target_os = "macos")]
    libc::getentropy(&buf[0], buf.len());
}
```

`#[cfg_attr(cond, ...)]` can be used to apply attributes to items based on the configuration.

For example, to change the symbol name for the import on MacOS:

```rust
#[cfg_attr(target_os="macos", link_name("_opendir$INODE64"))]
extern "C" fn opendir(dirname: &c_char) -> &mut DIR;
```

## `typeof` type

`typeof` is a keyword that can be used to specify the type from a type of any expression.

```rust
fn double<T>(val: T) -> typeof(val + val) {
    val + val
}

let x = 1;
```

`typeof` can be useful for specifying the return type of generic functions. The expression is type-checked, but not executed, so it is fine to use uninitialized variables and `null` pointers to express values of the desired type.

```rust
type iterable_yield_t<T> = typeof({ let t: T; t.iter().next().unwrap() });

fn first_element<T>(it: T) -> iterable_yield_t<T> {
    it.iter().next().unwrap()
}

let x = [1, 2, 3];
println!("{}", x.first_element()); // 1
```

## Reflection and specialization

Alumina has a rich compile-time reflection system that can be used to inspect the types and values at compile time and generate specialized code based on that information. The most common use case is to generate code for different types based on the type parameter of a generic function.

`when` expressions (static `if`) can be used to conditionally compile code that based on a condition that is constant at compile time. Unlike `#[cfg(...)]` attributes which are evaluated very early in the compilation process, `when` expressions run at monomorphization time, which means that the type information is already available.

Unlike `if` expressions, the non-taken branch is not monomorphized, so it can contain code that would not otherwise type check. The most common usage is as a means of generic specialization (different behavior based on the generic parameter).

```rust
use std::typing::{is_same, is_unsigned, is_pointer, is_zero_sized};

fn print_type<T>() {
    when is_same::<T, u8>() {
        println!("u8");
    } else when is_unsigned::<T>() {
        println!("some other unsigned type");
    } else when is_pointer::<T>() {
        print!("pointer to ");
        print_type::<*T>(); // this would not compile if T was not a pointer
    } else when !is_zero_sized::<T>() {
        println!("some sized type");
    } else {
        compile_fail!("zero-sized types are not supported");
    }
}

print_type::<u8>(); // "u8"
print_type::<&&u16>(); // "pointer to pointer to some other unsigned type"
print_type::<Option<i32>>(); // ""some sized type"
```

Similarly, a `when` type in type context to select the appropriate type

```rust
use std::typing::pointer;

type ensure_pointer_t<T> = when is_pointer::<T>() { T } else { &T };

let x: ensure_pointer_t<u8> = &5;
let y: ensure_pointer_t<&&u16> = &&5;
let z: ensure_pointer_t<Option<i32>> = &Some(5);
```

`for const` loops can be used to iterate over a range of values at compile time. The loop variable is a constant value, so it can be used in type context or e.g. as a tuple index.

```rust
let a = ("hello", 1, true);

for const i in 0usize..a.len() {
    println!("{}", a.(i));
}
```

Under the hood, the loop is unrolled and the body is repeated for each value in the range. `break` and `continue` are not supported in `for const` loops.

As a more complete example, consider a function that sets a field on a struct by name (which does not need to be a compile-time constant) using the reflection utilities in [`std::typing`](https://docs.alumina-lang.net/std/typing) module.

```rust
use std::typing::Type;
use std::builtins::{Struct, Union};

/// Set a field on an struct by name
fn set<T: Struct | Union, F>(obj: &mut T, name: &[u8], value: F) {
    let ty = Type::new::<T>();
    let value_ty = Type::new::<F>();

    let fields = ty.fields();
    for const i in 0usize..fields.len() {
        let field_ty = fields.(i).type();

        if fields.(i).name() == Option::some(name) {
            when field_ty.is_same_as(value_ty) {
                *fields.(i).as_mut_ptr(obj) = value;
                return;
            } else {
                panic!(
                    "expected type {}, got {}",
                    field_ty.debug_name(),
                    value_ty.debug_name()
                );
            }
        }
    }

    panic!("field not found: {}", name);
}

struct Foo {
    bar: i32,
    quux: bool,
}

let foo: Foo;
foo.set("bar", 42);
foo.set("quux", true);

// These would panic at runtime
// foo.set("bar", true);
// foo.set("unknown", 42);

println!("bar = {}", foo.bar);
println!("quux = {}", foo.quux);
```

The `when` expression is used to select the appropriate branch based on the actual type of the field. Most reflection operations are at zero runtime cost, though they may increase the binary size to include various type metadata, such as field names and attributes.

After monomorphization, the loop is unrolled and the body is repeated for each field in the struct, so with optimizations the above example is mostly equivalent to hand-written:

```rust
fn set__i32(obj: &mut Foo, name: &[u8], value: i32) {
    if name == "bar" {
        obj.bar = value;
        return;
    }
    if name == "quux" {
        panic!("expected type bool, got i32");
    }
    panic!("field not found: {}", name);
}

fn set__bool(obj: &mut Foo, name: &[u8], value: bool) {
    if name == "bar" {
        panic!("expected type i32, got bool");
    }
    if name == "quux" {
        obj.quux = value;
        return;
    }
    panic!("field not found: {}", name);
}

fn main() {
    let foo: Foo;
    set__i32(&mut foo, "bar", 42);
    set__bool(&mut foo, "quux", true);
}
```

## Unit testing

Alumina has a built-in minimal unit test framework. All the methods with `#[test]` attribute will be collected during compilation and run during the test phase. To exclude test methods when the program is compiled normally, use the `#[cfg(test)]` attribute. Like in rust, it is conventional to have the test methods in the same file as the module under test but in a submodule named `tests`.

```rust
fn add(x: i32, y: i32) -> i32 {
    x + y
}

fn sub(x: i32, y: i32) -> i32 {
    x - y
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_add() {
        assert_eq!(1.add(2), 3);
    }

    #[test]
    fn test_sub() {
        assert_eq!(1.sub(2), -1);
    }

    #[test]
    #[test::should_panic]
    fn test_panic() {
        panic!("oops");
    }
}
```

## Dyn pointers

The common way to achieve polymorphism in Alumina is using generics (static polymorphism). This is preferred as it usually leads to better performance (e.g. since monomorphized functions can be inlined), but can also lead to an explosion of program size.

Another issue is that generics are viral. Structs that want to contain generic fields, functions that accept generic arguments must be generic as well all the way to the top.

This can can be achieved by using `dyn` pointers. A `dyn` pointer is a "fat" pointer that contains a type-erased (`&void`) pointer to the underlying concrete object and a pointer to the virtual method table so that methods on it can be invoked without knowing the concrete type.

`dyn` pointers are always paired with the protocol that the types implement, for example:

```rust
protocol Greeter<Self> {
    fn greet(self: &Self);
}

struct Howdy {}
impl Howdy {
    fn greet(self: &Howdy) {
        println!("Howdy!");
    }
}

struct Hello {}
impl Hello {
    fn greet(self: &Hello) {
        println!("Hello!");
    }
}

let howdy = Howdy {};
let hello = Hello {};

let dynamic: &dyn Greeter<Self> = &howdy;
dynamic.greet(); // "Howdy!"

dynamic = &hello;
dynamic.greet(); // "Hello!"
```

Since the pointer to the vtable is stored in the `dyn` pointer itself, no size overhead is incurred when the structs are used in a non-dynamic manner. Like slices, `dyn` pointers are [just structs under the hood](https://docs.alumina-lang.net/std/typing/dyn.html).

Not all protocols are compatible with dynamic dispatch. Specifically, all methods on a protocol must have a pointer to self (of either mutability) as the first argument and the `Self` type cannot appear anywhere else in the signature.

Dyn pointers can also be used with multiple protocols with the `&dyn (A + B + ...)` syntax. Currently the order of the protocols is important. `&dyn (A + B)` is not the same type as `&dyn (B + A)`.

```rust
protocol Hello<Self> {
    fn hello(self: &Self);
}

protocol Goodbye<Self> {
    fn goodbye(self: &Self);
}

struct  Greeter {}
impl Greeter {
    fn hello(self: &Greeter) {
        println!("Hello!");
    }
    fn goodbye(self: &Greeter) {
        println!("Goodbye!");
    }
}

let greeter = Greeter {};
let dynamic: &dyn (Hello<Self> + Goodbye<Self>) = &greeter;

dynamic.hello(); // "Hello!"
dynamic.goodbye(); // "Goodbye!"
```

Dyn pointers cannot currently be used with builtin protocols, such as `Fn(Args) -> Ret`.


## Operator overloading

Alumina has limited support for operator overloading. Currently only comparison operators (`==`, `!=`, `<`, `<=`, `>`, `>=`) can be overloaded. This is achieved by implementing the [std::cmp::Equatable](https://docs.alumina-lang.net/std/cmp/Equatable.html) and [std::cmp::Comparable](https://docs.alumina-lang.net/std/cmp/Comparable.html) protocols.

```rust
use std::cmp::{Equatable, Comparable, Ordering};

struct FancyInt {
    inner: i32,
}

impl FancyInt {
    fn equals(self: &FancyInt, other: &FancyInt) -> bool {
        self.inner == other.inner
    }

    fn compare(self: &FancyInt, other: &FancyInt) -> Ordering {
        self.inner.compare(&other.inner)
    }

    mixin Equatable<FancyInt>;
    mixin Comparable<FancyInt>;
}

assert!(FancyInt { inner: 1 } < FancyInt { inner: 2 });
assert!(FancyInt { inner: 3 } == FancyInt { inner: 3 });
```

`Equatable` and `Comparable` protocols may be automatically derived for sufficiently simple types (i.e. enums and structs where all fields are `Equatable` or `Comparable`) by using [`DefaultEquatable`](https://docs.alumina-lang.net/std/cmp/DefaultEquatable.html) and [`LexicographicComparable`](https://docs.alumina-lang.net/std/cmp/LexicographicComparable.html) mixins.

For structs the comparison will be field-wise in order of definition.

```rust
use std::cmp::{DefaultEquatable, LexicographicComparable};

struct Point {
    x: i32,
    y: i32,
}

impl Point {
    mixin DefaultEquatable<Point>;
}

struct Date {
    year: i32,
    month: i32,
    day: i32,
}

impl Date {
    mixin LexicographicComparable<Date>;
}

assert!(Point { x: 1, y: 2 } == Point { x: 1, y: 2 });
assert!(Date { year: 2021, month: 1, day: 2 } < Date { year: 2021, month: 2, day: 1 });
```

# Miscellaneous

## Lints (warnings)

Alumina has a small number of compile-time warnings for code that is not invalid per se but may be a sign of a bug or a potential performance issue. Lints emit a compile-time warning enabled by default and can be disabled with the `#[allow(lint_name)]` on whichever scope enclosing the code that triggers the lint.

The innermost scope takes precedence, so if a lint is disabled on a function, it will be disabled for the entire function body, but for example it can be re-enabled for a specific statement.

Similarly, lints can be turned into errors with the `#[deny(lint_name)]` attribute.

Lints can be globally disabled with `-Zallow-warnings` or denied with `-Zdeny-warnings` command line flags. When an attribute is used to disable or deny a lint, it overrides the global setting.

Common lints:
 - `defer_in_a_loop` - A `defer` statement is used in a loop. See [this section](#defer-expressions) for more details.
 - `uninitialized_field` - A field is skipped in a struct initializer.
 - `unused_must_use` - A result of a function call is not used. This is notably used on functions that return a `Result` to guard against forgetting to handle the error case.
 - `unused_variable` - A variable is declared but not used.
 - `unused_parameter` - A function parameter is declared but not used.
 - `unused_import` - An item is imported but not used.

## Style conventions

Alumina follows similar naming and code formatting conventions for most items as Rust.

- Functions, macros, function parameters and local variables are `snake_case`
- Types and protocols are `PascalCase`
  - An exception to this are type operators, which are `snake_case` (e.g. [arguments_of](https://docs.alumina-lang.net/std/builtins/arguments_of.html))
- Constants and statics are `SCREAMING_SNAKE_CASE`
- Egyptian brackets are preferred for blocks
    ```rust
    if x == 5 {
        // ...
    }

    fn foo() {
        // ...
    }
    ```

Some other conventions:

- Private fields and methods are prefixed with an underscore
- `Self` is used as the first type parameter of protocols
- Protocol names are usually adjectives. They will often have the -able suffix where applicable (e.g. `Equatable`, `Comparable`, `Cloneable`)
