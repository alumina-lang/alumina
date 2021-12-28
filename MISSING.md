# List of known bugs and missing features

## General

- An actual CLI interafce for the compiler so it can compile more than one hardcoded file.
- Whole const_eval thing. It's very ad-hoc and messy. Full const-eval is not a priority, but it needs to be good enough
  so `consts` and enum members can have values that people usually put there + in as much as compiler intrinsics need them. 
- Force inlining in IR (especially for slice coercions - function call is an overkill)
    - It's not a priority, since C compiler can inline perfectly fine, except in special cases like `alloca` where the allocated buffer cannot leave the stack frame. To have a good wrapper around `alloca`, it needs to be force-inlined except if done in a macro (but macros don't really have a good type parameter system, params can only be expressions).
- impl for builtin types/arrays/...?
    - Done for primitive types, tuples and arrays are TBD (need `const usize` generic args and variadics to do nicely)
- stack overflow in codegen stage because infinite size recursive structs are not rejected during monomorphization
    - could be a similar issue with protocols, though these are more coservative vis-a-vis recursion
- Whole ZST and divergence handling might still be buggy, in particular, uninitialized variables of `!` type might be problematic since lowering is quite liberal with making temporary name bindings for various stuff.
    - It might be fine now, it's been a while since I last ran into a ZST bug
- compile flags support (cfg)
- if tentative monomorphization fails (e.g. error), but type inference still succeeds, we are left with unpopulated symbols (maybe fixed, not sure)
- generic-binding typedefs (e.g. `type HashSet<T> = HashMap<T, ()>`). 
  - This has been attempted and reverted because it was a big mess.
  - It sounds really simple to implement, but the naive approach leads to a bunch of issues (dependencies during AST construction, `impl` forwarding, whether IR should even be aware of them and if not, should they be handled in `mono`, name resolution needs another 'defered' type, ...). That's because they are in a way partial specializations of generic types.
  - typedefs that don't bind generic parameters are already possible with `use X as Y`.
  - It could be easier now with `rebind` in AST 
- unqualified types gaps:
  - unqualified string in if/else does not coerce to a slice
  - probably other places too, since it's very ad-hoc
- operator overloading
  - forward ==, !=, >, <, >=, <= to Equatable/Comparable (dubious - is this desired or not)

## Grammar, parsing, AST

- Switch is a bit cumbersome at the moment / improve?
- hex integer literals
- macros could be more expressive (esp. accept type parameters) - but this needs a nice-looking syntax.


## Std library

- basic structure. how big should it be?
- tests
- how portable should it be? I'm not sure if I'll have the grit to support anything other than `x86_64-unknown-linux-gnu` and maybe `aarch64`.
- these are definitely needed:
  - standard and file IO
  - string formatting
    - The pattern is well-established (Formattable protocol) and I'm very happy with it,
      but it's very very basic right now
  - heap-allocating collections
    - Vector is implemented, need at least a HashMap and HashSet. 
    - Maybe a heap? A VecDeque/ring buffer
    - No linked lists.
  - math
- extras, nice to have:
  - threading, atomics, ...
    - This will definitely defer to pthread
    - Need a good story for thread-local storage
  - network and unix sockets
  - random number generation
    - basic RNG is implemented, need a good way to make it generic over various integer lengths
  - date/time???? this is a big can of worms
- compound assignment with pointer arithmetic is incorrect (ptr += 1 != ptr = ptr + 1)

## Diagnostics

- More warnings and notes
- Add more specific spans to compile errors. It's pretty good right now, but could be better.
- do not panic on cyclic/recursive protocol bounds (figure out which ones are appropriate), but rather give a meaningful error message

## Compiler architecture

- Is IR low-level enough to eventually target LLVM?
- Should monomorphization and type checking be separate stages? Can this even be done with the loose duck-typed language?
- Will the compiler architecture scale to large programs? Is it possible to pre-compile the libraries at least to AST?
- AST expression should have a convenience builder, like the one for IR expressions. `expressions.rs` is overly verbose right now, especially with all the span tagging.

## Exploratory

- SFINAE/overloading?
  - I am leaning pretty strongly towards not having either of these. With protocols the language 
    is probably expressive enough to do string formatting and collections, which are a good litmus test if generics are any good.
- tuple unpacking 
- true variadic functions (certainly they'd be generic and variadic only pre-monomorphization, varargs is an abomination). This is hard to do, both from the syntax and `mono` perspective but the payoff is that tuples can have nice protocol implementations.
- instead of specialization, there could be a const if/const match expression - wow that'd be amazing!
  - Now easier with protocols 
- generators? coroutines? lmao, not gonna happen
     

## Tooling

- Syntax highlighter for VS Code
- rustdoc-like thing. This will have to wait until a self-hosted compiler
- test framework


## Bikeshedding

- Name conventions (PascalCase, snake_case, ...)
