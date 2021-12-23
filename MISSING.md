# List of known bugs and missing features

## General

- An actual CLI interafce for the compiler so it can compile more than one hardcoded file.
- Equality comparison for slices (should be fixed, memcmp is not appropriate everywhere)
  - Can be restricted to slices of primitive types once builtin protocols are implemented
- Whole const_eval thing. It's very ad-hoc and messy. Full const-eval is not a priority, but it needs to be good enough
  so `consts` and enum members can have values that people usually put there + in as much as compiler intrinsics need them. 
- Force inlining in IR (especially for slice coercions - function call is an overkill)
    - It's not a priority, since C compiler can inline perfectly fine, except in special cases like `alloca` where the allocated buffer cannot leave the stack frame. To have a good wrapper around `alloca`, it needs to be force-inlined except if done in a macro (but macros don't really have a good type parameter system, params can only be expressions).
- impl for builtin types/arrays/...?
    - Now easier to do with lang items :)
- stack overflow in codegen stage because infinite size recursive structs are not rejected during monomorphization
- Whole ZST and divergence handling might still be buggy, in particular, uninitialized variables of `!` type might be problematic since lowering is quite liberal with making temporary name bindings for various stuff.
- compile flags support (cfg)
- if tentative monomorphization fails (e.g. error), but type inference still succeeds, we are left with unpopulated symbols (maybe fixed, not sure)
- builtin protocols
- mixins (default protocol implementations)
- generic-binding typedefs (e.g. `type HashSet<T> = HashMap<T, ()>`). 
  - This has been attempted and reverted because it was a big mess.
  - It sounds really simple to implement, but the naive approach leads to a bunch of issues (dependencies during AST construction, `impl` forwarding, whether IR should even be aware of them and if not, should they be handled in `mono`, name resolution needs another 'defered' type, ...). That's because they are in a way partial specializations of generic types.
  - typedefs that don't bind generic parameters are already possible with `use X as Y`. 
- extern/opaque types
  - These types are unsized - they can only appear behind pointers and these pointers cannot be dereferenced.
  - This is low priority, should be simple to implement, but extern types are pretty marginal.
- dyn pointer downcasting
  - Does this require special syntax?



## Grammar, parsing, AST

- For loop
- Switch is a bit cumbersome at the moment / improve?
- hex integer literals
- macros could be more expressive (esp. accept type parameters) - but this needs a nice-looking syntax.


## Std library

- basic structure. how big should it be?
- how portable should it be? I'm not sure if I'll have the grit to support anything other than `x86_64-unknown-linux-gnu` and maybe `aarch64`.
- these are definitely needed:
  - standard and file IO
  - string formatting
  - collections
  - math

## Diagnostics

- More warnings and notes
- Add more specific spans to compile errors. It's pretty good right now, but could be better.
- do not panic on cyclic/recursive protocol bounds (figure out which ones are appropriate), but rather give a meaningful error message

## Compiler architecture

- Is IR low-level enough to eventually target LLVM?
- Should monomorphization and type checking be separate stages? Can this even be done with the loose duck-typed language?
- Will the compiler architecture scale to large programs? Is it possible to pre-compile the libraries at least to AST?


## Exploratory

- SFINAE/overloading?
  - I am leaning pretty strongly towards not having either of these. With protocols and RTTI/dyn the language 
    is probably expressive enough to do  string formatting and collections, which are a good litmus test if generics are any good.
- error handling/try operator. Could settle for go-style, eg:
  ```
  let (val, err) = io_operation;
  if err {
      return (null, err); 
  }
  ```
  Nah, that's ugly. Might need proper tagged unions at some point for Maybe/Either/...

- tuple unpacking 
- true variadic functions (certainly they'd be generic and variadic only pre-monomorphization, varargs is an abomination). This is hard to do, both from the syntax and `mono` perspective but the payoff is that `printf` can ditch `dyn` and tuples can have more semantics implemented in standard library instead of requiring compiler support.
- instead of specialization, there could be a const if/const match expression - wow that'd be amazing!
  - Now easier with protocols 
- generators? coroutines? lmao, not gonna happen
- `dyn Protocol` could be a classic dynamic dispatch thing. A vtable can be generated at compile time for
  when a pointer to a concrete type is coerced/casted into `dyn Protocol`
     

## Tooling

- Syntax highlighter for VS Code


## Bikeshedding

- Name conventions (PascalCase, snake_case, ...)
