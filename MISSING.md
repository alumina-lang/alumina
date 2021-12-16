# List of known bugs and missing features

## General

- An actual CLI interafce for the compiler so it can compile more than one hardcoded file.
- For loop
- Equality comparison for slices (should be fixed, memcmp is not appropriate everywhere)
- Whole const_eval thing
- Force inlining in IR (especially for slice coercions - function call is an overkill)
    - Is this needed or let C compiler do it?
    - It's needed for stuff like `alloca`
- impl for builtin types/arrays/...?
    - Now easier to do with lang items :)
- stack overflow in codegen stage because infinite size recursive structs are not rejected during monomorphization
- Whole ZST/never type handling might still be buggy, in particular, uninitialized variables of `!` type might be problematic since lowering is quite liberal with making temporary name bindings for various stuff.
- compile flags support (cfg)
- if tentative monomorphization fails (e.g. error), but type inference still succeeds, we are left with unpopulated symbols (maybe fixed, not sure)
- hex integer literals
- Switch is a bit cumbersome at the moment / improve?

## Std library

- basic structure. how big should it be?
- these are definitely needed:
  - standard and file IO
  - string formatting
  - collections
  - math

## Compiler architecture

- Is IR low-level enough to eventually target LLVM?
- Should monomorphization and type checking be separate stages? Can this even be done with the loose duck-typed language?
- Will the compiler architecture scale to large programs? Is it possible to pre-compile the libraries at least to AST?

## Exploratory

- concepts/protocols - should it be only for better error messages when substitution fails or
  should it also be used for typechecking non-monomorphized functions (e.g. you cannot call)
- SFINAE/overloading?
- error handling/try operator. Could settle for go-style, eg:
  ```
  let (val, err) = io_operation;
  if err {
      return (null, err); 
  }
  ```
  Nah, that's ugly. Might need proper tagged unions at some point for Maybe/Either/...

- tuple unpacking 
- defer expressions? or at that point full RAII? probably not.
- instead of specialization, there could be a const if/const match expression - wow that'd be amazing!
- generators? coroutines? lmao, not gonna happen

## Tooling

- Syntax highlighter for VS Code


## Bikeshedding

- Name conventions (PascalCase, snake_case, ...)
