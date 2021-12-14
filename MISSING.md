# List of known bugs and missing features

## General

- An actual CLI interafce for the compiler so it can compile more than one hardcoded file.
- For loop
- Macros
- Equality comparison for slices (should be fixed, memcmp is not appropriate everywhere)
- Whole const_eval thing
- Global variables (+ static initialization)
- Consts
- Tree-sitter ERROR nodes. Currently a lot of syntactically invalid code is accepted if it is in nodes that parse tree visitors don't care about.
- Force inlining in IR (especially for slice coercions - function call is an overkill)
    - Is this needed or let C compiler do it?
- impl for builtin types/arrays/...?
    - Now easier to do with lang items :)
- stack overflow in codegen stage because infinite size recursive structs are not rejected during monomorphization
- Whole ZST/never type handling might still be buggy, in particular, uninitialized variables of `!` type might be problematic since lowering is quite liberal with making temporary variable declarations for various stuff.
- compile flags support (cfg)
- compiler warnings

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

## Codegen

- Statement expresssion ends with a void type -> C does not compile (issue with if/else if one branch is `!` and the other is a value)

## Exploratory

- concepts/protocols - should it be only for better error messages when substitution fails or
  should it also be used for typechecking non-monomorphized functions (e.g. you cannot call)
- SFINAE/overloading?
- vtables/dyn
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


## Bikeshedding

- `void` vs `()`. I don't like `()` too much

## Tooling

- Syntax highlighter for VS Code
