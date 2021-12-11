# List of known bugs and missing features

## General

- For loop
- Equality comparison for slices
- Whole const_eval thing
- Global variables (+ static initialization)
- Consts
- Compile errrorrrsss (spans?)
    - Tree-sitter ERROR nodes
- Force inlining in IR (especially for slice coercions - function call is an overkill)
    - Is this needed or let C compiler do it?
    - It's easy tho? No it's not - simple substitution can lead to multiple evaluation.
- impl for builtin types/arrays/...?
    - Now easier to do with lang items :)
- Being able to take address of an rvalue (temporary name binding - important for method chaining)
    - This is critical, but can be tough. We need to bind temporary to somewhere above the current scope.
- `()` is not the only 0-sized type, also `[(); 0]`, structs with no fields, etc. How should this be handled?
- Lambdas cannot bind placeholders, leading to a panic during monomorphization, example:

  ```
  fn generic<T>() {
      let x = |x: T| -> T { x }; // panic: unbound placeholder
  }
  ```

  Resolving closures at monomorphization time would also be better as we can statically inline @ call site them 
  instead of having to pass them around as function pointers.

## Investigate

- What happens/should happen to UFCS associated function calls if they are renamed with `use` clause?

## Std library

- basic structure. how big should it be?
- idioms for IO
- string formatting
- collections

## Codegen

- Statement expresssion ends witha void type -> C does not compile (issue with if/else if one branch is ! or () and the other is a value

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
  Nah, that's ugly. 

- tuple unpacking 
- defer expressions? or at that point full RAII? probably not.
- instead of specialization, there could be a const if/const match expression - wow that'd be amazing!
- Rust-like macros?
- generators? coroutines? lmao, not gonna happen


## Bikeshedding

- `void` vs `()`. I don't like `()` too much as a type
