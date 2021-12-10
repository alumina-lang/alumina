# List of known bugs and missing features

## General

- For loop
- Whole const_eval thing
- Global variables (+ static initialization)
- Consts
- Compile errrorrrsss (spans?)
    - Tree-sitter ERROR nodes
- Force inlining in IR (especially for slice coercions - function call is an overkill)
    - Is this needed or let C compiler do it?
    - It's easy tho? No it's not - simple substitution can lead to multiple evaluation.
- impl for builtin types/arrays/...?
- Being able to take address of an rvalue (temporary name binding - important for method chaining)
    - This is critical, but can be tough. We need to bind temporary to somewhere above the current scope.
- () is not the onlz 0-sized type, also `[(); 0]`, structs with no fields, etc. How should this be handled?

## Std library

- everything?

## Codegen

- Statement expresssion ends witha void type -> C does not compile (issue with if/else if one branch is ! or () and the other is a value
- noreturn and other attributes

## Exploratory

- concepts/protocols - should it be only for better error messages when substitution fails or
  should it also be used for typechecking non-monomorphized functions (e.g. you cannot call)
- SFINAE/overloading? this basically solves the 
- vtables/dyn
- error handling/try operator
- tuple unpacking 
- instead of specialization, there could be a const if/const match expression - wow that'd be amazing!

## Bikeshedding

- `void` vs `()`. I don't like `()` too much as a type
