# List of known bugs and missing features

## General

- Slices
- Ranges
- For loop
- String literals
- Whole const_eval thing
- Global variables (+ static initialization)
- Compile errrorrrsss (spans?)
    - Tree-sitter ERROR nodes
- Force inlining in IR (especially for slice coercions - function call is an overkill)
    - Is this needed or let C compiler do it?
    - It's easy tho?
- impl for builtin types/arrays/...?

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
