# Aluminac Future Work

## Compiler Bugs

### Type alias static method calls fail for non-generic aliases
Calling static methods through non-generic type aliases fails:
`std::fmt::Result::ok(())` where `type Result = std::result::Result<(), Error>`.
**Workaround**: Use `let r: std::fmt::Result = std::result::Result::ok(()); r`

### Nested generic type inference in non-generic impl blocks
`Option::transpose()` with signature `fn transpose<T, E>(self: Option<Result<T, E>>)`
incorrectly binds T to `Result<i32, i32>` instead of `i32` when called on
`Option<Result<i32, i32>>`. The type inference doesn't decompose nested generic types.
**Workaround**: Avoid methods that pattern-match nested generic types in self position.

### Nested `Option<Option<T>>` causes LLVM IR verification failure
`Option::some(Option::some(42i32))` generates invalid IR where an `i32` is stored into
an `Option<Option<i32>>*`. Type inference for `Option::some()` incorrectly infers `T=i32`
instead of `T=Option<i32>` when the argument is itself an `Option<i32>`.

### UFCS doesn't work for free functions on built-in/slice types
Free functions defined with `self: &[u8]` as the first parameter cannot be called using
UFCS (universal function call syntax) as methods on `&[u8]` slices. E.g. defining
`fn starts_with(self: &[u8], prefix: &[u8]) -> bool` and calling `"hello".starts_with("hel")`
fails with "could not resolve method 'starts_with'". This also affects calls within the
same module (e.g. `trim_prefix` calling `self.starts_with(prefix)`).

**Workaround**: Use regular parameter names and call as `std::string::starts_with(s, prefix)`.

## Features to Port

### Protocol mixin annotations
The `/// @ cmp::Equatable::equals` doc comment annotation for registering protocol
implementations needs proper support.

### IteratorExt mixin triggers monomorphization of all methods
When a non-generic type like SplitIterator mixes in IteratorExt<SplitIterator, &[u8]>,
all methods get monomorphized eagerly, including those with additional generic parameters
(like `find<F: Fn(T) -> bool>`). This can cause "could not resolve method" errors even
for methods the user never calls.
**Workaround**: Only mixin Iterator (not IteratorExt) for simple types, and provide
a manual `iter()` method for for-in compatibility.

### Named parameter convention for mixin methods
Methods in protocols that use a parameter name other than `self` (e.g. `iter: &mut Self`)
fail to resolve when mixed in. The compiler appears to only properly bind Self for
parameters named `self`.
**Workaround**: Always use `self` as the first parameter name in protocol methods.
