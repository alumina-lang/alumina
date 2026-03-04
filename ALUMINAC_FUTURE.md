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

### Multiple impl blocks with different generic bounds
Adding a second impl block for the same struct with different generic bounds
(e.g. `impl FusedIterator<It: DoubleEndedIterator<It, T>, T>` alongside the
existing `impl FusedIterator<It: Iterator<It, T>, T>`) causes the first impl
block to malfunction when the type is used with a non-DoubleEndedIterator.
**Workaround**: Only use a single impl block per struct. Conditional protocol
implementations must wait for compiler support.

### Parameterized mixins on slice type fail
`mixin<Ptr> std::cmp::Comparable<slice<Ptr>>` generates invalid LLVM IR
(attempts `icmp ugt` on fat pointer struct types). The compiler does not
properly route comparison operators through the mixin's compare method.
**Workaround**: Comparison operators on slices (`<`, `>`) are not available.
Use `==` which works through the existing `equals` mechanism, and call
`slice::compare()` directly for ordering.

### Protocol-through-generic-parameter in `is` operator
When `is T2` appears inside a generic function and T2 is a protocol passed
through a generic parameter (Placeholder), the TypeCheck handler can't find
the protocol because it only resolves Named types, not Placeholders.
**Workaround**: Use `is` directly with concrete protocol types (e.g.
`std::intrinsics::uninitialized::<T>() is std::builtins::Signed`).

### Generic method in generic impl with same-name type parameter
When a generic method inside `impl Foo<T>` has a bound like `I: Iterator<I, T>`,
the monomorphizer incorrectly resolves T to the iterator type I instead of the
element type. For example, `vec.push(item.unwrap())` in
`fn extend<I: Iterator<I, T>>(self: &mut Vector<T>, iter: &mut I)` generates a
push call with SliceIterator type instead of i32.
**Workaround**: Move the generic method to a free function outside the impl block,
or use `iter.to_vector()` instead of `Vector::from_iter()`.

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

### Dyn dispatch method calls fail
Calling methods on `&dyn Protocol<Self, F>` references (e.g. `parts[i].fmt(f)`) fails with
"could not resolve method 'fmt'". The dyn vtable dispatch doesn't resolve protocol methods.
**Workaround**: Use non-dyn patterns. For formatting, use the static `format_args!` approach
with `static_format_args` instead of `dyn_format_args` + `write_fmt`.
