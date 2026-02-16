#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
OUTPUT_DIR="$REPO_ROOT/sysroot/libc"

TARGETS=(
    aarch64-apple-darwin
    aarch64-linux-android
    aarch64-unknown-linux-gnu
    aarch64-unknown-linux-musl
    riscv64gc-unknown-linux-gnu
    riscv64gc-unknown-linux-musl
    x86_64-apple-darwin
    x86_64-unknown-linux-gnu
    x86_64-unknown-linux-musl
)

LIBC_DIR=$(mktemp -d)
trap 'rm -rf "$LIBC_DIR"' EXIT

echo "Cloning libc crate..."
git clone --depth 1 https://github.com/rust-lang/libc.git "$LIBC_DIR"

echo "Adding rustup targets..."
rustup +nightly target add "${TARGETS[@]}"

echo "Building libc-bindgen..."
cargo +nightly build --manifest-path "$SCRIPT_DIR/Cargo.toml"

TARGET_ARGS=()
for target in "${TARGETS[@]}"; do
    TARGET_ARGS+=(--target "$target")
done

echo "Generating bindings..."
cargo +nightly run --manifest-path "$SCRIPT_DIR/Cargo.toml" -- \
    "${TARGET_ARGS[@]}" \
    -o "$OUTPUT_DIR" \
    "$LIBC_DIR/src/lib.rs"

echo "Done. Generated bindings in $OUTPUT_DIR"
