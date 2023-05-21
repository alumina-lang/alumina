# Tests

This directory contains tests for the compiler. They are organized into subdirectories:
- [`lang`](./lang/) - tests for various language features that are not specific to standard library. These tests run through the standard test runner (the whole direcory is one module).
- [`diag`](./diag/) - cases for which the compiler should emit a diagnostic (either a failed compilation or a warning). These tests are executed by the [`diag` test runner](../tools/diag.py). Each `.alu` file is compiled separately to C code, but the C code is not compiled into an executable.

To run these tests, run `make test-lang` or `make test-diag`

The standard library tests are not in this directory, but in [`sysroot`](../sysroot/) directory, collocated with the standard library source code.
