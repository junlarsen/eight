# Eight

Eight is a toy programming language for learning about compiler optimization and code generation. It is an imperative
programming language with a static type system.

The compiler is written in Rust and will use LLVM as the primary backend, with plans for an x86-64 backend. The type
system is based on the Hindley-Damas-Milner type system with extensions for type classes and struct types. Its semantics
highly resembles C. The following is a naive matrix-matrix multiplication example.

**Current project status**: The frontend is mostly complete, and current work is on the mid-level IR and LLVM codegen.

```rust
struct Matrix {
  r: i32,
  c: i32,
  buf: *i32,
}

fn matrix_matrix_multiply(a: Matrix, b: Matrix) -> Matrix {
  let c = new Matrix {
    r: a.r,
    c: b.c,
    buf: malloc(a.r * b.c * 4),
  };

  for (let i = 0; i < a.r; i = i + 1) {
    for (let j = 0; j < b.c; j = j + 1) {
      let sum = 0;
      for (let k = 0; k < a.c; k = k + 1) {
        sum = sum + a.buf[i * a.c + k] * b.buf[k * b.c + j];
      }
      c.buf[i * b.c + j] = sum;
    }
  }
  return c;
}
```

## Development

The compiler is written in Rust, and requires the LLVM Integrated Tester to run its test suite. The easiest way to get
started is to install both Rust and Poetry (to download Lit).

```bash
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
curl -sSL https://install.python-poetry.org | python3 -

# We depend on LLVM 15, so that has to be available somewhere too. Easiest is to grab it from the LLVM apt repo or
# equivalent for your distro. Clang-15 is required for Polly
sudo apt install llvm-15-dev llvm-15-tools clang-15
# Configure llvm-sys to point at the installed LLVM
export LLVM_SYS_150_PREFIX="/usr/lib/llvm-15"

# Run unit tests and snapshot tests
cargo test

# Install Lit, and run the integration test suite
poetry install
cargo xtask lit
```

Running the compiler is done through `cargo run --bin eightc`, or using the build output if you compile the project.

```bash
Usage: eightc [OPTIONS] <INPUT>

Arguments:
  <INPUT>  The input source. If this is `-`, the input is read from stdin

Options:
      --emit-ast                 Should the plain AST be emitted?
      --emit-hir                 Should the fully-typed, lowered HIR be emitted?
      --emit-mir                 Should the MIR be emitted?
      --emit-query <EMIT_QUERY>  Emission queries to specify which nodes should be emitted
      --syntax-only        Stop the compiler after the type checker
      --stop-token-mir-lower     Stop the compiler after MIR lowering
  -h, --help                     Print help
  -V, --version                  Print version
```

## Contact

If you have any questions, feel free to reach me by email at mats at jun dot codes.

## License

Everything in the repository is licensed under the Apache 2.0 License.
