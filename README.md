# Eight

Eight is a toy programming language built to learn compiler infrastructure, optimization, and code generation. The
compiler compiles an imperative-style programming language with a static type system. It has great type inference and
its semantics closely resemble the C programming language.

The compiler is written in Rust and uses LLVM as the primary code generator backend. Development of the compiler also
requires additional tools as described in [the Development secion](#development).

**Current project status**: The frontend is mostly complete, and current work is on the mid-level IR and LLVM codegen.

```rust
// Naive O(MKN) matrix-matrix multiplication
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

We also have some developer tooling specifically built for Eight (like our Lit-based regression tester) which will be
built alongside the compiler with `cargo build --all`. This is important as the Lit configuration searches for these
binaries in order to execute the tests.

The scripts below will take care of all the requirements needed to get started with developing the compiler.

```bash
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
curl -sSL https://install.python-poetry.org | python3 -

sudo apt install llvm-18-dev llvm-18-tools clang-18 libpolly-18-dev
# Configure llvm-sys to point at the installed LLVM
export LLVM_SYS_180_PREFIX="/usr/lib/llvm-18"

# Run unit tests
cargo test

# Install Lit, and run the integration test suite
poetry install
cargo xtask lit

# If any of the regression snapshots were updated, review them with eight-regtest
cargo regtest
# Which is a workspace alias for
cargo run --bin eightc-regtest -- verify tests
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
      --terminator <TERMINATOR>  Stop the compiler after the given step [default: never] [possible values: never, syntax, hir, mir]
  -h, --help                     Print help
  -V, --version                  Print version
```

## License

Everything in the repository is licensed under the Apache 2.0 License.
