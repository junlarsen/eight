# XD Programming Language

This is a toy compiler for a tiny programming language.

> The compiler is currently undergoing a C++ rewrite. Visit
> https://github.com/junlarsen/xd/tree/rust to see the Rust codebase. The
> motivation for the C++ rewrite is direct access to MLIR and LLVM C++ APIs.

## Language Tour

The language is a cruel mix of Rust & Scala syntax, C semantics, and a
Hindley-Milner type system with typeclasses.

```scala
intrinsic_fn malloc[T](size: i32) -> *T;

// Naive O(MKN) matrix-matrix multiplication
struct Matrix {
  r: i32,
  c: i32,
  buf: *i32,
}

fn matrix_matrix_multiply(a: Matrix, b: Matrix) -> Matrix {
  let c = new Matrix {
    r = a.r,
    c = b.c,
    buf = malloc(a.r * b.c * 4),
  };

  for (let i = 0; i < a.r; i = i + 1) {
    for (let j = 0; j < b.c; j = j + 1) {
      let sum = 0;
      for (let k = 0; k < a.c; k = k + 1) {
        sum = sum + a.buf(i * a.c + k) * b.buf(k * b.c + j);
      }
      c.buf(i * b.c + j) = sum;
    }
  }
  return c;
}
```

## Building

The project is built using the LLVM toolchain and is not tested against
gcc/libstdc++. We require a build of LLVM 21 that has been built with
LLVM libc++. In addition, we use LLVM and MLIR libraries.

- XD_LLVM_INSTALL_PREFIX: This is the location where LLVM 21 is expected to
  be available on the system. This defaults to `/usr/lib`. Read the next
  section on how to build a compatible LLVM build.

<details>
<summary>Building a compatible LLVM distribution</summary>

```bash
# Assuming llvm/llvm-project from trunk
cmake \
  -G "Ninja" \
  -DCMAKE_INSTALL_PREFIX="/some/directory" \
  -DCMAKE_BUILD_TYPE="Release" \
  -DCMAKE_CXX_COMPILER="clang++-18" \
  -DCMAKE_C_COMPILER="clang-18" \
  -DCMAKE_CXX_FLAGS="-stdlib=c++" \
  -DLLVM_ENABLE_LIBCXX="ON" \
  -DLLVM_USE_LINKER="/usr/lib/llvm-18/bin/ld.lld" \
  -DLLVM_CCACHE_BUILD="ON" \
  -DLLVM_ENABLE_RUNTIMES="libcxx;libcxxabi;libunwind;compiler-rt" \
  -DLLVM_ENABLE_PROJECTS="llvm;clang;lld;mlir" \
  -DLLVM_INSTALL_UTILS="ON" \
  -DLLVM_BUILD_TOOLS="ON" \
  -DLLVM_TARGETS_TO_BUILD="X86" \
  ../llvm
cmake --build .
sudo cmake --install .
```
</details>

## License & Attribution

Everything in the repository is licensed under the Apache 2.0 License with LLVM exception.
