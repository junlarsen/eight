# XD Programming Language

This is a toy compiler for a tiny programming language.

> The compiler is currently undergoing a C++ rewrite. Visit
> https://github.com/junlarsen/xd/tree/rust to see the Rust codebase. The
> motivation for the C++ rewrite is direct access to MLIR and LLVM C++ APIs.

## Building

The project is built using the LLVM toolchain and is not tested against
gcc/libstdc++. We require a build of LLVM 20.1.0 that has been built with
LLVM libc++. In addition, we use LLVM and MLIR libraries.

- XD_LLVM_INSTALL_PREFIX: This is the location where LLVM 20.1.0 is expected to
  be available on the system. This defaults to `/usr/lib/llvm-20`. Read the next
  section on how to build a compatible LLVM 20.1.0 build.

<details>
<summary>Building a compatible LLVM distribution</summary>
```bash
# Assuming llvm/llvm-project checked out at llvmorg-20.1.0
cmake \
  -G "Ninja" \
  -DCMAKE_INSTALL_PREFIX="/usr/lib/llvm-20" \
  -DCMAKE_BUILD_TYPE="Release" \
  -DCMAKE_CXX_COMPILER="clang++-18" \
  -DCMAKE_C_COMPILER="clang-18" \
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
