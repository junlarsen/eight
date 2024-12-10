# Hachi

Hachi is a toy programming language I'm building to learn about compiler optimization. The main research areas of the
project are:

1. Standard compiler optimizations such as constant folding, dead code elimination, and common subexpression
   elimination.
2. High-performance code generation using ISA-specific vector instructions. (x86 SSE/AVX is the primary target).
3. A generic type system with a simple type inference algorithm.

```rust
type Matrix = {
  r: i32,
  c: i32,
  buf: i32*,
}

fn matrix_matrix_multiply(a: Matrix, b: Matrix) -> Matrix {
  let c = Matrix {
    r: a.r,
    c: b.c,
    buf: malloc(a.r * b.c * sizeof::<i32>),
  };

  for let i = 0; i < a.r; i = i + 1 {
    for let j = 0; j < b.c; j = j + 1 {
      let sum = 0;
      for let k = 0; k < a.c; k = k + 1 {
        sum = sum + a.buf[i * a.c + k] * b.buf[k * b.c + j];
      }
      c.buf[i * b.c + j] = sum;
    }
  }
  return c;
}
```

## License

Everything in the repository is licensed under the Apache 2.0 License.
