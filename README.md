# OurLoopReduce

**OurLoopReduce** is a custom LLVM optimization pass that implements a variant of **Loop Strength Reduction (LSR)**.  
It focuses on reducing the computational cost of arithmetic and memory access operations inside loops by transforming expensive expressions into cheaper equivalents.

---

## Features

- **Detection of Induction Variables**  
  Identifies loop variables that change every iteration by a constant step (e.g., loop counters).

- **Multiplication to Addition Transformation**  
  Replaces multiplications involving induction variables with incremental additions —  
  for example, transforms `i * 4` into a running sum updated by `+4` on each iteration.

- **Index Address Simplification**  
  Detects array or pointer indexing expressions that depend linearly on the loop counter (e.g., `arr[4 * i + 2]`)  
  and replaces them with pointer arithmetic that advances by a fixed stride per iteration.

---

## Example

Before optimization:
```c
for (int i = 0; i < n; i++)
    A[i] = B[4 * i + 2];
```

After OurLoopReduce:
```c
int offset = 2;
for (int i = 0; i < n; i++) {
    A[i] = B[offset];
    offset += 4;
}
```

## Implementation Notes

- Uses IR transformations to insert preheaders and replace mul or getelementptr instructions.
- It is written for LLVM legacy modules, so it can be run using the command resembling the following:
```bash
./bin/clang -S -emit-llvm input.c
./bin/opt -load lib/LLVMOurLoopReduce.so -enable-new-pm=0 -our-loop-reduce input.ll -S -o output.ll
```

## Presentation

- You can see our presentation for further information on this topic: [Presentation(Serbian)](https://github.com/matejajanic/loop_reduce_optimization/blob/main/presentation.pdf)
