# cachelang

### Overview
This project implements a compiler for CacheLang, a DSL with manual cache control, using C as an intermediate. The current syntax supports assignment and component-wise operations on vectors and scalars at the memory, cache, and register levels. The following is a well-typed program in CacheLang:
```
c1 @ cache = load(1024)
c2 @ cache = load(1024)
m1 @ mem = load(1048576)
sc @ reg = 2
m2 @ mem = m1 / sc
m3 @ mem = c1 / c2
m4 @ mem = m1 / sc
m5 @ mem = c1 / c2
flush(m2[0], m3[0], m4[0], m5[0])
```
The `load` primitive reads bytes from `stdin` and the `@ level` decorator indicates which memory region the value should be stored and maintained in (e.g., by prefetching cache lines). The `flush` primitive prints a value to `stdout` and clears the variable context as a rudimentary form of scope.

### Installation

1. Clone the repository:
    ```
    git clone git@github.com:Wolfiej-k/cachelang.git
    cd cachelang
    ```
2. Build the project:
    ```
    cargo build --release
    ```

### Usage

The compiler accepts the following command-line arguments:
```
Usage: <memory> <cache> [--compile <output>]
```
1. `<memory>`: Number of 4-byte integers that fit in system memory.
2. `<cache>`: Number of 4-byte integers that fit in L1, L2, or L3 cache.
3. `--compile <output>` (optional): Create an executable with GCC.

In addition, it expects a CacheLang program string piped via `stdin`. If `--compile` is not provided, a plain-text C file or an appropriate compiler error is printed to `stdout`.