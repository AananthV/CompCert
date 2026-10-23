# libm_difftest: the C library's `sqrt` and `fabs` against their models

Under `-ftrust-libm` (issue #12), `cfrontend/C2C.ml` compiles calls to
`sqrt` and `fabs` as the builtins `__builtin_fsqrt` and `__builtin_fabs`.
This directory checks the two assumptions of that rewrite.

## `run.sh [COMPCERT_TREE] [N] [SEED]`: the library computes the model

It compares the C library's `sqrt` and `fabs` (glibc's `libm`) bit for bit
with the semantics of the code produced by the rewrite, extracted from Coq.
The tree must be built (`make proof`).
- `Semantics.v`: `sqrt` is modelled by the builtin `BI_fsqrt`
  (`builtin_function_sem`), and `fabs` by `Cop.sem_absfloat` at type
  `double`, because `C2C` translates `__builtin_fabs` to `Oabsfloat`.
  Both are also compared with `Float.sqrt` and `Float.abs` directly.
- `hw.c` calls the library through volatile function pointers (compiled
  with `-fno-builtin`), and also prints `errno` after each call. The inputs:
  - `special`: ±0, ±inf, quiet and signalling NaNs with payloads and both
    signs, the smallest and largest subnormals and normals, negative values,
    and 1 ± ulp;
  - `random`: `N` random bit patterns (default 10^7);
  - `squares`: `N/4` exact squares and their neighbours (the hard cases of
    rounding);
  - `subnormal`: `N/4` random subnormals of both signs.
- `check.ml` prints the special values, the mismatches and a summary. It
  exits 1 on any mismatch. `errno` is only reported, since `-ftrust-libm`
  does not set it.

Scratch files go to `$LIBM_DIFFTEST_OUT` (default: a fresh `mktemp -d`).
The model is slow (about 5000 tests per second), so the default run takes
about 45 minutes. Run several seeds in parallel to go faster.

## `rewrite.sh CCOMP [RUNTIME]`: which calls are rewritten

Each `rewrite/*.c` file says in its first line which calls `-ftrust-libm`
must compile as a builtin, which must stay calls, and which do not occur.
Optional extra options are given on a line `OPTIONS ...`. The script compiles
each file with `-S`, with and without the flag, and checks the assembly.
Without the flag, no call may be rewritten. The files cover: the `<math.h>`
declarations, block-scope declarations and typedefs (rewritten); a program
that defines `sqrt`/`fabs`, a `static` `sqrt`, an address taken in code or in
an initializer, a cast of the function to an integer, prototypes with
`float`, `int`, two arguments, `...` or no prototype, and a parameter named
`sqrt` (not rewritten).
