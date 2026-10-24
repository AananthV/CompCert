# libm_difftest: the C library's math functions against their models

Under `-ftrust-libm` (issue #12), `cfrontend/C2C.ml`:
- compiles calls to `sqrt` and `fabs` as the builtins `__builtin_fsqrt` and
  `__builtin_fabs` (phase 1: `run.sh`, `rewrite.sh`);
- declares 50 other functions (`floor`, `sin`, `pow`, ... and their `float`
  versions, listed in `libm_*_names` in `common/Builtins0.v`) as runtime
  functions whose result is an uninterpreted function of the arguments, with
  no effect on memory, so that calls can be shared (phase 2: `pure.sh`,
  `decl.sh`).

This directory checks these assumptions.

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

## `pure.sh [N] [SEED...]`: the 50 functions are pure

The model of phase 2 does not say what the functions compute, only that the
result is a function of the argument bits and that nothing else changes.
`det.c` checks this for each function, on the special values (all pairs for
the functions of two arguments) and `N` random bit patterns (default 10^6):
- two consecutive calls give the same bits and set the same `errno`;
- a second pass, in random order across functions and inputs, gives the same
  bits and `errno` as the first (no hidden state);
- a 64 KiB memory canary is unchanged.
`pure.sh` runs it for each seed (default 1 2 3) twice: with glibc's default
ifunc selection, and with the FMA and AVX2 variants disabled
(`GLIBC_TUNABLES=glibc.cpu.hwcaps=-AVX2,-FMA`; glibc 2.35 ignores the older
spelling `-AVX2_Usable,-FMA_Usable`). It checks that the library prints
nothing, and reports per function how many calls set `errno` and whether the
two selections give the same results.  They need not: each selection is a
fixed function within one process, which is all the model assumes.
The result tables take about 600 bytes per random input, so N = 2*10^6 uses
about 1.2 GB.

## `decl.sh CCOMP [RUNTIME]`: which declarations are trusted

Each `decl/*.c` file says in its first line how many direct calls to the
listed functions the assembly must contain with and without
`-ftrust-libm` (`EXPECT on=N off=M`).  The files call functions twice on the
same arguments, so that a trusted function is called once.  They cover the
`<math.h>` declarations, all 50 functions, block-scope declarations,
intervening stores (still shared), unknown calls and tail calls (not shared,
a limitation of CSE), dead calls (removed), an address taken (direct calls
still shared), and declarations that are not trusted: a definition in the
program, `static`, other prototypes, no prototype, variadic, and functions
that are not listed (`lgamma`, `frexp`, `fmin`).  Under `-interp`, phase 2 is
disabled.
