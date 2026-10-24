# CompCert
The formally-verified C compiler.

## Overview
The CompCert C verified compiler is a compiler for the core C language 
that generates code for the ARM, PowerPC, RISC-V and x86 processors.

The distinguishing feature of CompCert is that it has been formally
verified using the Coq proof assistant: the generated assembly code is
formally guaranteed to behave as prescribed by the semantics of the
source C code.

For more information on CompCert (supported platforms, supported C
features, installation instructions, using the compiler, etc), please
refer to the [Web site](https://compcert.org/) and especially
the [user's manual](https://compcert.org/man/).

## faster-compcert
This fork tracks **faster-compcert**, an experiment in closing the
performance gap between CompCert and GCC -O2 with new, fully verified
optimizations, many of them found, implemented and proved by LLM agents.
Details, measurements and the benchmarking harness are in
[faster-compcert/](faster-compcert/README.md).

Geomean run time relative to CompCert 3.18 (lower is better). `test/c` was
used for tuning; the other two suites are held out.

| compiler | `test/c` | big programs | PolyBench |
|---|---:|---:|---:|
| CompCert 3.18 | 1.000 | 1.000 | 1.000 |
| gcc -O1 | 0.891 | 0.931 | 0.764 |
| **faster-compcert (default flags, before 2026-10-24)** | **0.842** | **0.958** | **0.737** |
| **faster-compcert (all opt-in flags)** | **0.822** | **0.951** | **0.739** |
| gcc -O2, restricted to CompCert's semantic model | 0.795 | 0.874 | 0.651 |
| gcc -O2 | 0.785 | 0.876 | 0.649 |

Measured 2026-10-24, all compilers in one session, with interleaved timing
(`faster-compcert/results/`). "All opt-in flags" is
`-fload-op -fshift-mask -ftrust-libm -fzext-load -fmerge-bytes`.
faster-compcert is faster than gcc -O1 on `test/c` and PolyBench, slightly
slower on the big programs, and 1.05-1.14× gcc -O2's run time.

Progress so far:
- [x] Diagnose the gap. The semantic models account for only ~1.5 points of
  the 22-point gap to gcc -O2; the rest is missing passes and x86 code
  generation ([report](faster-compcert/REPORT.md)).
- [x] Better inlining heuristic and a second inlining round after constant
  propagation.
- [x] More precise dead-store elimination and CSE alias analysis.
- [x] x86 instruction selection: fused zero-extensions, rotates, division by
  2, false-dependency fixes.
- [x] Global load forwarding across loop back-edges (new pass `Loadfwd`).
- [x] Loop-invariant code motion and loop rotation (new passes `LICM`,
  `Looprot`, translation-validated).
- [x] Held-out evaluation on larger programs and PolyBench ([#2](https://github.com/AananthV/CompCert/issues/2)).
- [x] LICM of chains of dependent operations: loop-nest address arithmetic
  (PolyBench 0.845 → 0.776; [#16](https://github.com/AananthV/CompCert/issues/16)).
- [x] Induction-variable widening and strength reduction (new pass `IVwiden`;
  PolyBench −4.3%, sha1 −13%; [#4](https://github.com/AananthV/CompCert/issues/4)).
- [x] Load-op memory operands on x86, opt-in `-fload-op`. This is the first
  approved trusted-base change ([#5](https://github.com/AananthV/CompCert/issues/5),
  [ledger](faster-compcert/TRUSTED_BASE.md)).
- [x] Model x86 shift-count masking (approved trusted-base change, opt-in
  `-fshift-mask`; [#11](https://github.com/AananthV/CompCert/issues/11)).
- [x] Retroactive review of the round-1 trusted-base changes
  ([#10](https://github.com/AananthV/CompCert/issues/10)).
- [x] Opt-in `sqrt`/`fabs` builtins, `-ftrust-libm` (approved trusted-base
  change; nbody −17%; [#12](https://github.com/AananthV/CompCert/issues/12) phase 1).
- [x] Zero-extending 8/16-bit loads with 64-bit results, `-fzext-load`
  (approved trusted-base change; siphash24 −6%;
  [#25](https://github.com/AananthV/CompCert/issues/25)).
- [x] Unaligned 64-bit accesses and byte-load merging, `-fmerge-bytes`
  (approved memory-model change; siphash24 −21%;
  [#13](https://github.com/AananthV/CompCert/issues/13)).
- [x] Pure libm functions (50 functions, `-ftrust-libm`; approved trusted-base
  change; perlin −15%; [#12](https://github.com/AananthV/CompCert/issues/12)
  phase 2).
- [x] Fix the Loadfwd compile-time/memory blow-up on large functions (65 GB →
  112 MB on `test/abi/layout.c`; [#19](https://github.com/AananthV/CompCert/issues/19)).
- [ ] Reduce the remaining compile-time overhead: first round done
  (layout.c 11.6 → 6.5 s, spass 54.8 → 46.4 s; CompCert 3.18: 4.9 / 31.3 s);
  spass is still ~1.5× ([#9](https://github.com/AananthV/CompCert/issues/9)).

All changes keep CompCert's end-to-end correctness theorem. They add no
axioms: the only new assumptions are command-line flags and validated
oracles.

## License
CompCert is not free software.  This non-commercial release can only
be used for evaluation, research, educational and personal purposes.
A commercial version of CompCert, without this restriction and with
professional support and extra features, can be purchased from
[AbsInt](https://www.absint.com).  See the file [LICENSE](LICENSE) for more
information.

## Copyright
The CompCert verified compiler is Copyright Institut National de
Recherche en Informatique et en Automatique (INRIA) and 
AbsInt Angewandte Informatik GmbH.


## Contact
General discussions on CompCert take place on the
[compcert-users@inria.fr](https://sympa.inria.fr/sympa/info/compcert-users)
mailing list.

For inquiries on the commercial version of CompCert, please contact
info@absint.com
