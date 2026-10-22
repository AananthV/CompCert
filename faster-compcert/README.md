# faster-compcert

How far can CompCert's performance be pushed toward GCC's while keeping
its proofs? And can LLM agents find, implement and prove the missing
optimizations?

See [REPORT.md](REPORT.md) for the full methodology, measurements and
assembly before/after.

## Status

Geometric mean of run time relative to CompCert 3.18 (lower is better):

| compiler | `test/c` (tuned on) | big programs (held out) | PolyBench (held out) |
|---|---:|---:|---:|
| CompCert 3.18 | 1.000 | 1.000 | 1.000 |
| gcc -O1 | 0.889 | 0.951 | 0.763 |
| **faster-compcert (this fork)** | **0.862** | **0.969** | **0.751** |
| gcc -O2 restricted to CompCert's semantic model | 0.791 | 0.890 | 0.646 |
| gcc -O2 | 0.783 | 0.883 | 0.670 |

The heuristics were tuned on `test/c`, so the held-out columns are the honest
measure of generality ([REPORT.md §7](REPORT.md#7-held-out-evaluation-issue-2)).

Changes, each fully proved:

| change | flag | biggest wins |
|---|---|---|
| size-based inlining, second Inlining/Constprop round, if-conversion and layout heuristics | `-finline-small-functions` | integr 0.46x, vmach 0.75x, perlin 0.78x |
| Deadcode: loads through non-stack pointers no longer make the frame live; CSE: disjoint-offset aliasing | — | sha3 0.82x |
| x86: fused 32->64 zero-extension, small rotates, `x/2`, `cvtsi2sd`/`sqrtsd` false dependencies | — | aes 0.87x, siphash24 0.92x |
| new pass `Loadfwd`: load forwarding across join points | `-floadfwd` | spectral 0.60x |
| new pass `IVwiden`: induction-variable widening and strength reduction, validated (#4) | `-fiv-widen` | gemm 0.74x, sha1 0.87x, syrk 0.87x |
| new passes `Looprot` + `LICM`: validated loop rotation and loop-invariant code motion, including chains of dependent operations (#16) | `-floop-rotate`, `-flicm` | aes, sha1, fannkuch; gemm 0.72x, syrk 0.73x, floyd-warshall 0.74x |

| new pass `Loadop`: x86 arithmetic with memory operands (#5; **trusted-base change**, see [TRUSTED_BASE.md](TRUSTED_BASE.md)) | `-fload-op` (off by default) | gemm 0.91x, nbody 0.96x, spectral 0.97x |

Verification:

- No new axioms. The only new entries in `Print Assumptions` are three flags
  and two validated oracles (`results/`).
- `make proof` succeeds on x86_64, x86_32, aarch64, arm, powerpc and rv64.
- The regression suite (`make -C test all test`) passes.

Known gaps and next steps are in [REPORT.md, section 5](REPORT.md#5-what-remains-and-what-it-would-take).

## Layout

- `REPORT.md`: the report.
- `TRUSTED_BASE.md`: the ledger of approved trusted-base changes.
- `harness/bench.py`: compiles a benchmark suite with several compilers,
  checks each program's result, and times it. Suites (`--suite`):
  - `c`: the 24 programs of `test/c` (default);
  - `big`: `raytracer`, `spass` and the three `compression` programs;
  - `polybench`: the 30 PolyBench/C 4.2.1 kernels.
- `harness/suites.py`: definitions of the `big` and `polybench` suites.
- `harness/fetch_polybench.sh`: fetches PolyBench/C 4.2.1, pinned. It is not
  included in this repository because of its licence.
- `harness/show.py`: prints `bench.py` JSON files side by side, with the
  geomean.
- `harness/ablate.sh`: leave-one-out ablation of GCC pass families.
- `harness/compile_cost.py`: compile time and peak memory on large inputs
  (`test/abi/layout.c`, `staticlayout.c`, spass, `test/c`), under a memory
  cap, to catch compile-time blow-ups.
- `harness/asm_difftest/`: differential test of new Asm instruction
  semantics against the CPU, using the extracted Coq semantics.
- `harness/asmstats.py`: static statistics of one function, old vs. new `.s`.
- `harness/check_axioms.sh`: lists the assumptions of the end-to-end
  correctness theorems.
- `results/`: the latest timings on all three suites (`final.json`,
  `heldout-big.json`, `heldout-polybench.json`), earlier rounds
  (`round1/`, `round2/`), the phase-1 baseline (`baseline.json`), and the assumption
  lists of CompCert 3.18 and this fork.

## Reproducing

```sh
./configure x86_64-linux && make -j all          # needs Rocq 9.0-9.2 and menhir
git submodule update --init test                 # benchmarks and reference outputs
python3 faster-compcert/harness/bench.py --core 8 ccomp gcc-O1 gcc-O2-ccmodel gcc-O2 > r.json
python3 faster-compcert/harness/show.py r.json
python3 faster-compcert/harness/bench.py --suite big ccomp gcc-O2 > big.json
faster-compcert/harness/fetch_polybench.sh /path/to/polybench
python3 faster-compcert/harness/bench.py --suite polybench --polybench /path/to/polybench ccomp gcc-O2 > pb.json
faster-compcert/harness/check_axioms.sh | diff faster-compcert/results/axioms-master.txt -
```

To compare against unmodified CompCert, build a second tree from upstream and
add it with `--extra "master=/path/ccomp -stdlib /path/runtime" master`.
Any optimization can be turned off with its `-fno-*` flag to ablate it.

Timings depend on the machine. The numbers here were taken on an Intel Xeon
Silver 4314 with GCC 11.4, using the minimum of at least 7 runs pinned to one
core.
