# faster-compcert

How far can CompCert's performance be pushed toward GCC's while keeping
its proofs? And can LLM agents find, implement and prove the missing
optimizations?

See [REPORT.md](REPORT.md) for the full methodology, measurements and
assembly before/after.

## Status

Geometric mean of run time over the 24 programs of `test/c`, relative to
CompCert 3.18 (lower is better):

| compiler | time |
|---|---:|
| CompCert 3.18 | 1.000 |
| gcc -O1 | 0.891 |
| **faster-compcert (this fork)** | **0.871** |
| gcc -O2 restricted to CompCert's semantic model | 0.794 |
| gcc -O2 | 0.783 |

Changes, each fully proved:

| change | flag | biggest wins |
|---|---|---|
| size-based inlining, second Inlining/Constprop round, if-conversion and layout heuristics | `-finline-small-functions` | integr 0.46x, vmach 0.75x, perlin 0.78x |
| Deadcode: loads through non-stack pointers no longer make the frame live; CSE: disjoint-offset aliasing | — | sha3 0.82x |
| x86: fused 32->64 zero-extension, small rotates, `x/2`, `cvtsi2sd`/`sqrtsd` false dependencies | — | aes 0.87x, siphash24 0.92x |
| new pass `Loadfwd`: load forwarding across join points | `-floadfwd` | spectral 0.60x |
| new passes `Looprot` + `LICM`: validated loop rotation and loop-invariant code motion | `-floop-rotate`, `-flicm` | aes, sha1, fannkuch |

Verification:

- No new axioms. The only new entries in `Print Assumptions` are three flags
  and two validated oracles (`results/`).
- `make proof` succeeds on x86_64, x86_32, aarch64, arm, powerpc and rv64.
- The regression suite (`make -C test all test`) passes.

Known gaps and next steps are in [REPORT.md, section 5](REPORT.md#5-what-remains-and-what-it-would-take).

## Layout

- `REPORT.md`: the report.
- `harness/bench.py`: compiles the `test/c` benchmarks with several compilers,
  checks their outputs, and times them.
- `harness/show.py`: prints `bench.py` JSON files side by side, with the
  geomean.
- `harness/ablate.sh`: leave-one-out ablation of GCC pass families.
- `harness/asmstats.py`: static statistics of one function, old vs. new `.s`.
- `harness/check_axioms.sh`: lists the assumptions of the end-to-end
  correctness theorems.
- `results/`: final timings (`final.json`), the phase-1 baseline
  (`baseline.json`), and the assumption lists of master and this branch.

## Reproducing

```sh
./configure x86_64-linux && make -j all          # needs Rocq 9.0-9.2 and menhir
git submodule update --init test                 # benchmarks and reference outputs
python3 faster-compcert/harness/bench.py --core 8 ccomp gcc-O1 gcc-O2-ccmodel gcc-O2 > r.json
python3 faster-compcert/harness/show.py r.json
faster-compcert/harness/check_axioms.sh | diff faster-compcert/results/axioms-master.txt -
```

To compare against unmodified CompCert, build a second tree from upstream and
add it with `--extra "master=/path/ccomp -stdlib /path/runtime" master`.
Any optimization can be turned off with its `-fno-*` flag to ablate it.

Timings depend on the machine. The numbers here were taken on an Intel Xeon
Silver 4314 with GCC 11.4, using the minimum of at least 7 runs pinned to one
core.
