# faster-compcert: retrospective

This document looks back at the whole project: what was done, what it took, where a human was needed, and what comes next. [REPORT.md](REPORT.md) is the detailed technical log (sections 1-24), [TRUSTED_BASE.md](TRUSTED_BASE.md) is the ledger of trusted-base changes, and the [roadmap issue](https://github.com/AananthV/CompCert/issues/15) tracks the work item by item.

## 1. The question and the answer

**Question.** CompCert is much slower than GCC -O2. Is that because of its semantic models of C and x86-64, or because of the verified passes it has? And if it is the passes, can LLM agents find, implement and *prove* the missing transformations?

**Answer.**
1. **The models are not the main bottleneck.** GCC -O2 restricted to CompCert's semantic model (wrapping signed overflow, no type-based alias analysis, no SIMD, no FMA contraction) loses only about 1.5 of its 22 points of advantage. The gap is mostly missing optimizations and x86 code quality. A few real model limitations (opaque libm, aligned-only 64-bit access, unmodelled shift masking) were found and fixed, with the owner's approval of each trusted-base change.
2. **Yes, agents can do this, with a human gate on the trusted base.** Agents wrote every optimization in this fork and its proof (about 14,800 lines of Rocq and 2,600 of OCaml, no `Admitted`). They also did the diagnosis, the differential testing, the benchmarking and the bookkeeping. A human was needed for the questions a proof cannot answer: what to trust, what to make default, and what was worth doing.

## 2. Where performance stands (measured 2026-10-25, interleaved timing, one session)

**Geomean run time relative to CompCert 3.18** (lower is faster):

| compiler | `test/c` (tuned on) | big programs (held out) | PolyBench (held out) |
|---|---:|---:|---:|
| CompCert 3.18 | 1.000 | 1.000 | 1.000 |
| faster-compcert (defaults) | **0.831** | **0.967** | **0.738** |
| faster-compcert (all opt-in flags) | **0.815** | **0.961** | **0.733** |
| gcc -O1 | 0.893 | 0.950 | 0.756 |
| gcc -O2 (CompCert model) | 0.795 | 0.887 | 0.648 |
| gcc -O2 | 0.784 | 0.886 | 0.646 |
| gcc -O3 | 0.790 | 0.913 | 0.583 |

"All opt-in flags" adds `-fload-op -ftrust-libm` to the defaults. The other three trusted-base optimizations (`-fshift-mask`, `-fzext-load`, `-fmerge-bytes`) became defaults on 2026-10-24.

**Relative to gcc -O2** (1.00 = gcc -O2; lower is faster):

| compiler | `test/c` (tuned on) | big programs (held out) | PolyBench (held out) |
|---|---:|---:|---:|
| CompCert 3.18 | 1.28× | 1.13× | 1.55× |
| faster-compcert (defaults) | 1.06× | 1.09× | 1.14× |
| faster-compcert (all opt-in flags) | 1.04× | 1.09× | 1.13× |
| gcc -O1 | 1.14× | 1.07× | 1.17× |
| gcc -O3 | 1.01× | 1.03× | 0.90× |

**Share of the gap from CompCert 3.18 to gcc -O2 (CompCert model) that is closed** (log-geomean): `test/c` (tuned on): defaults 81%, all flags 89%; big programs (held out): defaults 28%, all flags 33%; PolyBench (held out): defaults 70%, all flags 72%.

**In short:**
- **vs gcc -O1:** faster-compcert is now faster on `test/c` and PolyBench, and about 1-2% behind on the big programs.
- **vs gcc -O2:** it is within **4-6%** on `test/c`, **9%** on the big programs, and **13-14%** on PolyBench. CompCert 3.18 started at 28%, 13% and 55% behind.
- **Overfitting:** the gap closed on the held-out big programs (28-33%) is far smaller than on the tuned-on `test/c` (81-89%). The improvements generalize least to call-heavy, pointer-heavy code.

Raw data is in `results/final.json` and `results/heldout-*.json`. The run had a load average of 2-3; an earlier attempt under load average 73 was discarded.

## 3. How we got here

| round | what | effect | PRs |
|---|---|---|---|
| 0. Diagnosis | 4 agents performed "assembly surgery" on 24 benchmarks: hand-editing CompCert's output one transformation at a time to measure what each missing optimization is worth. GCC pass-family ablation, and GCC restricted to CompCert's model. | Attributed the gap: missing passes (A), x86 codegen (B), real model limits (C), heuristics (D). | — |
| 1. First five changes | heuristics + a second inlining round; Deadcode/CSE precision; x86 instruction selection; **Loadfwd** (new pass); **LICM + loop rotation** (new passes). Integration of the five exposed three interactions, each fixed. | test/c 0.871× CompCert 3.18 | bd83427d |
| Held-out evaluation | the larger CompCert programs + PolyBench (30 kernels), not used for tuning | showed test/c overstated the gains; redirected priorities to loop nests | #17 |
| 2. Loop nests | **LICM of dependent chains**; **IVwiden** (new pass, IV widening and strength reduction) | PolyBench 0.845 → 0.776 (#16), then a further −4.3% (#4) | #18, #21 |
| Fixes | Loadfwd's 65 GB compile-time blow-up; small regressions; the arm build; compile time (round 1) | layout.c 65 GB → 110 MB; spass compile 55 → 46 s | #22, #23, #27, #36 |
| 3. Trusted-base changes | under the approval protocol: memory operands, shift masking, zero-extending loads, `sqrt`/`fabs` builtins, **bounded permissions + unaligned chunk**, pure libm functions; plus a retroactive review | siphash24 −21%, nbody −17%, perlin −15%, nsievebits −6% | #29-#43 |
| Smaller items | rotate recognition; accumulator tail recursion (fib only); a negative result (pressure-aware CSE) | sha3 −3%, fib −46% | #26, #33, #24 |

### The changes (each fully proved; no `Admitted`, no new `Axiom`)

| change | kind | trusted? |
|---|---|---|
| size-based inlining, second inlining round, if-conversion, block layout | heuristics + composition of existing proofs | no |
| Deadcode/CSE precision; rotate recognition | improved existing passes | no |
| x86 instruction selection (fused zero-extensions, `x/2`, false dependencies) | selection + Asm instructions | yes (ledger 2-3, reviewed retroactively) |
| **Loadfwd**: load forwarding across join points | new RTL pass, verified Kildall analysis | no |
| **LICM + loop rotation**, incl. dependent chains | new RTL passes, untrusted oracle + verified validator | no |
| **IVwiden**: induction-variable widening and strength reduction | new RTL pass, oracle + validator | no |
| **Tailacc**: accumulator tail recursion; bounded recursive inlining | new RTL pass + Inlining change | no |
| **Loadop**: x86 arithmetic with memory operands (`-fload-op`) | new Linear pass + 8 Asm instructions | yes (ledger 1) |
| shift-count masking (`-fshift-mask`, default) | Asm semantics refinement | yes (ledger 4) |
| `sqrt`/`fabs` builtins; 50 pure libm functions (`-ftrust-libm`) | C front end + builtin semantics | yes (ledger 5, 8) |
| zero-extending loads (`-fzext-load`, default) | 4 Asm instructions | yes (ledger 6) |
| bounded permissions + `Mint64u` + byte-load merging (`-fmerge-bytes`, default) | memory-model change + CSE | yes (ledger 7) |

Overall size, compared with upstream CompCert 3.18:
- **Compiler sources:** 116 files, +16,655 / −351 lines. That is +14,771 Rocq and +2,627 OCaml, with 33 new Rocq files (including per-target stubs).
- **Trusted base:** 11 trusted files touched, in 8 ledger entries.
- **`Print Assumptions`:** grew from 35 to 52 entries. All 17 additions are command-line flags, validated oracles, or the four uninterpreted libm `Parameter`s. There is no new `Axiom`.
- **Bookkeeping:** 23 merged PRs, and 21 issues, 16 of them closed.

## 4. Where human input was needed

The owner's interventions, in order. Everything else, including diagnosis, design, implementation, proofs, testing, benchmarking and merging, was done by agents, with an orchestrating agent auditing each result.

| when | decision | why a human was needed |
|---|---|---|
| start | the research question, the scope, and "don't commit agent metadata" | goals |
| after round 1 | publish the report; create issues and PRs for bookkeeping | outward-facing actions |
| #1 | **adopt the trusted-base approval protocol**; defer CI | a gate that proofs cannot provide: a wrong semantic assumption silently voids the correctness theorem |
| ongoing | "merge PRs that don't need my approval"; "issues and PRs are only bookkeeping" | delegation of authority |
| #5, #10, #11, #12 (×2), #13, #25 | **approve each trusted-base change**, on exact text | each one changes what CompCert's theorem means |
| #12 phase 2 | scope: all 50 libm functions rather than the recommended 8 | a policy trade-off (the `errno` contract) |
| #13 | after the first proposal proved impossible, **choose option A** (a memory-model change) among three | weighing the size of the trusted change against the payoff |
| #14 | **defer**, after the approved proposal was found to be wrong | judging whether the trusted-base cost is worth it |
| #25 | permit a git rebase that the permission system had blocked for an agent | security boundary: agents must not route around a denied permission |
| defaults | **make three trusted-base optimizations the default**; keep `-ftrust-libm` and `-fload-op` opt-in | product decision |

### What the human gate caught, and what it didn't

- **The gate's real value was forcing written, checkable proposals.**
- **Twice, the owner approved a proposal that was wrong:** #14 (it claimed `Pfreeframe` never reads the back-link) and #13 (it claimed 8 byte loads imply one 8-byte load, which fails at the 2^64 boundary). Both were caught by the **implementing agents**, which were required to stop rather than improvise trusted changes. One agent proved the #13 counterexample in Coq.
- **What changed afterwards:** every proposal is now prototyped (the trusted definitions are built and the key lemma is proved in a scratch copy), and every claim about existing semantics is checked against the source *before* it goes to the owner. Lesson: human approval is necessary but not sufficient; it must be backed by mechanical evidence.

## 5. What was automatable, and how well it worked

**Fully automated, reliably:**
- **Diagnosis.** Assembly surgery and pass ablation attributed the gap per benchmark, with causal measurements, in about an hour of agent time per benchmark group.
- **Implementation and proof of non-trivial passes.** The largest were Loadfwd (about 1,900 lines, with a redesign of its abstract domain), IVwiden (about 3,250), Tailacc (about 1,400), LICM (about 1,500), Loadop (about 1,000) and the bounded-permission memory model (23 files of fallout).
  - Each took one agent a few hours, typically 10-40 compile/fix iterations.
  - Translation validation (an untrusted oracle plus a verified checker) proved especially agent-friendly.
- **Differential testing of trusted assumptions.** The extracted Coq semantics were compared bit for bit against the CPU (`asm_difftest`: 9 instruction groups) and glibc (`libm_difftest`: 2.4 billion calls).
- **Cross-target proof repair.** All 6 targets were kept building.
- **Finding counterexamples.** The #13 wraparound was proved in Coq by an agent.
- **Bookkeeping.** Issues, PRs, the report, the ledger and the roadmap.

**Automated, but needing an orchestrator's audit.** Every agent result was independently re-checked:
- the axiom diff;
- a clean rebuild;
- the regression suite;
- trusted diffs compared against the approved text;
- assembly identity with a flag off;
- re-timing on a different core.

**The audits caught real problems:**
- Loadfwd's 65 GB compile-time blow-up;
- an arm build failure that proofs alone missed;
- an agent's claim that "nothing is running" when wait loops were still alive.

**Where automation went wrong** (and was caught):
- **Integration.** Changes that were each good measured worse together: Loadfwd×CSE spilling, rotation×layout. This needed combined ablations.
- **Measurement.** The machine is shared, and identical binaries varied by up to ±40% on memory-bound kernels. The harness timed configurations sequentially until a whole run was invalidated. Fix: interleaved timing, plus "attribute timing only where the assembly differs".
- **Process errors by the orchestrator:**
  - a bookkeeping file overwritten by a failed script run;
  - a partial documentation commit.

  Both are fixed; the scripts now fail loudly.
- **Overfitting.** Heuristics tuned on `test/c` gained much less on held-out code (round 1: −13% on test/c vs −2% on the big programs). This became visible only after the held-out evaluation was added.
- **Low-value work.** Some items were narrow (fib: −46% on one microbenchmark) or negative (#7). Choosing work by measured payoff on held-out code, rather than by the original list, mattered more as the project went on.

## 6. Limitations

- **Gains generalize unevenly.**
  - Loop-nest code (PolyBench) gained the most: from 1.55× to 1.13× gcc -O2.
  - Call- and pointer-heavy programs gained the least: the big programs went from 1.13× to 1.09×, and only one of them (lzss) beats gcc -O2.
  - None of the new passes targets that kind of code. Its remaining costs are the fixed calling convention, the frame back-link, and memory disambiguation limited to disjoint offsets and abstract pointers.
- **Remaining largest gaps vs gcc -O2** (all opt-in flags):
  - **test/c:** fib 1.27×, nbody 1.23×, spectral 1.23×, fftsp 1.18×, sha3 1.11×.
  - **big:** arcode 1.30×, raytracer 1.14×, spass 1.10×.
  - **PolyBench:** nussinov 1.57×, heat-3d 1.46×, floyd-warshall 1.45×, jacobi-1d 1.35×, trmm 1.32×.
  - **gcc -O3** is a further 10% ahead on PolyBench, mostly from vectorization.
- **The heuristics were tuned on `test/c`.** Inlining sizes, the if-conversion cost, LICM and IVwiden register-pressure limits, the CSE cap and rotation rules were all chosen on one 24-program suite and one CPU (Xeon Silver 4314). The held-out numbers above are the honest measure; other CPUs are untested.
- **Compile time** is 1.3-1.5× CompCert 3.18 (spass 46 s vs 31 s; `layout.c` 6.5 s vs 4.9 s). Memory is back to normal after the Loadfwd fix.
- **The trusted base grew.** There are 8 ledger entries:
  - memory model: a permission bound;
  - C front end: `-ftrust-libm`;
  - builtin semantics: four uninterpreted libm functions;
  - x86 Asm: 17 new instructions and refined shifts;
  - printer and expander changes.

  Each was approved by the owner and validated against the hardware or glibc. Still, the end-to-end theorem now rests on more assumptions, from 35 to 52 `Print Assumptions` entries.
- **Two opt-in flags change behaviour or have regressions.**
  - `-ftrust-libm` follows GCC's `-fno-math-errno`: programs must not use `errno` to detect libm errors, and it assumes glibc's libm (validated only for glibc 2.35 on x86-64).
  - `-fload-op` has an unexplained code-placement regression on syrk.
- **Measurement.**
  - One shared, noisy machine; memory-bound kernels such as gramschmidt vary by up to ±40% between runs even with interleaving.
  - Single-session minimums are reported.
  - Measurements before 2026-10-24 used sequential timing (see REPORT §22).
- **Verification scope.**
  - Every new pass is proved, and its proofs check on all six targets.
  - But only x86-64 has non-stub implementations of the new target hooks (IVwiden, LICM `op_safe`, Loadop, byte merging). The other targets get correct but unoptimized code.
  - Upstream's regression suite (154 tests) is the only functional test besides the benchmarks.

## 7. Blockers

These would need more than another verified pass.

1. **SIMD.** CompCert's x86 Asm model has no vector registers or instructions. GCC -O3's main advantage (vectorization) is impossible without a large trusted-base extension of `Asm.v`: 128/256-bit registers, vector operations, and their memory semantics.
2. **Type-based alias analysis.** CompCert's C semantics has no effective types, so `-fstrict-aliasing` reasoning is not justified by the model. Adding effective types is a change to the C semantics and the memory model.
3. **The calling convention is fixed in the semantics.** There is no IPA-RA: every call clobbers all caller-save registers, which hurts float-heavy code across calls (fftsp, integr before inlining). Per-callee clobber sets would change the LTL/Mach/Asm call semantics.
4. **Frame back-link (#14).** The Asm model restores the stack pointer from memory. Making this faithful needs the caller's stack pointer in the Asm state, a large trusted change.
5. **Floating point.** FMA contraction, reassociation and `-ffast-math` are forbidden by CompCert's exact IEEE semantics. They could only be added as opt-in semantic deviations, like `-ftrust-libm`.
6. **Infrastructure.** There is no CI (deferred, #3): proofs and tests run manually on each PR. The machine is shared and noisy, and the root disk is nearly full.
7. **Compile time** is 1.5× CompCert 3.18 on spass. The remaining cost comes from analyses whose cheap shortcuts are not exact (#9).

## 8. Roadmap

### Near term (verified-only; no trusted-base change)
- **Remaining gap diagnosis.** Before choosing more passes, measure (assembly surgery) the largest remaining PolyBench and big-program gaps. Known candidates:
  - gemm's invariant `A[i][k]` load, which is not hoisted because it might alias the `C[i][j]` store: **load hoisting with alias analysis**;
  - uncoalesced register copies;
  - the largest measured PolyBench gaps to gcc -O2, not yet analysed: nussinov 1.57×, heat-3d 1.46×, floyd-warshall 1.45×, jacobi-1d 1.35×, trmm 1.32×, durbin 1.31×. No PolyBench kernel beats gcc -O2 yet.
  - the big programs: arcode 1.30×, raytracer 1.14× and spass 1.10× (call- and pointer-heavy code; see Limitations).
- **#44:** LICM of pure libm calls (perlin −5-10%) and the CSE relaxation. Low payoff; do it after the above.
- **#9:** compile time.
- **`-fload-op`:** fix its code-placement regression (syrk), then consider making it the default.
- **Loop alignment** and **profile-guided block layout.** These are heuristics only, so cheap, and they addressed variance seen throughout.
- **CI (#3):** six-target `make proof` + `make ccomp`, the regression suite, and an axiom-allowlist gate.

### Medium term (verified)
- **Global value numbering / partial redundancy elimination** that subsumes Loadfwd and CSE, with proper alias analysis (points-to, not just disjoint offsets).
- **Loop unrolling** and **software pipelining** (translation-validated).
- **Better register allocation**: live-range splitting with a cost model (the #7 attempt showed that the cost model is the hard part), and rematerialization.
- **Instruction scheduling** for in-order or wide targets (validated, as in CompCert-KVX).

### Beyond -O2 (needs trusted-base or semantic decisions)
- **Vectorization.**
  - First: a vector extension of the x86 Asm model (SSE2, then AVX2), approved and difftested like ledger entries 1-7.
  - Then: a translation-validated SLP or loop vectorizer.
  - This is the largest step toward -O3, and the largest new trusted base.
- **Polyhedral loop transformations** (interchange, tiling, fusion), validated per loop nest. PolyBench is their home turf; GCC -O2 does not do them, so they would go *beyond* GCC -O2 on loop-nest code.
- **Interprocedural optimization:** IPA-RA (requires per-callee clobber semantics), constant propagation across calls, and whole-program inlining with link-time optimization.
- **Opt-in fast-math family:** FMA contraction, reassociation and reciprocal approximation, each as an explicit, documented semantic deviation, like `-ftrust-libm`.
- **Effective types / TBAA:** a C-semantics change, the deepest and most contentious item.

### Process
- **Every trusted-base proposal** is prototyped and source-checked before approval. The owner approves exact text, and implementers stop rather than improvise.
- **Benchmarks:** always interleaved, always on held-out suites, attributing only where the code differs.
- **Cost of a change:** compile time and memory (`compile_cost.py`) count alongside run time.
