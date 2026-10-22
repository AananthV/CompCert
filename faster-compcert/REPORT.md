# faster-compcert: report

This report asks two questions:

1. **Why is CompCert slower than GCC -O2?** Is it a limitation of CompCert's
   semantic models of C and x86-64, or of the set of verified passes that
   CompCert currently has?
2. **If it is the passes, can LLM agents find, implement and *prove* the
   missing transformations?**

**Short answer.**

1. The models are not the main bottleneck. If GCC -O2 is restricted to what
   CompCert's semantics allow, it is still 20% faster than CompCert. The
   restriction itself costs GCC only about 1.5 points.
2. Agents wrote, proved and merged five sets of changes, about 5,100 lines of
   which 4,470 are Rocq. They take CompCert from 1.00 to 0.871 of its original
   run time (geometric mean over 24 benchmarks). That is faster than gcc -O1
   (0.891) and closes about 60% of the gap to "gcc -O2 within CompCert's model"
   (0.794).
3. No new axioms were added. The proofs check on all six targets, and the
   regression suite passes.
4. **Held-out caveat (§7):** on code that was not used for tuning, the gains
   are smaller. The larger CompCert test programs reach 0.982 (gcc -O1:
   0.949), and PolyBench reaches 0.845 (gcc -O1: 0.739). The main remaining
   gap there is address arithmetic in loop nests.

Setup: CompCert 3.18, Rocq 9.1.1, OCaml 4.14.2, GCC 11.4, Intel Xeon Silver 4314.

- Every timing is the minimum over at least 7 runs (at least 1.5s in total),
  pinned to one core. Every run's output is checked against `test/c/Results`.
- `perf` was not available on the machine, so attribution below uses
  "assembly surgery": hand-edit CompCert's `.s` output for one transformation,
  re-assemble it, check the output, and time it.

---

## 1. Phase 1: where does the gap come from?

### 1.1 GCC restricted to CompCert's semantic model

CompCert's semantics forbid some optimizations that GCC performs. GCC has
flags that switch each of them off:

| CompCert semantics | GCC flag |
|---|---|
| signed overflow wraps around (no undefined-behaviour exploitation) | `-fwrapv` |
| no type-based alias analysis | `-fno-strict-aliasing` |
| no SIMD instructions in the x86-64 Asm model | `-fno-tree-vectorize` |
| no FMA contraction | `-fp-contract=off` |

We call `gcc -O2` with these four flags **gcc-O2-ccmodel**. The table below
shows run times relative to CompCert, so lower is faster.

| config | geomean vs CompCert |
|---|---:|
| CompCert 3.18 `ccomp -O` | 1.000 |
| gcc -O1 | 0.892 |
| gcc -O2 | 0.783 |
| **gcc -O2-ccmodel** | **0.795** |
| gcc -O3-ccmodel | 0.751 |

Restricting GCC to CompCert's model costs it about 1.5 points out of a
22-point gap. The rest of the gap must come from transformations that
CompCert's semantics would allow but that CompCert does not perform.

### 1.2 Leave-one-out ablation of GCC passes

Starting from gcc-O2-ccmodel, we turn off one family of GCC passes at a time
(`harness/ablate.sh`). Each value is a slowdown relative to gcc-O2-ccmodel,
so 1.00 means turning the family off has no effect. The "CompCert" column is
CompCert's own time relative to gcc-O2-ccmodel.

| benchmark | CompCert | inline | pre | ivopts | reassoc | licm | looprot | ifconv | layout | sched | vrp | sra | thread | builtin |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| fib | 2.99 | 1.56 | 0.89 | 0.92 | 1.00 | 1.01 | 0.96 | 1.01 | 1.17 | 1.00 | 1.02 | 0.99 | 0.99 | 1.00 |
| integr | 2.16 | 1.96 | 1.00 | 0.99 | 0.98 | 1.00 | 1.03 | 1.00 | 1.00 | 0.97 | 1.03 | 0.99 | 0.99 | 0.99 |
| qsort | 0.98 | 1.00 | 0.96 | 0.98 | 1.00 | 1.00 | 0.97 | 0.99 | 0.97 | 1.00 | 1.00 | 1.00 | 0.97 | 1.00 |
| fft | 1.09 | 1.00 | 1.00 | 1.01 | 1.00 | 1.01 | 1.00 | 1.00 | 1.00 | 0.99 | 1.01 | 1.00 | 1.00 | 1.02 |
| fftsp | 1.12 | 1.00 | 1.00 | 0.99 | 1.01 | 1.02 | 1.01 | 1.00 | 1.00 | 1.00 | 0.99 | 1.00 | 0.99 | 1.11 |
| fftw | 1.06 | 0.99 | 0.99 | 0.99 | 1.00 | 1.00 | 1.00 | 1.00 | 1.00 | 0.99 | 0.99 | 1.00 | 0.99 | 0.99 |
| sha1 | 1.32 | 0.99 | 0.99 | 1.11 | 1.11 | 1.00 | 1.00 | 1.00 | 1.00 | 0.99 | 1.00 | 0.99 | 0.99 | 0.99 |
| sha3 | 1.52 | 0.99 | 0.99 | 1.15 | 0.99 | 0.99 | 0.99 | 1.00 | 1.00 | 1.00 | 0.99 | 0.99 | 0.96 | 0.99 |
| aes | 1.15 | 1.00 | 0.85 | 0.96 | 1.03 | 1.00 | 1.00 | 1.00 | 1.01 | 1.00 | 1.00 | 1.00 | 1.00 | 1.00 |
| almabench | 1.04 | 1.00 | 1.00 | 1.02 | 0.99 | 1.00 | 0.99 | 1.00 | 1.00 | 0.99 | 0.99 | 1.00 | 0.99 | 0.99 |
| lists | 1.04 | 1.00 | 1.00 | 1.01 | 1.00 | 1.01 | 1.20 | 1.00 | 1.04 | 1.00 | 1.01 | 1.00 | 1.00 | 1.00 |
| binarytrees | 1.12 | 1.06 | 1.03 | 1.03 | 1.02 | 1.02 | 1.05 | 1.04 | 1.01 | 1.02 | 1.03 | 1.02 | 1.04 | 1.02 |
| fannkuch | 0.98 | 1.00 | 0.98 | 0.98 | 0.97 | 0.98 | 0.98 | 0.98 | 0.99 | 1.00 | 1.04 | 1.00 | 1.01 | 0.99 |
| knucleotide | 1.03 | 1.00 | 0.99 | 1.01 | 1.01 | 1.00 | 1.02 | 1.00 | 1.00 | 0.99 | 1.01 | 1.00 | 0.99 | 1.02 |
| mandelbrot | 1.04 | 1.00 | 1.00 | 1.00 | 1.00 | 1.00 | 1.00 | 1.00 | 1.00 | 0.99 | 1.00 | 1.00 | 0.99 | 1.00 |
| nbody | 1.50 | 1.00 | 0.97 | 1.02 | 0.99 | 0.99 | 0.98 | 0.97 | 0.96 | 0.98 | 0.97 | 1.00 | 0.97 | 1.04 |
| nsieve | 1.06 | 1.02 | 0.99 | 1.01 | 1.00 | 1.01 | 1.01 | 1.02 | 1.12 | 1.02 | 1.03 | 1.01 | 1.00 | 1.01 |
| nsievebits | 1.15 | 1.00 | 1.00 | 1.01 | 1.00 | 0.99 | 1.00 | 1.00 | 1.05 | 1.03 | 1.00 | 1.00 | 1.00 | 1.00 |
| spectral | 1.87 | 1.02 | 1.88 | 1.04 | 0.97 | 1.01 | 0.99 | 1.00 | 0.98 | 1.02 | 1.01 | 1.00 | 1.00 | 1.02 |
| vmach | 1.49 | 1.00 | 1.00 | 1.01 | 1.00 | 1.01 | 1.00 | 1.00 | 1.01 | 1.01 | 1.00 | 1.00 | 1.00 | 1.01 |
| bisect | 0.97 | 0.98 | 1.01 | 1.00 | 1.00 | 1.01 | 1.00 | 0.99 | 1.00 | 1.00 | 1.01 | 1.00 | 1.00 | 0.98 |
| chomp | 1.04 | 1.04 | 1.00 | 1.01 | 1.00 | 1.02 | 0.99 | 1.02 | 1.00 | 1.00 | 1.02 | 1.00 | 0.99 | 0.99 |
| perlin | 1.41 | 1.18 | 1.06 | 1.00 | 0.90 | 1.02 | 1.00 | 1.05 | 0.92 | 1.01 | 1.00 | 1.00 | 1.00 | 1.00 |
| siphash24 | 1.43 | 1.00 | 1.00 | 1.00 | 1.01 | 1.00 | 1.03 | 1.00 | 1.00 | 1.03 | 1.00 | 1.00 | 1.00 | 1.00 |
| **geomean** | **1.258** | 1.060 | 1.013 | 1.009 | 0.999 | 1.004 | 1.008 | 1.003 | 1.008 | 1.001 | 1.006 | 1.000 | 0.994 | 1.006 |

What the ablation shows:

- **Single families with a large effect:**
  - Inlining explains fib, integr and perlin.
  - PRE/GVN explains spectral (1.88x, which matches CompCert's 1.87x).
  - Induction-variable optimizations and reassociation explain about 11-15% on
    sha1 and sha3.
- **Benchmarks no single family explains:** sha3, nbody, vmach, siphash24
  and sha1. Either GCC's passes compensate for each other there, or the cause
  is in code generation rather than in an optimization pass.

### 1.3 Causal attribution by assembly surgery

For each benchmark with a large gap, we hand-applied one transformation at a
time to CompCert's assembly, checked the output, and measured the time. The
causes fall into four classes:

- **A:** a missing middle-end (RTL) optimization that CompCert's semantics
  would permit.
- **B:** backend code generation (instruction selection, register
  allocation, peephole).
- **C:** a genuine limitation of CompCert's C or x86-64 model.
- **D:** an unverified heuristic choice, where a change needs no proof.

| benchmark (ccomp / gcc-O2-ccmodel) | cause | class | measured effect of fixing it |
|---|---|---|---|
| spectral (1.87) | `Au[i]` is reloaded every iteration. CSE works only on extended basic blocks, so its knowledge is lost at the loop header. | A | 0.783 -> 0.464 s (85% of the gap) |
| integr (2.16) | the call through a constant function pointer becomes direct only after inlining has already run, so the callee is never inlined | A/D | 0.691 -> 0.310 s (all of the gap) |
| fib (2.99) | no accumulator tail recursion, no recursive inlining, no loop rotation | A/D | 0.626 -> 0.316 s |
| sha3 (1.52) | dead stores to the local array `bc[]` are kept: `NeedDomain.nmem_add` treats any load through a `Nonstack` pointer as reading the whole stack | A | 33.1 -> 28.2 ms |
| sha3 | CSE kills `st[j+1..4]` after a store to `st[j]` (no check for disjoint offsets) | A | -1.5 ms |
| aes (1.15) | global table addresses recomputed at every lookup (no LICM) | A | 85.2 -> 77.2 ms |
| aes | redundant `movl %r,%r` 32->64-bit zero-extensions (23 per round) | B | 85.2 -> 77.6 ms |
| sha1 (1.32) | `int` index not widened to 64 bits (needs range information), offsets not folded into addressing modes | A/B | 57.6 -> 46.8 ms |
| sha1 | `rol 1` not recognized (a shift by 1 has already become `lea`) | B | -2 ms |
| vmach (1.49) | if-conversion turns the interpreter's `pc` update into a `cmove`, which removes branch prediction | D | 70.7 -> 53.6 ms |
| nbody (1.50) | `sqrt` is an opaque libm call, so values are spilled around it; no load-op memory operands; no strength reduction | C/B/A | 133 -> 95 ms |
| nbody | **latent bug:** `__builtin_sqrt` emits `sqrtsd %x5,%x1` with a false dependency on `%x1` | B | 184 -> 112 ms |
| perlin (1.41) | `floor` is opaque (cannot be shared or hoisted); `grad` is not inlined | C/D | 55.7 -> 32.0 ms |
| siphash24 (1.43) | 8 byte loads cannot be merged into one 64-bit load: `Mint64` requires 8-byte alignment in the memory model | C | 89.1 -> 66.8 ms |
| nsieve/nsievebits | block layout takes 2 jumps per iteration; `andq $31,%rcx` before shifts (shift-count masking is not modelled) | D/C | ~-4% each |

**Conclusion of phase 1.** Most of the gap is in classes A, B and D. Class C,
genuine model limitations, matters for three groups of programs:

- programs that rely on libm: nbody, perlin, fftsp;
- programs that would need unaligned or merged memory accesses: siphash24;
- small x86 details: shift-count masking and the frame back-link.

---

## 2. Phase 2: verified transformations written by agents

Each change was given to an agent in its own git worktree, together with the
phase-1 diagnosis. The rules were the same for every change:

- complete proofs: no `Admitted`, `admit` or new `Axiom`;
- a new `Parameter` only for an untrusted oracle whose output is validated, or
  whose choice cannot affect correctness;
- the regression suite must pass;
- speedups must be measured.

Every result was re-checked independently: `Print Assumptions` on the
end-to-end theorems, a rebuild from scratch, the test suite, and re-timing on
a different core.

### 2.1 The changes

| # | change | kind | size | flag |
|---|---|---|---|---|
| 1 | size-based inlining heuristic; a second Inlining -> Constprop round; if-conversion heuristic; latch placement in Linearize | heuristics + composition of existing proofs | ~260 lines added | `-finline-small-functions` |
| 2 | Deadcode: loads through `Nonstack`/`Glob` pointers no longer make the stack frame live. CSE: offset-disjointness test, including int-indexed arrays with 32-bit overflow | changed proofs | ~470 lines added | (always on) |
| 3 | x86: fused zero-extending ops `Ozextshruimm`/`Ozextandimm`/`Ozextshlimm`; rotates by 1..3; `x/2` sequence; breaking false dependencies of `cvtsi2sd`/`sqrtsd` | instruction selection, Asm, proofs | ~380 lines added | (always on) |
| 4 | **new pass `Loadfwd`**: global load forwarding across join points and back edges | new RTL pass with a verified Kildall analysis | 916 + 1038 lines | `-floadfwd` |
| 5 | **new passes `Looprot` + `LICM`**: loop rotation and loop-invariant code motion | untrusted oracle + verified validator | ~1,500 lines | `-floop-rotate`, `-flicm` |

New RTL pipeline (changes marked `*`):

```
Tailcall -> Inlining -> Renumber -> Constprop -> Renumber
  -> *Inlining(2) -> *Renumber -> *Constprop -> *Renumber
  -> *Looprot -> *LICM -> *Renumber -> *Loadfwd(insert) -> *Loadfwd
  -> CSE -> Deadcode -> Unusedglob -> Allocation -> ...
```

### 2.2 How each change is proved

- **Inlining round 2.** Inlining takes a round number, and its correctness
  lemmas are parameterized by it. `Compiler.v` composes the existing
  simulations once more. That proof went through on the first try.
- **Deadcode.** A `Nonstack`/`Glob` abstract pointer satisfies
  `bc b <> BCstack`, so it cannot point into the current stack frame. Only two
  `nlive` lemmas needed new cases.
- **CSE disjointness.** A load equation is kept after a store when the load
  address is provably "store address + d" and the byte ranges do not overlap
  modulo 2^64.
  - For indices of the form `(long)(x + c)`, the 32-bit addition may wrap, so
    two candidate values of d are generated and both must be disjoint.
  - The candidates come from a per-architecture function,
    `CombineOp.addr_deltas`. It is real on x86 and a stub elsewhere.
- **x86 zero-extensions.** New Asm instructions
  `Pshrlzx_ri`/`Pandlzx_ri`/`Psallzx_ri` have the semantics
  `Val.longofintu (op32 x)`, which is the hardware rule that a 32-bit write
  zeroes the upper half. They are printed as plain `shrl`/`andl`/`sall`.
- **Loadfwd.** The pass has two parts.
  1. *Move insertion.* A fresh register `t_L` is created for each memory
     location (chunk, addressing mode, symbolic arguments). The pass inserts
     `t_L := r` after loads and full-width stores of that location.
     - This is a plus-simulation, with registers agreeing up to `max_reg`.
     - A copy is kept only if the analysis later actually forwards through it.
       This avoids feeding CSE copies that only increase register pressure.
  2. *Forwarding.* A forward Kildall analysis tracks facts "r = expr" and
     "r >= load(chunk, addr, args)", and replaces a matching load by a move.
     - At join points, facts are generalized by anti-unification. This
       unifies `long32signed(x6)` held in `x15` on one edge and in `x8` on the
       other.
     - The proof is a CSEproof-style lock-step simulation with `regs_lessdef`
       and `Mem.extends`.
- **LICM.** An OCaml oracle computes dominators, natural loops and the code
  to hoist. Coq rebuilds the function from these hints and `check_function`
  validates it. Among other things, it checks that:
  - each loop is entered only through its header;
  - each hoisted op is `op_safe`, i.e. proved never to fail, so executing it
    speculatively is sound;
  - each hoisted op does not depend on memory;
  - its arguments are invariant in the loop;
  - its destination register is fresh.

  The simulation invariant is: "at every node of loop L, `t` holds
  `op(args)`". The validator does not rely on the loops being natural, so the
  oracle remains untrusted.
- **Looprot.** A generic node-duplication validator. Each transformed node
  must be a copy of its original with only its successors redirected, and each
  new successor must be a copy of the corresponding original successor. The
  proof is a lock-step simulation.

### 2.3 Effect of each change alone

Each value is the change applied alone to master, relative to master (lower is
better).

| benchmark | heuristics + 2nd inlining | dead-store/alias | x86 isel | load forwarding |
|---|---:|---:|---:|---:|
| fib | 0.79 | 0.99 | 0.99 | 0.99 |
| integr | 0.46 | 1.00 | 0.99 | 1.00 |
| qsort | 1.00 | 1.00 | 0.99 | 1.00 |
| fft | 0.98 | 0.98 | 0.93 | 0.93 |
| fftsp | 0.99 | 0.98 | 0.97 | 0.99 |
| fftw | 0.99 | 1.00 | 0.99 | 0.99 |
| sha1 | 1.00 | 1.00 | 0.92 | 1.00 |
| sha3 | 0.99 | 0.82 | 0.99 | 0.99 |
| aes | 1.00 | 1.00 | 0.87 | 1.00 |
| almabench | 1.00 | 1.00 | 1.00 | 1.00 |
| lists | 1.00 | 1.00 | 1.00 | 1.00 |
| binarytrees | 0.88 | 1.00 | 0.99 | 0.98 |
| fannkuch | 1.00 | 1.00 | 1.00 | 1.00 |
| knucleotide | 1.00 | 0.99 | 0.99 | 0.98 |
| mandelbrot | 1.00 | 1.00 | 1.00 | 1.00 |
| nbody | 1.00 | 0.97 | 0.93 | 0.97 |
| nsieve | 0.85 | 1.00 | 0.99 | 0.98 |
| nsievebits | 0.97 | 1.00 | 0.99 | 0.99 |
| spectral | 1.00 | 1.00 | 1.00 | 0.60 |
| vmach | 0.75 | 1.00 | 0.96 | 0.99 |
| bisect | 1.00 | 1.00 | 1.00 | 1.00 |
| chomp | 0.94 | 1.00 | 0.99 | 0.99 |
| perlin | 0.78 | 1.00 | 1.00 | 1.00 |
| siphash24 | 1.00 | 1.00 | 0.92 | 1.00 |
| **geomean** | **0.922** | **0.987** | **0.974** | **0.968** |

Changes 4 and 5 measured alone, by their authors:

- LICM + rotation: aes -10.9%, sha1 -7.6%, siphash24 -4.8%, fannkuch -4.5%,
  geomean -1.5%. Before the fixes in 2.4 there was one regression: lists
  +13%.
- Loadfwd: spectral 0.126 -> 0.0755 s, faster than gcc-O2-ccmodel.

### 2.4 Interactions found while merging

Measured individually, every change looked good. Merged naively, the five
changes gave 0.889, *worse* than four of them alone (0.885). Ablating them with
their `-fno-*` flags inside one binary found three interactions:

1. **Loadfwd x CSE (sha3: 28.4 -> 33.6 ms).** Loadfwd forwarded nothing in
   `keccakf`, but the copies `t_L := r` it inserted were picked up by the new,
   more precise CSE as replacement registers. That merged ~27 values into
   one register and caused heavy spilling. *Fix:* keep only the fresh
   registers that are actually used, and prefer original registers in
   `find_load`.
2. **Loop rotation x latch placement (nsieve +16%, lists +15%).**
   - nsieve: rotation turns the latch's `goto H` into a copy of the exit test.
     The latch is then no longer eligible for latch placement, and the common
     path takes two branches per iteration. *Fix:* don't rotate loops whose
     latch starts at a join point.
   - lists: the rotated test reads a register just written by `l = next`.
     *Fix:* don't rotate when an argument of the exit test is defined by a
     move inside the loop.
3. **Proof portability.** Some proof scripts worked on x86-64 only:
   - automatically generated hypothesis names;
   - `simpl` reducing architecture stubs;
   - `eauto` closing goals earlier on arm;
   - `Archi.ptr64 = false` making hypotheses contradictory on x86_32.

   All of them were rewritten to be robust. They now check on x86_64,
   x86_32, aarch64, arm, powerpc and rv64.

---

## 3. Final results

| benchmark | CompCert 3.18 | faster-compcert | gcc -O1 | gcc -O2 (CompCert model) | gcc -O2 | gcc -O3 |
|---|---:|---:|---:|---:|---:|---:|
| fib | 57.7 | 45.7 | 56.5 | 19.3 | 19.3 | 18.5 |
| integr | 36.0 | 16.7 | 36.3 | 16.7 | 16.7 | 16.6 |
| qsort | 122.1 | 121.9 | 117.4 | 124.9 | 125.0 | 119.8 |
| fft | 61.9 | 57.7 | 56.6 | 57.0 | 56.6 | 56.5 |
| fftsp | 33.3 | 32.2 | 27.0 | 29.7 | 27.0 | 27.1 |
| fftw | 52.6 | 50.0 | 49.5 | 49.5 | 49.0 | 48.7 |
| sha1 | 58.7 | 50.4 | 43.7 | 44.2 | 44.1 | 81.4 |
| sha3 | 34.1 | 28.4 | 22.7 | 22.3 | 22.3 | 17.2 |
| aes | 83.6 | 67.5 | 65.1 | 72.8 | 72.4 | 72.3 |
| almabench | 227.5 | 227.0 | 220.3 | 218.2 | 216.4 | 213.2 |
| lists | 74.0 | 73.9 | 71.4 | 71.4 | 71.3 | 71.4 |
| binarytrees | 29.5 | 25.9 | 30.3 | 27.0 | 26.9 | 25.2 |
| fannkuch | 197.9 | 191.5 | 194.9 | 202.7 | 193.3 | 213.4 |
| knucleotide | 115.8 | 116.8 | 114.9 | 112.9 | 113.3 | 108.7 |
| mandelbrot | 112.9 | 112.6 | 110.5 | 108.6 | 108.4 | 108.7 |
| nbody | 131.6 | 121.9 | 95.0 | 84.8 | 85.6 | 160.3 |
| nsieve | 112.3 | 95.9 | 103.0 | 105.9 | 105.8 | 106.2 |
| nsievebits | 95.1 | 91.6 | 88.6 | 82.9 | 82.9 | 83.0 |
| spectral | 125.9 | 72.9 | 125.7 | 67.3 | 57.3 | 61.0 |
| vmach | 69.0 | 50.4 | 48.4 | 46.4 | 46.6 | 46.5 |
| bisect | 73.3 | 73.2 | 79.0 | 74.9 | 75.1 | 73.0 |
| chomp | 161.6 | 153.2 | 158.9 | 155.9 | 153.1 | 154.3 |
| perlin | 54.0 | 43.3 | 35.3 | 38.4 | 38.5 | 24.1 |
| siphash24 | 90.3 | 86.0 | 81.0 | 63.3 | 63.2 | 50.2 |
| **geomean vs CompCert** | **1.000** | **0.871** | **0.891** | **0.794** | **0.783** | **0.790** |

(Times are in ms. `faster-compcert` is this fork with all changes enabled.)

- **Overall:** faster-compcert is **0.871x** CompCert 3.18's time. That is
  ahead of gcc -O1 (0.891) and about **60%** of the way to gcc-O2-ccmodel
  (0.794), in log-geomean terms.
- **Where it now matches or beats gcc-O2-ccmodel:** integr, aes, binarytrees,
  fannkuch, nsieve, bisect and chomp, plus qsort, which was already ahead.
- **Where it is close:** spectral (73 vs 67 ms) and vmach (50 vs 46 ms).
- **Costs:** object-code `.text` of the 24 programs grows by +5.1% (57,257 ->
  60,167 bytes), mostly from inlining. Compiling `test/c` takes 1.43 -> 2.10 s
  (**+47%**): the second Inlining/Constprop round, Loadfwd's three analysis
  runs, LICM's dominator computation, and larger functions after inlining.
  Compile time was not optimized.

### Verification status

- `Print Assumptions transf_c_program_correct` shows 5 additions compared with
  master (`results/axioms-*.txt`):
  - three command-line flags, of the same kind as the existing `optim_*`:
    `Compopts.optim_loadfwd`, `optim_licm`, `optim_looprot`;
  - two untrusted oracles whose output is always validated by verified code:
    `LICM.licm_oracle`, `Looprot.rotate_oracle`.
- No `Admitted`, `admit` or `Axiom` was added.
- `make proof` succeeds for x86_64, x86_32, aarch64, arm, powerpc and rv64.
- `make -C test all test` passes: 154 tests.
- **Trusted base:** the Asm semantics of the three new zero-extending
  instructions, and the printer changes. The printer emits extra `xorps`/`xorpd`
  to clear a destination register before `cvtsi2sd`/`cvtss2sd`/`sqrtsd`.

---

## 4. What the assembly looks like

### spectral: `eval_A_times_u` inner loop (load forwarding + LICM + rotation + x86 fixes)

Before: `Au[i]` (`0(%rdx,%rax,8)`) is loaded, added to and stored on every
iteration. The loop is tested at the top, with a `jmp` back.
```asm
.L102:  cmpl    %edi, %r8d
        jge     .L103
        movsd   .L104(%rip), %xmm0
        leal    0(%r9d,%r8d,1), %eax
        leal    1(%r9d,%r8d,1), %r10d
        imull   %r10d, %eax
        testl   %eax, %eax              # x/2 via test/lea/cmov/sar
        leal    1(%eax), %ecx
        cmovl   %rcx, %rax
        sarl    $1, %eax
        leal    1(%eax,%r9d,1), %r10d
        cvtsi2sd %r10d, %xmm5           # false dependency on old xmm5
        divsd   %xmm5, %xmm0
        movslq  %r9d, %rax              # loop-invariant sign extension
        movsd   0(%rdx,%rax,8), %xmm1   # reload Au[i]
        movslq  %r8d, %r10
        movsd   0(%rsi,%r10,8), %xmm4
        mulsd   %xmm4, %xmm0
        addsd   %xmm0, %xmm1
        movsd   %xmm1, 0(%rdx,%rax,8)   # store Au[i]
        leal    1(%r8d), %r8d
        jmp     .L102
```
After: `Au[i]` stays in `%xmm1`, which carries the loop dependency, so only the
store remains. `movslq %r10d,%r9` is hoisted before the loop. The test is at
the bottom. `x/2` is `shr/lea/sar`. `cvtsi2sd`'s destination is cleared first.
```asm
.L103:  movsd   .L104(%rip), %xmm0
        leal    0(%r10d,%r8d,1), %eax
        leal    1(%r10d,%r8d,1), %r11d
        imull   %r11d, %eax
        movq    %rax, %rcx
        shrl    $31, %ecx
        leal    0(%eax,%ecx,1), %eax
        sarl    $1, %eax
        leal    1(%eax,%r10d,1), %r11d
        xorpd   %xmm3, %xmm3
        cvtsi2sd %r11d, %xmm3
        divsd   %xmm3, %xmm0
        movslq  %r8d, %r11
        movsd   0(%rsi,%r11,8), %xmm4
        mulsd   %xmm4, %xmm0
        addsd   %xmm0, %xmm1            # Au[i] forwarded in a register
        movsd   %xmm1, 0(%rdx,%r9,8)
        leal    1(%r8d), %r8d
        cmpl    %edi, %r8d
        jl      .L103
```
spectral: 125.9 -> 72.9 ms.

### aes: `rijndaelEncrypt` round loop (zero-extension fusion + LICM)

Before: every table lookup recomputes `leaq TeN(%rip)` and zero-extends the
index with `movl %r,%r`.
```asm
        leaq    Te0(%rip), %r9
        movq    %rbx, %rdx
        shrl    $24, %edx
        movl    %edx, %edx              # zero-extension
        movl    0(%r9,%rdx,4), %r10d
        leaq    Te1(%rip), %r11
        movq    %r8, %r9
        shrl    $16, %r9d
        andl    $255, %r9d
        movl    %r9d, %edx              # zero-extension
        movl    0(%r11,%rdx,4), %r11d
        xorl    %r11d, %r10d
```
After: the table bases live in `%rdx/%r9/%r14/%r8`, hoisted out of the loop.
`shrl`/`andl` are `Pshrlzx`/`Pandlzx`, whose 64-bit result is already
zero-extended.
```asm
        movq    %rax, %r10
        shrl    $24, %r10d
        movl    0(%rdx,%r10,4), %r13d
        movq    %r12, %r10
        shrl    $16, %r10d
        andl    $255, %r10d
        movl    0(%r9,%r10,4), %r10d
        xorl    %r10d, %r13d
```
Static counts for `rijndaelEncrypt`:

| | before | after |
|---|---:|---:|
| instructions | 433 | 363 |
| `movl %r,%r` | 34 | 0 |
| `leaq sym(%rip)` | 48 | 20 |

aes: 83.6 -> 67.5 ms, faster than gcc -O2 (72.4 ms).

### integr: `test` (second inlining round)

Before: `f(x)` (with `f = square`) becomes a direct `call square` only after
inlining has run. All xmm registers are caller-saved, so `s`, `x` and `h` live
in stack slots across the call.
```asm
.L101:  testl   %ebx, %ebx
        jle     .L102
        movsd   24(%rsp), %xmm0
        call    square
        movsd   16(%rsp), %xmm3
        addsd   %xmm0, %xmm3
        movsd   %xmm3, 16(%rsp)
        leal    -1(%ebx), %ebx
        movsd   24(%rsp), %xmm4
        movsd   32(%rsp), %xmm5
        addsd   %xmm5, %xmm4
        movsd   %xmm4, 24(%rsp)
        jmp     .L101
```
After: the second round inlines `square`. Everything stays in registers, and
the loop is rotated.
```asm
.L102:  movapd  %xmm1, %xmm2
        mulsd   %xmm1, %xmm2
        addsd   %xmm2, %xmm0
        leal    -1(%edi), %edi
        addsd   %xmm3, %xmm1
        testl   %edi, %edi
        jg      .L102
```
integr: 36.0 -> 16.7 ms, the same as gcc -O2.

### vmach: `wordcode_interp` (if-conversion heuristic)

Before: the conditional branch of the interpreted program becomes a `cmove`
on the interpreter `pc`. The next instruction fetch then depends on the
comparison through a data dependency, which defeats branch prediction.
```asm
        leaq    0(%r12,%rcx,4), %rdi
        cmpq    $0, %r11
        cmove   %r12, %rdi
        movq    %rdi, %r12
        jmp     .L100
```
After: a conditional update `if (c) x = e` is if-converted only when `e`
costs at most 3, so this becomes a predictable branch. The same function also
loses all 6 of its redundant `movl %r,%r`.

vmach: 69.0 -> 50.4 ms.

### sha3: `keccakf` (Deadcode precision)

The 34 stores per round to the local array `bc[]` are now recognized as dead
and removed. Before, every load through the parameter `st` (a `Nonstack`
pointer) made the whole stack frame live.

| | before | after |
|---|---:|---:|
| instructions | 329 | 290 |
| stores to `(%rsp)` | 41 | 8 |
| rotates recognized | 21 | 24 |

sha3: 34.1 -> 28.4 ms.

---

## 5. What remains, and what it would take

| remaining gap | example | class | what it would take |
|---|---|---|---|
| libm functions are opaque | nbody (`sqrt`), perlin (`floor`), fftsp (`sincosf`) | C | a trusted spec of libm functions, or an opt-in flag that maps them to builtins. The `sqrtsd` dependency fix (change 3) makes `__builtin_sqrt` profitable: nbody 182 -> 112 ms. |
| unaligned / merged memory accesses | siphash24 (82% of its gap) | C | an unaligned 64-bit memory chunk in the memory model |
| widening `int` induction variables | sha1, sha3 | A | an interval / range analysis in ValueAnalysis |
| load-op memory operands | nbody (-10%), aes (-3%) | B | Asm instructions with memory operands; Deadcode/CSE invariants for operators that read memory |
| accumulator tail recursion, recursive inlining | fib | A | a new pass; a bounded-depth Inlining proof |
| register allocation around calls | fftsp, nbody | B/C | live-range splitting; per-callee clobber sets (IPA-RA) |

## 6. Observations about agent-written proofs

- **Proof volume is not the bottleneck.** The largest pass, Loadfwd, is about
  1,950 lines. Its author's first design passed its proofs quickly but was
  imprecise: substituting definitions too early broke monotonicity at loop
  headers. It needed one redesign of the abstract domain, using
  anti-unification. Most other proofs needed about 10-15 compile/fix
  iterations, mostly for tactic details.
- **Translation validation is agent-friendly.** For LICM and loop rotation,
  agents wrote untrusted OCaml oracles and small verified checkers. The
  checkers are simpler to prove, and they keep the heuristics free to change.
- **Performance engineering was harder than the proofs.** The most expensive
  part was diagnosing performance interactions:
  - register pressure (the CSE cap; Loadfwd's copies feeding CSE);
  - layout (rotation vs. latch placement);
  - micro-architectural effects (the rotated test reading a register that was
    just written).

  This needed measuring each pass alone, then the merged set, and ablating
  with flags.
- **Proof robustness across targets was a real issue.** Several proofs
  depended on x86-only reductions. Checking all targets is needed before
  merging.

---

## 7. Held-out evaluation (issue #2)

Every faster-compcert heuristic was tuned on `test/c`. To see how well the results generalize, we measured two suites that played **no role** in tuning, with no retuning:

- **`big`:** the larger programs of the CompCert test suite: `raytracer`, `spass`, and the three `compression` programs, each checked against a reference result.
- **`polybench`:** the 30 PolyBench/C 4.2.1 kernels, at a dataset size chosen per kernel. Results are checked by dumping the arrays at MEDIUM size and comparing against gcc -O0.

Both run with `harness/bench.py --suite big|polybench`, minimum of 3 runs, in seconds. Raw data: `results/round1/heldout-*.json`.

| suite (geomean vs CompCert 3.18) | faster-compcert | gcc -O1 | gcc -O2 (CompCert model) | share of the gap to gcc-O2-ccmodel closed |
|---|---:|---:|---:|---:|
| `test/c` (tuned on) | 0.871 | 0.891 | 0.794 | 60% |
| `big` (held out) | **0.982** | 0.949 | 0.886 | 15% |
| `polybench` (held out) | **0.845** | 0.739 | 0.643 | 38% |

**The `test/c` result overstates the general effect.**

- On held-out code, faster-compcert is still faster than CompCert 3.18, but it **does not beat gcc -O1** in either suite. It beats gcc -O1 on only 2/5 big programs and 7/30 PolyBench kernels.
- The large integer programs gain almost nothing. Their remaining gap is in code that none of the new passes target: pointer chasing, calls, and struct-heavy code.

### big

| program | CompCert 3.18 | faster-compcert | gcc -O1 | gcc -O2 (CompCert model) | gcc -O2 |
|---|---:|---:|---:|---:|---:|
| raytracer | 0.826 | 0.831 | 0.749 | 0.681 | 0.669 |
| spass | 5.693 | 5.633 | 5.356 | 5.100 | 5.076 |
| arcode | 0.496 | 0.489 | 0.403 | 0.374 | 0.373 |
| lzw | 2.607 | 2.366 | 2.585 | 2.327 | 2.329 |
| lzss | 3.749 | 3.852 | 4.204 | 4.127 | 4.125 |
| **geomean vs CompCert** | **1.000** | **0.982** | **0.949** | **0.886** | **0.882** |

### polybench

| program | CompCert 3.18 | faster-compcert | gcc -O1 | gcc -O2 (CompCert model) | gcc -O2 |
|---|---:|---:|---:|---:|---:|
| correlation | 5.132 | 5.127 | 5.035 | 4.702 | 4.710 |
| covariance | 5.145 | 5.108 | 5.027 | 4.691 | 4.733 |
| 2mm | 5.366 | 2.926 | 5.184 | 2.517 | 2.517 |
| 3mm | 8.759 | 4.621 | 8.465 | 3.868 | 3.858 |
| atax | 0.057 | 0.033 | 0.036 | 0.029 | 0.029 |
| bicg | 0.053 | 0.036 | 0.033 | 0.033 | 0.033 |
| doitgen | 1.655 | 0.952 | 1.436 | 0.724 | 0.725 |
| mvt | 0.315 | 0.247 | 0.238 | 0.206 | 0.206 |
| gemm | 1.990 | 1.962 | 0.950 | 0.949 | 0.951 |
| gemver | 0.339 | 0.273 | 0.256 | 0.225 | 0.225 |
| gesummv | 0.132 | 0.115 | 0.103 | 0.103 | 0.103 |
| symm | 2.215 | 1.948 | 1.696 | 1.731 | 1.728 |
| syr2k | 3.659 | 3.383 | 2.669 | 2.998 | 2.985 |
| syrk | 1.351 | 1.352 | 0.758 | 0.760 | 0.761 |
| trmm | 2.176 | 2.072 | 2.015 | 1.545 | 1.552 |
| cholesky | 0.130 | 0.123 | 0.090 | 0.077 | 0.078 |
| durbin | 0.027 | 0.025 | 0.023 | 0.019 | 0.018 |
| gramschmidt | 5.780 | 5.633 | 5.686 | 6.049 | 6.088 |
| lu | 0.161 | 0.154 | 0.120 | 0.091 | 0.091 |
| ludcmp | 0.127 | 0.123 | 0.086 | 0.089 | 0.088 |
| trisolv | 0.121 | 0.059 | 0.072 | 0.058 | 0.059 |
| deriche | 0.401 | 0.372 | 0.361 | 0.356 | 0.359 |
| floyd-warshall | 0.246 | 0.225 | 0.097 | 0.097 | 0.097 |
| nussinov | 6.900 | 5.789 | 6.766 | 3.476 | 3.410 |
| adi | 0.111 | 0.110 | 0.110 | 0.104 | 0.103 |
| fdtd-2d | 3.180 | 3.131 | 1.905 | 2.085 | 1.922 |
| heat-3d | 0.061 | 0.060 | 0.029 | 0.031 | 0.031 |
| jacobi-1d | 0.011 | 0.011 | 0.008 | 0.008 | 0.008 |
| jacobi-2d | 4.276 | 3.767 | 2.173 | 2.274 | 2.141 |
| seidel-2d | 0.238 | 0.236 | 0.232 | 0.235 | 0.234 |
| **geomean vs CompCert** | **1.000** | **0.845** | **0.739** | **0.643** | **0.639** |

### Findings

1. **Where the new passes generalize.**
   - Kernels with a loop-carried accumulator in memory, like `C[i][j] += ...` in an inner `k` loop, gain 30-50% from **Loadfwd**: trisolv 0.49×, 3mm 0.53×, 2mm 0.55×, doitgen 0.57×, atax 0.59×, bicg 0.68×. This is the same pattern as spectral.
   - lzw gains 9%.
2. **The largest remaining gap: address arithmetic in loop nests.** The worst kernels against gcc-O2-ccmodel are floyd-warshall 2.31×, gemm 2.07×, heat-3d 1.92×, syrk 1.78×, lu 1.69×, nussinov 1.67×, jacobi-2d 1.66× and cholesky 1.59×. Even **gcc -O1** is about 2× faster on gemm, syrk, floyd-warshall and heat-3d. In gemm's inner loop (`C[i][j] += alpha*A[i][k]*B[k][j]`) faster-compcert executes 21 instructions per iteration; gcc -O1 executes 8.

   faster-compcert:
   ```asm
   .L114:  movq    %rsi, %r8
           imulq   $8800, %r8              # C[i] row base: invariant in the j loop
           leaq    0(%rbp,%r8,1), %r8
           movslq  %edx, %r11
           movq    %r11, %rcx
           movsd   0(%r8,%rcx,8), %xmm0
           movq    %rsi, %r10
           imulq   $9600, %r10             # A[i] row base: invariant
           leaq    0(%r12,%r10,1), %r10
           movslq  %r9d, %rax
           movsd   0(%r10,%rax,8), %xmm6   # A[i][k]
           movapd  %xmm2, %xmm3
           mulsd   %xmm6, %xmm3
           imulq   $8800, %rax             # B[k] row base: invariant
           leaq    0(%rbx,%rax,1), %r10
           movsd   0(%r10,%rcx,8), %xmm4
           mulsd   %xmm4, %xmm3
           addsd   %xmm3, %xmm0
           movsd   %xmm0, 0(%r8,%r11,8)
           leal    1(%edx), %edx
           cmpl    $1100, %edx
           jl      .L114
   ```
   gcc -O1:
   ```asm
   .L12:   movapd  %xmm2, %xmm0
           mulsd   (%rcx), %xmm0
           mulsd   (%r9,%rdx), %xmm0
           addsd   (%rdi,%rdx), %xmm0
           movsd   %xmm0, (%rdi,%rdx)
           addq    $8, %rdx
           cmpq    $8800, %rdx
           jne     .L12
   ```
   Three missing transformations, in order of impact:
   - (a) **LICM of chains of dependent pure operations.** `movslq i` → `imulq $8800` → `leaq base` is invariant, but faster-compcert's LICM hoists only single operations whose arguments are defined outside the loop. It does not hoist chains, nor ops whose argument was itself hoisted. This is a new Tier 1 item, #16.
   - (b) **Strength reduction** of `j` into a pointer increment (#4).
   - (c) **Memory operands** on arithmetic (#5).
3. **Regressions** (reproduced with ≥7 runs):
   - lzss is +2.8% slower than CompCert 3.18. With `-fno-loadfwd` it is 4% faster than with load forwarding on, and with `-fno-loop-rotate` 2.6% faster.
   - jacobi-1d (10 ms) is +2.8% slower.

   These are heuristic problems to fix under #7 / #16, not retuned here.
4. **What this means for the roadmap.** The next items should be chosen by their effect on held-out code, not on `test/c`. Address arithmetic in loop nests (#16, #4) dominates PolyBench. fib-specific work (#8) matters least.

---

## 8. Round 2: LICM of dependent chains (issue #16)

§7 showed that loop nests over 2-D arrays recompute their row base
addresses (`movslq i; imulq $ROW; leaq base`) on every inner iteration. The
LICM oracle now finds invariant operations as a fixpoint: an operation can
depend on other hoisted operations, or on copies of registers defined outside
the loop. Each chain is hoisted, in dependency order, to the outermost loop
where all of it is invariant.

The validator was extended in two ways, and the proof covers both:
- a hoisted operation may use hoisted registers defined earlier in the same
  preheader;
- a replaced instruction may use registers that are only *equal* to the
  hoisted arguments. These equations are produced by the oracle, and the
  validator checks that they form an inductive invariant of the transformed
  code.

Separately, loop rotation no longer copies loads into the rotated header,
which fixes the lzss regression from §7.

Cost of the change:
- 9 files, about 850 lines added.
- No trusted-base files touched.
- `Print Assumptions` unchanged.
- Proofs check on all six targets.
- 154 regression tests pass.
- Compile time on `test/c` is unchanged (1.80 s vs 1.82 s).

### Results

The same-session comparison against the previous master gives:
- PolyBench: **0.912×**;
- big programs: 0.986×;
- `test/c`: 1.001× (no program moves more than 2%).

Times in seconds:

| kernel | before #16 | after #16 | change | gcc -O1 |
|---|---:|---:|---:|---:|
| gemm | 1.959 | 1.408 | -28% | 0.952 |
| syrk | 1.359 | 0.986 | -27% | 0.775 |
| floyd-warshall | 0.226 | 0.168 | -26% | 0.097 |
| jacobi-2d | 3.800 | 2.958 | -22% | 2.157 |
| 2mm | 2.930 | 2.583 | -12% | 5.186 |
| fdtd-2d | 3.142 | 2.442 | -22% | 1.937 |
| lu | 0.155 | 0.135 | -13% | 0.121 |
| heat-3d | 0.059 | 0.051 | -13% | 0.030 |
| ludcmp | 0.124 | 0.103 | -17% | 0.088 |
| cholesky | 0.122 | 0.103 | -16% | 0.090 |
| gramschmidt | 5.652 | 5.804 | +3% | 5.957 |

gemm's inner loop goes from 21 to 13 instructions; gcc -O1 has 8.
```asm
.L114:  movslq  %r9d, %rsi
        movq    %r11, %r15              # uncoalesced copy
        movq    %rsi, %rdi              # uncoalesced copy
        movsd   0(%r15,%rdi,8), %xmm4   # C[i][j]
        movsd   0(%r10,%r8,8), %xmm8    # A[i][k]: invariant load, not hoisted
        movapd  %xmm5, %xmm6
        mulsd   %xmm8, %xmm6
        movsd   0(%rcx,%rdi,8), %xmm7   # B[k][j]
        mulsd   %xmm7, %xmm6
        addsd   %xmm6, %xmm4
        movsd   %xmm4, 0(%r11,%rsi,8)
        leal    1(%r9d), %r9d
        cmpl    $1100, %r9d
        jl      .L114
```
What remains in this loop:
- **Indexed addressing** instead of a pointer increment, and the `movslq` of `j`
  (#4).
- **The invariant load `A[i][k]`.** gcc -O1 also reloads it, because the store
  to `C[i][j]` may alias it.
- **Two copies that register allocation does not coalesce.** Removing them by
  hand gains only 1-2%.

**Known regression:** gramschmidt is +2.7% (memory-bound column walks; cause
not yet understood).

### Totals after round 2

All measured in one session against CompCert 3.18. Raw data is in
`results/final.json` and `results/heldout-*.json`; round-1 data is in
`results/round1/`.

| suite (geomean vs CompCert 3.18) | faster-compcert | gcc -O1 | gcc -O2 (CompCert model) | gcc -O2 |
|---|---:|---:|---:|---:|
| `test/c` (tuned on) | 0.877 | 0.887 | 0.791 | 0.781 |
| big (held out) | 0.966 | 0.948 | 0.886 | 0.886 |
| PolyBench (held out) | **0.776** (was 0.845) | 0.749 | 0.648 | 0.643 |

`test/c` and gcc moved by up to 0.6% from round 1 although their code did
not change. That is the machine's run-to-run drift between sessions.

---

## 9. Round 3: induction-variable widening and strength reduction (issue #4)

A new RTL pass, `IVwiden`, runs after LICM (`-fiv-widen`).

**What it does.** Take a 32-bit loop variable `i` that is incremented once
per iteration. An untrusted oracle:
- introduces a 64-bit shadow `li = (long)i`, and derived values
  `p = b + li*m` with `b` loop-invariant;
- maintains them on loop entry and after the increment;
- rewrites:
  - computations of `b + (long)i*m + d` into moves or `p + d`;
  - signed exit tests on `i` into 64-bit tests on `li`;
  - addressing modes, folding constant offsets.

**How it is checked.** A verified validator checks that:
- the oracle's facts form an inductive invariant of the transformed code. The
  facts are `x = b + (long)i*m + d`, register equalities, and bounds on 32-bit
  values;
- inserted nodes only compute safe operations into fresh registers;
- the facts justify each rewrite.

The crucial rule: an increment `i = i + c` keeps the facts about `i` only if
the bounds prove that `i + c` cannot overflow. For example, a guard `i < n`
on the path gives `i ≤ max-1`. If the check fails, the function is left
unchanged.

**Cost.**
- About 3,250 new lines; the largest file is `IVwidenproof.v` (1,614).
- The proof is a plus-simulation, executing inserted chains by fuel.
- The x86 recognizers are in `x86/IVop.v`; the other targets have stubs that
  disable the pass.
- New assumptions: the flag `Compopts.optim_ivwiden` and the validated oracle
  `IVwiden.iv_oracle`.
- No trusted-base files touched.
- Proofs check on all six targets.
- 154 regression tests pass.
- Compile time on `test/c`: +5%.

### Results (same session, previous master vs this change; min of ≥3 runs, seconds)

| suite | geomean ratio |
|---|---:|
| `test/c` | 0.989 |
| big | 1.005 |
| PolyBench | **0.957** |

| program | before #4 | after #4 | change |
|---|---:|---:|---:|
| sha1 | 0.0513 | 0.0447 | -12.8% |
| sha3 | 0.0290 | 0.0260 | -10.5% |
| gemm | 1.4121 | 1.0469 | -25.9% |
| ludcmp | 0.1016 | 0.0882 | -13.2% |
| syrk | 0.9822 | 0.8587 | -12.6% |
| heat-3d | 0.0490 | 0.0434 | -11.6% |
| doitgen | 0.8451 | 0.7498 | -11.3% |
| fdtd-2d | 2.4661 | 2.1962 | -10.9% |
| cholesky | 0.1033 | 0.0922 | -10.7% |
| jacobi-2d | 2.9777 | 2.6978 | -9.4% |
| symm | 1.8226 | 1.8810 | +3.2% |
| floyd-warshall | 0.1686 | 0.1764 | +4.6% |
| raytracer | 0.8000 | 0.8219 | +2.7% |

gemm's inner loop is now 11 instructions; it was 13, and gcc -O1 has 8.
```asm
.L114:  movsd   0(%rdi,%rcx,8), %xmm6   # C[i][j], 64-bit index, no movslq
        movsd   0(%rdx,%r11,8), %xmm7
        movapd  %xmm3, %xmm4
        mulsd   %xmm7, %xmm4
        movsd   0(%rsi,%rcx,8), %xmm8
        mulsd   %xmm8, %xmm4
        addsd   %xmm4, %xmm6
        movsd   %xmm6, 0(%rdi,%rcx,8)
        leaq    1(%rcx), %rcx
        cmpq    $1100, %rcx
        jl      .L114
```
- sha1's message expansion now uses `movl -12(%r9,%rdi,4)`, which is what the
  assembly surgery of §1.3 predicted.
- Column walks (2mm, syrk, gramschmidt) step a pointer with
  `leaq 7200(%rdi),%rdi` instead of `imulq; leaq`.

**Regressions:**
- **raytracer +2.7%.** Changing a lookup loop inside the interpreter makes the
  register allocator spill the token pointer on the dispatch path.
- **floyd-warshall +4.6% and symm +3.2%.** In floyd-warshall the inner loop
  drops from 12 to 10 instructions; it is branchy and layout-sensitive.

These and gramschmidt (§8) are tracked together in #20.

**Limitations.**
- Only `i = i + c` with a single increment, and only signed comparisons.
- Flattened indices (`i*n + j`) and `k - i` are not handled.
- The exit test stays on `li`; it is not moved onto the pointer.
- x86 only.

**Found while testing: compile-time blow-up.** `test/abi/layout.c` takes
3.9 s and 123 MB with CompCert 3.18, but 367 s and **65 GB** with master after
round 2. Bisecting with `-fno-*` flags points at **Loadfwd**: with
`-fno-loadfwd` it takes 8.9 s and 132 MB. This is tracked in #19 and fixed
next.

---

## 10. Fix: Loadfwd compile-time and memory blow-up (issue #19)

**Root cause.** The analysis recorded an expression fact ("r = op(args)") for
every operation result. CompCert's RTL rarely reuses registers, so these facts
were never killed, and the fact set grew linearly along straight-line code.
On the 4,220-node main function of a truncated `layout.c` there were about
1,200 facts per program point. In addition, `kill_reg`/`kill_loads` rebuilt
the whole map at every instruction, so the maps at different program points
shared no structure. Both time and memory were therefore quadratic, and this
happened in each of the three analysis runs.

**Fix.**
- Expression facts are now kept only for *relevant* registers: address
  arguments of loads and stores, and transitively, up to depth 8, the
  arguments of the operations that define them. Load facts are always kept.
- A size guard skips the analysis on functions where
  #instructions × #relevant registers exceeds 2·10⁷.
- Both changes only remove facts, which is trivially sound. The lattice and
  Kildall proofs are unchanged; the transfer lemmas take the relevance set as
  a parameter.
- Load/store locations are computed once per function, and the second
  analysis is skipped when there is no candidate.
- Generated code is unchanged: identical assembly on all 101 files of
  `test/c`, raytracer, compression and spass, and on the 30 PolyBench kernels.

**New check.** `harness/compile_cost.py` measures compile time and peak memory
on `test/abi/layout.c`, `staticlayout.c`, spass and `test/c`, under a memory
cap. Results are in `results/compile-cost.json`.

| target | CompCert 3.18 | master before fix | after fix |
|---|---:|---:|---:|
| layout.c | 4.0 s / 126 MB | 367 s / 65 GB | 11.2 s / 112 MB |
| staticlayout.c | 2.5 s / 74 MB | 66.8 s / 9.8 GB | 4.4 s / 65 MB |
| spass (51 files) | 30.0 s / 47 MB | 61.0 s / 270 MB | 52.8 s / 90 MB |
| test/c (24 files) | 1.5 s / 20 MB | 2.2 s / 28 MB | 2.0 s / 24 MB |

Memory is back to CompCert 3.18 levels. Compile *time* is still 1.3-2.8×
CompCert 3.18. The remaining cost is spread over the other new passes (on
layout.c, IVwiden, LICM and Looprot take 1.6-1.8 s each), and is tracked in
#9.

---

## 11. Small regressions (issue #20)

We re-examined the regressions reported in §8 and §9, each by `-fno-*`
ablation, assembly diffs and padding sweeps.

| program | finding | outcome |
|---|---|---|
| floyd-warshall (+4.6%) | **Real.** In `path[i][j] = path[i][j] < s ? path[i][j] : s`, the register allocator's coalescing tie-break made the common "keep" arm a taken branch: two taken branches per iteration. | Fixed by a new layout rule. 0.177 → 0.146 s (−17.5%), better than with IVwiden disabled (0.168 s). |
| raytracer (+2.7%) | **Code placement.** Inserting 8-56 bytes of padding between object files moves run time by ±2.5-4% for both builds. Averaged over paddings, IVwiden is 0.6% faster. | A general loop-exit layout rule: 0.823 → 0.794 s (−3.5%). |
| symm (+3.2%) | **Noise.** Its assembly is identical to master's. | No change. |
| gramschmidt (+2.7%) | **Unexplained.** DRAM-bound; identical binaries vary by 0.88-1.12× between sessions. | No change. |
| jacobi-1d | No regression (10.1 vs 10.2 ms). | No change. |

**The two layout rules** are in `backend/Linearizeaux.ml`, the unverified
oracle behind Linearize, whose proof accepts any block order.
- **Conditional update.** Take a loop block that loads `r` from an address,
  whose successor stores `r` back to the same address, with an alternative
  path through a moves-only block that assigns `r`. Then the path that
  leaves memory unchanged (e.g. a min/max relaxation that does not fire) is
  laid out as the fall-through. This fires in floyd-warshall and in one spass
  function.
- **Loop exit.** When a loop block falls through into an exit block and its
  in-loop successor follows right after, the exit run is moved after the
  loop.

**Results** (same session vs master):

| measure | result |
|---|---:|
| `test/c` geomean | 1.005 (no program > 2%) |
| big geomean | 0.991 |
| PolyBench geomean | 0.990 |
| spass compile time | 59.3 → 52.9 s |

Proofs and axioms are unchanged, and 154 tests pass.

**A lesson about measurement.** In the same verification run, symm measured
**+7.5%** and gramschmidt **−7%**, although both compile to *byte-identical*
assembly. That is run-to-run noise on this shared machine, for memory-bound
kernels. From now on, a timing difference is only attributed to a change if
the program's assembly differs. Differences of a few percent elsewhere in
this report (the §8/§9 regressions in particular) should be read with that in
mind.

---

## 12. Register-pressure-aware CSE and live-range splitting (issue #7): not merged

Two ideas were implemented, fully proved or validated, and measured. Neither
paid for its cost, so neither is merged. The code is kept on branch
`issue-7-cse-pressure` for reference.

1. **A register-pressure estimate in CSE**, replacing the fixed cap of 8 on
   loads kept by the disjoint-offset check.
   - **How:** liveness plus RTL types, with partial keeping of the oldest
     candidates. Soundness holds because keeping any subset is sound.
   - **Result:** no measurable gain. sha3 measured 25.9 vs 26.2 ms, which is
     within noise.
   - **Why:** sha3's Theta step has about 10 live registers and 24
     candidates, so the estimate keeps the same 5 as the old cap. Keeping
     more spills; gcc -O2 also spills here (46 `%rsp` references in
     `keccakf`).
   - **Cost:** about 4% compile time on spass (liveness), and ~280 lines of
     proof.
2. **Live-range splitting around call-free loops**, in the unverified part
   of register allocation, which the Allocation validator checks.
   - **How:** a variable is a candidate if it is spilled, live across a call,
     and used but not defined in the loop. It gets a copy at the loop entry,
     its uses inside the loop are renamed, and allocation is redone.
   - **Result:** fftsp −2.2% (all 6 reloads of `cc1/ss1/cc3` leave the inner
     loop) and nbody −0.9%. All other programs are unchanged.
   - **Cost:** **+5.7% compile time on spass**, from the second allocation.

**Lessons.**
- At this point the remaining gap is not in CSE precision or spill
  placement.
- **Compile time has become a cost that every new change must justify**
  (#9).
- **Found along the way:** 64-bit rotates by 1 are not recognised. sha3
  compiles `ROTL64(x,1)` to `lea/mov/shr/or`, 5 times per round. This is an
  instruction-selection fix, added to #6.

---

## 13. Rotates recognised during CSE (issue #6, Tier 1 part)

**Rotates.** sha3 compiled `ROTL64(x,1)` to `lea/mov/shr/or` 5 times per
round. Selection only matches `(x << n) | (x >>u (64-n))` when both sides
are the same variable. Here they are two loads of the same location, which
only become equal after CSE.
- x86 `CombineOp` now rewrites `Oorl`/`Oor` of a left shift (including the
  scaled-`lea` form) and a right shift of the same value number into a
  rotate, with a proof in `CombineOpproof.v` (176 lines in total).
- sha3 goes from 24 to 29 rotate instructions and is **−3.4%** faster.
- No other program's assembly changes.

**Stack-array addressing: dropped.** LICM now hoists the `leaq N(%rsp)`
array bases out of loops, so they are no longer recomputed per access.
Assembly surgery rewriting sha1's accesses to `ofs(%rsp,idx,4)` gives no
gain (44.5 vs 44.7 ms).

**Remaining Tier 2 parts of #6.** Zero-extending byte loads and byte-field
extraction need new Asm instructions. They are moved to #25.
