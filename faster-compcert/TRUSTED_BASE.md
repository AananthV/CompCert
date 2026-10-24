# Trusted-base ledger

Every change to CompCert's trusted base accepted under the protocol of
[issue #1](https://github.com/AananthV/CompCert/issues/1) is listed here. The
trusted base covers:
- axioms and parameters other than flags and validated oracles;
- the semantic models of C, memory and Asm;
- unverified code that runs after the proofs: printers, expanders,
  extraction, the runtime and the C front end.

## 1. x86 arithmetic with memory operands (#5)

- **Approved:** by the owner, 2026-10-22, for exactly the proposal on #5.
- **Merged in:** "Add Loadop: verified fusion of loads into x86 arithmetic memory operands".
- **Flag:** `-fload-op`, off by default. Making it the default needs a separate decision.

**Assumption.** There are eight new `x86/Asm.v` instructions:
`Paddd_fm`, `Psubd_fm`, `Pmuld_fm`, `Pdivd_fm` (`addsd/subsd/mulsd/divsd m64, xmm`)
and `Paddl_rm`, `Pxorl_rm`, `Pandl_rm`, `Porl_rm` (`addl/xorl/andl/orl m32, r32`).
Their semantics:
```coq
Definition exec_loadop (chunk: memory_chunk) (f: val -> val -> val) (setflags: bool)
                       (m: mem) (a: addrmode) (rs: regset) (rd: preg) :=
  match Mem.loadv chunk m (eval_addrmode a rs) with
  | Some v => Next ((if setflags then nextinstr_nf else nextinstr) (rs#rd <- (f rs#rd v))) m
  | None => Stuck
  end.
```
They use `Mfloat64` with `Val.addf/subf/mulf/divf` and no flags, and `Mint32`
with `Val.add/xor/and/or` with flags undefined. They are printed by
`x86/TargetPrinter.ml` as `addsd <addr>, %xmmN` etc.

**Justification.**
- Intel SDM Vol. 2: ADDSD/SUBSD/MULSD/DIVSD `xmm1, xmm2/m64`;
  ADD/XOR/AND/OR `r32, r/m32`.
- The memory read is modelled like the existing loads (`Pmovsd_fm`,
  `Pmovl_rm`), and the operation like the existing register forms
  (`Paddd_ff`, `Pxorl_rr`).
- SSE scalar memory operands have no alignment requirement, so CompCert's
  chunk alignment is stricter than the hardware. That is the safe direction.

**Validation.** `harness/asm_difftest/` compares the extracted Coq semantics
bit for bit against the instructions executed on the CPU. It covers about
120,000 cases per instruction: ±0, ±inf, quiet and signalling NaNs with
payloads, denormals, and integer edge values. There were 0 mismatches.

**Revert.** Remove the eight constructors, `exec_loadop` and the printer cases.
Also remove `backend/Loadop*.v`, `*/LoadopOp.v`, `Mloadop`/`Lloadop`, and the
`-fload-op` flag.

## 2. x86 zero-extending 32-bit shift/mask instructions (round 1, retroactive review #10)

- **Approved:** by the owner, 2026-10-22, in a retroactive review (#10).
- **Merged in:** round 1 (bd83427d).
- **Flag:** none, always on. They are produced by instruction selection for
  `(long)(x >> n)`, `(long)(x & n)` and small `(u64)e << n`.

**Assumption.** `x86/Asm.v` gains `Pshrlzx_ri rd n`, `Pandlzx_ri rd n` and
`Psallzx_ri rd n`, with semantics
`rs#rd <- Val.longofintu (Val.shru/and/shl rs#rd (Vint n))` and flags undefined
(`nextinstr_nf`). `x86/TargetPrinter.ml` prints them as `shrl $n, %r32`,
`andl $n, %r32` and `sall $n, %r32`.

**Justification.** Intel SDM Vol. 1 §3.4.1.1: 32-bit operands generate a 32-bit
result, zero-extended to 64 bits in the destination register. Inputs the
compiler never produces are `Vundef`, so they place no constraint on the
hardware.

**Validation.** `harness/asm_difftest/` group `zx`, about 20,000 tests per
instruction with 3 seeds: 0 mismatches wherever the model is defined, on all 64
bits of the result.

**Revert.** Remove the three constructors and their printer cases, and the
`Ozext*` operators and selection rules that produce them (`x86/Op.v`,
`SelectLong.vp`).

## 3. Printer/expander xor-zeroing before partial-register writes (round 1, retroactive review #10)

- **Approved:** by the owner, 2026-10-22, in a retroactive review (#10).
- **Merged in:** round 1 (bd83427d).
- **Flag:** none, always on.

**Change.** `x86/TargetPrinter.ml` emits `xorps`/`xorpd dst,dst` before
`cvtsi2sd/ss(q)` (always), and before `cvtss2sd`/`cvtsd2ss` when dst ≠ src.
`x86/Asmexpand.ml` emits `Pxorpd_f res` before `sqrtsd` when res ≠ src. This
removes false dependencies on the old value of the destination.

**Justification.** Xor-zeroing writes only the destination register. It does
not modify EFLAGS or any modelled state, and the upper lanes of xmm registers
are not modelled. `cvtsi2*` reads a general-purpose register, so its
destination can never alias its source.

**Validation.** `harness/asm_difftest/` group `cvt`, about 20,000 tests per
sequence with 3 seeds:
- the low lane equals the modelled single instruction;
- no other register and no flag changes;
- the upper lanes are zeroed;
- 0 failures.

**Revert.** Remove the xor-emitting lines in `TargetPrinter.ml` and
`Asmexpand.ml`.

## 4. x86 shift-count masking (#11)

- **Approved:** by the owner, 2026-10-22, for exactly the proposal on #11.
- **Merged in:** "x86: model shift-count masking; optional masked-shift selection".
- **Flag:** the semantic refinement is unconditional. The optimization that
  uses it is behind `-fshift-mask`: off by default when merged, **on by
  default since 2026-10-24** (owner decision; `-O0` turns it off).

**Assumption.** In `x86/Asm.v`, the variable-count shifts mask their count:
```coq
  | Psall_rcl rd => Next (nextinstr_nf (rs#rd <- (Val.shl  rs#rd (Val.and rs#RCX (Vint (Int.repr 31)))))) m
  (* likewise Pshrl_rcl (Val.shru) and Psarl_rcl (Val.shr) with 31;
     Psalq_rcl (Val.shll), Pshrq_rcl (Val.shrlu) and Psarq_rcl (Val.shrl) with 63 *)
```
Before this change these shifts were `Val.shl rs#rd rs#RCX` etc., which is
undefined for counts of 32 (or 64) and above.

**Justification.** Intel SDM Vol. 2, SAL/SAR/SHL/SHR: the count is masked to
5 bits (6 with REX.W). This is a refinement: for counts that were defined
before, the new semantics agrees with the old.

**Validation.** `harness/asm_difftest/` group `shift`, against the extracted new
semantics:
- all counts 0..255, with garbage in bits 8..63 of `%rcx`;
- about 20,000 tests per instruction, 3 seeds;
- 0 mismatches, and defined in 100% of the tests. Under the old semantics, only
  6-13% were defined.

**Revert.** Restore the six cases. Then remove the masked operators
(`Oshlmask`, …), their selection rules and the `-fshift-mask` flag.

## 5. `sqrt`/`fabs` as exact builtins under `-ftrust-libm` (#12, phase 1)

- **Approved:** by the owner, 2026-10-22, for phase 1 of the proposal on #12.
- **Merged in:** "C2C: opt-in -ftrust-libm rewrites sqrt/fabs calls into exact builtins".
- **Flag:** `-ftrust-libm`, off by default. It is OCaml-only, so there is no
  new Coq parameter.

**Assumption.** The C front end (`cfrontend/C2C.ml`) rewrites a call to `sqrt`
or `fabs` into `__builtin_fsqrt` / `__builtin_fabs` when all of these hold:
- the callee is the unique, non-static, external (undefined in the program)
  global with exactly the prototype `double(double)`;
- its name never appears outside direct-callee position.

We trust that, on the target platform:
- `sqrt` is the IEEE-754 correctly rounded square root (`Float.sqrt`), and
  `fabs` clears the sign bit (`Float.abs`), for all inputs including NaN
  payloads;
- **`errno` is not set:** sqrt of a negative number does not set `EDOM`, like
  GCC's `-fno-math-errno`. This is documented in the flag's help text.

**Justification.** IEEE 754-2008 §5.4.1 (correctly rounded `squareRoot`). C11
Annex F.10.4.5 and F.10.4.2 (`__STDC_IEC_559__` is defined by glibc on x86-64).

**Validation.** `harness/libm_difftest/` compares glibc 2.35 (called through
volatile pointers, `-fno-builtin`) against the extracted semantics of the
rewritten code.
- Inputs: 15M per function, two seeds. That is 38 special values, 10^7 random
  bit patterns, exact squares ±1 ulp, and subnormals.
- Result: **0 mismatches**, including NaN payload propagation and negative
  inputs (default NaN). The only difference is `errno`.
- `rewrite.sh`: 26 compilations confirm which declarations are and are not
  rewritten: own definitions, `static`, address taken, other prototypes,
  shadowing.

**Platform scope.** Validated for glibc 2.35 on x86-64 only.

**Revert.** Remove `trusted_libm` / `trusted_libm_calls` and the call case in
`C2C.ml`, and the flag.

## 6. Zero-extending 8/16-bit loads and moves with 64-bit results (#25)

- **Approved:** by the owner, 2026-10-22, for exactly the proposal on #25.
- **Merged in:** "x86: opt-in -fzext-load, zero-extending 8/16-bit loads with 64-bit results".
- **Flag:** `-fzext-load`: off by default when merged, **on by default since
  2026-10-24** (owner decision; `-O0` turns it off).

**Assumption.** There are four new `x86/Asm.v` instructions:
- `Pmovzbq_rm rd a` and `Pmovzwq_rm rd a` = `exec_load_zx Mint8unsigned/Mint16unsigned`,
  i.e. `rs#rd <- Val.longofintu v` after the load, with flags undefined;
- `Pmovzbq_rr rd r1` and `Pmovzwq_rr rd r1` =
  `rs#rd <- Val.longofintu (Val.zero_ext 8/16 rs#r1)`.

They are printed exactly like the existing `Pmovzb_rm`/`Pmovzw_rm`/`Pmovzb_rr`/`Pmovzw_rr`
(`movzbl`/`movzwl` into the 32-bit register).

**Justification.**
- Intel SDM Vol. 2, MOVZX: zero-extends the source into the 32-bit destination.
- Intel SDM Vol. 1 §3.4.1.1: a 32-bit destination is zero-extended to 64 bits.

The memory read is modelled like the existing `Pmovzb_rm`/`Pmovzw_rm`.

**Validation.** `harness/asm_difftest/` group `zxload`, comparing the full 64-bit
destination against the extracted semantics:
- coverage: every byte or halfword value, garbage in the upper bits of the
  source and the old destination, and 6 addressing modes at random addresses;
- results: 0 mismatches, and the upper 32 bits were zeroed in 100% of tests;
- undefined cases: only misaligned 16-bit addresses, which the model treats as
  invalid (`Stuck`), exactly as for the existing `Pmovzw_rm`.

**Revert.** Remove the four constructors, `exec_load_zx`, the printer cases, the
`Ozextb64`/`Ozextw64` operators, the selection rules, and the flag.

## 7. Bounded permissions and an unaligned 64-bit chunk (#13, option A)

- **Approved:** by the owner, 2026-10-23, for the corrected proposal (option A)
  on #13. The first proposal was withdrawn as unprovable.
- **Merged in:** "Bounded permissions, unaligned Mint64u chunk, and opt-in byte-load merging".
- **Flag:** the model change is unconditional, and it leaves generated code
  unchanged. Byte merging is behind `-fmerge-bytes`: off by default when
  merged, **on by default since 2026-10-24** (owner decision; `-O0` turns it
  off).

**Assumption.**
1. **Memory model** (`Memtype.v`, `Memory.v`): `perm_limit := Ptrofs.modulus - 8`.
   - Every `mem` satisfies `access_bounded`: no permission at offsets ≥ `perm_limit`.
   - `Mem.alloc` clips its upper bound to `perm_limit`.
   - Allocation lemmas that grant permissions gain the matching premise.
2. **`Mint64u`** (`AST.v`, `Memdata.v`, `Values.v`): an 8-byte, align-1 chunk.
   - Little-endian like `Mint64` for `Vlong`.
   - Pointer-free: pointers store as `Undef` and read back as `Vundef`.
   - It needed a `load_result` case and two forced lemma-spec adjustments,
     listed in the proposal.
3. **x86** (`Asm.v`, `TargetPrinter.ml`): `Pmovq_rm_u`/`Pmovq_mr_u` =
   `exec_load`/`exec_store Mint64u`, printed as `movq`.

**Justification.**
- No real object has a byte at offset ≥ 2^64 − 8: x86-64 user space is below
  2^47 or 2^56, and model offsets are relative to an object.
- Unaligned `movq` is architecturally defined (Intel SDM Vol. 1 §4.1.1;
  AC is off in Linux user mode).

**Validation.**
- **Prototype:** done before approval. 0 admits on all 6 targets, and
  generated code unchanged.
- **`harness/asm_difftest/` group `unal`:** unaligned `movq` loads and
  stores at offsets 0..7, across cache lines, across a page boundary, and at
  random addresses, against the extracted semantics. 160k tests per seed ×
  4 seeds: 0 mismatches.
- **Model unit tests around `perm_limit`:** 20/20 pass.
- **Flag off:** generated code is byte-identical on 127 files.

**Revert.**
- Remove `Mint64u` and its cases, and `Pmovq_rm_u`/`Pmovq_mr_u`.
- Remove `perm_limit`/`access_bounded`, the clipping in `alloc`, and the
  added premises, then re-prove the fallout.
- Remove the CSE hook and the flag.

