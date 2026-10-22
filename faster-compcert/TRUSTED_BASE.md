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

## Pending retroactive review

[#10](https://github.com/AananthV/CompCert/issues/10): the zero-extending
shift and mask instructions `Pshrlzx_ri`/`Pandlzx_ri`/`Psallzx_ri`, and
xor-zeroing in the printer and expander, merged in round 1 before this protocol
existed. The differential-test harness above can now check them.
