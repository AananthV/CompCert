# asm_difftest: differential testing of Asm.v semantics against the CPU

`run.sh [COMPCERT_TREE] [N] [SEED]` checks the x86 load-op instructions of
issue #5 (`Paddd_fm Psubd_fm Pmuld_fm Pdivd_fm Paddl_rm Pxorl_rm Pandl_rm Porl_rm`).
The tree must be built (`make proof`).

- `Semantics.v` runs the real `Asm.exec_instr` on one instruction, with the
  register operand in `%xmm0`/`%eax` and the memory operand in a fresh
  `Mem.alloc`ed block at `0(%rdi)`. `Extract.v` extracts it to OCaml, so the
  reference is the extracted Coq semantics (`exec_loadop`, `Mem.loadv`,
  `Val.addf`, ...), not a reimplementation.
- `hw.s` contains the same instructions, in the exact syntax printed by
  `TargetPrinter.ml`. `hw.c` runs them on the special values (±0, ±inf,
  quiet/signaling NaNs with payloads, denormals, extremes; 0, ±1, INT_MIN,
  INT_MAX, ...), all pairs of them, and N random pairs per instruction.
- `check.ml` compares the hardware result bit for bit with the semantics.
  It reports mismatches, and exits 1 if there are any.

To test another instruction, add a `sem_*` wrapper in `Semantics.v`, a
function in `hw.s`, and a case in `hw.c`/`check.ml`.
