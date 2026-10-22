From compcert Require Import Coqlib Values.
From Coq Require Import ExtrOcamlBasic ExtrOcamlNativeString.
Require Import Semantics.
Extraction Inline Coqlib.proj_sumbool.
Extract Inlined Constant Coqlib.proj_sumbool => "(fun x -> x)".
Extraction NoInline Memory.Mem.valid_pointer.
Extraction "difftest_sem.ml"
  (* load-op instructions (#5) *)
  sem_addsd sem_subsd sem_mulsd sem_divsd sem_addl sem_xorl sem_andl sem_orl
  (* register instructions (#10, #11) *)
  run_regs sem_fsqrt vint vlong vfloat_bits vsingle_bits res_of_val
  (* used by the proposed shift semantics of #11 in check_regs.ml *)
  Val.and Val.shl Val.shru Val.shr Val.shll Val.shrlu Val.shrl
  int64_of_Z Z_of_int64 int_of_Z Z_of_int.
