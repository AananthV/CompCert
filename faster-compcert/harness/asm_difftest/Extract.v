From compcert Require Import Coqlib.
From Coq Require Import ExtrOcamlBasic ExtrOcamlNativeString.
Require Import Semantics.
Extraction Inline Coqlib.proj_sumbool.
Extract Inlined Constant Coqlib.proj_sumbool => "(fun x -> x)".
Extraction NoInline Memory.Mem.valid_pointer.
Extraction "difftest_sem.ml"
  (* load-op instructions (#5) *)
  sem_addsd sem_subsd sem_mulsd sem_divsd sem_addl sem_xorl sem_andl sem_orl
  (* register instructions (#10, #11) *)
  run_regs run_mem sem_fsqrt vint vlong vfloat_bits vsingle_bits res_of_val
  int64_of_Z Z_of_int64 int_of_Z Z_of_int.
