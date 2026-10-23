From compcert Require Import Coqlib.
From Coq Require Import ExtrOcamlBasic ExtrOcamlNativeString.
Require Import Semantics.
Extraction Inline Coqlib.proj_sumbool.
Extract Inlined Constant Coqlib.proj_sumbool => "(fun x -> x)".
Extraction "libm_sem.ml" model_sqrt model_fabs float_sqrt float_abs.
