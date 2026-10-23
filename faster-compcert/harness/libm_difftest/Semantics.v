(** Models of [sqrt] and [fabs] under [-ftrust-libm] (issue #12), for the
  differential test against the C library.  See README.md. *)

From Coq Require Import ZArith.
From compcert Require Import Coqlib Integers Floats Values Ctypes Cop Builtins.

(** [-ftrust-libm] turns [sqrt(x)] into [__builtin_fsqrt(x)], whose semantics
  is the builtin [BI_fsqrt], i.e. [Float.sqrt]. *)

Definition sem_sqrt (v: val) : option val :=
  builtin_function_sem (BI_standard BI_fsqrt) (v :: nil).

(** [fabs(x)] becomes [__builtin_fabs(x)], which [C2C] translates to the
  unary operator [Oabsfloat] at type [double], i.e. [Float.abs]. *)

Definition sem_fabs (v: val) : option val :=
  sem_absfloat v (Tfloat F64 noattr).

(** Results as bit patterns ([None]: undefined or not a float). *)

Definition bits_of (r: option val) : option Z :=
  match r with
  | Some (Vfloat f) => Some (Int64.unsigned (Float.to_bits f))
  | _ => None
  end.

Definition model_sqrt (x: Z) : option Z :=
  bits_of (sem_sqrt (Vfloat (Float.of_bits (Int64.repr x)))).
Definition model_fabs (x: Z) : option Z :=
  bits_of (sem_fabs (Vfloat (Float.of_bits (Int64.repr x)))).

(** The [Float] operations themselves, as a cross-check. *)

Definition float_sqrt (x: Z) : Z :=
  Int64.unsigned (Float.to_bits (Float.sqrt (Float.of_bits (Int64.repr x)))).
Definition float_abs (x: Z) : Z :=
  Int64.unsigned (Float.to_bits (Float.abs (Float.of_bits (Int64.repr x)))).
