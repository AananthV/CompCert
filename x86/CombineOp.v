(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*                 Xavier Leroy, INRIA Paris                           *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Recognition of combined operations, addressing modes and conditions
  during the [CSE] phase. *)

Require Import Coqlib.
Require Import AST Integers.
Require Import Op CSEdomain.

Definition valnum := positive.

Section COMBINE.

Variable get: valnum -> option rhs.

Function combine_compimm_ne_0 (x: valnum) : option(condition * list valnum) :=
  match get x with
  | Some(Op (Ocmp c) ys) => Some (c, ys)
  | Some(Op (Oandimm n) ys) => Some (Cmasknotzero n, ys)
  | Some(Op (Oxorimm n) ys) => Some (Ccompimm Cne n, ys)
  | _ => None
  end.

Function combine_compimm_eq_0 (x: valnum) : option(condition * list valnum) :=
  match get x with
  | Some(Op (Ocmp c) ys) => Some (negate_condition c, ys)
  | Some(Op (Oandimm n) ys) => Some (Cmaskzero n, ys)
  | Some(Op (Oxorimm n) ys) => Some (Ccompimm Ceq n, ys)
  | _ => None
  end.

Function combine_compimm_eq_1 (x: valnum) : option(condition * list valnum) :=
  match get x with
  | Some(Op (Ocmp c) ys) => Some (c, ys)
  | _ => None
  end.

Function combine_compimm_ne_1 (x: valnum) : option(condition * list valnum) :=
  match get x with
  | Some(Op (Ocmp c) ys) => Some (negate_condition c, ys)
  | _ => None
  end.

Function combine_cond (cond: condition) (args: list valnum) : option(condition * list valnum) :=
  match cond, args with
  | Ccompimm Cne n, x::nil =>
      if Int.eq_dec n Int.zero then combine_compimm_ne_0 x
      else if Int.eq_dec n Int.one then combine_compimm_ne_1 x
      else None
  | Ccompimm Ceq n, x::nil =>
      if Int.eq_dec n Int.zero then combine_compimm_eq_0 x
      else if Int.eq_dec n Int.one then combine_compimm_eq_1 x
      else None
  | Ccompuimm Cne n, x::nil =>
      if Int.eq_dec n Int.zero then combine_compimm_ne_0 x
      else if Int.eq_dec n Int.one then combine_compimm_ne_1 x
      else None
  | Ccompuimm Ceq n, x::nil =>
      if Int.eq_dec n Int.zero then combine_compimm_eq_0 x
      else if Int.eq_dec n Int.one then combine_compimm_eq_1 x
      else None
  | _, _ => None
  end.

Definition combine_cond' (cond: condition) (args: list valnum) : option bool :=
  match cond, args with
  | (Ccomp c | Ccompu c | Ccompl c | Ccomplu c), x :: y :: nil => combine_comparison c x y
  | _, _ => None
  end.

Function combine_addr_32 (addr: addressing) (args: list valnum) : option(addressing * list valnum) :=
  match addr, args with
  | Aindexed n, x::nil =>
      match get x with
      | Some(Op (Olea a) ys) =>
          match offset_addressing a n with Some a' => Some (a', ys) | None => None end
      | _ => None
      end
  | _, _ => None
  end.

Function combine_addr_64 (addr: addressing) (args: list valnum) : option(addressing * list valnum) :=
  match addr, args with
  | Aindexed n, x::nil =>
      match get x with
      | Some(Op (Oleal a) ys) =>
          match offset_addressing a n with Some a' => Some (a', ys) | None => None end
      | _ => None
      end
  | _, _ => None
  end.

Definition combine_addr (addr: addressing) (args: list valnum) : option(addressing * list valnum) :=
  if Archi.ptr64 then combine_addr_64 addr args else combine_addr_32 addr args.

Function combine_op (op: operation) (args: list valnum) : option(operation * list valnum) :=
  match op, args with
  | Olea addr, _ =>
      match combine_addr_32 addr args with
      | Some(addr', args') => Some(Olea addr', args')
      | None => None
      end
  | Oleal addr, _ =>
      match combine_addr_64 addr args with
      | Some(addr', args') => Some(Oleal addr', args')
      | None => None
      end
  | Oandimm n, x :: nil =>
      match get x with
      | Some(Op (Oandimm m) ys) => Some(Oandimm (Int.and m n), ys)
      | _ => None
      end
  | Oorimm n, x :: nil =>
      match get x with
      | Some(Op (Oorimm m) ys) => Some(Oorimm (Int.or m n), ys)
      | _ => None
      end
  | Oxorimm n, x :: nil =>
      match get x with
      | Some(Op (Oxorimm m) ys) => Some(Oxorimm (Int.xor m n), ys)
      | _ => None
      end
  | Oandlimm n, x :: nil =>
      match get x with
      | Some(Op (Oandlimm m) ys) => Some(Oandlimm (Int64.and m n), ys)
      | _ => None
      end
  | Oorlimm n, x :: nil =>
      match get x with
      | Some(Op (Oorlimm m) ys) => Some(Oorlimm (Int64.or m n), ys)
      | _ => None
      end
  | Oxorlimm n, x :: nil =>
      match get x with
      | Some(Op (Oxorlimm m) ys) => Some(Oxorlimm (Int64.xor m n), ys)
      | _ => None
      end
  | Ocmp cond, _ =>
      match combine_cond' cond args with
      | Some b => Some ((if b then Ointconst Int.one else Ointconst Int.zero), nil)
      | None =>
          match combine_cond cond args with
          | Some(cond', args') => Some(Ocmp cond', args')
          | None => None
          end
      end
  | Osel cond ty, x :: y :: args =>
      match combine_cond' cond args with
      | Some b => Some (Omove, (if b then x else y) :: nil)
      | None =>
          if eq_valnum x y then Some (Omove, x :: nil) else
          match combine_cond cond args with
          | Some (cond', args') => Some (Osel cond' ty, x :: y :: args')
          | None => None
          end
      end
  | _, _ => None
  end.

(** Recognition of addresses that differ by a constant offset.
  [addr_deltas addr1 vl1 addr2 vl2] returns a list of integers [d]
  such that the address denoted by [addr2] and [vl2] is the address
  denoted by [addr1] and [vl1], plus one of the [d].  This is used by CSE to
  show that a store does not invalidate a load from a nearby address.
  Two cases are recognized:
- identical arguments, and addressing modes that differ only by their offsets;
- [b + (long)(x + c1) * sc + o1] and [b + (long)(x + c2) * sc + o2],
  where the 32-bit additions [x + c1] and [x + c2] can overflow,
  hence two possible values for [d]. *)

Definition addressing_delta (addr1 addr2: addressing) : option Z :=
  let delta :=
    match addr1, addr2 with
    | Aindexed n1, Aindexed n2 => n2 - n1
    | Aindexed2 n1, Aindexed2 n2 => n2 - n1
    | Ascaled _ n1, Ascaled _ n2 => n2 - n1
    | Aindexed2scaled _ n1, Aindexed2scaled _ n2 => n2 - n1
    | Aglobal _ n1, Aglobal _ n2 => Ptrofs.unsigned (Ptrofs.sub n2 n1)
    | Abased _ n1, Abased _ n2 => Ptrofs.unsigned (Ptrofs.sub n2 n1)
    | Abasedscaled _ _ n1, Abasedscaled _ _ n2 => Ptrofs.unsigned (Ptrofs.sub n2 n1)
    | Ainstack n1, Ainstack n2 => Ptrofs.unsigned (Ptrofs.sub n2 n1)
    | _, _ => 0
    end in
  if eq_addressing (offset_addressing_total addr1 delta) addr2
  then Some delta else None.

Definition index_offset (k: valnum) : valnum * Z :=
  match get k with
  | Some(Op (Olea (Aindexed c)) (x :: nil)) => (x, c)
  | _ => (k, 0)
  end.

Definition index_form (i: valnum) : option (bool * valnum * Z) :=
  match get i with
  | Some(Op Ocast32signed (k :: nil)) =>
      let (x, c) := index_offset k in Some (true, x, c)
  | Some(Op Ocast32unsigned (k :: nil)) =>
      let (x, c) := index_offset k in Some (false, x, c)
  | _ => None
  end.

Definition index_deltas (sc: Z) (i1 i2: valnum) (d: Z) : list Z :=
  match index_form i1, index_form i2 with
  | Some (s1, x1, c1), Some (s2, x2, c2) =>
      if Bool.eqb s1 s2 && peq x1 x2 then
        let r := (c2 - c1) mod Int.modulus in
        (d + sc * r) :: (d + sc * (r - Int.modulus)) :: nil
      else nil
  | _, _ => nil
  end.

Definition addr_deltas (addr1: addressing) (vl1: list valnum)
                       (addr2: addressing) (vl2: list valnum) : list Z :=
  if list_eq_dec peq vl1 vl2 then
    match addressing_delta addr1 addr2 with
    | Some d => d :: nil
    | None => nil
    end
  else if Archi.ptr64 then
    match addr1, addr2, vl1, vl2 with
    | Aindexed2 o1, Aindexed2 o2, b1 :: i1 :: nil, b2 :: i2 :: nil =>
        if peq b1 b2 then index_deltas 1 i1 i2 (o2 - o1) else nil
    | Aindexed2scaled sc1 o1, Aindexed2scaled sc2 o2, b1 :: i1 :: nil, b2 :: i2 :: nil =>
        if zeq sc1 sc2 && peq b1 b2 then index_deltas sc1 i1 i2 (o2 - o1) else nil
    | _, _, _, _ => nil
    end
  else nil.

End COMBINE.
