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

(** Recognition of rotates [(x << n1) | (x >>u n2)] with [n1 + n2] equal
  to the word size.  This complements the recognition performed during
  instruction selection, which only applies when both shifts are applied
  to the same variable.  Small left shifts are recognized also when
  they have been turned into [lea] instructions. *)

Definition scale_shift (sc ofs: Z) : option int :=
  if zeq ofs 0 then
    if zeq sc 2 then Some (Int.repr 1)
    else if zeq sc 4 then Some (Int.repr 2)
    else if zeq sc 8 then Some (Int.repr 3)
    else None
  else None.

Definition shl_of (x: valnum) : option (int * valnum) :=
  match get x with
  | Some(Op (Oshlimm n) (a :: nil)) => Some (n, a)
  | Some(Op (Olea (Ascaled sc ofs)) (a :: nil)) =>
      match scale_shift sc ofs with Some n => Some (n, a) | None => None end
  | _ => None
  end.

Definition shll_of (x: valnum) : option (int * valnum) :=
  match get x with
  | Some(Op (Oshllimm n) (a :: nil)) => Some (n, a)
  | Some(Op (Oleal (Ascaled sc ofs)) (a :: nil)) =>
      match scale_shift sc ofs with Some n => Some (n, a) | None => None end
  | _ => None
  end.

Definition combine_ror (x y: valnum) : option (operation * list valnum) :=
  match shl_of x, get y with
  | Some (n1, a), Some(Op (Oshruimm n2) (b :: nil)) =>
      if eq_valnum a b && Int.eq (Int.add n1 n2) Int.iwordsize
      then Some (Ororimm n2, a :: nil) else None
  | _, _ => None
  end.

Definition combine_rorl (x y: valnum) : option (operation * list valnum) :=
  match shll_of x, get y with
  | Some (n1, a), Some(Op (Oshrluimm n2) (b :: nil)) =>
      if eq_valnum a b && Int.eq (Int.add n1 n2) Int64.iwordsize'
      then Some (Ororlimm n2, a :: nil) else None
  | _, _ => None
  end.

Definition combine_or (x y: valnum) : option (operation * list valnum) :=
  match combine_ror x y with
  | Some r => Some r
  | None => combine_ror y x
  end.

Definition combine_orl (x y: valnum) : option (operation * list valnum) :=
  match combine_rorl x y with
  | Some r => Some r
  | None => combine_rorl y x
  end.

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
  | Oor, x :: y :: nil => combine_or x y
  | Oorl, x :: y :: nil => combine_orl x y
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


(** Merging of byte loads (option [-fmerge-bytes]).  We recognize, through
  the value numbering, a 64-bit OR of zero-extended byte loads
  [(u64)p[o] | (u64)p[o+1] << 8 | ... | (u64)p[o+7] << 56], in any
  association order, possibly with 32-bit partial results
  ([p[o] | p[o+1] << 8 | ...]) zero-extended to 64 bits.  It is replaced
  by a single unaligned 64-bit load [Mint64u] at [p + o].

  A [bytecomp] describes a value that is the OR of bytes loaded from
  [base + ofs], each shifted left by [pos] bits, as a 32-bit or a 64-bit
  integer. *)

Record bytecomp : Type := mkbytecomp {
  bc64: bool;                    (**r 64-bit result? *)
  bcbase: valnum;                (**r base address *)
  bcbytes: list (Z * Z)          (**r (offset, bit position) of each byte *)
}.

Definition bytes_fit (w: Z) (l: list (Z * Z)) : bool :=
  forallb (fun p => zle 0 (snd p) && zle (snd p + 8) w) l.

Definition bytes_shift (n: Z) (l: list (Z * Z)) : list (Z * Z) :=
  map (fun p => (fst p, snd p + n)) l.

Definition bytecomp_widen (oc: option bytecomp) (w: Z) : option bytecomp :=
  match oc with
  | Some c => if negb (bc64 c) && bytes_fit w (bcbytes c)
              then Some (mkbytecomp true (bcbase c) (bcbytes c)) else None
  | None => None
  end.

Definition bytecomp_shl (oc: option bytecomp) (is64 res64: bool) (n: Int.int) : option bytecomp :=
  match oc with
  | Some c =>
      let l := bytes_shift (Int.unsigned n) (bcbytes c) in
      if Bool.eqb (bc64 c) is64 && bytes_fit (if is64 then 64 else 32) l
      then Some (mkbytecomp res64 (bcbase c) l) else None
  | None => None
  end.

Definition bytecomp_or (oc1 oc2: option bytecomp) (is64: bool) : option bytecomp :=
  match oc1, oc2 with
  | Some c1, Some c2 =>
      if Bool.eqb (bc64 c1) is64 && Bool.eqb (bc64 c2) is64 && peq (bcbase c1) (bcbase c2)
      then Some (mkbytecomp is64 (bcbase c1) (bcbytes c1 ++ bcbytes c2)) else None
  | _, _ => None
  end.

Definition bytecomp_op (rec: valnum -> option bytecomp)
                       (op: operation) (args: list valnum) : option bytecomp :=
  match op, args with
  | Ocast32unsigned, x :: nil => bytecomp_widen (rec x) 32
  | Ozextb64, x :: nil => bytecomp_widen (rec x) 8
  | Ozextb64_ld, _ :: x :: nil => bytecomp_widen (rec x) 8
  | Oshlimm n, x :: nil =>
      if Int.ltu n Int.iwordsize then bytecomp_shl (rec x) false false n else None
  | Ozextshlimm n, x :: nil =>
      if Int.ltu n Int.iwordsize then bytecomp_shl (rec x) false true n else None
  | Oshllimm n, x :: nil =>
      if Int.ltu n Int64.iwordsize' then bytecomp_shl (rec x) true true n else None
  | Oor, x :: y :: nil => bytecomp_or (rec x) (rec y) false
  | Oorl, x :: y :: nil => bytecomp_or (rec x) (rec y) true
  | _, _ => None
  end.

Fixpoint bytecomp_of (fuel: nat) (v: valnum) : option bytecomp :=
  match fuel with
  | O => None
  | S fuel' =>
      match get v with
      | Some (Load Mint8unsigned (Aindexed ofs) (b :: nil) _) =>
          Some (mkbytecomp false b ((ofs, 0) :: nil))
      | Some (Op op args) => bytecomp_op (bytecomp_of fuel') op args
      | _ => None
      end
  end.

(** The 8 bytes [o, ..., o+7] at bit positions [0, 8, ..., 56]. *)

Definition bytes_le64 (o: Z) : list (Z * Z) :=
  (o, 0) :: (o + 1, 8) :: (o + 2, 16) :: (o + 3, 24) ::
  (o + 4, 32) :: (o + 5, 40) :: (o + 6, 48) :: (o + 7, 56) :: nil.

Definition pair_eq (p q: Z * Z) : {p = q} + {p <> q}.
Proof. decide equality; apply Z.eq_dec. Defined.

Definition bytes_incl (l1 l2: list (Z * Z)) : bool :=
  forallb (fun p => if In_dec pair_eq p l2 then true else false) l1.

Definition combine_merge_load (op: operation) (args: list valnum)
                               : option (addressing * list valnum) :=
  if Archi.ptr64 then
    match op with
    | Oorl =>
        match bytecomp_op (bytecomp_of 12%nat) op args with
        | Some c =>
            match find (fun p => zeq (snd p) 0) (bcbytes c) with
            | Some (o, _) =>
                if bc64 c && bytes_incl (bcbytes c) (bytes_le64 o)
                          && bytes_incl (bytes_le64 o) (bcbytes c)
                then Some (Aindexed o, bcbase c :: nil)
                else None
            | None => None
            end
        | None => None
        end
    | _ => None
    end
  else None.

End COMBINE.
