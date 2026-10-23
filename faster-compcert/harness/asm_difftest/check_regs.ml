(* Check the output of [hw_regs] (register-only instructions of issues
   #10 and #11) against the Asm.v semantics extracted from Coq
   ([Semantics.run_regs], i.e. the real [Asm.exec_instr]; [sqrtsd] uses
   the semantics of the builtin [__builtin_fsqrt] it is expanded from).

   For every test the model is run on the register contents the
   compiler would have, i.e. a [Vint] of the low 32 bits for a 32-bit
   integer, a [Vlong] for a 64-bit integer, a [Vfloat]/[Vsingle] of the
   low lane of an XMM register.  The result is classified as
     match     the model is defined and equals the hardware bit for bit,
     MISMATCH  the model is defined and differs from the hardware,
     undef     the model gives [Vundef] (no constraint on the hardware).
   Since #11, Asm.v masks the count of the shifts by %cl as the hardware
   does, so for them the model must be defined on every test: an undef
   result is a failure.

   Independently of the model, the test fails if a register other than
   the destination changed, and, for the conversions (whose semantics
   uses [nextinstr], not [nextinstr_nf]), if a flag changed.
   Reads the output of [hw_regs] on stdin; exits 1 on any failure. *)

open Difftest_sem

let rec pos_of_int64 (n: int64) : positive =
  if n = 1L then XH
  else if Stdlib.Int64.logand n 1L = 1L then XI (pos_of_int64 (Stdlib.Int64.shift_right_logical n 1))
  else XO (pos_of_int64 (Stdlib.Int64.shift_right_logical n 1))
let z_of_uint64 (n: int64) : z = if n = 0L then Z0 else Zpos (pos_of_int64 n)
let rec int64_of_pos (p: positive) : int64 =
  match p with
  | XH -> 1L
  | XO p -> Stdlib.Int64.shift_left (int64_of_pos p) 1
  | XI p -> Stdlib.Int64.logor (Stdlib.Int64.shift_left (int64_of_pos p) 1) 1L
let uint64_of_z (z: z) : int64 =
  match z with Z0 -> 0L | Zpos p -> int64_of_pos p | Zneg _ -> failwith "negative"

let lo32 x = Stdlib.Int64.logand x 0xffffffffL
let hi32 x = Stdlib.Int64.shift_right_logical x 32
let z = z_of_uint64

(* Signed 64-bit integers as [z]. *)
let z_of_int64 (n: int64) : z =
  if Stdlib.Int64.compare n 0L >= 0 then z_of_uint64 n else
  match z_of_uint64 (Stdlib.Int64.neg n) with Zpos p -> Zneg p | z -> z

(* Integer registers, in hardware encoding order. *)
let ireg_of_num = function
  | 0 -> RAX | 1 -> RCX | 2 -> RDX | 3 -> RBX | 4 -> RSP | 5 -> RBP | 6 -> RSI | 7 -> RDI
  | 8 -> R8 | 9 -> R9 | 10 -> R10 | 11 -> R11 | 12 -> R12 | 13 -> R13 | 14 -> R14
  | 15 -> R15 | n -> failwith (string_of_int n)

(* The instruction of Asm.v, with its source operand in [src]. *)
let instr name imm src =
  let n = int_of_Z (z imm) in
  match name with
  | "sallzx" -> Psallzx_ri (RAX, n)
  | "shrlzx" -> Pshrlzx_ri (RAX, n)
  | "andlzx" -> Pandlzx_ri (RAX, n)
  | "sall_rcl" -> Psall_rcl RAX | "shrl_rcl" -> Pshrl_rcl RAX | "sarl_rcl" -> Psarl_rcl RAX
  | "salq_rcl" -> Psalq_rcl RAX | "shrq_rcl" -> Pshrq_rcl RAX | "sarq_rcl" -> Psarq_rcl RAX
  | "cvtsi2sd" -> Pcvtsi2sd_fr (XMM0, RDX)
  | "cvtsi2ss" -> Pcvtsi2ss_fr (XMM0, RDX)
  | "cvtsl2sd" -> Pcvtsl2sd_fr (XMM0, RDX)
  | "cvtsl2ss" -> Pcvtsl2ss_fr (XMM0, RDX)
  | "cvtss2sd" -> Pcvtss2sd_ff (XMM0, src)
  | "cvtsd2ss" -> Pcvtsd2ss_ff (XMM0, src)
  | s -> failwith s

type group = Zx | Shift | Cvt | ZxLoad
let group_of = function
  | "sallzx" | "shrlzx" | "andlzx" -> Zx
  | "movzbq_rr" | "movzwq_rr" | "movzbq_rm" | "movzwq_rm" -> ZxLoad
  | "sall_rcl" | "shrl_rcl" | "sarl_rcl" | "salq_rcl" | "shrq_rcl" | "sarq_rcl" -> Shift
  | _ -> Cvt
let is_q name = String.length name > 4 && name.[3] = 'q'

(* Model inputs (destination, source) as the compiler has them, and the
   expected kind of result: [`L] Vlong, [`I] Vint, [`F] Vfloat, [`S] Vsingle. *)
let model_inputs name a b =
  match name with
  | "sallzx" | "shrlzx" | "andlzx" -> vint (z (lo32 a)), Vundef, `L
  | "sall_rcl" | "shrl_rcl" | "sarl_rcl" -> vint (z (lo32 a)), vint (z (lo32 b)), `I
  | "salq_rcl" | "shrq_rcl" | "sarq_rcl" -> vlong (z a), vint (z (lo32 b)), `L
  | "cvtsi2sd" -> Vundef, vint (z (lo32 b)), `F
  | "cvtsi2ss" -> Vundef, vint (z (lo32 b)), `S
  | "cvtsl2sd" -> Vundef, vlong (z b), `F
  | "cvtsl2ss" -> Vundef, vlong (z b), `S
  | "cvtss2sd" -> Vundef, vsingle_bits (z (lo32 b)), `F
  | "cvtsd2ss" | "sqrtsd" -> Vundef, vfloat_bits (z b), `S
  | "movzbq_rr" | "movzwq_rr" -> vlong (z a), vint (z (lo32 b)), `L
  | "movzbq_rm" | "movzwq_rm" -> vlong (z a), Vundef, `L
  | s -> failwith s
let model_inputs name a b =
  let (d, s, k) = model_inputs name a b in
  (d, s, if name = "sqrtsd" then `F else k)

(* The memory operand of a test: base and index registers, scale,
   displacement, offset of the base in the buffer, value of the index. *)
type memop = { base: int; index: int; scale: int; disp: int; baseoff: int64; idx: int64 }

(* Run the model.  [same]: source and destination are the same register.
   For [ZxLoad], the destination is register [dst] and [mo] the memory
   operand; [b] is the 16-bit word at the effective address. *)
let run_model ?(dst = 0) ?mo ?(b = 0L) name imm same vd vs =
  if name = "sqrtsd" then sem_fsqrt vs else
  match group_of name with
  | ZxLoad when name.[7] = 'r' && name.[8] = 'r' ->
      let rd = ireg_of_num dst in
      let r1 = if same then rd else (if rd = RDX then RCX else RDX) in
      let i = if name.[4] = 'b' then Pmovzbq_rr (rd, r1) else Pmovzwq_rr (rd, r1) in
      run_regs i [(IR rd, vd); (IR r1, vs)] (IR rd)
  | ZxLoad ->
      let mo = match mo with Some mo -> mo | None -> failwith "memop" in
      let rd = ireg_of_num dst in
      let index = if mo.index < 0 then None
                  else Some (ireg_of_num mo.index, z_of_int64 (Stdlib.Int64.of_int mo.scale)) in
      let am = Addrmode (Some (ireg_of_num mo.base), index, Inl (z_of_int64 (Stdlib.Int64.of_int mo.disp))) in
      let i = if name.[4] = 'b' then Pmovzbq_rm (rd, am) else Pmovzwq_rm (rd, am) in
      let ea = Stdlib.Int64.(add mo.baseoff (add (mul mo.idx (of_int mo.scale)) (of_int mo.disp))) in
      let bytes = [(z_of_int64 ea, z (Stdlib.Int64.logand b 0xffL));
                   (z_of_int64 (Stdlib.Int64.succ ea), z (Stdlib.Int64.shift_right_logical b 8))] in
      let inits = (IR rd, vd) :: (if mo.index < 0 then []
                                  else [(IR (ireg_of_num mo.index), vlong (z mo.idx))]) in
      run_mem i inits (IR (ireg_of_num mo.base)) (z_of_int64 mo.baseoff) bytes (IR rd)
  | Zx -> run_regs (instr name imm XMM0) [(IR RAX, vd)] (IR RAX)
  | Shift -> run_regs (instr name imm XMM0) [(IR RAX, vd); (IR RCX, vs)] (IR RAX)
  | Cvt ->
      let src = if same then XMM0 else XMM1 in
      let inits = if name.[4] = 'i' || name.[4] = 'l'
                  then [(FR XMM0, vd); (IR RDX, vs)]
                  else [(FR XMM0, vd); (FR src, vs)] in
      run_regs (instr name imm src) inits (FR XMM0)

(* The hardware result, viewed as the expected kind. *)
let hw_bits kind r = match kind with `L | `F -> r | `I | `S -> lo32 r

type outcome = Match | Mismatch of string | Undef
let classify kind r (v: val0 option) =
  match v with
  | None -> Mismatch "stuck"
  | Some v ->
      match kind, res_of_val v with
      | _, RUndef -> Undef
      | (`L, RLong n) | (`I, RInt n) | (`F, RFloat n) | (`S, RSingle n) ->
          let n = uint64_of_z n in
          if n = hw_bits kind r then Match else Mismatch (Printf.sprintf "%Lx" n)
      | _ -> Mismatch "wrong type"

type stats = {
  mutable tests: int;
  mutable ok: int; mutable bad: int; mutable undef: int;        (* Asm.v *)
  mutable regs: int;           (* other registers or flags changed *)
  mutable other_in: int;       (* wrong-kind inputs giving Vundef / tested *)
  mutable other_undef: int;
  mutable info: int;           (* see [info] below *)
  mutable info_of: int;
}
let new_stats () = { tests = 0; ok = 0; bad = 0; undef = 0;
                     regs = 0; other_in = 0; other_undef = 0; info = 0; info_of = 0 }

(* Inputs of a kind the compiler never produces for this instruction:
   the model should give Vundef on all of them. *)
let other_inputs name a b =
  let vf = vfloat_bits (z a) in
  match group_of name with
  | Zx -> List.map (fun v -> (v, Vundef)) [vlong (z a); Vundef; vf]
  | Shift ->
      let d, s, _ = model_inputs name a b in
      let wrong = if is_q name then vint (z (lo32 a)) else vlong (z a) in
      [(wrong, s); (Vundef, s); (d, vlong (z b)); (d, Vundef)]
  | Cvt ->
      let _, s, _ = model_inputs name a b in
      let wrong = match s with Vint _ | Vlong _ -> vf | _ -> vlong (z b) in
      [(Vundef, wrong); (Vundef, Vundef)]
  | ZxLoad when name.[7] = 'r' && name.[8] = 'r' ->
      [(vlong (z a), vlong (z b)); (vlong (z a), Vundef); (vlong (z a), vf)]
  | ZxLoad -> []

let names = ["sallzx"; "shrlzx"; "andlzx";
             "sall_rcl"; "shrl_rcl"; "sarl_rcl"; "salq_rcl"; "shrq_rcl"; "sarq_rcl";
             "cvtsi2sd"; "cvtsi2ss"; "cvtsl2sd"; "cvtsl2ss"; "cvtss2sd"; "cvtsd2ss"; "sqrtsd";
             "movzbq_rr"; "movzwq_rr"; "movzbq_rm"; "movzwq_rm"]

let () =
  let tbl = Hashtbl.create 16 in
  let get k = match Hashtbl.find_opt tbl k with
    | Some s -> s | None -> let s = new_stats () in Hashtbl.add tbl k s; s in
  let failures = ref 0 in
  let report fmt = incr failures;
    if !failures <= 50 then Printf.printf fmt else Printf.ifprintf stdout fmt in
  (try
    while true do
      let line = input_line stdin in
      Scanf.sscanf line "%s %Lx %Lx %Lx %Lx %Lx %d %d %d %d %d %d %d %d %d %Lx %Lx | %[^\n]"
        (fun name imm a b r rh flags_kept others_kept xor dst src
             base index scale disp baseoff idx text ->
        let mo = { base; index; scale; disp; baseoff; idx } in
        let s = get name in
        let g = group_of name in
        s.tests <- s.tests + 1;
        let same = (g = Cvt && xor = 0) || (g = ZxLoad && dst = src) in
        let b = if same then a else b in
        let vd, vs, kind = model_inputs name a b in
        let where = Printf.sprintf "[%s] a=%Lx b=%Lx hw=%Lx" text a b r in
        let res = run_model ~dst ~mo ~b name imm same vd vs in
        (* A memory access that is not possible in the model (here: an
           unaligned 16-bit load) is stuck, i.e. undefined. *)
        let res = if g = ZxLoad && res = None then Some Vundef else res in
        (match classify kind r res with
         | Match -> s.ok <- s.ok + 1
         | Undef -> s.undef <- s.undef + 1;
             if g = Shift then report "UNDEF %s %s\n" name where
         | Mismatch m -> s.bad <- s.bad + 1; report "MISMATCH %s %s model=%s\n" name where m);
        if others_kept = 0 || (g = Cvt && flags_kept = 0) then begin
          s.regs <- s.regs + 1;
          report "REGS %s %s: other registers kept=%d, flags kept=%d\n"
            name where others_kept flags_kept
        end;
        List.iter (fun (d, src) ->
            s.other_in <- s.other_in + 1;
            match run_model ~dst ~mo ~b name imm same d src with
            | Some v when res_of_val v = RUndef -> s.other_undef <- s.other_undef + 1
            | _ -> ())
          (other_inputs name a b);
        (* Information, not modelled:
           Zx, Shift (32-bit): upper 32 bits of the result are zero
             (counted over the tests where they were non-zero before);
           Cvt: the lanes above the result are zero after the xor
             (counted over the tests with the xor). *)
        (match g with
         | Zx | Shift | ZxLoad when not (is_q name) ->
             if hi32 a <> 0L then begin
               s.info_of <- s.info_of + 1;
               if hi32 r = 0L then s.info <- s.info + 1
             end
         | Cvt when xor = 1 ->
             s.info_of <- s.info_of + 1;
             if rh = 0L && (kind = `F || hi32 r = 0L) then s.info <- s.info + 1
         | _ -> ()))
    done
  with End_of_file -> ());
  Printf.printf "%-9s %7s | %-27s | %5s | %-15s | %s\n" "instr" "tests"
    "Asm.v: match MISMATCH undef" "regs" "wrong-kind:undef" "info";
  List.iter (fun k ->
      match Hashtbl.find_opt tbl k with
      | None -> ()
      | Some s ->
          let info = match group_of k with
            | Zx -> Printf.sprintf "upper 32 zeroed %d/%d" s.info s.info_of
            | Shift | ZxLoad when not (is_q k) -> Printf.sprintf "upper 32 zeroed %d/%d" s.info s.info_of
            | Cvt -> Printf.sprintf "upper lanes zero after xor %d/%d" s.info s.info_of
            | _ -> "" in
          Printf.printf "%-9s %7d | %8d %8d %8d  | %5d | %7d/%-7d | %s\n" k s.tests
            s.ok s.bad s.undef s.regs s.other_undef s.other_in info)
    names;
  exit (if !failures = 0 then 0 else 1)
