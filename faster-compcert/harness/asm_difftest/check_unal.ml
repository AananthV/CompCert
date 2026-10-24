(* Check the output of [hw_unal] (unaligned movq loads and stores, issue
   #13) against the extracted Asm.v semantics of [Pmovq_rm_u] and
   [Pmovq_mr_u] ([Semantics.run_mem] / [Semantics.run_store], i.e. the
   real [Asm.exec_instr] on a memory block holding the same 24 bytes
   around the access).
   - load: the model must be defined and give the hardware's 64 bits;
   - store: the model must be defined and the 24 bytes around the access
     after the store must equal the hardware's (so exactly the 8 stored
     bytes change, little-endian).
   Also runs the unit tests of the memory model around [perm_limit]
   ([Semantics.perm_limit_tests]).  Exits 1 on any failure. *)

open Difftest_sem

let rec pos_of_int64 (n: int64) : positive =
  if n = 1L then XH
  else if Stdlib.Int64.logand n 1L = 1L then XI (pos_of_int64 (Stdlib.Int64.shift_right_logical n 1))
  else XO (pos_of_int64 (Stdlib.Int64.shift_right_logical n 1))
let z_of_uint64 (n: int64) : z = if n = 0L then Z0 else Zpos (pos_of_int64 n)
let z_of_int64 (n: int64) : z =
  if Stdlib.Int64.compare n 0L >= 0 then z_of_uint64 n else
  match z_of_uint64 (Stdlib.Int64.neg n) with Zpos p -> Zneg p | z -> z
let zi (n: int) = z_of_int64 (Stdlib.Int64.of_int n)
let rec int64_of_pos (p: positive) : int64 =
  match p with
  | XH -> 1L
  | XO p -> Stdlib.Int64.shift_left (int64_of_pos p) 1
  | XI p -> Stdlib.Int64.logor (Stdlib.Int64.shift_left (int64_of_pos p) 1) 1L
let uint64_of_z (z: z) : int64 =
  match z with Z0 -> 0L | Zpos p -> int64_of_pos p | Zneg _ -> failwith "negative"
let rec nat_of n = if n = 0 then O else S (nat_of (n - 1))

let bytes_of_hex h = Array.init 24 (fun i -> int_of_string ("0x" ^ String.sub h (2 * i) 2))

(* The model block holds the 24 bytes at offsets [m-8, m+16), where [m]
   keeps the alignment of the hardware address within a page. *)
let model_bytes m w = List.init 24 (fun i -> (zi (m - 8 + i), zi w.(i)))

let byte_of_val v = match res_of_val v with RInt z -> Some (Stdlib.Int64.to_int (uint64_of_z z)) | _ -> None

type stats = { mutable tests: int; mutable ok: int; mutable bad: int }

let () =
  let tbl = Hashtbl.create 16 in
  let get k = match Hashtbl.find_opt tbl k with
    | Some s -> s | None -> let s = { tests = 0; ok = 0; bad = 0 } in Hashtbl.add tbl k s; s in
  let failures = ref 0 in
  let fail fmt = incr failures;
    if !failures <= 30 then Printf.printf fmt else Printf.ifprintf stdout fmt in
  (try
    while true do
      let line = input_line stdin in
      let kind = line.[0] in
      if kind = 'L' then
        Scanf.sscanf line "L %s %d %d %d %s %Lx" (fun cat form idx aoff wh r ->
          let w = bytes_of_hex wh in
          let m = 4096 + aoff mod 4096 in
          let s = get ("load " ^ cat) in
          s.tests <- s.tests + 1;
          let res =
            if form = 0 then
              run_mem (Pmovq_rm_u (RAX, Addrmode (Some RDI, None, Inl Z0))) [] (IR RDI) (zi m)
                      (model_bytes m w) (IR RAX)
            else
              run_mem (Pmovq_rm_u (RAX, Addrmode (Some RDI, Some (RSI, zi 4), Inl (zi 5))))
                      [(IR RSI, vlong (zi idx))] (IR RDI) (zi (m - 5 - 4 * idx))
                      (model_bytes m w) (IR RAX) in
          match res with
          | Some v when (match res_of_val v with RLong z -> uint64_of_z z = r | _ -> false) ->
              s.ok <- s.ok + 1
          | _ -> s.bad <- s.bad + 1;
                 fail "MISMATCH load %s form=%d aoff=%d hw=%016Lx\n" cat form aoff r)
      else if kind = 'S' then
        Scanf.sscanf line "S %s %d %d %d %s %Lx %s" (fun cat form idx aoff wh v ah ->
          let w = bytes_of_hex wh and a = bytes_of_hex ah in
          let m = 4096 + aoff mod 4096 in
          let s = get ("store " ^ cat) in
          s.tests <- s.tests + 1;
          let res =
            if form = 0 then
              run_store (Pmovq_mr_u (Addrmode (Some RDI, None, Inl Z0), RSI))
                        [(IR RSI, vlong (z_of_uint64 v))] (IR RDI) (zi m)
                        (model_bytes m w) (zi (m - 8)) (nat_of 24)
            else
              run_store (Pmovq_mr_u (Addrmode (Some RDI, Some (RSI, zi 8), Inl (zi (-3))), RDX))
                        [(IR RSI, vlong (zi idx)); (IR RDX, vlong (z_of_uint64 v))] (IR RDI)
                        (zi (m + 3 - 8 * idx)) (model_bytes m w) (zi (m - 8)) (nat_of 24) in
          match res with
          | Some l when List.length l = 24
                        && List.for_all2 (fun mv hb -> byte_of_val mv = Some hb) l (Array.to_list a) ->
              s.ok <- s.ok + 1
          | _ -> s.bad <- s.bad + 1;
                 fail "MISMATCH store %s form=%d aoff=%d v=%016Lx\n" cat form aoff v)
    done
  with End_of_file -> ());
  let keys = List.sort compare (Hashtbl.fold (fun k _ acc -> k :: acc) tbl []) in
  Printf.printf "%-14s %8s %8s %9s\n" "test" "tests" "match" "MISMATCH";
  List.iter (fun k -> let s = Hashtbl.find tbl k in
    Printf.printf "%-14s %8d %8d %9d\n" k s.tests s.ok s.bad) keys;
  let pt = perm_limit_tests in
  List.iter (fun (name, ok) -> if not ok then fail "MODEL TEST FAILED: %s\n" name) pt;
  Printf.printf "model tests around perm_limit: %d/%d pass\n"
    (List.length (List.filter snd pt)) (List.length pt);
  if !failures > 0 then (Printf.printf "FAILED (%d)\n" !failures; exit 1)
