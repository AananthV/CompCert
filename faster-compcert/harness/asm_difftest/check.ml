(* Check the hardware results printed by [hw] against the Asm.v semantics
   of the same instructions, extracted from Coq ([Semantics.v]).
   Reads the output of [hw] on stdin; prints mismatches and a summary. *)

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

let sem_d = function
  | "addsd" -> sem_addsd | "subsd" -> sem_subsd
  | "mulsd" -> sem_mulsd | "divsd" -> sem_divsd | s -> failwith s
let sem_i = function
  | "addl" -> sem_addl | "xorl" -> sem_xorl
  | "andl" -> sem_andl | "orl" -> sem_orl | s -> failwith s

let () =
  let counts = Hashtbl.create 8 in
  let bump k ok =
    let (n, bad) = try Hashtbl.find counts k with Not_found -> (0, 0) in
    Hashtbl.replace counts k (n + 1, if ok then bad else bad + 1) in
  let mismatches = ref 0 in
  (try
    while true do
      let line = input_line stdin in
      Scanf.sscanf line "%s %Lx %Lx %Lx" (fun name x m r ->
        let expected =
          if String.length name > 2 && String.sub name (String.length name - 2) 2 = "sd" then
            (match sem_d name (int64_of_Z (z_of_uint64 x)) (int64_of_Z (z_of_uint64 m)) with
             | Some v -> Some (uint64_of_z (z_of_int64 v))
             | None -> None)
          else
            (match sem_i name (int_of_Z (z_of_uint64 x)) (int_of_Z (z_of_uint64 m)) with
             | Some v -> Some (uint64_of_z (z_of_int v))
             | None -> None) in
        let ok = (expected = Some r) in
        bump name ok;
        if not ok then begin
          incr mismatches;
          if !mismatches <= 50 then
            Printf.printf "MISMATCH %s x=%Lx m=%Lx hw=%Lx sem=%s\n" name x m r
              (match expected with Some v -> Printf.sprintf "%Lx" v | None -> "stuck")
        end)
    done
  with End_of_file -> ());
  List.iter (fun k ->
    match Hashtbl.find_opt counts k with
    | Some (n, bad) -> Printf.printf "%-6s %7d tests, %d mismatches\n" k n bad
    | None -> ())
    ["addsd"; "subsd"; "mulsd"; "divsd"; "addl"; "xorl"; "andl"; "orl"];
  exit (if !mismatches = 0 then 0 else 1)
