(* Check the results of the C library printed by [hw] against the models of
   [sqrt] and [fabs] under [-ftrust-libm], extracted from Coq ([Semantics.v]).
   Reads the output of [hw] on stdin; prints mismatches, the special values,
   and a summary.  Exits 1 on any mismatch. *)

open Libm_sem

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

let () =
  let counts = Hashtbl.create 8 in      (* (category, function) -> tests, mismatches *)
  let errnos = Hashtbl.create 8 in      (* (function, errno) -> count *)
  let bump tbl k = Hashtbl.replace tbl k (1 + try Hashtbl.find tbl k with Not_found -> 0) in
  let cat = ref "" and mismatches = ref 0 in
  (try
    while true do
      let line = input_line stdin in
      if not (String.contains line ' ') then cat := line else
      Scanf.sscanf line "%s %Lx %Lx %d" (fun f x r err ->
        let zx = z_of_uint64 x in
        let (model, direct) =
          if f = "sqrt" then (model_sqrt zx, float_sqrt zx)
          else (model_fabs zx, float_abs zx) in
        let model = Option.map uint64_of_z model in
        let ok = (model = Some r) && (uint64_of_z direct = r) in
        bump counts (!cat, f);
        if not ok then bump counts (!cat, f ^ " MISMATCH");
        bump errnos (f, err);
        if not ok then begin
          incr mismatches;
          if !mismatches <= 50 then
            Printf.printf "MISMATCH %s x=%016Lx libm=%016Lx model=%s\n" f x r
              (match model with Some v -> Printf.sprintf "%016Lx" v | None -> "undefined")
        end;
        if !cat = "special" then
          Printf.printf "  %s(%016Lx) = %016Lx  errno=%d  %s\n" f x r err
            (if ok then "match" else "MISMATCH"))
    done
  with End_of_file -> ());
  List.iter (fun c ->
    List.iter (fun f ->
      let get k = try Hashtbl.find counts k with Not_found -> 0 in
      Printf.printf "%-10s %s: %9d tests, %d mismatches\n" c f
        (get (c, f)) (get (c, f ^ " MISMATCH")))
      ["sqrt"; "fabs"])
    ["special"; "random"; "squares"; "subnormal"];
  Hashtbl.iter (fun (f, e) n -> Printf.printf "errno %s=%d: %d tests\n" f e n) errnos;
  Printf.printf "%s: %d mismatches\n"
    (if !mismatches = 0 then "OK" else "FAILED") !mismatches;
  exit (if !mismatches = 0 then 0 else 1)
