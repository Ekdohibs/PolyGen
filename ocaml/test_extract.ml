open BinNums
open Datatypes
open PolyLang
open Loop
open ImpureConfig
open Extraction

let coqnat_to_int n =
  let rec iter n r =
    match n with
    | O -> r
    | S n -> iter n (r + 1)
  in iter n 0

let int_to_coqnat n =
  assert (n >= 0);
  let rec iter n r =
    match n with
    | 0 -> r
    | _ -> iter (n - 1) (S r)
  in iter n O

let rec coqpos_to_int n =
  match n with
  | Coq_xH -> 1
  | Coq_xO n -> 2 * coqpos_to_int n
  | Coq_xI n -> 2 * coqpos_to_int n + 1

let rec int_to_coqpos n =
  assert (n > 0);
  if n = 1 then Coq_xH
  else if n land 1 = 0 then Coq_xO (int_to_coqpos (n lsr 1))
  else Coq_xI (int_to_coqpos (n lsr 1))

let coqZ_to_int n =
  match n with
  | Z0 -> 0
  | Zpos n -> coqpos_to_int n
  | Zneg n -> - coqpos_to_int n

let int_to_coqZ n =
  if n = 0 then Z0
  else if n > 0 then Zpos (int_to_coqpos n)
  else Zneg (int_to_coqpos (-n))

let letter_of_int n =
  assert (n < 26);
  char_of_int (97 + n)

let print_var_name ff n =
  assert (n >= 0);
  if (n < 26) then
    Format.fprintf ff "%c" (letter_of_int n)
  else
    Format.fprintf ff "%c%d" (letter_of_int (n mod 26)) (n / 26)

let print_linear ff l =
  let l = List.filter (fun x -> snd x <> 0) (List.mapi (fun i x -> (i, coqZ_to_int x)) l) in
  match l with
   | [] -> Format.fprintf ff "0"
   | (i, x) :: l -> Format.fprintf ff "%d*%a" x print_var_name i; List.iter (fun (i, x) -> Format.fprintf ff " + %d*%a" x print_var_name i) l

let print_affine ff a =
  let l = List.filter (fun x -> snd x <> 0) (List.mapi (fun i x -> (i, coqZ_to_int x)) (fst a)) in
  match l with
   | [] -> Format.fprintf ff "%d" (coqZ_to_int (snd a))
   | (i, x) :: l ->
     let u = coqZ_to_int (snd a) in
     if u = 0 then
       Format.fprintf ff "%d*%a" x print_var_name i
     else
       Format.fprintf ff "%d + %d*%a" u x print_var_name i;
     List.iter (fun (i, x) -> Format.fprintf ff " + %d*%a" x print_var_name i) l

let print_constraint ff c =
  Format.fprintf ff "%a <= %d" print_linear (fst c) (coqZ_to_int (snd c))

let print_poly ff p =
  Format.fprintf ff "@[<v 2>[@,";
  List.iter (Format.fprintf ff "%a ,@," print_constraint) p;
  Format.fprintf ff "@]]"

let print_alist ff l =
  Format.fprintf ff "(";
  List.iter (Format.fprintf ff "%a," print_affine) l;
  Format.fprintf ff ")"

let print_pi ff p =
  Format.fprintf ff "@[<v 2>{@,";
  Format.fprintf ff "pi_instr = %d@," p.pi_instr;
  Format.fprintf ff "pi_poly = %a@," print_poly p.pi_poly;
  Format.fprintf ff "pi_schedule = %a@," print_alist p.pi_schedule;
  Format.fprintf ff "pi_transformation = %a@," print_alist p.pi_transformation;
  Format.fprintf ff "@]}"

let rec print_expr depth ff = function
  | Constant n -> Format.fprintf ff "%d" (coqZ_to_int n)
  | Sum (e1, e2) -> Format.fprintf ff "(%a) + (%a)" (print_expr depth) e1 (print_expr depth) e2
  | Mult (n, e) -> Format.fprintf ff "%d * (%a)" (coqZ_to_int n) (print_expr depth) e
  | Div (e, n) -> Format.fprintf ff "(%a) / %d" (print_expr depth) e (coqZ_to_int n)
  | Mod (e, n) -> Format.fprintf ff "(%a) %% %d" (print_expr depth) e (coqZ_to_int n)
  | Var n -> Format.fprintf ff "%a" print_var_name (depth - 1 - coqnat_to_int n)
  | Max (e1, e2) -> Format.fprintf ff "max(%a, %a)" (print_expr depth) e1 (print_expr depth) e2
  | Min (e1, e2) -> Format.fprintf ff "min(%a, %a)" (print_expr depth) e1 (print_expr depth) e2

let rec print_test depth ff = function
  | LE (e1, e2) -> Format.fprintf ff "%a <= %a" (print_expr depth) e1 (print_expr depth) e2
  | EQ (e1, e2) -> Format.fprintf ff "%a == %a" (print_expr depth) e1 (print_expr depth) e2
  | And (t1, t2) -> Format.fprintf ff "(%a) && (%a)" (print_test depth) t1 (print_test depth) t2
  | Or (t1, t2) -> Format.fprintf ff "(%a) || (%a)" (print_test depth) t1 (print_test depth) t2
  | Not t -> Format.fprintf ff "!(%a)" (print_test depth) t
  | TConstantTest b -> Format.fprintf ff "%s" (if b then "true" else "false")

let rec print_loop depth ff = function
  | Guard (cond, s) -> Format.fprintf ff "@[<v 2>guard %a@,%a@]" (print_test depth) cond (print_loop depth) s
  | Loop (lb, ub, s) ->
    if ub = Sum(lb, Constant (Zpos Coq_xH)) then
      Format.fprintf ff "let %a = %a in@,%a" print_var_name depth (print_expr depth) lb (print_loop (depth + 1)) s
    else
      Format.fprintf ff "@[<v 2>loop %a = %a to %a@,%a@]" print_var_name depth (print_expr depth) lb (print_expr depth) ub (print_loop (depth + 1)) s
  | Seq l -> List.iter (print_loop depth ff) l
  | Instr (x, l) -> Format.fprintf ff "instr %d (" x; List.iter (fun x -> Format.fprintf ff "%a, " (print_expr depth) x) l; Format.fprintf ff ")@,"

let coqstring_to_string l =
  let n = List.length l in
  let s = Bytes.create n in
  let rec iter i = function
    | [] -> ()
    | c :: l -> Bytes.set s i c; iter (i + 1) l
  in iter 0 l; Bytes.to_string s

let process_pi (((env_size, scan_dimensions), name), pi) =
  let env_size = coqnat_to_int env_size in
  let scan_dimensions = coqnat_to_int scan_dimensions in
  let name = coqstring_to_string name in
  let () = Format.printf "%s:@.@." name in
  let () = Format.printf "Origninal:@.%a@.@." print_pi pi in
  let sd = int_to_coqnat scan_dimensions in
  let ev = int_to_coqnat env_size in
  let pi_lex = PolyLang.pi_elim_schedule sd ev pi in
  let () = Format.printf "No schedule:@.%a@.@." print_pi pi_lex in
  let scand = int_to_coqnat (scan_dimensions + List.length pi.pi_schedule) in
  let totald = int_to_coqnat (env_size + scan_dimensions + List.length pi.pi_schedule) in
  let (gen, ok) = CodeGen.complete_generate scand totald pi_lex in
  if ok then
    Format.printf "Generated code:@.%a@.@." (print_loop env_size) gen
  else
    Format.printf "Generation failed.@.@."


let () = List.iter process_pi Extraction.test_pis
