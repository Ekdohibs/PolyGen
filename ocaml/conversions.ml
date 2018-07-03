open BinNums
open Datatypes

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
