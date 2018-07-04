Require Import CodeGen.
Require Import PolyLang.
Require Import Instr.
Require Import ImpureAlarmConfig.
Require Import List.
Require Import String.
Require Import Linalg.
Require Import ZArith.

Open Scope Z_scope.
Import ListNotations.

Require Extraction.

Set Extraction AccessOpaque.

Extract Inlined Constant CoqAddOn.posPr => "CoqPr.posPr'".
Extract Inlined Constant CoqAddOn.posPrRaw => "CoqPr.posPrRaw'".
Extract Inlined Constant CoqAddOn.zPr => "CoqPr.zPr'".
Extract Inlined Constant CoqAddOn.zPrRaw => "CoqPr.zPrRaw'".

(*
Extract Inlined Constant CoqAddOn.posPr => "(fun x -> Vpl.CoqPr.posPr' (Obj.magic x))".
Extract Inlined Constant CoqAddOn.posPrRaw => "(fun x -> Vpl.CoqPr.posPrRaw' (Obj.magic x))".
Extract Inlined Constant CoqAddOn.zPr => "(fun x -> Vpl.CoqPr.zPr' (Obj.magic x))".
Extract Inlined Constant CoqAddOn.zPrRaw => "(fun x -> Vpl.CoqPr.zPrRaw' (Obj.magic x))".

Extract Constant PedraQBackend.t => "Vpl.PedraQOracles.t".
Extract Constant PedraQBackend.top => "Vpl.PedraQOracles.top".
Extract Constant PedraQBackend.isEmpty => "(fun x -> Vpl.PedraQOracles.isEmpty (Obj.magic x))".
Extract Constant PedraQBackend.add => "(fun x -> Vpl.PedraQOracles.add (Obj.magic x))".
Extract Constant PedraQBackend.pr => "(fun x -> Vpl.PedraQOracles.pr (Obj.magic x))".
*)

Extract Inductive sumbool => "bool" [ "true" "false" ].

Extract Inlined Constant topo_sort_untrusted => "(fun l -> (Topo.coq_toposort l, true))".

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Extract Inlined Constant instr => "int".

Extraction Blacklist String List.
Extraction Blacklist Misc. (* used by the VPL *)

Axiom make_instr : nat -> instr.
Extract Inlined Constant dummy_instr => "0".
Extract Inlined Constant make_instr => "Conversions.coqnat_to_int".

(* begin: debugging code *)
Extract Inlined Constant Debugging.failwith =>
  "(fun st mesg _ -> raise (CertcheckerConfig.CertCheckerFailure (st, (CoqPr.charListTr mesg))))".
(*
Extract Inlined Constant Debugging.trace =>
   "(fun mode l a -> if (Debugging.traceCmp INFO mode) then (print_string (CoqPr.charListTr l); print_newline()); a)".
*)
Definition vr n := (assign n 1 nil, 0).
Arguments vr n%nat.

Delimit Scope aff_scope with aff.
Notation "x * y" := (mult_constraint x y) : aff_scope.
Local Arguments mult_constraint k%Z c%aff.

Notation "x + y" := (add_constraint x y) : aff_scope.
Notation "- x" := (mult_constraint (-1) x) : aff_scope.
Notation "x - y" := (x + -y)%aff : aff_scope.
Notation "$ x" := (nil, x) (at level 30) : aff_scope.

Notation "x /\ y" := (x ++ y) : aff_scope.
Notation "x <= y" := [ (mult_constraint_cst (-1) (add_constraint x (mult_constraint (-1) y))) ] : aff_scope.
Notation "x >= y" := (y <= x)%aff : aff_scope.
Notation "x <= y <= z" := (x <= y /\ y <= z)%aff : aff_scope.
Notation "x >= y >= z" := (x >= y /\ y >= z)%aff (at level 70, y at next level) : aff_scope.
Notation "x == y" := (x <= y /\ y <= x)%aff (at level 70) : aff_scope.

Notation "{{ x }}" := x (only parsing).

Definition a := vr 0. Definition b := vr 1. Definition c := vr 2. Definition d := vr 3. Definition e := vr 4. Definition f := vr 5.

(*
Definition test_pi_1 := {|
   pi_instr := dummy ;
   pi_poly := [ ([0; 0; -1; 0], 0); ([0; 0; 0; -1], 0); ([-1; 0; 1; 0], 0); ([0; -1; 0; 1], 0) ] ;
   pi_schedule := [([0; 0; 0; 1], 0); ([0; 0; 1; 0], 0)] ;
   pi_transformation := [([0; 0; 1; 0], 0); ([0; 0; 0; 1], 0)] ;
|}%aff.

Definition test_pi_2 := {|
   pi_instr := dummy ;
   pi_poly := [ ([0; 0; 0; -1], 0); ([-1; 0; 0; 1], 0); ([0; 1; 0; -3], 0); ([0; -1; 0; 3], 0); ([0; 0; 1; -2], 0); ([0; 0; -1; 2], 0) ] ;
   pi_schedule := [([0; 1; 0; 0], 0); ([0; 0; 1; 0], 0); ([0; 0; 0; 1], 0)] ;
   pi_transformation := [([0; 1; 0; 0], 0); ([0; 0; 1; 0], 0); ([0; 0; 0; 1], 0)] ;
|}.

Definition test_pi_3 := {|
   pi_instr := dummy ;
   pi_poly := [ ([0; 0; -1], 0); ([-1; 0; 1], 0); ([0; 3; -1], 0); ([0; -3; 1], 2) ] ;
   pi_schedule := [([0; 1; 0], 0); ([0; -3; 1], 0)] ;
   pi_transformation := [([0; 0; 1], 0)] ;
|}.

Definition test_pi_4 := {|
   pi_instr := dummy ;
   pi_poly := [ ([0; 0; -1], 0); ([-1; 0; 1], 0); ([0; 3; -1], 0); ([0; -3; 1], 2) ] ;
   pi_schedule := [([0; -3; 1], 0); ([0; 1; 0], 0)] ;
   pi_transformation := [([0; 0; 1], 0)] ;
|}.
*)

Open Scope aff_scope.

Definition test_pi_1 := {|
   pi_instr := make_instr 0%nat ;
   pi_poly := {{ $0 <= c <= a /\ $0 <= d <= b }} ;
   pi_schedule := [d ; c] ;
   pi_transformation := [c ; d] ;
|}.

Definition test_pi_2 := {|
   pi_instr := make_instr 0%nat ;
   pi_poly := {{ $0 <= d <= a /\ b == 3 * d /\ c == 2 * d }} ;
   pi_schedule := [b ; c ; d] ;
   pi_transformation := [b ; c ; d] ;
|}.

Definition test_pi_3 := {|
   pi_instr := make_instr 0%nat ;
   pi_poly := {{ $0 <= c <= a /\ $0 <= c - 3 * b <= $2 }} ;
   pi_schedule := [b ; c - 3 * b] ;
   pi_transformation := [c] ;
|}.

Definition test_pi_4 := {|
   pi_instr := make_instr 0%nat ;
   pi_poly := {{ $0 <= c <= a /\ $0 <= c - 3 * b <= $2 }} ;
   pi_schedule := [c - 3 * b ; b] ;
   pi_transformation := [c] ;
|}.


Open Scope string_scope.

Definition test_pis := [
  (2%nat, 2%nat, "Swap Loop", test_pi_1) ;
  (1%nat, 3%nat, "Linear 3-2-1", test_pi_2) ;
  (1%nat, 2%nat, "Tiling-1", test_pi_3) ;
  (1%nat, 2%nat, "Tiling-2", test_pi_4)
].

Definition test_many := [{|
   pi_instr := make_instr 0%nat ;
   pi_poly := {{ $1 <= c <= a /\ d == c}} ;
   pi_schedule := [] ;
   pi_transformation := [c ; d] ;
  |};
  {|
   pi_instr := make_instr 1%nat ;
   pi_poly := {{ $1 <= c <= a /\ c <= d <= a}} ;
   pi_schedule := [] ;
   pi_transformation := [c ; d] ;
  |};
  {|
   pi_instr := make_instr 2%nat ;
   pi_poly := {{ $1 <= c <= b /\ d == a}} ;
   pi_schedule := [] ;
   pi_transformation := [c ; d] ;
|}].

Extraction Inline CoreAlarmed.Base.pure CoreAlarmed.Base.imp.

Cd "extraction".

Separate Extraction ZArith_dec complete_generate complete_generate_many test_many pi_elim_schedule test_pis Ring_polynom_AddOnQ CstrLCF ProgVar LinTerm(* test_pi_lex test_pi_generate *).