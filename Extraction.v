Require Import CodeGen.
Require Import PolyLang.
Require Import Instr.
Require Import Vpl.ImpureConfig.
Require Import List.
Require Import String.
Require Import Linalg.
Require Import ZArith.

Open Scope Z_scope.
Import ListNotations.

Require Extraction.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Extract Inlined Constant instr => "int".

Extraction Blacklist String List.

Axiom dummy : instr.
Extract Inlined Constant dummy => "0".

Definition vr n := (assign n 1 nil, 0).
Arguments vr n%nat.

Delimit Scope aff_scope with aff.
Notation "x * y" := (mult_constraint x y) : aff_scope.
Local Arguments mult_constraint k%Z c%aff.

Notation "x + y" := (add_constraint x y) : aff_scope.
Notation "- x" := (mult_constraint (-1) x) : aff_scope.
Notation "x - y" := (x + -y)%aff : aff_scope.
Notation "$ x" := (nil, x) (at level 30) : aff_scope.

Notation "x <= y" := (mult_constraint_cst (-1) (add_constraint x (mult_constraint (-1) y))) : aff_scope.
Notation "x >= y" := (y <= x)%aff : aff_scope.

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
   pi_instr := dummy ;
   pi_poly := [ $0 <= c ; $0 <= d ; c <= a ; d <= b ] ;
   pi_schedule := [d ; c] ;
   pi_transformation := [c ; d] ;
|}.

Definition test_pi_2 := {|
   pi_instr := dummy ;
   pi_poly := [ $0 <= d ; d <= a ; b <= 3 * d ; 3 * d <= b ; c <= 2 * d ; 2 * d <= c ] ;
   pi_schedule := [b ; c ; d] ;
   pi_transformation := [b ; c ; d] ;
|}.

Definition test_pi_3 := {|
   pi_instr := dummy ;
   pi_poly := [ $0 <= c ; c <= a ; $0 <= c - 3 * b ; c - 3 * b <= $2 ] ;
   pi_schedule := [b ; c - 3 * b] ;
   pi_transformation := [c] ;
|}%aff.

Definition test_pi_4 := {|
   pi_instr := dummy ;
   pi_poly := [ $0 <= c ; c <= a ; $0 <= c - 3 * b ; c - 3 * b <= $2 ] ;
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

Extraction Inline CoreAlarmed.Base.pure CoreAlarmed.Base.imp.

Cd "extraction".

Separate Extraction generate pi_elim_schedule test_pis(* test_pi_lex test_pi_generate *).