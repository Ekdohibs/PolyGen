Require Import CodeGen.
Require Import PolyLang.
Require Import Instr.
Require Import Vpl.ImpureConfig.
Require Import List.
Require Import String.

Import ListNotations.

Require Extraction.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Extract Inlined Constant instr => "int".

Extraction Blacklist String List.

Axiom dummy : instr.
Extract Inlined Constant dummy => "0".

Definition test_pi_1 := {|
   pi_instr := dummy ;
   pi_poly := [ ([0; 0; -1; 0], 0); ([0; 0; 0; -1], 0); ([-1; 0; 1; 0], 0); ([0; -1; 0; 1], 0) ] ;
   pi_schedule := [([0; 0; 0; 1], 0); ([0; 0; 1; 0], 0)] ;
   pi_transformation := [([0; 0; 1; 0], 0); ([0; 0; 0; 1], 0)] ;
|}.

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