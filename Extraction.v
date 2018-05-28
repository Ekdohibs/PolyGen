Require Import CodeGen.
Require Import PolyLang.
Require Import Instr.
Require Import Vpl.ImpureConfig.
Require Import List.

Import ListNotations.

Require Extraction.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Extract Inlined Constant instr => "int".

Extraction Blacklist String List.

Axiom dummy : instr.
Extract Inlined Constant dummy => "0".

Definition test_pi := {|
   pi_instr := dummy ;
   pi_poly := [ ([0; 0; -1; 0], 0); ([0; 0; 0; -1], 0); ([-1; 0; 1; 0], 0); ([0; -1; 0; 1], 0) ] ;
   pi_schedule := [([0; 0; 0; 1], 0); ([0; 0; 1; 0], 0)] ;
   pi_transformation := [([0; 0; 1; 0], 0); ([0; 0; 0; 1], 0)] ;
|}.

Definition test_pi_lex := pi_elim_schedule 2%nat 2%nat test_pi.
Definition test_pi_generate := generate 4%nat 6%nat test_pi_lex.

(*
Definition test_pi := {|
   pi_instr := dummy ;
   pi_poly := [ ([0; 0; 0; -1], 0); ([-1; 0; 0; 1], 0); ([0; 1; 0; -3], 0); ([0; -1; 0; 3], 0); ([0; 0; 1; -2], 0); ([0; 0; -1; 2], 0) ] ;
   pi_schedule := [([0; 1; 0; 0], 0); ([0; 0; 1; 0], 0); ([0; 0; 0; 1], 0)] ;
   pi_transformation := [([0; 1; 0; 0], 0); ([0; 0; 1; 0], 0); ([0; 0; 0; 1], 0)] ;
|}.

Definition test_pi_lex := pi_elim_schedule 3%nat 1%nat test_pi.
Definition test_pi_generate := generate 3%nat 4%nat test_pi.
*)

Extraction Inline CoreAlarmed.Base.pure CoreAlarmed.Base.imp.

Cd "extraction".

Separate Extraction generate test_pi_lex test_pi_generate.