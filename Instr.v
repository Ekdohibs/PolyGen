Require Import ZArith.
Require Import List.

Require Import Semantics.

(** * The basic instructions and their semantics *)

Parameter instr : Type.
Parameter dummy_instr : instr.
Parameter instr_semantics : instr -> list Z -> mem -> mem -> Prop.