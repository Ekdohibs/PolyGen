(* *****************************************************************)
(*                                                                 *)
(*               Verified polyhedral AST generation                *)
(*                                                                 *)
(*                 Nathanaël Courant, Inria Paris                  *)
(*                                                                 *)
(*  Copyright Inria. All rights reserved. This file is distributed *)
(*  under the terms of the GNU Lesser General Public License as    *)
(*  published by the Free Software Foundation, either version 2.1  *)
(*  of the License, or (at your option) any later version.         *)
(*                                                                 *)
(* *****************************************************************)

Require Import ZArith.
Require Import List.
Require Import Psatz.


Require Import Linalg.
Require Import ImpureAlarmConfig.

Require Import PolyLang.
Require Import ASTGen.
Require Import PolyLoop.
Require Import PolyLoopSimpl.
Require Import LoopGen.
Require Import Loop.

Open Scope Z_scope.

Definition complete_generate d n pi :=
  BIND polyloop <- generate d n pi -;
  polyloop_to_loop (n - d)%nat polyloop.

Theorem complete_generate_preserve_sem :
  forall d n pi env mem1 mem2,
    (d <= n)%nat ->
    WHEN st <- complete_generate d n pi THEN
    loop_semantics st env mem1 mem2 ->
    length env = (n - d)%nat ->
    (forall c, In c pi.(pi_poly) -> fst c =v= resize n (fst c)) ->
    env_poly_lex_semantics (rev env) n (pi :: nil) mem1 mem2.
Proof.
  intros d n pi env mem1 mem2 Hdn st Hst Hloop Henv Hsize.
  unfold complete_generate in Hst.
  bind_imp_destruct Hst polyloop Hpolyloop.
  eapply generate_preserves_sem; eauto.
  eapply polyloop_to_loop_correct; eauto.
Qed.



Definition complete_generate_many d n pis :=
  BIND polyloop <- generate_loop_many d n pis -;
  BIND simp <- polyloop_simplify polyloop (n - d)%nat nil -;
  polyloop_to_loop (n - d)%nat simp.

Theorem complete_generate_many_preserve_sem :
  forall d n pis env mem1 mem2,
    (d <= n)%nat ->
    WHEN st <- complete_generate_many d n pis THEN
    loop_semantics st env mem1 mem2 ->
    length env = (n - d)%nat ->
    pis_have_dimension pis n ->
    env_poly_lex_semantics (rev env) n pis mem1 mem2.
Proof.
  intros d n pis env mem1 mem2 Hdn st Hst Hloop Henv Hpis.
  unfold complete_generate_many in Hst.
  bind_imp_destruct Hst polyloop Hpolyloop; bind_imp_destruct Hst simp Hsimp.
  eapply generate_loop_many_preserves_sem; eauto; [|unfold generate_invariant; auto].
  eapply polyloop_simplify_correct; [|exact Hsimp| | |]; auto; [unfold poly_nrl; simpl; lia|].
  eapply polyloop_to_loop_correct; eauto.
Qed.
