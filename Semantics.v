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

Require Import List.

Require Import Vpl.Impure.
Require Import Mymap.
Require Import ImpureOperations.

Require Import Misc.

Parameter mem : Type.

(** * Iterating semantics on a list *)

Inductive iter_semantics {A : Type} (P : A -> mem -> mem -> Prop) : list A -> mem -> mem -> Prop :=
| IDone : forall mem, iter_semantics P nil mem mem
| IProgress : forall x l mem1 mem2 mem3,
    P x mem1 mem2 -> iter_semantics P l mem2 mem3 ->
    iter_semantics P (x :: l) mem1 mem3.

Lemma iter_semantics_map {A : Type} (P Q : A -> mem -> mem -> Prop) :
  forall l mem1 mem2,
    (forall x mem1 mem2, In x l -> P x mem1 mem2 -> Q x mem1 mem2) ->
    iter_semantics P l mem1 mem2 ->
    iter_semantics Q l mem1 mem2.
Proof.
  intros l mem1 mem2 Himp Hsem.
  induction Hsem; econstructor; eauto; [eapply Himp|eapply IHHsem]; eauto.
  - simpl; auto.
  - intros; apply Himp; simpl; auto.
Qed.

Lemma iter_semantics_mapl :
  forall (A B : Type) P (f : A -> B) (l : list A) mem1 mem2,
    iter_semantics P (map f l) mem1 mem2 <-> iter_semantics (fun x => P (f x)) l mem1 mem2.
Proof.
  intros A B P f. induction l.
  - intros; split; simpl; intros H; inversion_clear H; constructor.
  - intros; split; simpl; intros H; inversion_clear H; econstructor; eauto; rewrite IHl in *; auto.
Qed.

Lemma iter_semantics_combine :
  forall (A B : Type) P (xs : list A) (ys : list B) mem1 mem2,
    length xs = length ys -> iter_semantics P xs mem1 mem2 <-> iter_semantics (fun p => P (fst p)) (combine xs ys) mem1 mem2.
Proof.
  intros A B P xs ys mem1 mem2 H.
  replace xs with (map fst (combine xs ys)) at 1 by (apply map_combine; auto).
  rewrite iter_semantics_mapl; reflexivity.
Qed.

Module IterImpureSemantics (Import Imp: FullImpureMonad).

  Module ImpOps := ImpureOps Imp.
  Import ImpOps.

  Lemma iter_semantics_sequence :
    forall (A : Type) P (xs : list (imp A)) (ys : list A) mem1 mem2,
      mayReturn (sequence xs) ys ->
      iter_semantics (fun x mem3 mem4 => WHEN y <- x THEN P y mem3 mem4) xs mem1 mem2 -> iter_semantics P ys mem1 mem2.
  Proof.
    intros A P. induction xs.
    - intros ys mem1 mem2 Hys Hsem; simpl in *. apply mayReturn_pure in Hys; rewrite <- Hys.
      inversion_clear Hsem; constructor.
    - intros ys mem1 mem2 Hys Hsem; simpl in *.
      bind_imp_destruct Hys y Hy.
      bind_imp_destruct Hys ys1 Hys1.
      apply mayReturn_pure in Hys; rewrite <- Hys in *.
      inversion_clear Hsem. 
      econstructor; [apply H; auto|].
      apply IHxs; auto.
  Qed.

  (* yet another unfortunately needed lemma because of mymap... *)
  Lemma iter_semantics_mymapl :
    forall (A B : Type) P (f : A -> B) (l : list A) mem1 mem2,
      iter_semantics P (mymap f l) mem1 mem2 <-> iter_semantics (fun x => P (f x)) l mem1 mem2.
  Proof.
    intros A B P f. induction l.
    - intros; split; simpl; intros H; inversion_clear H; constructor.
    - intros; split; simpl; intros H; inversion_clear H; econstructor; eauto; rewrite IHl in *; auto.
  Qed.

  Lemma iter_semantics_mapM :
    forall (A B : Type) f P (xs : list A) (ys : list B) mem1 mem2,
      mayReturn (mapM f xs) ys ->
      iter_semantics (fun x mem3 mem4 => WHEN y <- f x THEN P y mem3 mem4) xs mem1 mem2 -> iter_semantics P ys mem1 mem2.
  Proof.
    intros A B f P xs ys mem1 mem2 Hmap Hsem.
    eapply iter_semantics_sequence; [exact Hmap|].
    rewrite iter_semantics_mymapl. auto.
  Qed.

  Lemma iter_semantics_mapM_rev :
    forall (A B : Type) P f (xs : list A) (ys : list B) mem1 mem2,
      mayReturn (mapM f xs) ys ->
      iter_semantics P ys mem1 mem2 ->
      iter_semantics (fun '(x, y) mem3 mem4 => mayReturn (f x) y /\ P y mem3 mem4) (combine xs ys) mem1 mem2.
  Proof.
    intros A B P f. induction xs.
    - intros ys mem1 mem2 Hys Hsem; simpl in *. apply mayReturn_pure in Hys; rewrite <- Hys in Hsem.
      inversion_clear Hsem; constructor.
    - intros ys mem1 mem2 Hys Hsem; simpl in *.
      bind_imp_destruct Hys y Hy.
      bind_imp_destruct Hys ys1 Hys1.
      apply mayReturn_pure in Hys; rewrite <- Hys in *.
      inversion_clear Hsem.
      econstructor; [eauto|].
      apply IHxs; auto.
  Qed.

End IterImpureSemantics.
