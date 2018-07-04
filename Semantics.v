Require Import List.

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