Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Parameter instr : Type.
Parameter mem : Type.
Parameter instr_semantics : instr -> list Z -> mem -> mem -> Prop.

Inductive iter_semantics (P : Z -> mem -> mem -> Prop) : Z -> Z -> mem -> mem -> Prop :=
| IDone : forall lb ub mem, ub <= lb -> iter_semantics P lb ub mem mem
| IProgress : forall lb ub mem1 mem2 mem3,
    lb < ub -> P lb mem1 mem2 -> iter_semantics P (lb + 1) ub mem2 mem3 ->
    iter_semantics P lb ub mem1 mem3.

Lemma iter_semantics_map (P Q : Z -> mem -> mem -> Prop) :
  forall lb ub mem1 mem2,
    (forall x mem1 mem2, lb <= x < ub -> P x mem1 mem2 -> Q x mem1 mem2) ->
    iter_semantics P lb ub mem1 mem2 ->
    iter_semantics Q lb ub mem1 mem2.
Proof.
  intros lb ub mem1 mem2 Himp Hsem.
  induction Hsem; econstructor; eauto; [eapply Himp|eapply IHHsem]; eauto.
  - lia.
  - intros; apply Himp; auto; lia.
Qed.