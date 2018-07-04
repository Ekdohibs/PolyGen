Require Import Result.
Require Import Vpl.Impure.
Require Vpl.ImpureConfig.

Module CoreAlarmed := AlarmImpureMonad Vpl.ImpureConfig.Core.
Export CoreAlarmed.

Ltac bind_imp_destruct H id1 id2 :=
  apply CoreAlarmed.Base.mayReturn_bind in H; destruct H as [id1 [id2 H]].

Definition res_to_alarm {A : Type} (d : A) (x : result A) : imp A :=
  match x with
  | Ok a => pure a
  | Err s => alarm s d
  end.

Lemma res_to_alarm_correct :
  forall (A : Type) (d : A) (x : result A) (y : A),
    mayReturn (res_to_alarm d x) y -> x = Ok y.
Proof.
  intros A d x y. destruct x; simpl.
  - intros H. f_equal. apply mayReturn_pure. auto.
  - intros H. apply mayReturn_alarm in H. tauto.
Qed.
