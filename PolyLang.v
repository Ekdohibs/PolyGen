Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Psatz.
Open Scope Z_scope.
Open Scope list_scope.

Parameter instr : Type.
Parameter mem : Type.
Parameter instr_semantics : instr -> list Z -> mem -> mem -> Prop.

Require Import Linalg.

Record Polyhedral_Instruction := {
  pi_instr : instr ;
  pi_poly : polyhedron ;
  pi_schedule : list (vector * Z)%type ;
  (* pi_transformation : list (vector * Z)%type ; *)
}.


Definition Poly_Program := list Polyhedral_Instruction.

(*
Record Instruction_Point := {
  ip_instr : instr ;
  ip_args : list Z ;
  ip_timestamp : list Z ;
}.
 *)

Fixpoint timestamp_compare t1 t2 :=
  match t1, t2 with
  | nil, nil => Eq
  | x :: t1, nil => Gt
  | nil, y :: t2 => Lt
  | x :: t1, y :: t2 => match x ?= y with Eq => timestamp_compare t1 t2 | c => c end
  end.

Definition timestamp_at schedule p := map (fun t => dot_product (fst t) p + (snd t)) schedule.

Definition scanned to_scan n p m q := to_scan m q && negb (is_eq p q && (n =? m)%nat).
Hint Unfold scanned.

Inductive poly_semantics : (nat -> vector -> bool) -> Poly_Program -> mem -> mem -> Prop :=
| PolyDone : forall to_scan prog mem, (forall n p, to_scan n p = false) -> poly_semantics to_scan prog mem mem
| PolyProgress : forall to_scan prog mem1 mem2 mem3 poly_instr n p,
    to_scan n p = true -> nth_error prog n = Some poly_instr ->
    (forall n2 p2 poly_instr2, nth_error prog n2 = Some poly_instr2 ->
                          timestamp_compare (timestamp_at poly_instr2.(pi_schedule) p2) (timestamp_at poly_instr.(pi_schedule) p) = Lt ->
                          to_scan n2 p2 = false) ->
    instr_semantics poly_instr.(pi_instr) p mem1 mem2 ->
    poly_semantics (scanned to_scan n p) prog mem2 mem3 ->
    poly_semantics to_scan prog mem1 mem3.

Theorem poly_semantics_extensionality :
  forall to_scan1 prog mem1 mem2,
    poly_semantics to_scan1 prog mem1 mem2 -> forall to_scan2, (forall n p, to_scan1 n p = to_scan2 n p) -> poly_semantics to_scan2 prog mem1 mem2.
Proof.
  intros to_scan1 prog mem1 mem2 Hsem.
  induction Hsem as [to_scan3 prog1 mem4 Hdone|to_scan3 prog1 mem3 mem4 mem5 pi n p Hscanp Heqpi Hts Hsem1 Hsem2 IH].
  - intros. constructor. intros. eauto.
  - intros to_scan2 Heq. econstructor; eauto. apply IH. intros. autounfold. rewrite Heq. auto.
Qed.

Definition wf_scan (to_scan : nat -> vector -> bool) := forall n p q, is_eq p q = true -> to_scan n p = to_scan n q.

Lemma scanned_wf_compat :
  forall to_scan n p, wf_scan to_scan -> wf_scan (scanned to_scan n p).
Proof.
  intros to_scan n p Hwf m q r Heq.
  autounfold. rewrite (Hwf m q r); auto. f_equal; f_equal; f_equal. apply is_eq_is_eq_right; auto.
Qed.

Theorem poly_semantics_concat :
  forall to_scan1 prog mem1 mem2,
    poly_semantics to_scan1 prog mem1 mem2 ->
    forall to_scan2 mem3,
    wf_scan to_scan1 ->
    (forall n p, to_scan1 n p = false \/ to_scan2 n p = false) ->
    (forall n1 p1 pi1 n2 p2 pi2, nth_error prog n1 = Some pi1 -> nth_error prog n2 = Some pi2 ->
                           timestamp_compare (timestamp_at pi2.(pi_schedule) p2) (timestamp_at pi1.(pi_schedule) p1) = Lt ->
                           to_scan1 n1 p1 = false \/ to_scan2 n2 p2 = false) ->
    
    poly_semantics to_scan2 prog mem2 mem3 ->
    poly_semantics (fun n p => to_scan1 n p || to_scan2 n p) prog mem1 mem3.
Proof.
  intros to_scan1 prog mem1 mem2 Hsem.
  induction Hsem as [to_scan3 prog1 mem4 Hdone|to_scan3 prog1 mem4 mem5 mem6 pi n p Hscanp Heqpi Hts Hsem1 Hsem2 IH].
  - intros to_scan2 mem3 Hwf1 Hdisj Hcmp Hsem1. eapply poly_semantics_extensionality; eauto. intros. rewrite Hdone. auto.
  - intros to_scan2 mem3 Hwf1 Hdisj Hcmp Hsem3. eapply PolyProgress with (n := n) (p := p); eauto.
    + rewrite Hscanp. auto.
    + intros n2 p2 pi2 Heqpi2 Hts2.
      rewrite orb_false_iff. split.
      * apply (Hts n2 p2 pi2); auto.
      * destruct (Hcmp n p pi n2 p2 pi2) as [H | H]; auto; congruence.
    + eapply poly_semantics_extensionality; [apply IH|]; eauto.
      * apply scanned_wf_compat; auto.
      * intros n2 p2. autounfold. destruct (Hdisj n2 p2) as [H | H]; rewrite H; auto.
      * intros n1 p1 pi1 n2 p2 pi2 Heqpi1 Heqpi2 Hcmp1.
        destruct (Hcmp n1 p1 pi1 n2 p2 pi2) as [H | H]; autounfold; auto. rewrite H. simpl.
        destruct (is_eq p p1 && (n =? n1)%nat) eqn:Hd; simpl; auto.
      * intros n0 p0. autounfold. simpl.
        destruct (to_scan3 n0 p0) eqn:Hscan3; simpl; auto.
        -- destruct (Hdisj n0 p0) as [H | H]; [congruence|rewrite H; auto using orb_false_r].
        -- destruct (is_eq p p0 && (n =? n0)%nat) eqn:Hd; simpl; auto using andb_true_r.
           rewrite andb_true_iff in Hd. destruct Hd as [Heqp Hn]. erewrite Hwf1 in Hscanp; [|eauto]. rewrite Nat.eqb_eq in Hn. congruence.
Qed.

