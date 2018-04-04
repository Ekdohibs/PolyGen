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
  pi_transformation : list (vector * Z)%type ;
}.


Definition Poly_Program := list Polyhedral_Instruction.

(*
Record Instruction_Point := {
  ip_instr : instr ;
  ip_args : list Z ;
  ip_timestamp : list Z ;
}.
 *)

Fixpoint timestamp_compare_nil t :=
  match t with
  | nil => Eq
  | x :: t => match 0 ?= x with Eq => timestamp_compare_nil t | c => c end
  end.

Lemma timestamp_compare_nil_is_null :
  forall t, is_null t = true -> timestamp_compare_nil t = Eq.
Proof.
  induction t; auto.
  intros H; simpl in *. rewrite andb_true_iff in H. destruct H as [Ha Hn].
  rewrite Z.eqb_eq in Ha; rewrite Ha; auto.
Qed.

Lemma timestamp_compare_nil_eq :
  forall t1 t2, is_eq t1 t2 = true -> timestamp_compare_nil t1 = timestamp_compare_nil t2.
Proof.
  induction t1.
  - intros t2 H. simpl. rewrite timestamp_compare_nil_is_null; auto. rewrite is_eq_nil_left in H; auto.
  - intros t2 H. destruct t2.
    + rewrite timestamp_compare_nil_is_null; auto.
    + simpl in H. rewrite andb_true_iff in H. destruct H as [Ha Hn]. rewrite Z.eqb_eq in Ha. rewrite Ha.
      simpl. destruct z; auto.
Qed.

Fixpoint timestamp_compare t1 t2 :=
  match t1, t2 with
  | nil, nil => Eq
  | _, nil => CompOpp (timestamp_compare_nil t1)
  | nil, _ => timestamp_compare_nil t2
  | x :: t1, y :: t2 => match x ?= y with Eq => timestamp_compare t1 t2 | c => c end
  end.

Lemma timestamp_compare_antisym :
  forall t1 t2, timestamp_compare t1 t2 = CompOpp (timestamp_compare t2 t1).
Proof.
  induction t1.
  - destruct t2; simpl; auto using CompOpp_involutive.
  - destruct t2; simpl; auto.
    rewrite Z.compare_antisym.
    rewrite IHt1. destruct (z ?= a); auto.
Qed.

Lemma timestamp_compare_null_left :
  forall t1 t2, is_null t1 = true -> timestamp_compare t1 t2 = timestamp_compare_nil t2.
Proof.
  induction t1.
  - intros; destruct t2; auto.
  - intros t2 H; destruct t2; simpl in *; rewrite andb_true_iff in H; destruct H as [Ha Hn]; rewrite Z.eqb_eq in Ha; rewrite Ha.
    + rewrite timestamp_compare_nil_is_null; auto.
    + rewrite IHt1; auto.
Qed.

Lemma timestamp_compare_nil_left :
  forall t, timestamp_compare nil t = timestamp_compare_nil t.
Proof.
  intros; destruct t; auto.
Qed.

Lemma timestamp_compare_nil_right :
  forall t, timestamp_compare t nil = CompOpp (timestamp_compare_nil t).
Proof.
  intros; destruct t; auto.
Qed.

Lemma timestamp_compare_left_eq :
  forall t1 t2 t3, is_eq t1 t2 = true -> timestamp_compare t1 t3 = timestamp_compare t2 t3.
Proof.
  induction t1.
  - intros t2 t3 H. rewrite timestamp_compare_nil_left. rewrite timestamp_compare_null_left; auto. rewrite is_eq_nil_left in H; auto.
  - intros t2 t3 H. destruct t2.
    + rewrite timestamp_compare_nil_left. rewrite timestamp_compare_null_left; auto. 
    + simpl in H. rewrite andb_true_iff in H. destruct H as [Ha Hn].
      rewrite Z.eqb_eq in Ha. rewrite Ha. destruct t3.
      * simpl in *. erewrite timestamp_compare_nil_eq; eauto.
      * simpl. erewrite IHt1; auto.
Qed.

Lemma timestamp_compare_right_eq :
  forall t1 t2 t3, is_eq t2 t3 = true -> timestamp_compare t1 t2 = timestamp_compare t1 t3.
Proof.
  intros t1 t2 t3 H.
  rewrite timestamp_compare_antisym.
  erewrite timestamp_compare_left_eq; [|apply H]. rewrite <- timestamp_compare_antisym. auto.
Qed.

Lemma timestamp_compare_app :
  forall t1 t2 t3 t4, length t1 = length t3 ->
                 timestamp_compare (t1 ++ t2) (t3 ++ t4) = match timestamp_compare t1 t3 with Eq => timestamp_compare t2 t4 | c => c end.
Proof.
  induction t1.
  - intros t2 t3 t4 H. destruct t3; simpl in *; auto; lia.
  - intros t2 t3 t4 H. destruct t3; simpl in *; auto; try lia.
    rewrite IHt1; try lia.
    destruct (a ?= z); auto.
Qed.

Definition matrix_product schedule p := map (fun t => dot_product (fst t) p + (snd t)) schedule.

Definition scanned to_scan n p m q := to_scan m q && negb (is_eq p q && (n =? m)%nat).
Hint Unfold scanned.

Inductive poly_semantics : (nat -> vector -> bool) -> Poly_Program -> mem -> mem -> Prop :=
| PolyDone : forall to_scan prog mem, (forall n p, to_scan n p = false) -> poly_semantics to_scan prog mem mem
| PolyProgress : forall to_scan prog mem1 mem2 mem3 poly_instr n p,
    to_scan n p = true -> nth_error prog n = Some poly_instr ->
    (forall n2 p2 poly_instr2, nth_error prog n2 = Some poly_instr2 ->
                          timestamp_compare (matrix_product poly_instr2.(pi_schedule) p2) (matrix_product poly_instr.(pi_schedule) p) = Lt ->
                          to_scan n2 p2 = false) ->
    instr_semantics poly_instr.(pi_instr) (matrix_product poly_instr.(pi_transformation) p) mem1 mem2 ->
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
                           timestamp_compare (matrix_product pi2.(pi_schedule) p2) (matrix_product pi1.(pi_schedule) p1) = Lt ->
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

(* Semantics with an identity schedule. *)
Inductive poly_lex_semantics : (nat -> vector -> bool) -> Poly_Program -> mem -> mem -> Prop :=
| PolyLexDone : forall to_scan prog mem, (forall n p, to_scan n p = false) -> poly_lex_semantics to_scan prog mem mem
| PolyLexProgress : forall to_scan prog mem1 mem2 mem3 poly_instr n p,
    to_scan n p = true -> nth_error prog n = Some poly_instr ->
    (forall n2 p2, timestamp_compare p2 p = Lt -> to_scan n2 p2 = false) ->
    instr_semantics poly_instr.(pi_instr) (matrix_product poly_instr.(pi_transformation) p) mem1 mem2 ->
    poly_lex_semantics (scanned to_scan n p) prog mem2 mem3 ->
    poly_lex_semantics to_scan prog mem1 mem3.

Theorem poly_lex_semantics_extensionality :
  forall to_scan1 prog mem1 mem2,
    poly_lex_semantics to_scan1 prog mem1 mem2 -> forall to_scan2, (forall n p, to_scan1 n p = to_scan2 n p) -> poly_lex_semantics to_scan2 prog mem1 mem2.
Proof.
  intros to_scan1 prog mem1 mem2 Hsem.
  induction Hsem as [to_scan3 prog1 mem4 Hdone|to_scan3 prog1 mem3 mem4 mem5 pi n p Hscanp Heqpi Hts Hsem1 Hsem2 IH].
  - intros. constructor. intros. eauto.
  - intros to_scan2 Heq. econstructor; eauto. apply IH. intros. autounfold. rewrite Heq. auto.
Qed.

Theorem poly_lex_concat :
  forall to_scan1 prog mem1 mem2,
    poly_lex_semantics to_scan1 prog mem1 mem2 ->
    forall to_scan2 mem3,
    wf_scan to_scan1 ->
    (forall n p, to_scan1 n p = false \/ to_scan2 n p = false) ->
    (forall n1 p1 n2 p2, timestamp_compare p2 p1 = Lt -> to_scan1 n1 p1 = false \/ to_scan2 n2 p2 = false) ->
    poly_lex_semantics to_scan2 prog mem2 mem3 ->
    poly_lex_semantics (fun n p => to_scan1 n p || to_scan2 n p) prog mem1 mem3.
Proof.
  intros to_scan1 prog mem1 mem2 Hsem.
  induction Hsem as [to_scan3 prog1 mem4 Hdone|to_scan3 prog1 mem4 mem5 mem6 pi n p Hscanp Heqpi Hts Hsem1 Hsem2 IH].
  - intros to_scan2 mem3 Hwf1 Hdisj Hcmp Hsem1. eapply poly_lex_semantics_extensionality; eauto. intros. rewrite Hdone. auto.
  - intros to_scan2 mem3 Hwf1 Hdisj Hcmp Hsem3. eapply PolyLexProgress with (n := n) (p := p); eauto.
    + rewrite Hscanp. auto.
    + intros n2 p2 Hts2.
      rewrite orb_false_iff. split.
      * apply (Hts n2 p2); auto.
      * destruct (Hcmp n p n2 p2) as [H | H]; auto; congruence.
    + eapply poly_lex_semantics_extensionality; [apply IH|]; eauto.
      * apply scanned_wf_compat; auto.
      * intros n2 p2. autounfold. destruct (Hdisj n2 p2) as [H | H]; rewrite H; auto.
      * intros n1 p1 n2 p2 Hcmp1.
        destruct (Hcmp n1 p1 n2 p2) as [H | H]; autounfold; auto. rewrite H. simpl.
        destruct (is_eq p p1 && (n =? n1)%nat) eqn:Hd; simpl; auto.
      * intros n0 p0. autounfold. simpl.
        destruct (to_scan3 n0 p0) eqn:Hscan3; simpl; auto.
        -- destruct (Hdisj n0 p0) as [H | H]; [congruence|rewrite H; auto using orb_false_r].
        -- destruct (is_eq p p0 && (n =? n0)%nat) eqn:Hd; simpl; auto using andb_true_r.
           rewrite andb_true_iff in Hd. destruct Hd as [Heqp Hn]. erewrite Hwf1 in Hscanp; [|eauto]. rewrite Nat.eqb_eq in Hn. congruence.
Qed.

Fixpoint prefix (d : nat) (l : vector) :=
  match d with
  | O => l
  | S d => 0 :: prefix d l
  end.

Fixpoint resize (d : nat) (l : vector) :=
  match d with
  | O => nil
  | S d => match l with nil => 0 :: resize d nil | x :: l => x :: resize d l end
  end.

Theorem resize_length :
  forall d l, length (resize d l) = d.
Proof.
  induction d; destruct l; simpl; auto.
Qed.
Hint Immediate resize_length.

Theorem resize_nil_null :
  forall d, is_null (resize d nil) = true.
Proof.
  induction d; auto.
Qed.

Theorem resize_eq :
  forall d l, (length l <= d)%nat -> is_eq (resize d l) l = true.
Proof.
  induction d.
  - intros l H; destruct l; simpl in *; auto; lia.
  - intros l H; destruct l; simpl in *.
    + apply resize_nil_null.
    + rewrite IHd; [rewrite Z.eqb_refl; auto|lia].
Qed.

Theorem resize_skipn_eq :
  forall d l, is_eq (resize d l ++ skipn d l) l = true.
Proof.
  induction d.
  - intros l; simpl in *; auto.
  - intros l; destruct l; simpl in *.
    + rewrite app_nil_r; apply resize_nil_null.
    + rewrite IHd; rewrite Z.eqb_refl; auto.
Qed.

Definition prefix_constraint (d : nat) (c : vector * Z) := (prefix d (fst c), snd c).

Definition pi_elim_schedule (d : nat) (pi : Polyhedral_Instruction) :=
  {|
    pi_instr := pi.(pi_instr) ;
    pi_schedule := nil ;
    pi_transformation := map (prefix_constraint d) pi.(pi_transformation) ;
    pi_poly := nil ; (* todo *)
  |}.

Definition elim_schedule (d : nat) (p : Poly_Program) := map (pi_elim_schedule d) p.

Lemma map_nth_error_none :
  forall A B n (f : A -> B) l, nth_error l n = None -> nth_error (map f l) n = None.
Proof.
  intros; rewrite nth_error_None in *; rewrite map_length; auto.
Qed.

Lemma is_eq_add :
  forall l1 l2 l3 l4, length l1 = length l3 -> is_eq (l1 ++ l2) (l3 ++ l4) = is_eq l1 l3 && is_eq l2 l4.
Proof.
  induction l1.
  - intros l2 l3 l4 H. destruct l3; simpl in *; auto; lia.
  - intros l2 l3 l4 H. destruct l3; simpl in *; try lia.
    rewrite IHl1; try lia. destruct (a =? z); auto.
Qed.

Lemma matrix_product_eq :
  forall m l1 l2, is_eq l1 l2 = true -> matrix_product m l1 = matrix_product m l2.
Proof.
  intros m l1 l2 H.
  unfold matrix_product. apply map_ext. intros c. f_equal. apply dot_product_eq_compat_right; auto.
Qed.

Lemma prefix_product_skipn :
  forall d l1 l2, dot_product (prefix d l1) l2 = dot_product l1 (skipn d l2).
Proof.
  induction d.
  - intros l1 l2; simpl; auto.
  - intros l1 l2. destruct l2; simpl.
    + destruct l1; auto.
    + auto.
Qed.

Lemma matrix_product_skipn :
  forall d m l, matrix_product (map (prefix_constraint d) m) l = matrix_product m (skipn d l).
Proof.
  intros. unfold matrix_product. rewrite map_map.
  apply map_ext. intros. unfold prefix_constraint; simpl. rewrite prefix_product_skipn. auto.
Qed.

Theorem poly_elim_schedule_semantics_preserve :
  forall d to_scan_lex prog_lex mem1 mem2,
    poly_lex_semantics to_scan_lex prog_lex mem1 mem2 ->
    forall to_scan prog,
      prog_lex = elim_schedule d prog ->
      wf_scan to_scan -> wf_scan to_scan_lex ->
      (forall n pi, nth_error prog n = Some pi -> (length pi.(pi_schedule) <= d)%nat) ->
      (forall n p ts pi, nth_error prog n = Some pi -> length ts = d ->
                    to_scan_lex n (ts ++ p) = is_eq ts (matrix_product pi.(pi_schedule) p) && to_scan n p) ->
      (forall n p, nth_error prog n = None -> to_scan n p = false) ->
      poly_semantics to_scan prog mem1 mem2.
Proof.
  intros d to_scan_lex prog mem1 mem2 Hsem.
  induction Hsem as [to_scan_l1 prog_l1 mem3 Hdone|to_scan_l1 prog_l1 mem3 mem4 mem5 pi n p Hscanp Heqpi Hts Hsem1 Hsem2 IH].
  - intros to_scan prog Hprogeq Hwf Hwflex Hsched_length Hcompat Hout.
    apply PolyDone. intros n p.
    destruct (nth_error prog n) as [pi|] eqn:Heq.
    + specialize (Hcompat n p (resize d (matrix_product pi.(pi_schedule) p)) pi).
      rewrite Hdone in Hcompat. rewrite resize_eq in Hcompat.
      * simpl in Hcompat. symmetry; apply Hcompat; auto.
      * unfold matrix_product. rewrite map_length. eauto.
    + auto.
  - intros to_scan prog Hprogeq Hwf Hwflex Hsched_length Hcompat Hout.
    assert (Hs : to_scan_l1 n (resize d p ++ skipn d p) = true).
    { unfold wf_scan in Hwflex; erewrite Hwflex; eauto using resize_skipn_eq. }
    rewrite Hprogeq in *; unfold elim_schedule in Heqpi.
    destruct (nth_error prog n) as [pi1|] eqn:Hpi1; [| rewrite map_nth_error_none in Heqpi; congruence ].
    erewrite map_nth_error in Heqpi; eauto; inversion Heqpi as [Heqpi1].
    rewrite Hcompat with (pi := pi1) in Hs. rewrite andb_true_iff in Hs; destruct Hs as [Heqp Hscan].
    eapply PolyProgress with (n := n) (p := skipn d p); eauto.
    + intros n2 p2 pi2 Heqpi2 Hcmp.
      specialize (Hts n2 ((resize d (matrix_product pi2.(pi_schedule) p2)) ++ p2)).
      unfold wf_scan in Hwflex. rewrite Hcompat with (pi := pi2) in Hts; auto.
      rewrite resize_eq in Hts by (unfold matrix_product; rewrite map_length; eauto). simpl in Hts.
      apply Hts. erewrite <- timestamp_compare_right_eq; [|apply resize_skipn_eq with (d := d)].
      rewrite timestamp_compare_app by (repeat (rewrite resize_length); reflexivity).
      erewrite timestamp_compare_right_eq; [|apply Heqp].
      erewrite timestamp_compare_left_eq; [|apply resize_eq with (d := d); unfold matrix_product; rewrite map_length; eauto].
      rewrite Hcmp; auto.
    + rewrite <- Heqpi1 in Hsem1; unfold pi_elim_schedule in Hsem1; simpl in *.
      rewrite matrix_product_skipn in Hsem1. apply Hsem1.
    + apply IH; auto.
      * apply scanned_wf_compat; auto.
      * apply scanned_wf_compat; auto.
      * intros n0 p0 ts pi0 Hpi0 Hlts.
        unfold scanned. rewrite Hcompat with (pi := pi0); auto.
        destruct (is_eq ts (matrix_product (pi_schedule pi0) p0)) eqn:Htseq; auto.
        simpl.
        f_equal; f_equal.
        destruct (n =? n0)%nat eqn:Heqn; [|repeat (rewrite andb_false_r); auto]. repeat (rewrite andb_true_r).
        erewrite <- is_eq_is_eq_left; [|apply resize_skipn_eq with (d := d)].
        rewrite is_eq_add; [|rewrite Hlts; auto].
        destruct (is_eq (skipn d p) p0) eqn:Heqp0; auto using andb_false_r.
        rewrite andb_true_r.
        rewrite Nat.eqb_eq in Heqn. rewrite Heqn in *. assert (Heqpi0 : pi0 = pi1) by congruence. rewrite Heqpi0 in *.
        erewrite matrix_product_eq in Heqp; eauto.
        erewrite is_eq_is_eq_right; eauto.
      * intros n0 p0 H. unfold scanned. rewrite Hout; auto.
    + auto.
    + auto.
Qed.