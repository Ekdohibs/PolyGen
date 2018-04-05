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

Lemma timestamp_compare_reflexive :
  forall t, timestamp_compare t t = Eq.
Proof.
  induction t; simpl; try rewrite Z.compare_refl; auto.
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

(*
Fixpoint prefix (d : nat) (l : vector) :=
  match d with
  | O => l
  | S d => 0 :: prefix d l
  end.
 *)

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

Definition insert_zeros (d : nat) (i : nat) (l : vector) := resize i l ++ repeat 0 d ++ skipn i l.
Definition insert_zeros_constraint (d : nat) (i : nat) (c : vector * Z) := (insert_zeros d i (fst c), snd c).

Fixpoint make_null_poly (d : nat) (n : nat) :=
  match n with
  | O => nil
  | S n => (repeat 0 d ++ (-1 :: nil), 0) :: (repeat 0 d ++ (1 :: nil), 0) :: make_null_poly (S d) n
  end.

Fixpoint make_sched_poly (d : nat) (i : nat) (env_size : nat) (l : list (vector * Z)) :=
  (* add scheduling constraints in polyhedron after env, so that with fixed env, lexicographical ordering preserves semantics *)
  match l with
  | nil => make_null_poly (i + env_size)%nat (d - i)%nat
  | (v, c) :: l =>
    let vpref := resize env_size v in
    let vsuf := skipn env_size v in
    (vpref ++ repeat 0 i ++ (-1 :: repeat 0 (d - i - 1)%nat) ++ vsuf, -c)
      :: (mult_vector (-1) vpref ++ repeat 0 i ++ (1 :: repeat 0 (d - i - 1)%nat) ++ (mult_vector (-1) vsuf), c)
      :: make_sched_poly d (S i) env_size l
  end.

Lemma dot_product_split :
  forall l1 l2 l3 l4, length l1 = length l3 -> dot_product (l1 ++ l2) (l3 ++ l4) = dot_product l1 l3 + dot_product l2 l4.
Proof.
  induction l1.
  - intros l2 l3 l4 H. destruct l3; simpl in *; auto; lia.
  - intros l2 l3 l4 H. destruct l3; simpl in *; try lia. rewrite IHl1; lia.
Qed.

Lemma repeat_zero_is_null :
  forall n, is_null (repeat 0 n) = true.
Proof.
  induction n; auto.
Qed.

Lemma dot_product_repeat_zero_right :
  forall n l, dot_product l (repeat 0 n) = 0.
Proof.
  intros. apply dot_product_null_right. apply repeat_zero_is_null.
Qed.

Lemma dot_product_repeat_zero_left :
  forall n l, dot_product (repeat 0 n) l = 0.
Proof.
  intros. rewrite dot_product_commutative; apply dot_product_repeat_zero_right.
Qed.

Theorem make_null_poly_correct :
  forall n d p q r, length p = d -> length q = n -> in_poly (p ++ q ++ r) (make_null_poly d n) = is_null q.
Proof.
  induction n.
  - intros; destruct q; simpl in *; auto; lia.
  - intros d p q r Hlp Hlq.
    destruct q as [|x q]; simpl in *; [lia|].
    unfold satisfies_constraint; simpl.
    repeat (rewrite dot_product_split; [|rewrite repeat_length; lia]; simpl).
    repeat (rewrite dot_product_repeat_zero_right).
    repeat (rewrite dot_product_nil_right).
    assert (He : p ++ x :: q ++ r = (p ++ (x :: nil)) ++ q ++ r).
    { rewrite <- app_assoc; auto. }
    rewrite He. rewrite IHn; [|rewrite app_length; simpl; lia|lia].
    rewrite andb_assoc. f_equal.
    destruct (x =? 0) eqn:Hx.
    + rewrite andb_true_iff. repeat (rewrite Z.leb_le); rewrite Z.eqb_eq in Hx. lia.
    + rewrite andb_false_iff. repeat (rewrite Z.leb_gt); rewrite Z.eqb_neq in Hx. lia.
Qed.

Theorem mult_vector_length :
  forall k v, length (mult_vector k v) = length v.
Proof.
  intros. apply map_length.
Qed.

Theorem make_sched_poly_correct_aux :
  forall l i d es, (length l <= d - i)%nat ->
           forall p q r s, length p = es -> length q = i -> length r = (d - i)%nat ->
                    in_poly (p ++ q ++ r ++ s) (make_sched_poly d i es l) = is_eq r (matrix_product l (p ++ s)).
Proof.
  induction l.
  - intros. simpl in *. rewrite is_eq_nil_right. rewrite app_assoc. apply make_null_poly_correct; auto. rewrite app_length; lia.
  - intros i d es Hlength p q r s Hlp Hlq Hlr.
    simpl in *. destruct a as [v c]. simpl in *.
    destruct r as [|x r]; simpl in *; [lia|].
    unfold satisfies_constraint; simpl.
    repeat (rewrite dot_product_split; [|try rewrite repeat_length; try rewrite mult_vector_length; try rewrite resize_length; lia]; simpl).
    repeat (rewrite dot_product_mult_right).
    repeat (rewrite dot_product_repeat_zero_right).
    assert (He : p ++ q ++ x :: r ++ s = p ++ (q ++ (x :: nil)) ++ r ++ s).
    { rewrite <- app_assoc. auto. }
    rewrite He. rewrite IHl; [|lia|auto|rewrite app_length;simpl;lia|lia].
    rewrite andb_assoc. f_equal.
    assert (Hde : dot_product v (p ++ s) = dot_product p (resize es v) + dot_product s (skipn es v)).
    { rewrite <- dot_product_split by (rewrite resize_length; lia).
      rewrite dot_product_commutative. apply dot_product_eq_compat_right.
      rewrite is_eq_commutative. apply resize_skipn_eq.
    }
    destruct (x =? dot_product v (p ++ s) + c) eqn:Hx.
    + rewrite andb_true_iff. repeat (rewrite Z.leb_le); rewrite Z.eqb_eq in Hx. lia.
    + rewrite andb_false_iff. repeat (rewrite Z.leb_gt); rewrite Z.eqb_neq in Hx. lia.
Qed.


Theorem make_sched_poly_correct :
  forall l d es, (length l <= d)%nat ->
            forall p q r, length p = es -> length q = d ->
                    in_poly (p ++ q ++ r) (make_sched_poly d 0%nat es l) = is_eq q (matrix_product l (p ++ r)).
Proof.
  intros. apply make_sched_poly_correct_aux with (q := nil); auto; lia.
Qed.

Definition pi_elim_schedule (d : nat) (env_size : nat) (pi : Polyhedral_Instruction) :=
  {|
    pi_instr := pi.(pi_instr) ;
    pi_schedule := nil ;
    pi_transformation := map (insert_zeros_constraint d env_size) pi.(pi_transformation) ;
    pi_poly := make_sched_poly d 0%nat env_size pi.(pi_schedule) ++
               map (insert_zeros_constraint d env_size) pi.(pi_poly) ;
  |}.

Definition elim_schedule (d : nat) (env_size : nat) (p : Poly_Program) := map (pi_elim_schedule d env_size) p.

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

Lemma dot_product_split_left :
  forall l1 l2 l3, dot_product (l1 ++ l2) l3 = dot_product l1 (resize (length l1) l3) + dot_product l2 (skipn (length l1) l3).
Proof.
  intros.
  erewrite dot_product_eq_compat_right; [|rewrite is_eq_commutative; apply resize_skipn_eq].
  rewrite dot_product_split; [reflexivity|rewrite resize_length; auto].
Qed.

Lemma dot_product_split_right :
  forall l1 l2 l3, dot_product l1 (l2 ++ l3) = dot_product (resize (length l2) l1) l2 + dot_product (skipn (length l2) l1) l3.
Proof.
  intros. rewrite dot_product_commutative. rewrite dot_product_split_left.
  f_equal; apply dot_product_commutative.
Qed.

Lemma skipn_skipn :
  forall A n m (l : list A), skipn n (skipn m l) = skipn (n + m)%nat l.
Proof.
  induction m.
  - simpl. rewrite Nat.add_0_r; auto.
  - rewrite Nat.add_succ_r. destruct l; simpl.
    + destruct n; auto.
    + auto.
Qed.

Lemma split3_eq :
  forall i d l, is_eq l (resize i l ++ resize d (skipn i l) ++ skipn (d + i)%nat l) = true.
Proof.
  intros.
  erewrite is_eq_is_eq_left; [|rewrite is_eq_commutative; apply resize_skipn_eq].
  rewrite is_eq_add; [|reflexivity]. rewrite is_eq_reflexive; simpl.
  erewrite is_eq_is_eq_left; [|rewrite is_eq_commutative; apply resize_skipn_eq].
  rewrite is_eq_add; [|reflexivity]. rewrite is_eq_reflexive; simpl.
  rewrite skipn_skipn; apply is_eq_reflexive.
Qed.

Lemma insert_zeros_product_skipn :
  forall d i l1 l2, dot_product (insert_zeros d i l1) l2 = dot_product l1 (resize i l2 ++ skipn (d + i)%nat l2).
Proof.
  intros.
  unfold insert_zeros.
  repeat (rewrite dot_product_split_left); rewrite dot_product_split_right.
  repeat (rewrite resize_length). rewrite repeat_length.
  rewrite dot_product_repeat_zero_left.
  rewrite skipn_skipn. lia.
Qed.

Lemma matrix_product_skipn :
  forall d i m l, matrix_product (map (insert_zeros_constraint d i) m) l = matrix_product m (resize i l ++ skipn (d + i)%nat l).
Proof.
  intros. unfold matrix_product. rewrite map_map.
  apply map_ext. intros.
  unfold insert_zeros_constraint; simpl.
  rewrite insert_zeros_product_skipn. auto.
Qed.

Theorem poly_elim_schedule_semantics_preserve :
  forall d es env to_scan_lex prog_lex mem1 mem2,
    poly_lex_semantics to_scan_lex prog_lex mem1 mem2 ->
    forall to_scan prog,
      prog_lex = elim_schedule d es prog ->
      wf_scan to_scan -> wf_scan to_scan_lex ->
      (forall n pi, nth_error prog n = Some pi -> (length pi.(pi_schedule) <= d)%nat) ->
      (forall n p q ts pi, nth_error prog n = Some pi -> length p = es -> length ts = d ->
                      to_scan_lex n (p ++ ts ++ q) = is_eq ts (matrix_product pi.(pi_schedule) (p ++ q)) && to_scan n (p ++ q)) ->
      (forall n p q, length p = es -> to_scan n (p ++ q) = true -> is_eq p env = true) ->
      (forall n p, nth_error prog n = None -> to_scan n p = false) ->
      poly_semantics to_scan prog mem1 mem2.
Proof.
  intros d es env to_scan_lex prog mem1 mem2 Hsem.
  induction Hsem as [to_scan_l1 prog_l1 mem3 Hdone|to_scan_l1 prog_l1 mem3 mem4 mem5 pi n p Hscanp Heqpi Hts Hsem1 Hsem2 IH].
  - intros to_scan prog Hprogeq Hwf Hwflex Hsched_length Hcompat Hscanenv Hout.
    apply PolyDone. intros n p.
    destruct (nth_error prog n) as [pi|] eqn:Heq.
    + specialize (Hcompat n (resize es p) (skipn es p) (resize d (matrix_product pi.(pi_schedule) p)) pi).
      rewrite Hdone in Hcompat.
      erewrite matrix_product_eq in Hcompat; [|rewrite is_eq_commutative; apply resize_skipn_eq].
      rewrite resize_eq in Hcompat.
      * simpl in Hcompat. erewrite Hwf in Hcompat; [|apply resize_skipn_eq]. symmetry; apply Hcompat; auto.
      * unfold matrix_product. rewrite map_length. eauto.
    + auto.
  - intros to_scan prog Hprogeq Hwf Hwflex Hsched_length Hcompat Hscanenv Hout.
    assert (Hs : to_scan_l1 n (resize es p ++ resize d (skipn es p) ++ skipn (d + es)%nat p) = true).
    { unfold wf_scan in Hwflex; erewrite Hwflex; eauto. rewrite is_eq_commutative; apply split3_eq. }
    rewrite Hprogeq in *; unfold elim_schedule in Heqpi.
    destruct (nth_error prog n) as [pi1|] eqn:Hpi1; [| rewrite map_nth_error_none in Heqpi; congruence ].
    erewrite map_nth_error in Heqpi; eauto; inversion Heqpi as [Heqpi1].
    rewrite Hcompat with (pi := pi1) in Hs; auto.
    rewrite andb_true_iff in Hs; destruct Hs as [Heqp Hscan].
    eapply PolyProgress with (n := n) (p := resize es p ++ skipn (d + es)%nat p); eauto.
    + intros n2 p2 pi2 Heqpi2 Hcmp.
      specialize (Hts n2 (resize es p2 ++ (resize d (matrix_product pi2.(pi_schedule) p2)) ++ skipn es p2)).
      unfold wf_scan in Hwflex. rewrite Hcompat with (pi := pi2) in Hts; auto.
      erewrite matrix_product_eq with (l1 := resize es p2 ++ skipn es p2) in Hts; [|apply resize_skipn_eq].
      rewrite resize_eq in Hts by (unfold matrix_product; rewrite map_length; eauto). simpl in Hts.
      erewrite Hwf in Hts; [|apply resize_skipn_eq].
      destruct (to_scan n2 p2) eqn:Hscan2; auto.
      apply Hts.
      erewrite timestamp_compare_right_eq; [|apply split3_eq with (d := d) (i := es)].
      repeat (rewrite timestamp_compare_app by (repeat (rewrite resize_length); reflexivity)).
      erewrite timestamp_compare_right_eq; [|eapply Hscanenv; eauto].
      erewrite timestamp_compare_left_eq; [|eapply Hscanenv; eauto; erewrite Hwf; [|apply resize_skipn_eq]; eauto].
      rewrite timestamp_compare_reflexive; simpl.
      erewrite timestamp_compare_right_eq; [|apply Heqp].
      erewrite timestamp_compare_left_eq; [|apply resize_eq with (d := d); unfold matrix_product; rewrite map_length; eauto].
      rewrite Hcmp; auto.
    + rewrite <- Heqpi1 in Hsem1; unfold pi_elim_schedule in Hsem1; simpl in *.
      rewrite matrix_product_skipn in Hsem1. apply Hsem1.
    + apply IH; auto.
      * apply scanned_wf_compat; auto.
      * apply scanned_wf_compat; auto.
      * intros n0 p0 q0 ts pi0 Hpi0 Hlp0 Hlts.
        unfold scanned. rewrite Hcompat with (pi := pi0); auto.
        destruct (is_eq ts (matrix_product (pi_schedule pi0) (p0 ++ q0))) eqn:Htseq; auto.
        simpl.
        f_equal; f_equal.
        destruct (n =? n0)%nat eqn:Heqn; [|repeat (rewrite andb_false_r); auto]. repeat (rewrite andb_true_r).
        erewrite is_eq_is_eq_left; [|apply split3_eq with (d := d) (i := es)].
        repeat (rewrite is_eq_add; [|rewrite resize_length; auto]).
        destruct (is_eq (resize es p) p0) eqn:Heqp0; simpl; auto.
        destruct (is_eq (skipn (d + es)%nat p) q0) eqn:Heqq0; simpl; auto using andb_false_r.
        rewrite andb_true_r.
        rewrite Nat.eqb_eq in Heqn. rewrite Heqn in *. assert (Heqpi0 : pi0 = pi1) by congruence. rewrite Heqpi0 in *.
        rewrite matrix_product_eq with (l2 := p0 ++ q0) in Heqp;
        [| rewrite is_eq_add by (rewrite resize_length; auto); rewrite Heqp0; rewrite Heqq0; auto ].
        erewrite is_eq_is_eq_right; eauto.
      * intros n0 p0 q0 H. unfold scanned. rewrite andb_true_iff. intros [H1 H2]. eapply Hscanenv; eauto.
      * intros n0 p0 H. unfold scanned. rewrite Hout; auto.
Qed.

Definition env_scan (prog : Poly_Program) (env : vector) (n : nat) (p : vector) :=
  match nth_error prog n with
  | Some pi => is_eq env (resize (length env) p) && in_poly p pi.(pi_poly)
  | None => false
  end.

Definition env_poly_semantics (env : vector) (prog : Poly_Program) (mem1 mem2 : mem) :=
  poly_semantics (env_scan prog env) prog mem1 mem2.

Definition env_poly_lex_semantics (env : vector) (prog : Poly_Program) (mem1 mem2 : mem) :=
  poly_lex_semantics (env_scan prog env) prog mem1 mem2.

Lemma resize_app :
  forall n p q, length p = n -> resize n (p ++ q) = p.
Proof.
  induction n.
  - intros; destruct p; simpl in *; auto; lia.
  - intros p q Hlength; destruct p; simpl in *.
    + lia.
    + rewrite IHn; auto.
Qed.

Lemma skipn_app :
  forall A n (p q : list A), length p = n -> skipn n (p ++ q) = q.
Proof.
  induction n.
  - intros; destruct p; simpl in *; auto; lia.
  - intros; destruct p; simpl in *; auto; lia.
Qed.

Lemma in_poly_app :
  forall p pol1 pol2, in_poly p (pol1 ++ pol2) = in_poly p pol1 && in_poly p pol2.
Proof.
  intros. unfold in_poly. apply forallb_app.
Qed.

Lemma forallb_map :
  forall A B f (g : A -> B) l, forallb f (map g l) = forallb (fun x => f (g x)) l.
Proof.
  intros. induction l; simpl; auto; congruence.
Qed.

Lemma forallb_ext :
  forall A f g (l : list A), (forall x, f x = g x) -> forallb f l = forallb g l.
Proof.
  intros. induction l; simpl; auto; congruence.
Qed.

Lemma in_poly_is_eq_compat :
  forall p1 p2 pol, is_eq p1 p2 = true -> in_poly p1 pol = in_poly p2 pol.
Proof.
  intros p1 p2 pol Heq.
  unfold in_poly. apply forallb_ext.
  intros c. unfold satisfies_constraint. f_equal. apply dot_product_eq_compat_left; auto.
Qed.

Lemma resize_null_repeat :
  forall n l, is_null l = true -> resize n l = repeat 0 n.
Proof.
  induction n.
  - intros; simpl; auto.
  - intros l H; destruct l; simpl in *.
    + rewrite IHn; auto.
    + rewrite andb_true_iff in H; rewrite Z.eqb_eq in H; destruct H.
      rewrite IHn; auto; congruence.
Qed.

Lemma resize_eq_compat :
  forall n l1 l2, is_eq l1 l2 = true -> resize n l1 = resize n l2.
Proof.
  induction n.
  - intros; simpl; auto.
  - intros l1 l2 H.
    destruct l1; destruct l2; simpl in *; try (rewrite andb_true_iff in H; destruct H as [H1 H2]; rewrite Z.eqb_eq in H1); auto;
      f_equal; auto; apply IHn; try rewrite is_eq_nil_left; try rewrite is_eq_nil_right; auto.
Qed.

Lemma env_scan_wf :
  forall prog env, wf_scan (env_scan prog env).
Proof.
  intros prog env n p1 p2 Heq. unfold env_scan.
  destruct (nth_error prog n) as [pi|]; simpl; auto.
  f_equal.
  - f_equal. apply resize_eq_compat. auto.
  - apply in_poly_is_eq_compat; auto.
Qed.

Theorem poly_elim_schedule_semantics_env_preserve :
  forall d es env prog mem1 mem2,
    es = length env ->
    env_poly_lex_semantics env (elim_schedule d es prog) mem1 mem2 ->
    (forall n pi, nth_error prog n = Some pi -> (length pi.(pi_schedule) <= d)%nat) ->
    env_poly_semantics env prog mem1 mem2.
Proof.
  intros d es env prog mem1 mem2 Hlength Hsem Hsched_length.
  unfold env_poly_semantics. unfold env_poly_lex_semantics in Hsem.
  eapply poly_elim_schedule_semantics_preserve.
  - exact Hsem.
  - reflexivity.
  - apply env_scan_wf.
  - apply env_scan_wf.
  - exact Hsched_length.
  - intros n p q ts pi Heqpi Hlp Hlts.
    unfold env_scan. unfold elim_schedule. rewrite map_nth_error with (d := pi); auto. rewrite Heqpi.
    rewrite <- Hlength. unfold pi_elim_schedule; simpl.
    repeat (rewrite resize_app by apply Hlp).
    destruct (is_eq env p); simpl; auto using andb_false_r.
    rewrite in_poly_app. f_equal.
    + apply make_sched_poly_correct; eauto.
    + unfold in_poly. rewrite forallb_map. apply forallb_ext.
      intros c. unfold satisfies_constraint. unfold insert_zeros_constraint. simpl.
      f_equal. rewrite dot_product_commutative. rewrite insert_zeros_product_skipn.
      rewrite resize_app by apply Hlp.
      rewrite app_assoc. rewrite skipn_app; [|rewrite app_length; lia].
      apply dot_product_commutative.
  - intros n p q Hlp Hscan. unfold env_scan in Hscan.
    destruct (nth_error prog n) as [pi|]; [|congruence].
    rewrite andb_true_iff in Hscan; destruct Hscan as [He Hp].
    rewrite resize_app in He by congruence. rewrite is_eq_commutative. exact He.
  - intros n p Hout. unfold env_scan. rewrite Hout. auto.
Qed.
