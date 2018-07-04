Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Psatz.
Require Import Setoid.
Open Scope Z_scope.
Open Scope list_scope.

Require Import Linalg.
Require Import Instr.
Require Import Misc.
Require Import Setoid Morphisms.

(** * The semantics of polyhedral programs with schedules *)

Record Polyhedral_Instruction := {
  pi_instr : instr ;
  pi_poly : polyhedron ;
  pi_schedule : list (list Z * Z)%type ;
  pi_transformation : list (list Z * Z)%type ;
}.

Definition Poly_Program := list Polyhedral_Instruction.

Definition scanned to_scan n p m q := to_scan m q && negb (is_eq p q && (n =? m)%nat).
Hint Unfold scanned.

Instance scanned_proper : Proper ((eq ==> veq ==> eq) ==> eq ==> veq ==> (eq ==> veq ==> eq)) scanned.
Proof.
  intros to_scan1 to_scan2 Hto_scan n1 n2 Hn p1 p2 Hp m1 m2 Hm q1 q2 Hq.
  unfold scanned.
  erewrite Hto_scan by (exact Hm || exact Hq).
  rewrite Hn. rewrite Hm. rewrite Hp. rewrite Hq.
  reflexivity.
Qed.

(* Definition wf_scan (to_scan : nat -> vector -> bool) := Proper (eq ==> veq ==> eq) to_scan.
Transparent wf_scan.
Hint Unfold wf_scan. *)
Notation "'wf_scan'" := (Proper (eq ==> veq ==> eq)) (only parsing).
(* forall n p q, is_eq p q = true -> to_scan n p = to_scan n q. *)

Inductive poly_semantics : (nat -> list Z -> bool) -> Poly_Program -> mem -> mem -> Prop :=
| PolyDone : forall to_scan prog mem, (forall n p, to_scan n p = false) -> poly_semantics to_scan prog mem mem
| PolyProgress : forall to_scan prog mem1 mem2 mem3 poly_instr n p,
    to_scan n p = true -> nth_error prog n = Some poly_instr ->
    (forall n2 p2 poly_instr2, nth_error prog n2 = Some poly_instr2 ->
                          lex_compare (affine_product poly_instr2.(pi_schedule) p2) (affine_product poly_instr.(pi_schedule) p) = Lt ->
                          to_scan n2 p2 = false) ->
    instr_semantics poly_instr.(pi_instr) (affine_product poly_instr.(pi_transformation) p) mem1 mem2 ->
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

Lemma scanned_wf_compat :
  forall to_scan n p, wf_scan to_scan -> wf_scan (scanned to_scan n p).
Proof.
  intros to_scan n p Hwf. apply scanned_proper; [exact Hwf | reflexivity | reflexivity].
(*  intros to_scan n p Hwf m q r Heq.
  autounfold. rewrite (Hwf m q r); auto. f_equal; f_equal; f_equal. apply is_eq_is_eq_right; auto. *)
Qed.

Theorem poly_semantics_concat :
  forall to_scan1 prog mem1 mem2,
    poly_semantics to_scan1 prog mem1 mem2 ->
    forall to_scan2 mem3,
    wf_scan to_scan1 ->
    (forall n p, to_scan1 n p = false \/ to_scan2 n p = false) ->
    (forall n1 p1 pi1 n2 p2 pi2, nth_error prog n1 = Some pi1 -> nth_error prog n2 = Some pi2 ->
                           lex_compare (affine_product pi2.(pi_schedule) p2) (affine_product pi1.(pi_schedule) p1) = Lt ->
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
      reflect; split.
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
           reflect. destruct Hd as [Heqp Hn]. rewrite Heqp, Hn in Hscanp. congruence.
Qed.

(** * The semantics of polyhedral programs with lexicographical ordering *)

Inductive poly_lex_semantics : (nat -> list Z -> bool) -> Poly_Program -> mem -> mem -> Prop :=
| PolyLexDone : forall to_scan prog mem, (forall n p, to_scan n p = false) -> poly_lex_semantics to_scan prog mem mem
| PolyLexProgress : forall to_scan prog mem1 mem2 mem3 poly_instr n p,
    to_scan n p = true -> nth_error prog n = Some poly_instr ->
    (forall n2 p2, lex_compare p2 p = Lt -> to_scan n2 p2 = false) ->
    instr_semantics poly_instr.(pi_instr) (affine_product poly_instr.(pi_transformation) p) mem1 mem2 ->
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

Lemma poly_lex_semantics_pis_ext_single :
  forall pis1 pis2 to_scan mem1 mem2,
    Forall2 (fun pi1 pi2 => pi1.(pi_instr) = pi2.(pi_instr) /\ pi1.(pi_transformation) = pi2.(pi_transformation)) pis1 pis2 ->
    poly_lex_semantics to_scan pis1 mem1 mem2 -> poly_lex_semantics to_scan pis2 mem1 mem2.
Proof.
  intros pis1 pis2 to_scan mem1 mem2 Hsame Hsem.
  induction Hsem as [to_scan1 prog mem Hdone|to_scan1 prog mem1 mem2 mem3 pi n p Hscanp Heqpi Hts Hsem1 Hsem2 IH].
  - apply PolyLexDone; auto.
  - destruct (Forall2_nth_error _ _ _ _ _ _ _ Hsame Heqpi) as [pi2 [Hpi2 [H1 H2]]].
    eapply PolyLexProgress; [exact Hscanp|exact Hpi2|exact Hts| |apply IH; auto].
    rewrite H1, H2 in *; auto.
Qed.

Lemma poly_lex_semantics_pis_ext_iff :
  forall pis1 pis2 to_scan mem1 mem2,
    Forall2 (fun pi1 pi2 => pi1.(pi_instr) = pi2.(pi_instr) /\ pi1.(pi_transformation) = pi2.(pi_transformation)) pis1 pis2 ->
    poly_lex_semantics to_scan pis1 mem1 mem2 <-> poly_lex_semantics to_scan pis2 mem1 mem2.
Proof.
  intros pis1 pis2 to_scan mem1 mem2 Hsame.
  split.
  - apply poly_lex_semantics_pis_ext_single; auto.
  - apply poly_lex_semantics_pis_ext_single.
    eapply Forall2_imp; [|apply Forall2_sym; exact Hsame].
    intros x y H; simpl in *; destruct H; auto.
Qed.

Lemma poly_lex_semantics_ext_iff :
  forall pis to_scan1 to_scan2 mem1 mem2,
    (forall n p, to_scan1 n p = to_scan2 n p) ->
    poly_lex_semantics to_scan1 pis mem1 mem2 <-> poly_lex_semantics to_scan2 pis mem1 mem2.
Proof.
  intros pis to_scan1 to_scan2 mem1 mem2 Hsame.
  split; intros H.
  - eapply poly_lex_semantics_extensionality; [exact H|]. auto.
  - eapply poly_lex_semantics_extensionality; [exact H|]. auto.
Qed.

Theorem poly_lex_concat :
  forall to_scan1 prog mem1 mem2,
    poly_lex_semantics to_scan1 prog mem1 mem2 ->
    forall to_scan2 mem3,
    wf_scan to_scan1 ->
    (forall n p, to_scan1 n p = false \/ to_scan2 n p = false) ->
    (forall n1 p1 n2 p2, lex_compare p2 p1 = Lt -> to_scan1 n1 p1 = false \/ to_scan2 n2 p2 = false) ->
    poly_lex_semantics to_scan2 prog mem2 mem3 ->
    poly_lex_semantics (fun n p => to_scan1 n p || to_scan2 n p) prog mem1 mem3.
Proof.
  intros to_scan1 prog mem1 mem2 Hsem.
  induction Hsem as [to_scan3 prog1 mem4 Hdone|to_scan3 prog1 mem4 mem5 mem6 pi n p Hscanp Heqpi Hts Hsem1 Hsem2 IH].
  - intros to_scan2 mem3 Hwf1 Hdisj Hcmp Hsem1. eapply poly_lex_semantics_extensionality; eauto. intros. rewrite Hdone. auto.
  - intros to_scan2 mem3 Hwf1 Hdisj Hcmp Hsem3. eapply PolyLexProgress with (n := n) (p := p); eauto.
    + rewrite Hscanp. auto.
    + intros n2 p2 Hts2.
      reflect. split.
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
           reflect. destruct Hd as [Heqp Hn]. rewrite Heqp, Hn in Hscanp. congruence.
Qed.

Theorem poly_lex_concat_seq :
  forall A to_scans (l : list A) prog mem1 mem2,
    iter_semantics (fun x => poly_lex_semantics (to_scans x) prog) l mem1 mem2 ->
    (forall x, wf_scan (to_scans x)) ->
    (forall x1 k1 x2 k2 n p, to_scans x1 n p = true -> to_scans x2 n p = true -> nth_error l k1 = Some x1 -> nth_error l k2 = Some x2 -> k1 = k2) ->
    (forall x1 n1 p1 k1 x2 n2 p2 k2, lex_compare p2 p1 = Lt -> to_scans x1 n1 p1 = true -> to_scans x2 n2 p2 = true -> nth_error l k1 = Some x1 -> nth_error l k2 = Some x2 -> (k2 <= k1)%nat) ->
    poly_lex_semantics (fun n p => existsb (fun x => to_scans x n p) l) prog mem1 mem2.
Proof.
  intros A to_scans l1 prog mem1 mem3 Hsem.
  induction Hsem as [mem|x l mem1 mem2 mem3 Hsem1 Hsem2 IH].
  - intros Hwf Hscans Hcmp.
    simpl.
    apply PolyLexDone; auto.
  - intros Hwf Hscans Hcmp.
    eapply poly_lex_semantics_extensionality.
    + eapply poly_lex_concat; [exact Hsem1| | | |apply IH; auto].
      * apply Hwf.
      * intros n p. simpl.
        destruct (to_scans x n p) eqn:Hscanl; [|auto]. right.
        apply not_true_is_false; rewrite existsb_exists; intros [x1 [Hin Hscanx1]].
        apply In_nth_error in Hin; destruct Hin as [u Hu].
        specialize (Hscans x O x1 (S u) n p Hscanl Hscanx1).
        simpl in Hscans. intuition congruence.
      * intros n1 p1 n2 p2 H.
        destruct (to_scans x n1 p1) eqn:Hscanl; [|auto]. right.
        apply not_true_is_false; rewrite existsb_exists; intros [x1 [Hin Hscanx1]].
        apply In_nth_error in Hin; destruct Hin as [u Hu].
        specialize (Hcmp x n1 p1 O x1 n2 p2 (S u) H Hscanl Hscanx1).
        intuition lia.
      * intros x1 k1 x2 k2 n p H1 H2 H3 H4; specialize (Hscans x1 (S k1) x2 (S k2) n p).
        intuition congruence.
      * intros x1 n1 p1 k1 x2 n2 p2 k2 H1 H2 H3 H4 H5; specialize (Hcmp x1 n1 p1 (S k1) x2 n2 p2 (S k2)).
        intuition lia.
    + intros n p. simpl. reflexivity.
Qed.

(** * Translating a program from explicit scheduling to lexicographical scanning *)

Definition insert_zeros (d : nat) (i : nat) (l : list Z) := resize i l ++ repeat 0 d ++ skipn i l.
Definition insert_zeros_constraint (d : nat) (i : nat) (c : list Z * Z) := (insert_zeros d i (fst c), snd c).

(** [make_null_poly d n] creates a polyhedron with the constraints that the variables from [d] to [d+n-1] are null *)
Fixpoint make_null_poly (d : nat) (n : nat) :=
  match n with
  | O => nil
  | S n => (repeat 0 d ++ (-1 :: nil), 0) :: (repeat 0 d ++ (1 :: nil), 0) :: make_null_poly (S d) n
  end.

(** [make_sched_poly d i env_size l] adds the lexicographical constraints in [l] as equalities, preserving the [env_size] first variables,
    and inserting [d] variables after that. *)
Fixpoint make_sched_poly (d : nat) (i : nat) (env_size : nat) (l : list (list Z * Z)) :=
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

Theorem make_null_poly_correct :
  forall n d p q r, length p = d -> length q = n -> in_poly (p ++ q ++ r) (make_null_poly d n) = is_null q.
Proof.
  induction n.
  - intros; destruct q; simpl in *; auto; lia.
  - intros d p q r Hlp Hlq.
    destruct q as [|x q]; simpl in *; [lia|].
    unfold satisfies_constraint; simpl.
    repeat (rewrite dot_product_app; [|rewrite repeat_length; lia]; simpl).
    autorewrite with vector.
    assert (He : p ++ x :: q ++ r = (p ++ (x :: nil)) ++ q ++ r).
    { rewrite <- app_assoc; auto. }
    rewrite He. rewrite IHn; [|rewrite app_length; simpl; lia|lia].
    rewrite andb_assoc. f_equal.
    destruct (x =? 0) eqn:Hx; reflect; lia.
Qed.

Theorem make_sched_poly_correct_aux :
  forall l i d es, (length l <= d - i)%nat ->
           forall p q r s, length p = es -> length q = i -> length r = (d - i)%nat ->
                    in_poly (p ++ q ++ r ++ s) (make_sched_poly d i es l) = is_eq r (affine_product l (p ++ s)).
Proof.
  induction l.
  - intros. simpl in *. rewrite is_eq_nil_right. rewrite app_assoc. apply make_null_poly_correct; auto. rewrite app_length; lia.
  - intros i d es Hlength p q r s Hlp Hlq Hlr.
    simpl in *. destruct a as [v c]. simpl in *.
    destruct r as [|x r]; simpl in *; [lia|].
    unfold satisfies_constraint; simpl.
    repeat (rewrite dot_product_app; [|rewrite ?repeat_length, ?mult_vector_length, ?resize_length; lia]; simpl).
    autorewrite with vector.
    assert (He : p ++ q ++ x :: r ++ s = p ++ (q ++ (x :: nil)) ++ r ++ s).
    { rewrite <- app_assoc. auto. }
    rewrite He. rewrite IHl; [|lia|auto|rewrite app_length;simpl;lia|lia].
    rewrite andb_assoc. f_equal.
    assert (Hde : dot_product v (p ++ s) = dot_product p (resize es v) + dot_product s (skipn es v)).
    { rewrite <- dot_product_app by (rewrite resize_length; lia).
      rewrite dot_product_commutative. rewrite resize_skipn_eq. reflexivity.
    }
    destruct (x =? dot_product v (p ++ s) + c) eqn:Hx; reflect; lia.
Qed.

Theorem make_sched_poly_correct :
  forall l d es, (length l <= d)%nat ->
            forall p q r, length p = es -> length q = d ->
                    in_poly (p ++ q ++ r) (make_sched_poly d 0%nat es l) = is_eq q (affine_product l (p ++ r)).
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

Lemma split3_eq :
  forall i d l, resize i l ++ resize d (skipn i l) ++ skipn (d + i)%nat l =v= l.
Proof.
  intros.
  rewrite <- is_eq_veq.
  rewrite is_eq_app_left. autorewrite with vector. rewrite is_eq_reflexive. simpl.
  rewrite is_eq_app_left. autorewrite with vector. rewrite is_eq_reflexive. simpl.
  rewrite skipn_skipn. apply is_eq_reflexive.
Qed.

Lemma insert_zeros_product_skipn :
  forall d i l1 l2, dot_product (insert_zeros d i l1) l2 = dot_product l1 (resize i l2 ++ skipn (d + i)%nat l2).
Proof.
  intros.
  unfold insert_zeros.
  rewrite !dot_product_app_left, dot_product_app_right.
  autorewrite with vector. rewrite repeat_length.
  rewrite skipn_skipn. lia.
Qed.

Lemma affine_product_skipn :
  forall d i m l, affine_product (map (insert_zeros_constraint d i) m) l = affine_product m (resize i l ++ skipn (d + i)%nat l).
Proof.
  intros. unfold affine_product. rewrite map_map.
  apply map_ext. intros.
  unfold insert_zeros_constraint; simpl.
  rewrite insert_zeros_product_skipn. auto.
Qed.

(** * Schedule elimination is correct *)

Theorem poly_elim_schedule_semantics_preserve :
  forall d es env to_scan_lex prog_lex mem1 mem2,
    poly_lex_semantics to_scan_lex prog_lex mem1 mem2 ->
    forall to_scan prog,
      prog_lex = elim_schedule d es prog ->
      wf_scan to_scan -> wf_scan to_scan_lex ->
      (forall n pi, nth_error prog n = Some pi -> (length pi.(pi_schedule) <= d)%nat) ->
      (forall n p q ts pi, nth_error prog n = Some pi -> length p = es -> length ts = d ->
                      to_scan_lex n (p ++ ts ++ q) = is_eq ts (affine_product pi.(pi_schedule) (p ++ q)) && to_scan n (p ++ q)) ->
      (forall n p q, length p = es -> to_scan n (p ++ q) = true -> p =v= env) ->
      (forall n p, nth_error prog n = None -> to_scan n p = false) ->
      poly_semantics to_scan prog mem1 mem2.
Proof.
  intros d es env to_scan_lex prog mem1 mem2 Hsem.
  induction Hsem as [to_scan_l1 prog_l1 mem3 Hdone|to_scan_l1 prog_l1 mem3 mem4 mem5 pi n p Hscanp Heqpi Hts Hsem1 Hsem2 IH].
  - intros to_scan prog Hprogeq Hwf Hwflex Hsched_length Hcompat Hscanenv Hout.
    apply PolyDone. intros n p.
    destruct (nth_error prog n) as [pi|] eqn:Heq.
    + specialize (Hcompat n (resize es p) (skipn es p) (resize d (affine_product pi.(pi_schedule) p)) pi).
      rewrite Hdone in Hcompat.
      rewrite resize_skipn_eq in Hcompat. rewrite resize_eq in Hcompat.
      * simpl in Hcompat. symmetry; apply Hcompat; auto.
      * unfold affine_product. rewrite map_length. eauto.
    + auto.
  - intros to_scan prog Hprogeq Hwf Hwflex Hsched_length Hcompat Hscanenv Hout.
    rewrite <- split3_eq with (d := d) (i := es) in Hscanp.
    rewrite Hprogeq in *; unfold elim_schedule in Heqpi.
    destruct (nth_error prog n) as [pi1|] eqn:Hpi1; [| rewrite map_nth_error_none in Heqpi; congruence ].
    erewrite map_nth_error in Heqpi; eauto; inversion Heqpi as [Heqpi1].
    rewrite Hcompat with (pi := pi1) in Hscanp; auto.
    reflect; destruct Hscanp as [Heqp Hscan].
    eapply PolyProgress with (n := n) (p := resize es p ++ skipn (d + es)%nat p); eauto.
    + intros n2 p2 pi2 Heqpi2 Hcmp.
      specialize (Hts n2 (resize es p2 ++ (resize d (affine_product pi2.(pi_schedule) p2)) ++ skipn es p2)).
      rewrite Hcompat with (pi := pi2) in Hts; auto.
      rewrite resize_skipn_eq in Hts.
      rewrite resize_eq in Hts by (unfold affine_product; rewrite map_length; eauto). simpl in Hts.
      destruct (to_scan n2 p2) eqn:Hscan2; auto. apply Hts.
      rewrite <- split3_eq with (l := p) (d := d) (i := es).
      rewrite !lex_compare_app by (rewrite !resize_length; reflexivity).
      rewrite Hscanenv with (p := resize es p2) by (apply resize_length || rewrite resize_skipn_eq; apply Hscan2).
      rewrite Hscanenv with (p := resize es p) by (apply resize_length || apply Hscan).
      rewrite lex_compare_reflexive. simpl.
      rewrite Heqp. rewrite resize_eq by (unfold affine_product; rewrite map_length; eauto).
      rewrite Hcmp. reflexivity.
    + rewrite <- Heqpi1 in Hsem1; unfold pi_elim_schedule in Hsem1; simpl in *.
      rewrite affine_product_skipn in Hsem1. apply Hsem1.
    + apply IH; auto.
      * apply scanned_wf_compat; auto.
      * apply scanned_wf_compat; auto.
      * intros n0 p0 q0 ts pi0 Hpi0 Hlp0 Hlts.
        unfold scanned. rewrite Hcompat with (pi := pi0); auto.
        destruct (is_eq ts (affine_product (pi_schedule pi0) (p0 ++ q0))) eqn:Htseq; auto.
        simpl.
        f_equal; f_equal.
        destruct (n =? n0)%nat eqn:Heqn; [|rewrite !andb_false_r; auto]. rewrite !andb_true_r.
        rewrite <- split3_eq with (l := p) (d := d) (i := es) at 1.
        rewrite !is_eq_app by (rewrite resize_length; auto).
        destruct (is_eq (resize es p) p0) eqn:Heqp0; simpl; auto.
        destruct (is_eq (skipn (d + es)%nat p) q0) eqn:Heqq0; simpl; auto using andb_false_r.
        rewrite andb_true_r.
        reflect. rewrite Heqn in *.
        assert (Heqpi0 : pi0 = pi1) by congruence. rewrite Heqpi0 in *.
        rewrite Heqp. rewrite Htseq. f_equal.
        assert (H : p0 ++ q0 =v= resize es p ++ skipn (d + es) p); [|rewrite H; reflexivity].
        rewrite <- is_eq_veq. rewrite is_eq_app by (rewrite resize_length; auto).
        reflect; split; symmetry; assumption.
      * intros n0 p0 q0 H. unfold scanned. reflect. intros [H1 H2]. eapply Hscanenv; eauto.
      * intros n0 p0 H. unfold scanned. rewrite Hout; auto.
Qed.

(** * Semantics in a fixed environment *)

Definition env_scan (prog : Poly_Program) (env : list Z) (dim : nat) (n : nat) (p : list Z) :=
  match nth_error prog n with
  | Some pi => is_eq env (resize (length env) p) && is_eq p (resize dim p) && in_poly p pi.(pi_poly)
  | None => false
  end.

Definition env_poly_semantics (env : list Z) (dim : nat) (prog : Poly_Program) (mem1 mem2 : mem) :=
  poly_semantics (env_scan prog env dim) prog mem1 mem2.

Definition env_poly_lex_semantics (env : list Z) (dim : nat) (prog : Poly_Program) (mem1 mem2 : mem) :=
  poly_lex_semantics (env_scan prog env dim) prog mem1 mem2.

Instance env_scan_proper : forall prog env dim, Proper (eq ==> veq ==> eq) (env_scan prog env dim).
Proof.
  intros prog env dim n1 n2 Hn p1 p2 Hp. rewrite Hn. unfold env_scan.
  destruct (nth_error prog n2) as [pi|]; simpl; auto.
  rewrite Hp at 1 2 4; rewrite Hp at 1. reflexivity.
Qed.

(** * Schedule elimination in a fixed environment is correct as well *)

Theorem poly_elim_schedule_semantics_env_preserve :
  forall d es env dim prog mem1 mem2,
    es = length env ->
    (es <= dim)%nat ->
    env_poly_lex_semantics env (dim + d) (elim_schedule d es prog) mem1 mem2 ->
    (forall n pi, nth_error prog n = Some pi -> (length pi.(pi_schedule) <= d)%nat) ->
    env_poly_semantics env dim prog mem1 mem2.
Proof.
  intros d es env dim prog mem1 mem2 Hlength Hdim Hsem Hsched_length.
  unfold env_poly_semantics. unfold env_poly_lex_semantics in Hsem.
  eapply poly_elim_schedule_semantics_preserve.
  - exact Hsem.
  - reflexivity.
  - apply env_scan_proper.
  - apply env_scan_proper.
  - exact Hsched_length.
  - intros n p q ts pi Heqpi Hlp Hlts.
    unfold env_scan. unfold elim_schedule. rewrite map_nth_error with (d := pi); auto. rewrite Heqpi.
    rewrite <- Hlength. unfold pi_elim_schedule; simpl.
    rewrite !resize_app with (n := es) by apply Hlp.
    destruct (is_eq env p); simpl; auto using andb_false_r.
    rewrite in_poly_app. rewrite andb_comm. rewrite <- andb_assoc. f_equal.
    + apply make_sched_poly_correct; eauto.
    + rewrite andb_comm. f_equal.
      * rewrite !resize_app_le by lia.
        rewrite !is_eq_app by lia. rewrite !is_eq_reflexive. simpl.
        f_equal. f_equal. lia.
      * unfold in_poly. rewrite forallb_map. apply forallb_ext.
        intros c. unfold satisfies_constraint. unfold insert_zeros_constraint. simpl.
        f_equal. rewrite dot_product_commutative. rewrite insert_zeros_product_skipn.
        rewrite resize_app by apply Hlp.
        rewrite app_assoc. rewrite skipn_app; [|rewrite app_length; lia].
        apply dot_product_commutative.
  - intros n p q Hlp Hscan. unfold env_scan in Hscan.
    destruct (nth_error prog n) as [pi|]; [|congruence].
    reflect. destruct Hscan as [[He Hr] Hp].
    rewrite resize_app in He by congruence. symmetry. exact He.
  - intros n p Hout. unfold env_scan. rewrite Hout. auto.
Qed.

(** * Sequence concatenation is correct as well *)
(*
Theorem poly_lex_env_concat_seq :
  forall env dim lb ub prog mem1 mem2,
    iter_semantics (fun x => env_poly_lex_semantics dim (rev (x :: env)) prog) lb ub mem1 mem2 ->
    (forall x n p, env_scan prog (rev (x :: env)) dim n p = true -> lb <= x < ub) ->
    (forall x, wf_scan (to_scans x)) ->
    (forall x1 x2 n p, to_scans x1 n p = true -> to_scans x2 n p = true -> x1 = x2) ->
    (forall x1 n1 p1 x2 n2 p2, lex_compare p2 p1 = Lt -> to_scans x1 n1 p1 = true -> to_scans x2 n2 p2 = true -> x2 <= x1) ->
    poly_lex_semantics (fun n p => existsb (fun x => to_scans x n p) (Zrange lb ub)) prog mem1 mem2.
Proof.
  intros to_scans lb ub prog mem1 mem2 Hsem.
  induction Hsem as [lb ub mem Hempty|lb ub mem1 mem2 mem3 Hcontinue Hsem1 Hsem2 IH].
  - intros Hwf Hscans Hcmp.
    rewrite Zrange_empty by lia. simpl.
    apply PolyLexDone; auto.
  - intros Hwf Hscans Hcmp.
    eapply poly_lex_semantics_extensionality.
    + eapply poly_lex_concat; [exact Hsem1| | | |apply IH; auto].
      * apply Hwf.
      * intros n p. simpl.
        destruct (to_scans lb n p) eqn:Hscanl; [|auto]. right.
        apply not_true_is_false; rewrite existsb_exists; intros [x [Hin Hscanx]].
        rewrite Zrange_in in Hin. specialize (Hscans lb x n p Hscanl Hscanx). lia.
      * intros n1 p1 n2 p2 H.
        destruct (to_scans lb n1 p1) eqn:Hscanl; [|auto]. right.
        apply not_true_is_false; rewrite existsb_exists; intros [x [Hin Hscanx]].
        rewrite Zrange_in in Hin. specialize (Hcmp lb n1 p1 x n2 p2 H Hscanl Hscanx). lia.
    + intros n p. simpl. rewrite Zrange_begin with (lb := lb) by lia.
      simpl. reflexivity.
Qed.
*)