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
Require Import Bool.
Require Import Psatz.
Require Import Setoid Morphisms.
Require Import Permutation.

Require Import Linalg.
Require Import Loop.
Require Import PolyLoop.
Require Import Misc.
Require Import Semantics.
Require Import Instr.
Require Import VplInterface.
Require Import Result.
Require Import Heuristics.

Require Import Vpl.Impure.
Require Import ImpureAlarmConfig.

Open Scope Z_scope.
Open Scope list_scope.

(** * Creating expressions that evaluate to a given linear function *)

Fixpoint make_linear_expr (n : nat) (l : list Z) :=
  match n, l with
  | O, _ | _, nil => Constant 0
  | S n, x :: l => make_sum (make_mult x (Var n)) (make_linear_expr n l)
  end.

Theorem make_linear_expr_correct_aux :
  forall n l env, (length env >= n)%nat -> eval_expr env (make_linear_expr n l) = dot_product l (rev (firstn n env)).
Proof.
  induction n.
  - intros l env Hel. destruct env; destruct l; simpl in *; auto; lia.
  - intros l env Hel.
    destruct l as [|x l]; simpl in Hel; destruct (rev (firstn (S n) env)) as [|y ev] eqn:Hrev; auto; simpl; auto.
    + destruct env as [|e env]; simpl in *; [lia | destruct (rev (firstn n env)); simpl in *; congruence].
    + rewrite firstn_nth_app with (d := 0) in Hrev by auto. rewrite rev_unit in Hrev.
      injection Hrev as Hnth Hrev. rewrite make_sum_correct, make_mult_correct, IHn by lia; simpl. congruence.
Qed.

Theorem make_linear_expr_correct :
  forall n l env, length env = n -> eval_expr env (make_linear_expr n l) = dot_product l (rev env).
Proof.
  intros. rewrite make_linear_expr_correct_aux by lia. f_equal. f_equal. apply firstn_all2. lia.
Qed.

Definition make_affine_expr (n : nat) (e : (list Z * Z)%type) := make_sum (make_linear_expr n (fst e)) (Constant (snd e)).

Theorem make_affine_expr_correct :
  forall n e env, length env = n -> eval_expr env (make_affine_expr n e) = dot_product (fst e) (rev env) + snd e.
Proof.
  intros. unfold make_affine_expr. rewrite make_sum_correct, make_linear_expr_correct; auto.
Qed.

(** * Creating upper and lower bounds for a given variable in a constraint *)

Definition make_lower_bound n c :=
  make_div (make_sum (Constant ((- nth n (fst c) 0) - 1)) (make_affine_expr n (fst c, -(snd c)))) (-(nth n (fst c) 0)).

Lemma make_lower_bound_correct :
  forall n c env x, length env = n -> nth n (fst c) 0 < 0 -> (eval_expr env (make_lower_bound n c) <= x <-> satisfies_constraint (rev env ++ x :: nil) c = true).
Proof.
  intros n c env x Hlen Hneg.
  unfold satisfies_constraint. simpl.
  reflect. unfold make_lower_bound; rewrite make_div_correct, make_sum_correct, make_affine_expr_correct by auto. simpl.
  rewrite dot_product_app_left, dot_product_resize_right, dot_product_commutative.
  rewrite rev_length, Hlen.
  replace (dot_product (x :: nil) (skipn n (fst c))) with (x * nth n (fst c) 0) at 1;
    [| transitivity (x * nth 0 (skipn n (fst c)) 0);
       [ rewrite nth_skipn; f_equal; f_equal; lia
       | destruct (skipn n (fst c)) as [|z l]; [|destruct l]; simpl; lia
       ]
    ].
  rewrite div_le_iff by lia. nia.
Qed.

Definition make_upper_bound n c :=
  make_div (make_sum (Constant (nth n (fst c) 0)) (make_affine_expr n (mult_vector (-1) (fst c), snd c))) (nth n (fst c) 0).

Lemma make_upper_bound_correct :
  forall n c env x, length env = n -> 0 < nth n (fst c) 0 -> (x < eval_expr env (make_upper_bound n c) <-> satisfies_constraint (rev env ++ x :: nil) c = true).
Proof.
  intros n c env x Hlen Hpos.
  unfold satisfies_constraint. simpl.
  reflect. unfold make_upper_bound; rewrite make_div_correct, make_sum_correct, make_affine_expr_correct by auto. simpl.
  rewrite dot_product_mult_left.
  rewrite dot_product_app_left, dot_product_resize_right, dot_product_commutative.
  rewrite rev_length, Hlen.
  replace (dot_product (x :: nil) (skipn n (fst c))) with (x * nth n (fst c) 0) at 1;
    [| transitivity (x * nth 0 (skipn n (fst c)) 0);
       [ rewrite nth_skipn; f_equal; f_equal; lia
       | destruct (skipn n (fst c)) as [|z l]; [|destruct l]; simpl; lia
       ]
    ].
  rewrite div_gt_iff by lia. nia.
Qed.

Opaque make_lower_bound make_upper_bound.

(** * Finding the upper and lower bounds for a given variable of a polyhedron *)

Fixpoint find_lower_bound_aux (e : option expr) (n : nat) (p : polyhedron) :=
  match p with
  | nil => match e with Some e => Ok e | None => Err "No lower bound found" end
  | c :: p => if nth n (fst c) 0 <? 0 then
               find_lower_bound_aux (Some (match e with Some e => make_max e (make_lower_bound n c) | None => make_lower_bound n c end)) n p
             else
               find_lower_bound_aux e n p
  end.

Lemma find_lower_bound_aux_correct :
  forall n pol env x e lb, find_lower_bound_aux e n pol = Ok lb -> length env = n ->
                      eval_expr env lb <= x <->
                      ((match e with Some e => eval_expr env e <= x | None => True end) /\
                       forall c, In c pol -> nth n (fst c) 0 < 0 -> satisfies_constraint (rev env ++ x :: nil) c = true).
Proof.
  intros n pol. induction pol.
  - intros env x e lb Hlb Hlength. simpl in *.
    destruct e; simpl in *; [|congruence].
    injection Hlb as Hlb; rewrite Hlb.
    split; intros H; tauto.
  - intros env x e lb Hlb Hlen. simpl in *.
    destruct (nth n (fst a) 0 <? 0) eqn:Hcmp.
    + reflect. rewrite IHpol; eauto; simpl.
      destruct e; simpl; [rewrite make_max_correct, Z.max_lub_iff|]; rewrite make_lower_bound_correct by auto; split.
      * intros [[H1 H2] H3]. split; auto. intros c [Hce|Hcin] Hcnth; [congruence|auto].
      * intros [H1 H2]. split; [split|]; auto.
      * intros [H1 H2]. split; auto. intros c [Hce|Hcin] Hcnth; [congruence|auto].
      * intros [H1 H2]. split; auto.
    + reflect. rewrite IHpol; eauto; simpl. f_equiv. split.
      * intros H c [Hce|Hcin] Hcnth; auto; rewrite Hce in *; lia.
      * intros H c Hcin Hcnth; auto.
Qed.

Fixpoint find_upper_bound_aux (e : option expr) (n : nat) (p : polyhedron) :=
  match p with
  | nil => match e with Some e => Ok e | None => Err "No upper bound found" end
  | c :: p => if 0 <? nth n (fst c) 0 then
               find_upper_bound_aux (Some (match e with Some e => make_min e (make_upper_bound n c) | None => make_upper_bound n c end)) n p
             else
               find_upper_bound_aux e n p
  end.

Lemma find_upper_bound_aux_correct :
  forall n pol env x e ub, find_upper_bound_aux e n pol = Ok ub -> length env = n ->
                      x < eval_expr env ub <->
                      ((match e with Some e => x < eval_expr env e | None => True end) /\
                       forall c, In c pol -> 0 < nth n (fst c) 0 -> satisfies_constraint (rev env ++ x :: nil) c = true).
Proof.
  intros n pol. induction pol.
  - intros env x e ub Hub Hlength. simpl in *.
    destruct e; simpl in *; [|congruence].
    injection Hub as Hub; rewrite Hub.
    split; intros H; tauto.
  - intros env x e lb Hub Hlen. simpl in *.
    destruct (0 <? nth n (fst a) 0) eqn:Hcmp.
    + reflect. rewrite IHpol; eauto; simpl.
      destruct e; simpl; [rewrite make_min_correct, Z.min_glb_lt_iff|]; rewrite make_upper_bound_correct by auto; split.
      * intros [[H1 H2] H3]. split; auto. intros c [Hce|Hcin] Hcnth; [congruence|auto].
      * intros [H1 H2]. split; [split|]; auto.
      * intros [H1 H2]. split; auto. intros c [Hce|Hcin] Hcnth; [congruence|auto].
      * intros [H1 H2]. split; auto.
    + reflect. rewrite IHpol; eauto; simpl. f_equiv. split.
      * intros H c [Hce|Hcin] Hcnth; auto; rewrite Hce in *; lia.
      * intros H c Hcin Hcnth; auto.
Qed.

Definition find_lower_bound := find_lower_bound_aux None.
Definition find_upper_bound := find_upper_bound_aux None.

Theorem find_lower_bound_correct :
  forall n pol env x lb, find_lower_bound n pol = Ok lb -> length env = n ->
                    eval_expr env lb <= x <-> (forall c, In c pol -> nth n (fst c) 0 < 0 -> satisfies_constraint (rev env ++ x :: nil) c = true).
Proof.
  intros n pol env x lb Hlb Hlen.
  rewrite find_lower_bound_aux_correct by eauto. simpl. tauto.
Qed.

Theorem find_upper_bound_correct :
  forall n pol env x ub, find_upper_bound n pol = Ok ub -> length env = n ->
                    x < eval_expr env ub <-> (forall c, In c pol -> 0 < nth n (fst c) 0 -> satisfies_constraint (rev env ++ x :: nil) c = true).

Proof.
  intros n pol env x ub Hub Hlen.
  rewrite find_upper_bound_aux_correct by eauto. simpl. tauto.
Qed.

Theorem find_bounds_correct :
  forall n pol env x lb ub, find_lower_bound n pol = Ok lb -> find_upper_bound n pol = Ok ub -> length env = n ->
                       eval_expr env lb <= x < eval_expr env ub <-> (forall c, In c pol -> nth n (fst c) 0 <> 0 -> satisfies_constraint (rev env ++ x :: nil) c = true).
Proof.
  intros n pol env x lb ub Hlb Hub Hlen.
  rewrite find_lower_bound_correct; eauto.
  rewrite find_upper_bound_correct; eauto.
  split.
  - intros [H1 H2] c Hin Hnotzero. destruct (nth n (fst c) 0 <=? 0) eqn:Hcmp; reflect; [apply H1 | apply H2]; auto; lia.
  - intros H; split; intros c Hin Hcmp; apply H; auto; lia.
Qed.


Definition solve_eq n c :=
  (make_div (make_affine_expr n (mult_vector (-1) (fst c), snd c)) (nth n (fst c) 0),
   make_eq (make_mod (make_affine_expr n (mult_vector (-1) (fst c), snd c)) (nth n (fst c) 0)) (Constant 0)).

Lemma solve_eq_correct :
  forall n c env x, length env = n -> nth n (fst c) 0 <> 0 ->
               (eval_expr env (fst (solve_eq n c)) = x /\ eval_test env (snd (solve_eq n c)) = true) <->
                dot_product (rev env ++ x :: nil) (fst c) = snd c.
Proof.
  intros n c env x Hlen Hnz. simpl.
  rewrite make_div_correct, make_eq_correct, make_mod_correct, !make_affine_expr_correct by auto. simpl.
  rewrite !dot_product_mult_left, dot_product_app_left, dot_product_resize_right, dot_product_commutative.
  rewrite rev_length, Hlen.
  replace (dot_product (x :: nil) (skipn n (fst c))) with (x * nth n (fst c) 0) at 1;
    [| transitivity (x * nth 0 (skipn n (fst c)) 0);
       [ rewrite nth_skipn; f_equal; f_equal; lia
       | destruct (skipn n (fst c)) as [|z l]; [|destruct l]; simpl; lia
       ]
    ].
  reflect. split.
  - intros [Hdiv Hmod]. rewrite <- Z.div_exact in Hmod by auto. nia.
  - intros H. rewrite <- H, Z.add_assoc, Z.add_opp_diag_l, Z.add_0_l. split.
    + apply Z.div_mul; auto.
    + apply Z.mod_mul; auto.
Qed.

Definition make_affine_test n c := make_le (make_linear_expr n (fst c)) (Constant (snd c)).

Lemma make_affine_test_correct :
  forall env n c, length env = n -> eval_test env (make_affine_test n c) = satisfies_constraint (rev env) c.
Proof.
  intros. simpl in *. unfold make_affine_test. rewrite make_le_correct, make_linear_expr_correct; auto.
  rewrite dot_product_commutative. reflexivity.
Qed.

Definition make_poly_test n poly :=
  and_all (map (make_affine_test n) poly).

Lemma make_poly_test_correct :
  forall n poly env, length env = n ->
                eval_test env (make_poly_test n poly) = in_poly (rev env) poly.
Proof.
  intros n poly env Hlen.
  unfold make_poly_test. rewrite and_all_correct. unfold in_poly.
  rewrite forallb_map. apply forallb_ext. intros c. apply make_affine_test_correct. auto.
Qed.

Definition scan_dimension (n : nat) (inner : stmt) (p : polyhedron) : imp stmt :=
  match find_eq n p with
  | Some c =>
    let '(result, test) := solve_eq n c in
    let cstrs := map (fun c1 => make_affine_test n (make_constraint_with_eq n c c1)) (filter (fun c => negb (nth n (fst c) 0 =? 0)) p) in
    let cstrs1 := map (make_affine_test n) (filter (fun c => nth n (fst c) 0 =? 0) p) in
    pure (make_guard (make_and test (and_all (cstrs ++ cstrs1))) (make_let result inner))
  | None =>
    BIND lb <- res_to_alarm (Constant 0) (find_lower_bound n p) -;
    BIND ub <- res_to_alarm (Constant 0) (find_upper_bound n p) -;
    let cstrs := filter (fun c => nth n (fst c) 0 =? 0) p in
    pure (make_guard (make_poly_test n cstrs) (Loop lb ub inner))
  end.


Lemma dot_product_nth_zero_eval :
  forall env n u x, nth n u 0 = 0 -> length env = n -> dot_product (env ++ x :: nil) u = dot_product env u.
Proof.
  intros env n u x H1 H2.
  rewrite <- dot_product_assign_left_zero with (k := n) (s := 0) by auto.
  rewrite assign_app_ge by lia. rewrite H2, Nat.sub_diag.
  unfold assign. simpl.
  f_equiv. rewrite <- app_nil_r. f_equiv.
Qed.

Lemma satisfies_constraint_nth_zero_eq :
  forall env n c x, nth n (fst c) 0 = 0 -> length env = n -> satisfies_constraint (env ++ x :: nil) c = satisfies_constraint env c.
Proof.
  intros. unfold satisfies_constraint.
  erewrite dot_product_nth_zero_eval; eauto.
Qed.

Lemma scan_dimension_sem :
  forall n inner pol,
    WHEN st <- scan_dimension n inner pol THEN
         forall env mem1 mem2,
           length env = n ->
           exists lb ub,
             (loop_semantics st env mem1 mem2 <-> iter_semantics (fun x => loop_semantics inner (x :: env)) (Zrange lb ub) mem1 mem2) /\
             (forall x, in_poly (rev (x :: env)) pol = true <-> lb <= x < ub).
Proof.
  intros n inner pol st Hst env mem1 mem2 Henvlen.
  unfold scan_dimension in Hst.
  destruct (find_eq n pol) as [c|] eqn:Hfindeq.
  - destruct (solve_eq n c) as [result test] eqn:Hsolve. apply mayReturn_pure in Hst; rewrite <- Hst.
    match goal with [ Hst : make_guard ?T _ = _ |- _ ] => set (test1 := T) end.
    assert (Hcnth : 0 < nth n (fst c) 0) by (eapply find_eq_nth; eauto).
    destruct (eval_test env test1) eqn:Htest1.
    + exists (eval_expr env result). exists (eval_expr env (Sum result (Constant 1))). split.
      * split.
        -- intros Hsem. rewrite make_guard_correct, Htest1 in Hsem. unfold make_let in Hsem. inversion_clear Hsem. auto.
        -- intros Hsem. rewrite make_guard_correct, Htest1. unfold make_let. constructor; auto.
      * intros x. simpl.
        unfold test1 in Htest1. rewrite make_and_correct in Htest1; reflect.
        rewrite and_all_correct in Htest1. destruct Htest1 as [Htest Hcstr].
        rewrite forallb_app, andb_true_iff in Hcstr. destruct Hcstr as [Hcstr1 Hcstr2].
        transitivity (eval_expr env (fst (solve_eq n c)) = x /\ eval_test env (snd (solve_eq n c)) = true); [|rewrite Hsolve; simpl; intuition lia].
        rewrite solve_eq_correct by (auto || lia).
        split.
        -- intros H. unfold in_poly in H. rewrite forallb_forall in H.
           eapply find_eq_correct_1; eauto.
        -- intros H. unfold in_poly; rewrite forallb_forall. intros c1 Hc1in.
           rewrite forallb_map, forallb_forall in Hcstr1, Hcstr2. specialize (Hcstr1 c1). specialize (Hcstr2 c1).
           rewrite filter_In, make_affine_test_correct in Hcstr1, Hcstr2 by auto.
           destruct (nth n (fst c1) 0 =? 0) eqn:Hc1nth; reflect.
           ++ erewrite satisfies_constraint_nth_zero_eq; rewrite ?rev_length; eauto.
           ++ rewrite <- make_constraint_with_eq_correct_1 with (n := n) (c1 := c) by (auto || lia).
              erewrite satisfies_constraint_nth_zero_eq; rewrite ?rev_length; eauto.
              apply make_constraint_with_eq_nth; lia.
    + exists 0. exists 0. split.
      * split.
        -- intros Hsem. rewrite make_guard_correct, Htest1 in Hsem; rewrite Hsem. constructor; lia.
        -- intros Hsem. rewrite make_guard_correct, Htest1. inversion_clear Hsem. reflexivity.
      * split; [|lia]. intros H. exfalso.
        enough (eval_test env test1 = true) by congruence.
        unfold test1. rewrite make_and_correct, and_all_correct, forallb_app, !forallb_map. reflect.
        unfold in_poly in H. rewrite forallb_forall in H.
        assert (Heq : dot_product (rev (x :: env)) (fst c) = snd c) by (eapply find_eq_correct_1; eauto). simpl in Heq.
        split; [|split].
        -- rewrite <- solve_eq_correct in Heq; [|exact Henvlen|lia]. rewrite Hsolve in Heq; simpl in Heq; tauto.
        -- rewrite forallb_forall. intros c1 Hc1in. rewrite filter_In in Hc1in. reflect.
           rewrite make_affine_test_correct by auto. destruct Hc1in as [Hc1in Hc1n]. specialize (H c1 Hc1in).
           rewrite <- make_constraint_with_eq_correct_1 with (n := n) (c1 := c) in H by (auto || lia).
           simpl in H; erewrite satisfies_constraint_nth_zero_eq in H; rewrite ?rev_length; eauto.
           apply make_constraint_with_eq_nth; lia.
        -- rewrite forallb_forall. intros c1 Hc1in. rewrite filter_In in Hc1in. reflect.
           rewrite make_affine_test_correct by auto. destruct Hc1in as [Hc1in Hc1n]. specialize (H c1 Hc1in).
           simpl in H; erewrite satisfies_constraint_nth_zero_eq in H; rewrite ?rev_length; eauto.
  - bind_imp_destruct Hst lb Hlb. apply res_to_alarm_correct in Hlb.
    bind_imp_destruct Hst ub Hub. apply res_to_alarm_correct in Hub.
    apply mayReturn_pure in Hst. rewrite <- Hst.
    match goal with [ Hst : make_guard ?T _ = _ |- _ ] => set (test1 := T) end.
    destruct (eval_test env test1) eqn:Htest1.
    + exists (eval_expr env lb). exists (eval_expr env ub).
      rewrite make_guard_correct, Htest1.
      split.
      * split.
        -- intros Hsem; inversion_clear Hsem; auto.
        -- intros Hsem; constructor; auto.
      * intros x. rewrite find_bounds_correct; [|exact Hlb|exact Hub|exact Henvlen].
        unfold test1 in Htest1. rewrite make_poly_test_correct in Htest1 by auto.
        unfold in_poly in *. rewrite forallb_forall. rewrite forallb_forall in Htest1.
        split.
        -- intros H c Hc Hcnth; apply H; auto.
        -- intros H c Hc. destruct (nth n (fst c) 0 =? 0) eqn:Hcnth; reflect.
           ++ simpl; erewrite satisfies_constraint_nth_zero_eq; rewrite ?rev_length; [|eauto|eauto].
              apply Htest1. rewrite filter_In; reflect; auto.
           ++ apply H; auto.
    + exists 0. exists 0. rewrite make_guard_correct, Htest1. split.
      * split.
        -- intros H; rewrite H. econstructor; lia.
        -- intros H; inversion_clear H; reflexivity.
      * unfold test1 in Htest1. intros x. split; [|lia].
        intros H; unfold in_poly in H; rewrite forallb_forall in H.
        exfalso; eapply eq_true_false_abs; [|exact Htest1].
        rewrite make_poly_test_correct by auto. unfold in_poly; rewrite forallb_forall.
        intros c Hc; rewrite filter_In in Hc; destruct Hc as [Hcin Hcnth].
        specialize (H c Hcin). reflect. simpl in H.
        erewrite satisfies_constraint_nth_zero_eq in H; rewrite ?rev_length; eauto.
Qed.

Fixpoint polyloop_to_loop n pstmt : imp stmt :=
  match pstmt with
  | PSkip => pure (Seq nil)
  | PSeq s1 s2 =>
    BIND u1 <- polyloop_to_loop n s1 -;
    BIND u2 <- polyloop_to_loop n s2 -;
    pure (Seq (u1 :: u2 :: nil))
  | PInstr i es =>
    pure (Instr i (map (fun e => make_div (make_affine_expr n (snd e)) (Zpos (fst e))) es))
  | PLoop pol inner =>
    BIND inner1 <- polyloop_to_loop (S n) inner -;
    scan_dimension n inner1 pol
  | PGuard pol inner =>
    BIND inner1 <- polyloop_to_loop n inner -;
    pure (make_guard (make_poly_test n pol) inner1)
  end.

Lemma polyloop_to_loop_correct :
  forall pstmt n env mem1 mem2,
    WHEN st <- polyloop_to_loop n pstmt THEN
    loop_semantics st env mem1 mem2 ->
    length env = n ->
    poly_loop_semantics pstmt env mem1 mem2.
Proof.
  induction pstmt; intros n env mem1 mem2 st Hst Hsem Henv; simpl in *.
  - bind_imp_destruct Hst inner Hinner.
    generalize (scan_dimension_sem _ _ _ _ Hst _ mem1 mem2 Henv).
    intros [lb [ub [H1 H2]]].
    econstructor; [exact H2|]. rewrite H1 in Hsem.
    eapply iter_semantics_map; [|exact Hsem].
    intros x mem3 mem4 Hx Hsem2. simpl in Hsem2. eapply IHpstmt; simpl; eauto.
  - apply mayReturn_pure in Hst. rewrite <- Hst in *.
    inversion_clear Hsem. constructor.
    rewrite map_map in H.
    unfold eval_affine_expr. erewrite map_ext; [exact H|].
    intros [k a]; simpl. rewrite make_div_correct, make_affine_expr_correct by auto. reflexivity.
  - apply mayReturn_pure in Hst. rewrite <- Hst in *.
    inversion_clear Hsem. econstructor; auto.
  - bind_imp_destruct Hst u1 Hu1. bind_imp_destruct Hst u2 Hu2.
    apply mayReturn_pure in Hst; rewrite <- Hst in *.
    inversion_clear Hsem; inversion_clear H0. replace mem2 with mem4 by (inversion_clear H2; auto).
    econstructor; [eapply IHpstmt1|eapply IHpstmt2]; eauto.
  - bind_imp_destruct Hst inner Hinner. apply mayReturn_pure in Hst; rewrite <- Hst in *.
    rewrite make_guard_correct in Hsem.
    rewrite make_poly_test_correct in Hsem by auto.
    destruct (in_poly (rev env) p) eqn:Htest.
    + apply PLGuardTrue; [|auto]. eapply IHpstmt; eauto.
    + rewrite Hsem; apply PLGuardFalse; auto.
Qed.
