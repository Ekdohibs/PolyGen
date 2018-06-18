Require Import QArith.
Require Import QOrderedType.

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Psatz.
Require Import Setoid Morphisms.

Require Import Linalg.
Require Import Loop.
Require Import PolyLang.
Require Import Misc.
Require Import Instr.
Require Import VplInterface.
Require Import Result.

Require Import Vpl.Impure.
Require Vpl.ImpureConfig.

Open Scope Z_scope.
Open Scope list_scope.


Notation affine_expr := (positive * (list Z * Z))%type.
Definition eval_affine_expr env (e : affine_expr) :=
  (dot_product (fst (snd e)) (rev env) + snd (snd e)) / (Zpos (fst e)).
Definition affine_expr_ok env (e : affine_expr) :=
  ((dot_product (fst (snd e)) (rev env) + snd (snd e)) mod (Zpos (fst e)) =? 0).

Inductive poly_stmt :=
| PLoop : polyhedron -> poly_stmt -> poly_stmt
| PInstr : instr -> list affine_expr -> poly_stmt
| PSkip : poly_stmt
| PSeq : poly_stmt -> poly_stmt -> poly_stmt
| PGuard : polyhedron -> poly_stmt -> poly_stmt.

Inductive poly_loop_semantics : poly_stmt -> list Z -> mem -> mem -> Prop :=
| PLInstr : forall i es env mem1 mem2,
(*    forallb (affine_expr_ok env) es = true -> *)
    instr_semantics i (map (eval_affine_expr env) es) mem1 mem2 ->
    poly_loop_semantics (PInstr i es) env mem1 mem2
| PLSkip : forall env mem, poly_loop_semantics PSkip env mem mem
| PLSeq : forall env st1 st2 mem1 mem2 mem3,
    poly_loop_semantics st1 env mem1 mem2 ->
    poly_loop_semantics st2 env mem2 mem3 ->
    poly_loop_semantics (PSeq st1 st2) env mem1 mem3
| PLGuardTrue : forall env t st mem1 mem2,
    poly_loop_semantics st env mem1 mem2 ->
    in_poly (rev env) t = true ->
    poly_loop_semantics (PGuard t st) env mem1 mem2
| PLGuardFalse : forall env t st mem,
    in_poly (rev env) t = false -> poly_loop_semantics (PGuard t st) env mem mem
| PLLoop : forall env p lb ub st mem1 mem2,
    (forall x, in_poly (rev (x :: env)) p = true <-> lb <= x < ub) ->
    iter_semantics (fun x => poly_loop_semantics st (x :: env)) lb ub mem1 mem2 ->
    poly_loop_semantics (PLoop p st) env mem1 mem2.

Lemma PLLoop_inv_sem :
  forall env p st mem1 mem2,
    poly_loop_semantics (PLoop p st) env mem1 mem2 ->
    exists lb ub, (forall x, in_poly (rev (x :: env)) p = true <-> lb <= x < ub) /\ iter_semantics (fun x => poly_loop_semantics st (x :: env)) lb ub mem1 mem2.
Proof.
  intros env p st mem1 mem2 H. inversion_clear H.
  eexists; eexists; eauto.
Qed.

Lemma PLGuard_inv_sem :
  forall env p st mem1 mem2,
    poly_loop_semantics (PGuard p st) env mem1 mem2 ->
    if in_poly (rev env) p then poly_loop_semantics st env mem1 mem2 else mem1 = mem2.
Proof.
  intros env p st mem1 mem2 H.
  inversion_clear H.
  - rewrite H1; simpl; auto.
  - rewrite H0; simpl; auto.
Qed.


(*
(* TODO *)
Parameter split_polys : list polyhedron -> result (list (polyhedron * list nat)%type).

Axiom split_poly_disjoint :
  forall pl r, split_polys pl = Ok r -> all_disjoint (map fst r).

Axiom split_poly_indices :
  forall pl r p l n, split_polys pl = Ok r -> In (p, l) r -> In n l -> (n < length pl)%nat.

Axiom split_poly_eq :
  forall pl r n p, split_polys pl = Ok r -> (n < length pl)%nat -> in_poly p (nth n pl nil) = existsb (fun z => in_poly p (fst z) && existsb (fun m => (m =? n)%nat) (snd z)) r.
 *)

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

Fixpoint minindex {A : Type} (f : A -> Z) (l : list A) : option A :=
  match l with
  | nil => None
  | x :: l => match minindex f l with None => Some x | Some y => if f x <? f y then Some x else Some y end
  end.

Lemma minindex_In :
  forall A f (l : list A) x, minindex f l = Some x -> In x l.
Proof.
  induction l.
  - intros; simpl in *; congruence.
  - intros x H; simpl in *. destruct (minindex f l) as [u|].
    + specialize (IHl u). destruct (f a <? f u); injection H; intros H1; rewrite <- H1; tauto.
    + injection H; intros; tauto.
Qed.

Definition find_eq (n : nat) (p : polyhedron) :=
  let l1 := filter (fun c => 0 <? nth n (fst c) 0) p in
  let l2 := filter (fun c => nth n (fst c) 0 <? 0) p in
  let l12 := list_prod l1 l2 in
  let flt := map fst (filter (fun c12 => is_eq (fst (fst c12)) (mult_vector (-1) (fst (snd c12))) && (snd (fst c12) =? -snd (snd c12))) l12) in
  minindex (fun c => nth n (fst c) 0) flt.

Theorem find_eq_in :
  forall n pol c, find_eq n pol = Some c -> In c pol.
Proof.
  intros n pol c Hfind. unfold find_eq in *.
  apply minindex_In in Hfind.
  rewrite in_map_iff in Hfind; destruct Hfind as [[c1 c2] [Heq Hfind1]].
  simpl in Heq; rewrite Heq in *.
  rewrite filter_In in Hfind1. destruct Hfind1 as [Hfind1 Heq1].
  rewrite in_prod_iff, !filter_In in Hfind1. tauto.
Qed.

Theorem find_eq_correct :
  forall n pol c p t, 0 < t -> find_eq n pol = Some c ->
                 (forall c, In c pol -> nth n (fst c) 0 <> 0 -> satisfies_constraint p (mult_constraint_cst t c) = true) -> dot_product p (fst c) = t * snd c.
Proof.
  intros n pol c p t Ht Hfind Hin.
  unfold find_eq, in_poly, satisfies_constraint in *.
  apply minindex_In in Hfind.
  rewrite in_map_iff in Hfind; destruct Hfind as [[c1 c2] [Heq Hfind1]].
  simpl in Heq; rewrite Heq in *.
  rewrite filter_In, in_prod_iff, !filter_In in Hfind1. reflect. destruct Hfind1 as [[[Hin1 ?] [Hin2 ?]] [Heql Heqr]].
  simpl in *; reflect.
  apply Hin in Hin1; apply Hin in Hin2; try lia; reflect.
  rewrite Heql, dot_product_mult_right in *. nia.
Qed.

Theorem find_eq_correct_1 :
  forall n pol c p, find_eq n pol = Some c -> (forall c, In c pol -> nth n (fst c) 0 <> 0 -> satisfies_constraint p c = true) -> dot_product p (fst c) = snd c.
Proof.
  intros n pol c p Hfind Hin.
  rewrite find_eq_correct with (t := 1) (n := n) (pol := pol); auto; try lia.
  intros c1. rewrite mult_constraint_cst_1. apply Hin.
Qed.

Theorem find_eq_nth :
  forall n pol c, find_eq n pol = Some c -> 0 < nth n (fst c) 0.
Proof.
  intros n pol c Hfind.
  unfold find_eq in *.
  apply minindex_In in Hfind.
  rewrite in_map_iff in Hfind; destruct Hfind as [[c1 c2] [Heq Hfind1]].
  simpl in Heq; rewrite Heq in *.
  rewrite filter_In, in_prod_iff, !filter_In in Hfind1. reflect. destruct Hfind1 as [[[? ?] [? ?]] ?].
  auto.
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

Definition make_constraint_with_eq n c1 c2 :=
  let '(g, (aa, bb)) := Z.ggcd (nth n (fst c1) 0) (nth n (fst c2) 0) in
  add_constraint (mult_constraint (Z.sgn aa * -bb) c1) (mult_constraint (Z.abs aa) c2).

Lemma make_constraint_with_eq_correct :
  forall n c1 c2 p t, dot_product p (fst c1) = t * snd c1 -> nth n (fst c1) 0 <> 0 ->
                 satisfies_constraint p (mult_constraint_cst t (make_constraint_with_eq n c1 c2)) = satisfies_constraint p (mult_constraint_cst t c2).
Proof.
  intros n c1 c2 p t Hc1 Hcnz1. unfold make_constraint_with_eq.
  remember (nth n (fst c1) 0) as a. 
  remember (nth n (fst c2) 0) as b.
  generalize (Z.ggcd_correct_divisors a b). generalize (Z.ggcd_gcd a b).
  destruct Z.ggcd as [g [aa bb]] eqn:Hggcd. simpl. intros Hg [Haa Hbb].
  unfold satisfies_constraint, add_constraint, mult_constraint; simpl.
  rewrite add_vector_dot_product_distr_right, !dot_product_mult_right, eq_iff_eq_true; reflect.
  nia.
Qed.

Lemma make_constraint_with_eq_correct_1 :
  forall n c1 c2 p, dot_product p (fst c1) = snd c1 -> nth n (fst c1) 0 <> 0 ->
               satisfies_constraint p (make_constraint_with_eq n c1 c2) = satisfies_constraint p c2.
Proof.
  intros n c1 c2 p Hc1 Hcnz1.
  generalize (make_constraint_with_eq_correct n c1 c2 p 1).
  rewrite !mult_constraint_cst_1. intros H; apply H; lia.
Qed.

Lemma make_constraint_with_eq_nth :
  forall n c1 c2, nth n (fst c1) 0 <> 0 -> nth n (fst (make_constraint_with_eq n c1 c2)) 0 = 0.
Proof.
  intros n c1 c2 Hcnz1. unfold make_constraint_with_eq.
  remember (nth n (fst c1) 0) as a. 
  remember (nth n (fst c2) 0) as b.
  generalize (Z.ggcd_correct_divisors a b). generalize (Z.ggcd_gcd a b).
  destruct Z.ggcd as [g [aa bb]] eqn:Hggcd. simpl. intros Hg [Haa Hbb].
  unfold satisfies_constraint, add_constraint, mult_constraint; simpl.
  rewrite add_vector_nth, !mult_nth.
  nia.
Qed.

Lemma make_constraint_with_eq_preserve_zeros :
  forall n m c1 c2, nth n (fst c1) 0 = 0 -> nth n (fst c2) 0 = 0 -> nth n (fst (make_constraint_with_eq m c1 c2)) 0 = 0.
Proof.
  intros n m c1 c2 H1 H2. unfold make_constraint_with_eq.
  destruct Z.ggcd as [? [? ?]]. unfold add_constraint, mult_constraint. simpl.
  rewrite add_vector_nth, !mult_nth. nia.
Qed.

(** * Polyhedral projection *)
(** Two different implementations:
- an untrusted oracle and a certificate
- Fourier-Motzkin elimination and polyhedral canonization (that can use an untrusted oracle)
*)

Module Type PolyProject (Import Imp: FullImpureMonad).
  Parameter project : nat * polyhedron -> imp polyhedron.

  Parameter project_inclusion :
    forall n p pol, in_poly p pol = true -> WHEN proj <- project (n, pol) THEN in_poly (resize n p) proj = true.

  Parameter project_invariant : nat -> polyhedron -> list Z -> Prop.

  Parameter project_invariant_inclusion :
    forall n pol p, in_poly p pol = true -> project_invariant n pol (resize n p).

  Parameter project_id :
    forall n pol p, (forall c, In c pol -> fst c =v= resize n (fst c)) -> project_invariant n pol p -> in_poly p pol = true.

  Parameter project_next_r_inclusion :
    forall n pol p, project_invariant n pol p ->
               WHEN proj <- project (S n, pol) THEN
               (forall c, In c proj -> nth n (fst c) 0 <> 0 -> satisfies_constraint p c = true) ->
                 project_invariant (S n) pol p.

  Parameter project_invariant_resize :
    forall n pol p, project_invariant n pol p <-> project_invariant n pol (resize n p).

  Parameter project_invariant_export : nat * polyhedron -> imp polyhedron.

  Parameter project_invariant_export_correct :
    forall n p pol, WHEN res <- project_invariant_export (n, pol) THEN in_poly p res = true <-> project_invariant n pol p.

  Parameter project_constraint_size :
    forall n pol c, WHEN proj <- project (n, pol) THEN In c proj -> fst c =v= resize n (fst c).
(*
  Parameter project_invariant_reduce :
    forall n pol1 pol2 p, (forall v, in_poly v pol2 = true -> in_poly v pol1 = true) ->
                     project_invariant n pol1 p -> in_poly p pol2 = true -> project_invariant n pol2 p.
*)
End PolyProject.

Module Type PolyCanonizer (Import Imp: FullImpureMonad).

  Parameter canonize : polyhedron -> imp polyhedron.

  Parameter canonize_correct :
    forall p, WHEN r <- canonize p THEN (forall k v, 0 < k -> in_poly v (expand_poly k r) = in_poly v (expand_poly k p)).

  Parameter canonize_no_new_var :
    forall k p, (forall c, In c p -> nth k (fst c) 0 = 0) -> WHEN r <- canonize p THEN (forall c, In c r -> nth k (fst c) 0 = 0).

End PolyCanonizer.

Module NaiveCanonizer(Import Imp: FullImpureMonad) <: PolyCanonizer Imp.

  Definition canonize (p : polyhedron) := pure p.

  Theorem canonize_correct :
    forall p, WHEN r <- canonize p THEN (forall k v, 0 < k -> in_poly v (expand_poly k r) = in_poly v (expand_poly k p)).
  Proof.
    intros p r Hcanon k v Hk. unfold canonize in Hcanon.
    apply mayReturn_pure in Hcanon. rewrite Hcanon. reflexivity.
  Qed.

  Theorem canonize_no_new_var :
    forall k p, (forall c, In c p -> nth k (fst c) 0 = 0) -> WHEN r <- canonize p THEN (forall c, In c r -> nth k (fst c) 0 = 0).
  Proof.
    intros k p H r Hcanon. unfold canonize in Hcanon.
    apply mayReturn_pure in Hcanon. rewrite Hcanon in H. exact H.
  Qed.

End NaiveCanonizer.

Definition isExactProjection n pol proj :=
  forall p s, 0 < s -> in_poly p (expand_poly s proj) = true <->
                 exists t k, 0 < t /\ in_poly (assign n k (mult_vector t p)) (expand_poly (s * t) pol) = true.

Definition isExactProjection1 n pol proj :=
  forall p, in_poly p proj = true <-> exists t k, 0 < t /\ in_poly (assign n k (mult_vector t p)) (expand_poly t pol) = true.

Lemma isExactProjection_weaken1 :
  forall n pol proj, isExactProjection n pol proj -> isExactProjection1 n pol proj.
Proof.
  intros n pol proj H p.
  specialize (H p 1). rewrite expand_poly_1 in H; rewrite H by lia. 
  split; intros [t [k Htk]]; exists t; exists k; rewrite Z.mul_1_l in *; auto.
Qed.

Lemma isExactProjection_assign :
  forall n p x t pol proj, 0 < t -> isExactProjection n pol proj -> in_poly p (expand_poly t pol) = true ->
                      in_poly (assign n x p) (expand_poly t proj) = true.
Proof.
  intros n p x t pol proj Ht Hproj Hpol.
  rewrite (Hproj _ t) by lia. exists 1. exists (nth n p 0). split; [lia|].
  rewrite <- Hpol. f_equiv; [|f_equal; lia].
  rewrite mult_vector_1. rewrite assign_assign.
  apply assign_id.
Qed.

Lemma isExactProjection_assign_1 :
  forall n p x pol proj, isExactProjection1 n pol proj -> in_poly p pol = true ->
                      in_poly (assign n x p) proj = true.
Proof.
  intros n p x pol proj Hproj Hpol.
  rewrite (Hproj _) by lia. exists 1. exists (nth n p 0). split; [lia|].
  rewrite <- Hpol. rewrite expand_poly_1. f_equiv.
  rewrite mult_vector_1. rewrite assign_assign.
  apply assign_id.
Qed.

Module Type ProjectOperator (Import Imp: FullImpureMonad).

  Parameter project : (nat * polyhedron) -> imp polyhedron.

  Parameter project_projected :
    forall n pol, WHEN proj <- project (n, pol) THEN forall c, In c proj -> nth n (fst c) 0 = 0.

  Parameter project_no_new_var :
    forall n k pol, (forall c, In c pol -> nth k (fst c) 0 = 0) -> WHEN proj <- project (n, pol) THEN (forall c, In c proj -> nth k (fst c) 0 = 0).

  Parameter project_in_iff :
    forall n pol, WHEN proj <- project (n, pol) THEN isExactProjection n pol proj.

End ProjectOperator.

Module FourierMotzkinProject (Import Imp: FullImpureMonad) <: ProjectOperator Imp.

  Definition merge_constraints n c1 c2 :=
    let '(g, (aa, bb)) := Z.ggcd (nth n (fst c1) 0) (nth n (fst c2) 0) in
    add_constraint (mult_constraint bb c1) (mult_constraint (-aa) c2).

  Lemma Q_exists_rec :
    forall (l1 l2 : list Q) (y1 : Q), ((exists x : Q, (forall y : Q, In y l1 -> (y <= x)%Q) /\ (forall z : Q, In z l2 -> (x <= z)%Q)) <->
                                  (forall y z : Q, In y l1 -> In z l2 -> (y <= z)%Q)) ->
                                 ((exists x : Q, (forall y : Q, In y (y1 :: l1) -> (y <= x)%Q) /\ (forall z : Q, In z l2 -> (x <= z)%Q)) <->
                                  (forall y z : Q, In y (y1 :: l1) -> In z l2 -> (y <= z)%Q)).
  Proof.
    intros l1 l2 y1 [Himp1 Himp2].
    split.
    - intros [x [Hxy Hxz]] y z Hiny Hinz.
      specialize (Hxy y Hiny). specialize (Hxz z Hinz). q_order.
    - intros H. destruct Himp2 as [x [Hxy Hxz]].
      + intros y z Hiny Hinz. apply H; simpl; auto.
      + destruct (Qlt_le_dec x y1).
        * exists y1. split.
          -- intros y [Hy1| Hiny]; [rewrite Hy1 | specialize (Hxy y Hiny)]; q_order.
          -- intros z Hinz. apply H; simpl; auto.
        * exists x. split.
          -- intros y [Hy1 | Hiny]; [rewrite Hy1 in *; q_order | apply Hxy; auto].
          -- auto.
  Qed.

  Lemma Q_exists_min :
    forall (l : list Q), exists x : Q, forall y : Q, In y l -> (x <= y)%Q.
  Proof.
    induction l as [|y1 l IH].
    - exists 0%Q; intros; simpl in *; tauto.
    - destruct IH as [x IH].
      destruct (Qlt_le_dec x y1).
      + exists x. intros y [Hy1 | Hiny]; [rewrite Hy1 in *; q_order | apply (IH y Hiny)].
      + exists y1. intros y [Hy1 | Hiny]; [rewrite Hy1 | specialize (IH y Hiny)]; q_order.
  Qed.


  Lemma Q_exists_between :
    forall (l1 l2 : list Q), (exists x : Q, (forall y : Q, In y l1 -> (y <= x)%Q) /\ (forall z : Q, In z l2 -> (x <= z)%Q)) <->
                        (forall y z : Q, In y l1 -> In z l2 -> (y <= z)%Q).
  Proof.
    induction l1 as [|y1 l1 IH1].
    - intros l2. split.
      + intros; simpl in *; tauto.
      + intros H; destruct (Q_exists_min l2) as [x Hx]; exists x.
        split; [intros; simpl in *; tauto | apply Hx].
    - intros l2; apply Q_exists_rec. apply IH1.
  Qed.

  Definition bound k c p :=
    (inject_Z (snd c - dot_product (assign k 0 p) (fst c))%Z / inject_Z (nth k (fst c) 0)%Z)%Q.

  Lemma assign_0_eq :
    forall k c p s, nth k (fst c) 0 = 0 -> satisfies_constraint (assign k s p) c = satisfies_constraint p c.
  Proof.
    intros k c p s H.
    unfold satisfies_constraint. f_equal. apply dot_product_assign_left_zero; auto.
  Qed.

  Lemma assign_pos_bound :
    forall k c p s t , 0 < nth k (fst c) 0 -> 0 < t ->
                  satisfies_constraint (assign k s (mult_vector t p)) (mult_constraint_cst t c) =
                  (Qle_bool (inject_Z s / inject_Z t) (bound k c p))%Q.
  Proof.
    intros k c p s t Hckpos Htpos. unfold bound.
    destruct t as [|tpos|tneg]; [lia| |lia].
    destruct (nth k (fst c) 0) as [|upos|uneg] eqn:Hu; [lia| |lia].
    unfold satisfies_constraint, Qle_bool, Qdiv, Qmult, Qinv, inject_Z; simpl.
    rewrite !dot_product_assign_left, dot_product_mult_left, mult_nth.
    rewrite eq_iff_eq_true; reflect. destruct (snd c); nia.
  Qed.

  Lemma assign_neg_bound :
    forall k c p s t , nth k (fst c) 0 < 0 -> 0 < t ->
                  satisfies_constraint (assign k s (mult_vector t p)) (mult_constraint_cst t c) =
                  (Qle_bool (bound k c p) (inject_Z s / inject_Z t))%Q.
  Proof.
    intros k c p s t Hckpos Htpos. unfold bound.
    destruct t as [|tpos|tneg]; [lia| |lia].
    destruct (nth k (fst c) 0) as [|upos|uneg] eqn:Hu; [lia|lia|].
    unfold satisfies_constraint, Qle_bool, Qdiv, Qmult, Qinv, inject_Z; simpl.
    rewrite !dot_product_assign_left, dot_product_mult_left, mult_nth.
    rewrite eq_iff_eq_true; reflect. destruct (snd c); nia.
  Qed.

  Lemma is_projected_separate :
    forall n pol p s, 0 < s ->
      (exists t k, 0 < t /\ in_poly (assign n k (mult_vector t p)) (expand_poly (s * t) pol) = true) <->
      (in_poly p (expand_poly s (filter (fun c => nth n (fst c) 0 =? 0) pol)) = true /\
       forall y z, In y (map (fun c => bound n (mult_constraint_cst s c) p) (filter (fun c => nth n (fst c) 0 <? 0) pol)) ->
              In z (map (fun c => bound n (mult_constraint_cst s c) p) (filter (fun c => nth n (fst c) 0 >? 0) pol)) ->
              (y <= z)%Q).
  Proof.
    intros n pol p s Hs.
    rewrite <- Q_exists_between.
    split.
    - intros [t [k [Ht Hin]]]. split.
      + unfold in_poly, expand_poly in *.
        rewrite forallb_map, forallb_forall in *. intros c Hinc.
        rewrite filter_In in Hinc. destruct Hinc as [Hinc Hnthc].
        specialize (Hin c Hinc). reflect.
        rewrite assign_0_eq, Z.mul_comm, <- mult_constraint_cst_comp, mult_constraint_cst_eq in Hin by (simpl; auto).
        exact Hin.
      + exists ((inject_Z k) / (inject_Z t))%Q. split.
        * intros y Hy. rewrite in_map_iff in Hy; destruct Hy as [c [Hy Hinc]].
          rewrite filter_In in Hinc; destruct Hinc as [Hinc Hnthc]. reflect.
          rewrite <- Hy. rewrite <- Qle_bool_iff, <- assign_neg_bound by auto.
          rewrite mult_constraint_cst_comp. unfold in_poly in Hin. rewrite forallb_forall in Hin.
          apply Hin. rewrite Z.mul_comm. unfold expand_poly. apply in_map. auto.
        * intros y Hy. rewrite in_map_iff in Hy; destruct Hy as [c [Hy Hinc]].
          rewrite filter_In in Hinc; destruct Hinc as [Hinc Hnthc]. reflect.
          rewrite <- Hy. rewrite <- Qle_bool_iff, <- assign_pos_bound by auto.
          rewrite mult_constraint_cst_comp. unfold in_poly in Hin. rewrite forallb_forall in Hin.
          apply Hin. rewrite Z.mul_comm. unfold expand_poly. apply in_map. auto.
    - intros [Hin0 [x [Hinneg Hinpos]]].
      exists (Zpos (Qden x)). exists (Qnum x).
      split; [lia|].
      unfold in_poly, expand_poly in *. rewrite forallb_map, forallb_forall in *.
      intros c Hinc.
      destruct (Z.compare_spec (nth n (fst c) 0) 0).
      + rewrite assign_0_eq, Z.mul_comm, <- mult_constraint_cst_comp, mult_constraint_cst_eq by (simpl; auto; lia).
        apply Hin0. rewrite filter_In. reflect; auto.
      + rewrite Z.mul_comm, <- mult_constraint_cst_comp, assign_neg_bound, Qle_bool_iff, <- Qmake_Qdiv by (auto; lia).
        apply Hinneg. rewrite in_map_iff; exists c; split; [auto|].
        rewrite filter_In; reflect; auto.
      + rewrite Z.mul_comm, <- mult_constraint_cst_comp, assign_pos_bound, Qle_bool_iff, <- Qmake_Qdiv by (auto; lia).
        apply Hinpos. rewrite in_map_iff; exists c; split; [auto|].
        rewrite filter_In; reflect; auto.
  Qed.

  Lemma merge_constraints_correct :
    forall n c1 c2 p, nth n (fst c1) 0 < 0 -> nth n (fst c2) 0 > 0 ->
                 satisfies_constraint p (merge_constraints n c1 c2) =
                 Qle_bool (bound n c1 p) (bound n c2 p).
  Proof.
    intros n c1 c2 p Hneg Hpos.
    unfold merge_constraints, bound.
    destruct (nth n (fst c1) 0) as [|a|a] eqn:Ha; [lia|lia|].
    destruct (nth n (fst c2) 0) as [|b|b] eqn:Hb; [lia| |lia].
    generalize (Z.ggcd_correct_divisors (Zneg a) (Zpos b)). generalize (Z.ggcd_gcd (Zneg a) (Zpos b)).
    destruct Z.ggcd as [g [aa bb]] eqn:Hggcd. simpl. intros Hg [Hag Hbg].
    unfold satisfies_constraint, Qle_bool, Qdiv, Qmult, Qinv, inject_Z. simpl.
    rewrite add_vector_dot_product_distr_right, !dot_product_mult_right.
    rewrite !dot_product_assign_left, Ha, Hb, eq_iff_eq_true; reflect.
    rewrite Z.mul_le_mono_pos_l with (p := g) by lia. nia.
  Qed.

  Lemma merge_constraints_mult_constraint_cst :
    forall n c1 c2 s, merge_constraints n (mult_constraint_cst s c1) (mult_constraint_cst s c2) =
                 mult_constraint_cst s (merge_constraints n c1 c2).
  Proof.
    intros n c1 c2 s; unfold merge_constraints, mult_constraint_cst, add_constraint, mult_constraint.
    simpl. destruct (Z.ggcd (nth n (fst c1) 0) (nth n (fst c2) 0)) as [g [aa bb]]. simpl.
    f_equal. nia.
  Qed.

  Definition pure_project n p :=
    let zero := filter (fun c => nth n (fst c) 0 =? 0) p in
    let pos := filter (fun c => nth n (fst c) 0 >? 0) p in
    let neg := filter (fun c => nth n (fst c) 0 <? 0) p in
    zero ++ flatten (map (fun nc => map (merge_constraints n nc) pos) neg).

  Definition project np := pure (pure_project (fst np) (snd np)).

  Theorem pure_project_in_iff :
    forall n pol, isExactProjection n pol (pure_project n pol).
  Proof.
    intros n pol p s Hs.
    rewrite is_projected_separate by auto.
    unfold pure_project. rewrite expand_poly_app, in_poly_app, andb_true_iff.
    f_equiv. unfold in_poly, expand_poly.
    rewrite forallb_map, <- flatten_forallb, forallb_map, forallb_forall.
    split.
    - intros H y z Hiny Hinz.
      rewrite in_map_iff in Hiny, Hinz; destruct Hiny as [cy [Hy Hiny]]; destruct Hinz as [cz [Hz Hinz]].
      specialize (H cy Hiny). rewrite forallb_map, forallb_forall in H. specialize (H cz Hinz).
      rewrite filter_In in Hiny, Hinz; reflect.
      rewrite <- Hy, <- Hz, <- Qle_bool_iff, <- merge_constraints_correct by (simpl; lia).
      rewrite merge_constraints_mult_constraint_cst; exact H.
    - intros H cy Hincy. rewrite forallb_map, forallb_forall. intros cz Hincz.
      rewrite <- merge_constraints_mult_constraint_cst, merge_constraints_correct by (rewrite filter_In in *; reflect; simpl; lia).
      rewrite Qle_bool_iff; apply H; rewrite in_map_iff; [exists cy | exists cz]; auto.
  Qed.

  Theorem project_in_iff :
    forall n pol, WHEN proj <- project (n, pol) THEN isExactProjection n pol proj.
  Proof.
    intros n pol proj Hproj.
    unfold project in Hproj. apply mayReturn_pure in Hproj. simpl in Hproj. rewrite <- Hproj.
    apply pure_project_in_iff; auto.
  Qed.

  Theorem merge_constraints_projected :
    forall n c1 c2, nth n (fst (merge_constraints n c1 c2)) 0 = 0.
  Proof.
    intros n c1 c2.
    unfold merge_constraints, add_constraint, mult_constraint.
    generalize (Z.ggcd_correct_divisors (nth n (fst c1) 0) (nth n (fst c2) 0)).
    destruct Z.ggcd as [g [aa bb]]. intros [H1 H2]. simpl.
    rewrite add_vector_nth, !mult_nth. nia.
  Qed.

  Lemma pure_project_constraint_in :
    forall n pol c, In c (pure_project n pol) ->
               ((In c pol /\ nth n (fst c) 0 = 0) \/
                (exists y z, In y pol /\ In z pol /\ nth n (fst y) 0 < 0 /\ 0 < nth n (fst z) 0 /\ c = merge_constraints n y z)).
  Proof.
    intros n pol c Hin. unfold pure_project in Hin.
    rewrite in_app_iff in Hin. destruct Hin as [Hin | Hin].
    - left; rewrite filter_In in Hin. reflect; tauto.
    - right; rewrite flatten_In in Hin. destruct Hin as [u [Hinu Huin]].
      rewrite in_map_iff in Huin; destruct Huin as [nc [Hu Hnc]].
      rewrite <- Hu, in_map_iff in Hinu. destruct Hinu as [pc [Hc Hpc]].
      rewrite <- Hc. exists nc; exists pc.
      rewrite filter_In in *; reflect; tauto.
  Qed.

  Theorem pure_project_projected :
    forall n pol c, In c (pure_project n pol) -> nth n (fst c) 0 = 0.
  Proof.
    intros n pol c Hin. apply pure_project_constraint_in in Hin.
    destruct Hin as [[Hcin Hcn] | [y [z [Hyin [Hzin [Hyn [Hzn Hc]]]]]]].
    - auto.
    - rewrite Hc. apply merge_constraints_projected.
  Qed.

  Theorem project_projected :
    forall n pol, WHEN proj <- project (n, pol) THEN forall c, In c proj -> nth n (fst c) 0 = 0.
  Proof.
    intros n pol proj Hproj c Hinproj.
    unfold project in Hproj; apply mayReturn_pure in Hproj; rewrite <- Hproj in *; simpl in *.
    eapply pure_project_projected; eauto.
  Qed.

  Theorem merge_constraints_no_new_var :
    forall n k c1 c2, nth k (fst c1) 0 = 0 -> nth k (fst c2) 0 = 0 -> nth k (fst (merge_constraints n c1 c2)) 0 = 0.
  Proof.
    intros n k c1 c2 Hc1 Hc2.
    unfold merge_constraints, add_constraint, mult_constraint.
    destruct Z.ggcd as [g [aa bb]]. simpl.
    rewrite add_vector_nth, !mult_nth. nia.
  Qed.

  Theorem pure_project_no_new_var :
    forall n k pol, (forall c, In c pol -> nth k (fst c) 0 = 0) -> (forall c, In c (pure_project n pol) -> nth k (fst c) 0 = 0).
  Proof.
    intros n k pol H c Hin.
    apply pure_project_constraint_in in Hin.
    destruct Hin as [[Hcin Hcn] | [y [z [Hyin [Hzin [Hyn [Hzn Hc]]]]]]].
    - auto.
    - rewrite Hc. apply merge_constraints_no_new_var; auto.
  Qed.

  Theorem project_no_new_var :
    forall n k pol, (forall c, In c pol -> nth k (fst c) 0 = 0) -> WHEN proj <- project (n, pol) THEN (forall c, In c proj -> nth k (fst c) 0 = 0).
  Proof.
    intros n k pol H proj Hproj.
    unfold project in Hproj; apply mayReturn_pure in Hproj; rewrite <- Hproj in *; simpl in *.
    eapply pure_project_no_new_var; eauto.
  Qed.

End FourierMotzkinProject.

Module PolyProjectImpl (Import Imp: FullImpureMonad) (Canon : PolyCanonizer Imp) (Proj : ProjectOperator Imp) <: PolyProject Imp.

  Ltac bind_imp_destruct H id1 id2 :=
  apply mayReturn_bind in H; destruct H as [id1 [id2 H]].

  Fixpoint do_project d k pol :=
    match k with
    | O => pure pol
    | S k1 =>
      BIND proj <- Proj.project ((d + k1)%nat, pol) -;
      BIND canon <- Canon.canonize proj -;
      do_project d k1 canon
    end.

  Lemma do_project_succ :
    forall k d pol, impeq (do_project d (S k) pol)
                     (BIND proj1 <- do_project (S d) k pol -; BIND proj <- Proj.project (d, proj1) -; Canon.canonize proj).
  Proof.
    induction k.
    - intros; simpl in *. rewrite Nat.add_0_r.
      rewrite impeq_bind_pure_l. f_equiv; intro proj1. rewrite impeq_bind_pure_r. reflexivity.
    - intros d pol; simpl in *.
      rewrite impeq_bind_assoc. rewrite Nat.add_succ_r. f_equiv; intro proj.
      rewrite impeq_bind_assoc. f_equiv; intro canon.
      rewrite IHk. reflexivity.
  Qed.

  Lemma do_project_in_iff :
    forall k s d p pol, 0 < s ->
                   WHEN proj <- do_project d k pol THEN
                        in_poly p (expand_poly s proj) = true <->
                   exists t m, length m = k /\ 0 < t /\
                          in_poly (resize d (mult_vector t p) ++ m ++ skipn (d + k)%nat (mult_vector t p))
                                  (expand_poly (s * t) pol) = true.
  Proof.
    induction k.
    - intros s d p pol Hs proj Hproj; simpl in *.
      apply mayReturn_pure in Hproj; rewrite Hproj.
      split.
      + intros Hin. exists 1. exists nil. simpl.
        split; [auto|split;[lia|]].
        rewrite !mult_vector_1, Nat.add_0_r, resize_skipn_eq, Z.mul_1_r.
        exact Hin.
      + intros [t [m [Hm [Ht Hin]]]].
        destruct m; simpl in *; [|congruence].
        rewrite Nat.add_0_r, resize_skipn_eq, Z.mul_comm, <- expand_poly_comp, expand_poly_eq in Hin by auto.
        exact Hin.
    - intros s d p pol Hs proj Hproj; simpl in *.
      bind_imp_destruct Hproj proja Hproja.
      bind_imp_destruct Hproj canon Hcanon.
      rewrite (IHk s d p canon Hs proj Hproj).
      split; intros [t [m [Hmlen [Ht Hin]]]]; assert (Hst : 0 < s * t) by nia.
      + rewrite (Canon.canonize_correct proja) in Hin by auto.
        rewrite (Proj.project_in_iff _ _ _ Hproja _ _ Hst) in Hin.
        destruct Hin as [r [u [Hr Hin]]].
        exists (t * r). exists (mult_vector r m ++ (u :: nil)).
        split; [rewrite app_length, mult_vector_length, Nat.add_1_r; auto|].
        split; [nia|].
        rewrite <- Hin, Z.mul_assoc. f_equiv.
        rewrite !mult_vector_app, <- !mult_vector_resize, <- !mult_vector_skipn, !mult_vector_comp.
        rewrite assign_app_ge; rewrite resize_length; [|lia].
        rewrite assign_app_ge; rewrite mult_vector_length, Hmlen; [|lia].
        replace (d + k - d - k)%nat with 0%nat by lia.
        rewrite <- app_assoc.
        f_equiv; [f_equal; f_equal; nia|].
        f_equiv. unfold assign. rewrite skipn_skipn. replace (1 + (d + k))%nat with (d + S k)%nat by lia.
        simpl. f_equiv. f_equiv. f_equal. nia.
      + exists t. exists (resize k m). split; [apply resize_length|].
        split; [auto|].
        rewrite (Canon.canonize_correct proja) by auto.
        rewrite (Proj.project_in_iff _ _ _ Hproja _ _ Hst).
        exists 1. exists (nth k m 0).
        split; [lia|].
        rewrite mult_vector_1. rewrite <- Hin.
        f_equiv; [|f_equal; lia].
        rewrite assign_app_ge; rewrite resize_length; [|lia].
        rewrite assign_app_ge; rewrite resize_length; [|lia].
        replace (d + k - d - k)%nat with 0%nat by lia.
        unfold assign.
        rewrite skipn_skipn. replace (1 + (d + k))%nat with (d + S k)%nat by lia.
        replace m with (resize k m ++ (nth k m 0 :: nil)) at 3 by (rewrite <- resize_succ; apply resize_length_eq; auto).
        rewrite <- app_assoc. reflexivity.
  Qed.

  Fixpoint simplify_poly (n : nat) (p : polyhedron) :=
    match n with
    | 0%nat => p
    | S n =>
      let nz := filter (fun c => negb (nth n (fst c) 0 =? 0)) p in
      let z := filter (fun c => nth n (fst c) 0 =? 0) p in
      match find_eq n nz with
      | None => nz ++ simplify_poly n z
      | Some c => c :: mult_constraint (-1) c ::
                   simplify_poly n (map (fun c1 => make_constraint_with_eq n c c1) nz ++ z)
      end
    end.

  Lemma simplify_poly_correct :
    forall n pol p t, 0 < t -> in_poly p (expand_poly t (simplify_poly n pol)) = in_poly p (expand_poly t pol).
  Proof.
    induction n.
    - intros; simpl; reflexivity.
    - intros pol p t Ht. simpl.
      set (nz := filter (fun c => negb (nth n (fst c) 0 =? 0)) pol).
      set (z := filter (fun c => nth n (fst c) 0 =? 0) pol).
      transitivity (in_poly p (expand_poly t nz) && in_poly p (expand_poly t z)).
      + destruct (find_eq n nz) as [c|] eqn:Hfindeq.
        * unfold in_poly in *. simpl. rewrite IHn; auto. rewrite andb_assoc.
          replace (satisfies_constraint p (mult_constraint_cst t c) &&
                   satisfies_constraint p (mult_constraint_cst t (mult_constraint (-1) c))) with
              (dot_product p (fst c) =? t * snd c)
            by (unfold satisfies_constraint, mult_constraint; simpl; rewrite eq_iff_eq_true, dot_product_mult_right; reflect; lia).
          assert (Hcnth : nth n (fst c) 0 <> 0) by (apply find_eq_nth in Hfindeq; lia).
          destruct (dot_product p (fst c) =? t * snd c) eqn:Heq; simpl; reflect.
          -- unfold expand_poly.
             rewrite map_app, forallb_app, map_map, !forallb_map. f_equal. apply forallb_ext.
             intros c1. rewrite make_constraint_with_eq_correct; auto.
          -- destruct (forallb (satisfies_constraint p) (expand_poly t nz)) eqn:Hin; simpl; [|reflexivity]. exfalso; apply Heq.
             unfold expand_poly in Hin. rewrite forallb_map, forallb_forall in Hin.
             eapply find_eq_correct; eauto.
        * rewrite expand_poly_app, in_poly_app. rewrite IHn by auto. reflexivity.
      + rewrite eq_iff_eq_true. reflect. unfold expand_poly, in_poly, nz, z; rewrite !forallb_map, !forallb_forall.
        split.
       * intros [H1 H2] c Hc; specialize (H1 c); specialize (H2 c).
         rewrite filter_In in H1, H2. destruct (nth n (fst c) 0 =? 0); auto.
       * intros H. split; intros c Hcin; rewrite filter_In in Hcin; apply H; tauto.
  Qed.


  Lemma simplify_poly_preserve_zeros :
    forall n m pol, (forall c, In c pol -> nth m (fst c) 0 = 0) -> (forall c, In c (simplify_poly n pol) -> nth m (fst c) 0 = 0).
  Proof.
    induction n.
    - intros; auto.
    - intros m pol H c Hc.
      simpl in Hc.
      set (nz := filter (fun c => negb (nth n (fst c) 0 =? 0)) pol) in *.
      set (z := filter (fun c => nth n (fst c) 0 =? 0) pol) in *.
      destruct (find_eq n nz) as [c1|] eqn:Hfindeq.
      + simpl in Hc.
        assert (Hc1 : nth m (fst c1) 0 = 0) by (apply find_eq_in in Hfindeq; apply H; unfold nz in Hfindeq; rewrite filter_In in Hfindeq; tauto).
        destruct Hc as [Hc | [Hc | Hc]];
          [rewrite <- Hc; auto | rewrite <- Hc; unfold mult_constraint; simpl; rewrite mult_nth; lia|].
        eapply IHn; [|apply Hc].
        intros c2 Hin2; rewrite in_app_iff, in_map_iff in Hin2.
        destruct Hin2 as [[c3 [Heq2 Hin3]] | Hin2]; [|apply H; unfold z in Hin2; rewrite filter_In in Hin2; tauto].
        rewrite <- Heq2, make_constraint_with_eq_preserve_zeros; auto. apply H.
        unfold nz in Hin3; rewrite filter_In in Hin3; tauto.
      + rewrite in_app_iff in Hc.
        destruct Hc as [Hc | Hc]; [apply H; unfold nz in Hc; rewrite filter_In in Hc; tauto|].
        eapply IHn; [|apply Hc]. intros c1 Hc1; apply H; unfold z in Hc1; rewrite filter_In in Hc1; tauto.
  Qed.

  Definition project (np : nat * polyhedron) : imp polyhedron :=
    let (n, p) := np in
    let k := poly_nrl p in
    BIND r <- do_project n (k - n)%nat p -; pure (simplify_poly n r).

  Lemma project_in_iff :
    forall s n p pol, 0 < s -> WHEN proj <- project (n, pol) THEN
                              in_poly p (expand_poly s proj) = true <->
                         exists t m, 0 < t /\ in_poly (resize n (mult_vector t p) ++ m) (expand_poly (s * t) pol) = true.
  Proof.
    intros s n p pol Hs proj Hproj.
    unfold project in Hproj.
    bind_imp_destruct Hproj r Hr; apply mayReturn_pure in Hproj; rewrite <- Hproj in *.
    rewrite simplify_poly_correct by auto.
    remember (poly_nrl pol) as u.
    rewrite (do_project_in_iff _ _ _ _ _ Hs _ Hr).
    split.
    - intros [t [m [Hmlen [Ht Hin]]]]; exists t. exists m. split; [auto|].
      rewrite <- in_poly_nrlength with (n := u) in Hin by (rewrite expand_poly_nrl; nia).
      rewrite <- in_poly_nrlength with (n := u) by (rewrite expand_poly_nrl; nia).
      rewrite app_assoc in Hin. rewrite resize_app_ge in Hin; [exact Hin|].
      rewrite app_length, resize_length, Hmlen. lia.
    - intros [t [m [Ht Hin]]]; exists t. exists (resize (u - n)%nat m).
      split; [apply resize_length|]. split; [auto|].
      rewrite <- in_poly_nrlength with (n := u) in Hin by (rewrite expand_poly_nrl; nia).
      rewrite <- in_poly_nrlength with (n := u) by (rewrite expand_poly_nrl; nia).
      rewrite app_assoc, resize_app_ge by (rewrite app_length, !resize_length; lia).
      destruct (u <=? n)%nat eqn:Hun; reflect.
      + rewrite resize_app_ge in * by (rewrite resize_length; lia). exact Hin.
      + rewrite resize_app_le in * by (rewrite resize_length; lia). rewrite !resize_length in *.
        rewrite resize_resize; [exact Hin|lia].
  Qed.

  Lemma project_in_iff1 :
    forall n p pol, WHEN proj <- project (n, pol) THEN
                    in_poly p proj = true <->
               exists t m, 0 < t /\ in_poly (resize n (mult_vector t p) ++ m) (expand_poly t pol) = true.
  Proof.
    intros n p pol proj Hproj.
    rewrite <- expand_poly_1 with (p := proj).
    assert (H01 : 0 < 1) by lia.
    rewrite (project_in_iff _ _ _ _ H01 _ Hproj). apply exists_ext. intros t.
    destruct t; reflexivity.
  Qed.

  Theorem project_inclusion :
    forall n p pol, in_poly p pol = true -> WHEN proj <- project (n, pol) THEN in_poly (resize n p) proj = true.
  Proof.
    intros n p pol Hp proj Hproj.
    rewrite (project_in_iff1 _ _ _ _ Hproj). exists 1. exists (skipn n p).
    split; [lia|].
    rewrite mult_vector_1, resize_resize, resize_skipn_eq, expand_poly_1 by lia.
    auto.
  Qed.

  Definition project_invariant n p v :=
    exists t m, 0 < t /\ in_poly (resize n (mult_vector t v) ++ m) (expand_poly t p) = true.

  Theorem project_invariant_inclusion :
    forall n pol p, in_poly p pol = true -> project_invariant n pol (resize n p).
  Proof.
    intros n pol p H.
    exists 1. exists (skipn n p).
    split; [lia|].
    rewrite mult_vector_1, resize_resize, resize_skipn_eq, expand_poly_1 by lia.
    auto.
  Qed.

  Theorem project_id :
    forall n pol p, (forall c, In c pol -> fst c =v= resize n (fst c)) -> project_invariant n pol p -> in_poly p pol = true.
  Proof.
    intros n pol p Hclen Hinv. rewrite poly_nrl_def in Hclen.
    destruct Hinv as [t [m [Ht Hinv]]].
    rewrite <- in_poly_nrlength with (n := n) in Hinv by (rewrite expand_poly_nrl; auto; lia).
    rewrite resize_app in Hinv by (apply resize_length).
    rewrite in_poly_nrlength in Hinv by (rewrite expand_poly_nrl; auto; lia).
    rewrite expand_poly_eq in Hinv; auto.
  Qed.

  Theorem project_invariant_resize :
    forall n pol p, project_invariant n pol p <-> project_invariant n pol (resize n p).
  Proof.
    intros n pol p. unfold project_invariant.
    apply exists_ext. intros t.
    rewrite <- mult_vector_resize. rewrite resize_resize by lia.
    reflexivity.
  Qed.

  Lemma do_project_no_new_var :
    forall k d pol n, (forall c, In c pol -> nth n (fst c) 0 = 0) -> WHEN proj <- do_project d k pol THEN (forall c, In c proj -> nth n (fst c) 0 = 0).
  Proof.
    induction k.
    - intros; simpl in *. xasimplify eauto.
    - intros; simpl in *. xasimplify eauto.
      generalize (Proj.project_no_new_var _ _ _ H _ Hexta). intros H1.
      generalize (Canon.canonize_no_new_var _ _ H1 _ Hexta0). intros H2.
      apply (IHk _ _ _ H2 _ Hexta1).
  Qed.

  Lemma do_project_constraints :
    forall k d pol n, (d <= n < d + k)%nat -> WHEN proj <- do_project d k pol THEN (forall c, In c proj -> nth n (fst c) 0 = 0).
  Proof.
    induction k.
    - intros; lia.
    - intros d pol n Hn proj Hproj.
      simpl in Hproj.
      bind_imp_destruct Hproj proja Hproja.
      bind_imp_destruct Hproj canon Hcanon.
      destruct (n =? d + k)%nat eqn:Heqn; reflect.
      + rewrite Heqn. generalize (Proj.project_projected _ _ _ Hproja). intros H1.
        generalize (Canon.canonize_no_new_var _ _ H1 _ Hcanon). intros H2.
        apply (do_project_no_new_var _ _ _ _ H2 _ Hproj).
      + assert (H : (d <= n < d + k)%nat) by lia.
        apply (IHk _ _ _ H _ Hproj).
  Qed.

  Theorem project_constraint_size :
    forall n pol c, WHEN proj <- project (n, pol) THEN In c proj -> fst c =v= resize n (fst c).
  Proof.
    intros n pol c proj Hproj Hin.
    apply vector_nth_veq.
    unfold project in Hproj.
    bind_imp_destruct Hproj r Hr; apply mayReturn_pure in Hproj; rewrite <- Hproj in *.
    intros k.
    rewrite nth_resize.
    destruct (k <? n)%nat eqn:Hkn; reflect; [reflexivity|].
    assert (Hcr : forall c1, In c1 r -> nth k (fst c1) 0 = 0).
    - intros c1 Hin1.
      destruct (k <? n + (poly_nrl pol - n))%nat eqn:Hkrl; reflect.
      + apply (do_project_constraints _ _ _ _ (conj Hkn Hkrl) _ Hr); auto.
      +  assert (Hnrl : (poly_nrl pol <= k)%nat) by lia.
         rewrite <- poly_nrl_def in Hnrl.
         assert (H : forall c, In c pol -> nth k (fst c) 0 = 0).
         * intros c2 Hin2; specialize (Hnrl c2 Hin2).
           apply nth_eq with (n := k) in Hnrl. rewrite nth_resize in Hnrl. destruct (k <? k)%nat eqn:Hkk; reflect; lia.
         * apply (do_project_no_new_var _ _ _ _  H _ Hr _ Hin1).
    - eapply simplify_poly_preserve_zeros; eauto.
  Qed.

  Theorem project_next_r_inclusion :
    forall n pol p, project_invariant n pol p ->
               WHEN proj <- project (S n, pol) THEN
               (forall c, In c proj -> nth n (fst c) 0 <> 0 -> satisfies_constraint p c = true) ->
               project_invariant (S n) pol p.
  Proof.
    intros n pol p Hinv proj Hproj Hsat.
    destruct Hinv as [t [m [Ht Hinv]]].
    apply (project_in_iff1 _ _ _ _ Hproj).
    unfold in_poly. rewrite forallb_forall. intros c Hinproj.
    destruct (nth n (fst c) 0 =? 0) eqn:Hzero; reflect; [|apply Hsat; auto].
    unfold project_invariant in Hinv.
    rewrite <- resize_skipn_eq with (d := 1%nat) (l := m) in Hinv.
    rewrite app_assoc in Hinv.
    assert (H : in_poly (resize n (mult_vector t p) ++ resize 1 m) (expand_poly t proj) = true).
    - rewrite (project_in_iff _ _ _ _ Ht _ Hproj). exists 1. exists (skipn 1%nat m).
      split; [lia|]. rewrite mult_vector_1. rewrite resize_length_eq by (rewrite app_length, !resize_length; lia).
      rewrite Z.mul_1_r; apply Hinv.
    - unfold in_poly in H. rewrite forallb_forall in H.
      rewrite <- mult_constraint_cst_eq with (k := t) by auto.
      specialize (H (mult_constraint_cst t c)).
      generalize (project_constraint_size _ _ _ _ Hproj Hinproj); intros Hsize.
      rewrite resize_succ, Hzero in Hsize.
      setoid_replace (0 :: nil) with (@nil Z) using relation veq in Hsize by (rewrite <- is_eq_veq; reflexivity).
      rewrite app_nil_r in Hsize. symmetry in Hsize; rewrite nrlength_def in Hsize.
      replace (fst c) with (fst (mult_constraint_cst t c)) in Hsize by reflexivity.
      rewrite <- satisfies_constraint_nrlength with (n := n) in H by auto.
      rewrite <- satisfies_constraint_nrlength with (n := n) by auto.
      rewrite resize_app in H by (apply resize_length). apply H.
      unfold expand_poly. apply in_map. auto.
  Qed.

  Definition project_invariant_export (np : nat * polyhedron) : imp polyhedron :=
    project np.

  Theorem project_invariant_export_correct :
    forall n p pol, WHEN res <- project_invariant_export (n, pol) THEN in_poly p res = true <-> project_invariant n pol p.
  Proof.
    intros n p pol proj Hproj.
    apply (project_in_iff1 _ _ _ _ Hproj).
  Qed.

End PolyProjectImpl.

Module CoreAlarmed := AlarmImpureMonad Vpl.ImpureConfig.Core.
Import CoreAlarmed.

Ltac bind_imp_destruct H id1 id2 :=
  apply mayReturn_bind in H; destruct H as [id1 [id2 H]].

Module VplCanonizer <: PolyCanonizer CoreAlarmed.

  Definition check_not_new n (l1 l2 : polyhedron) :=
    (negb (forallb (fun c => nth n (fst c) 0 =? 0) l1)) || (forallb (fun c => nth n (fst c) 0 =? 0) l2).

  Lemma check_not_new_correct :
    forall n l1 l2, check_not_new n l1 l2 = true -> (forall c, In c l1 -> nth n (fst c) 0 = 0) -> (forall c, In c l2 -> nth n (fst c) 0 = 0).
  Proof.
    intros n l1 l2 H1 H2 c Hc.
    unfold check_not_new in H1. reflect. destruct H1 as [H1 | H1].
    - exfalso. eapply eq_true_false_abs; [|exact H1].
      rewrite forallb_forall. intros c1; specialize (H2 c1). reflect; auto.
    - rewrite forallb_forall in H1. specialize (H1 c). reflect; auto.
  Qed.

  Definition check_no_new_vars l1 l2 :=
    let n := poly_nrl l2 in
    forallb (fun n => check_not_new n l1 l2) (n_range n).

  Lemma check_no_new_vars_correct :
    forall n l1 l2, check_no_new_vars l1 l2 = true -> (forall c, In c l1 -> nth n (fst c) 0 = 0) -> (forall c, In c l2 -> nth n (fst c) 0 = 0).
  Proof.
    intros n l1 l2 H.
    destruct (n <? poly_nrl l2)%nat eqn:Hn; reflect.
    - apply check_not_new_correct.
      unfold check_no_new_vars in H. rewrite forallb_forall in H.
      apply H. rewrite n_range_in. auto.
    - intros H1 c Hc. rewrite <- poly_nrl_def in Hn. specialize (Hn c Hc).
      eapply nth_eq in Hn; rewrite Hn. rewrite nth_resize.
      destruct (n <? n)%nat eqn:Hn2; reflect; auto; lia.
  Qed.

  Definition canonize l :=
    BIND r <- lift (canonize_Cs (poly_to_Cs l)) -;
    pure match Cs_to_poly_Q r with
    | None => l
    | Some l2 =>
        if check_no_new_vars l l2 then l2 else l
  end.

  Lemma canonize_correct :
    forall p, WHEN r <- canonize p THEN (forall k v, 0 < k -> in_poly v (expand_poly k r) = in_poly v (expand_poly k p)).
  Proof.
    intros l l2 Hl2 k v Hk.
    unfold canonize in Hl2. bind_imp_destruct Hl2 r Hr.
    apply mayReturn_lift in Hr. apply mayReturn_pure in Hl2.
    destruct (Cs_to_poly_Q r) as [u|] eqn:Hu; [|congruence].
    destruct (check_no_new_vars l u); [|congruence].
    apply eq_iff_eq_true.
    rewrite <- poly_to_Cs_correct_Q with (p := l) by auto.
    rewrite (canonize_Cs_correct _ _ Hr _).
    rewrite (Cs_to_poly_Q_correct _ _ _ _ Hk Hu).
    rewrite Hl2. reflexivity.
  Qed.

  Lemma canonize_no_new_var :
    forall k p, (forall c, In c p -> nth k (fst c) 0 = 0) -> WHEN r <- canonize p THEN (forall c, In c r -> nth k (fst c) 0 = 0).
  Proof.
    intros k l H l2 Hl2.
    unfold canonize in Hl2. bind_imp_destruct Hl2 r Hr. apply mayReturn_pure in Hl2.
    destruct (Cs_to_poly_Q r) as [u|]; [|rewrite <- Hl2; auto].
    destruct (check_no_new_vars l u) eqn:Hchk; [|rewrite <- Hl2; auto].
    rewrite <- Hl2. eapply check_no_new_vars_correct; eauto.
  Qed.

End VplCanonizer.

Module VplCanonizerZ.

  Definition canonize_constraint_Z (c : list Z * Z) :=
    let g := list_gcd (fst c) in
    if (g =? 0) then c
    else (map (fun x => x / g) (fst c), (snd c / g)).

  Lemma canonize_constraint_Z_correct :
    forall c p, satisfies_constraint p (canonize_constraint_Z c) = satisfies_constraint p c.
  Proof.
    intros c p. unfold canonize_constraint_Z.
    remember (list_gcd (fst c)) as g. destruct (g =? 0) eqn:Hg; auto.
    reflect. unfold satisfies_constraint; rewrite eq_iff_eq_true; reflect.
    assert (Hpos : 0 < g) by (generalize (list_gcd_nonneg (fst c)); lia).
    simpl.
    rewrite div_ge_iff by auto. f_equiv.
    rewrite <- Z.mul_comm, <- dot_product_mult_right. f_equal.
    unfold mult_vector. rewrite map_map.
    erewrite map_ext_in; [apply map_id|]. intros x Hx. simpl.
    symmetry; apply Znumtheory.Zdivide_Zdiv_eq; [auto|].
    rewrite Heqg; apply list_gcd_div. auto.
  Qed.

  Lemma canonize_constraint_Z_no_new_var :
    forall k c, nth k (fst c) 0 = 0 -> nth k (fst (canonize_constraint_Z c)) 0 = 0.
  Proof.
    intros k c H. unfold canonize_constraint_Z.
    destruct (list_gcd (fst c) =? 0); auto. simpl.
    transitivity (nth k (fst c) 0 / (list_gcd (fst c))).
    - rewrite <- map_nth with (f := fun x => x / list_gcd (fst c)). auto.
    - rewrite H. auto.
  Qed.

  Definition canonize l :=
    BIND r <- VplCanonizer.canonize (map canonize_constraint_Z l) -;
    pure (map canonize_constraint_Z r).

  Lemma canonize_correct :
    forall p, WHEN r <- canonize p THEN (forall v, in_poly v r = in_poly v p).
  Proof.
    intros l l2 Hl2 v.
    unfold canonize in Hl2. bind_imp_destruct Hl2 r Hr.
    apply mayReturn_pure in Hl2. apply VplCanonizer.canonize_correct in Hr.
    specialize (Hr 1 v). rewrite !expand_poly_1 in Hr.
    rewrite <- Hl2. unfold in_poly in *. rewrite forallb_map in *.
    erewrite forallb_ext; [|intros; rewrite canonize_constraint_Z_correct; reflexivity].
    rewrite Hr by lia.
    apply forallb_ext. intros; apply canonize_constraint_Z_correct.
  Qed.

  Lemma canonize_no_new_var :
    forall k p, (forall c, In c p -> nth k (fst c) 0 = 0) -> WHEN r <- canonize p THEN (forall c, In c r -> nth k (fst c) 0 = 0).
  Proof.
    intros k l H l2 Hl2.
    unfold canonize in Hl2. bind_imp_destruct Hl2 r Hr. apply mayReturn_pure in Hl2.
    apply VplCanonizer.canonize_no_new_var with (k := k) in Hr.
    - intros c Hc. rewrite <- Hl2 in Hc. rewrite in_map_iff in Hc.
      destruct Hc as [c1 [Hc1 Hin1]]; rewrite <- Hc1; apply canonize_constraint_Z_no_new_var; auto.
    - intros c Hc; rewrite in_map_iff in Hc.
      destruct Hc as [c1 [Hc1 Hin1]]; rewrite <- Hc1; apply canonize_constraint_Z_no_new_var; auto.
  Qed.

End VplCanonizerZ.

Definition neg_constraint c :=
  (mult_vector (-1) (fst c), -snd c - 1).
Lemma neg_constraint_correct :
  forall p c, satisfies_constraint p (neg_constraint c) = negb (satisfies_constraint p c).
Proof.
  intros p c. unfold satisfies_constraint.
  apply eq_iff_eq_true. reflect. unfold neg_constraint.
  simpl. rewrite dot_product_mult_right. lia.
Qed.

Fixpoint poly_difference p1 p2 :=
  match p2 with
  | nil => nil
  | c :: p2 => (neg_constraint c :: p1) :: poly_difference (c :: p1) p2
  end.

Lemma poly_difference_def :
  forall p2 p1 v, existsb (in_poly v) (poly_difference p1 p2) =
             in_poly v p1 && negb (in_poly v p2).
Proof.
  induction p2.
  - intros p1 v. simpl. destruct in_poly; auto.
  - intros p1 v. simpl. rewrite IHp2.
    rewrite neg_constraint_correct; unfold in_poly; simpl.
    destruct (satisfies_constraint v a); simpl.
    + reflexivity.
    + destruct forallb; reflexivity.
Qed.

Definition poly_disjoint pol1 pol2 := forall p, in_poly p pol1 = false \/ in_poly p pol2 = false.

Fixpoint all_disjoint (l : list polyhedron) :=
  match l with
  | nil => True
  | p :: l => (forall p2, In p2 l -> poly_disjoint p p2) /\ all_disjoint l
  end.

Lemma poly_difference_disjoint :
  forall p2 p1, all_disjoint (poly_difference p1 p2).
Proof.
  induction p2.
  - intros; simpl; auto.
  - intros p1. simpl. split; [|apply IHp2].
    intros p Hp. unfold poly_disjoint.
    intros v. unfold in_poly. simpl.
    rewrite neg_constraint_correct.
    destruct (satisfies_constraint v a) eqn:Hsat; simpl.
    + left; reflexivity.
    + right. generalize (poly_difference_def p2 (a :: p1) v).
      simpl; rewrite Hsat, existsb_forall; unfold in_poly; simpl.
      intros Hdef; apply Hdef. auto.
Qed.

Definition isBottom pol :=
  BIND p <- lift (ExactCs.fromCs_unchecked (poly_to_Cs pol)) -; lift (CstrDomain.isBottom p).

Lemma isBottom_correct :
  forall pol t, 0 < t -> If isBottom pol THEN forall p, in_poly p (expand_poly t pol) = false.
Proof.
  intros pol t Ht b Hbot.
  destruct b; simpl; [|auto]. intros p.
  unfold isBottom in Hbot.
  apply mayReturn_bind in Hbot; destruct Hbot as [p1 [Hp1 Hbot]].
  apply mayReturn_lift in Hp1; apply mayReturn_lift in Hbot.
  apply CstrDomain.isBottom_correct in Hbot; simpl in Hbot.
  apply ExactCs.fromCs_unchecked_correct in Hp1.
  apply not_true_is_false; intros Hin.
  rewrite <- poly_to_Cs_correct_Q in Hin by auto.
  eauto.
Qed.

Lemma isBottom_correct_1 :
  forall pol, If isBottom pol THEN forall p, in_poly p pol = false.
Proof.
  intros pol. generalize (isBottom_correct pol 1).
  rewrite expand_poly_1. intros H; apply H; lia.
Qed.

(*
Definition canPrecede n (pol1 proj1 pol2 proj2 : polyhedron) :=
  let g1 := filter (fun c => 0 <? nth n (fst c) 0) pol1 in
  let g2 := filter (fun c => nth n (fst c) 0 <? 0) pol2 in
  isBottom (proj1 ++ proj2 ++ g1 ++ g2).

Lemma canPrecede_correct :
  forall n pol1 proj1 pol2 proj2,
    isExactProjection n pol1 proj1 -> isExactProjection n pol2 proj2 ->
    If canPrecede n pol1 proj1 pol2 proj2 THEN
       forall p1 x, in_poly p1 pol1 = true -> in_poly (assign n x p1) pol2 = true -> nth n p1 0 < x.
Proof.
  intros n pol1 proj1 pol2 proj2 Hproj1 Hproj2 b Hprec.
  destruct b; simpl; [|auto].
  intros p1 x Hp1 Hpx.
  unfold canPrecede in Hprec. apply isBottom_correct_1 in Hprec; simpl in Hprec.
  specialize (Hprec p1). rewrite !in_poly_app in Hprec. reflect.
  apply isExactProjection_weaken1 in Hproj1. eapply isExactProjection_assign_1 in Hproj1; [|exact Hp1].
  rewrite assign_id in Hproj1. rewrite Hproj1 in Hprec.
  apply isExactProjection_weaken1 in Hproj2. eapply isExactProjection_assign_1 in Hproj2; [|exact Hpx].
  rewrite assign_assign, assign_id in Hproj2. rewrite Hproj2 in Hprec.
  destruct Hprec as [? | [? | [Hprec | Hprec]]]; try congruence.
  - exfalso; eapply eq_true_false_abs; [|exact Hprec].
    unfold in_poly in *; rewrite forallb_forall in *.
    intros c. rewrite filter_In. intros; apply Hp1; tauto.
  - assert (Hin : in_poly (assign n x p1) (filter (fun c => nth n (fst c) 0 <? 0) pol2) = true).
    + unfold in_poly in *; rewrite forallb_forall in *.
      intros c. rewrite filter_In. intros; apply Hpx; tauto.
    + rewrite <- Z.nle_gt. intros Hle.
      eapply eq_true_false_abs; [|exact Hprec].
      unfold in_poly in *; rewrite forallb_forall in *.
      intros c. rewrite filter_In. intros Hc.
      specialize (Hin c). rewrite filter_In in Hin. specialize (Hin Hc).
      destruct Hc as [Hcin Hc].
      unfold satisfies_constraint in *. reflect. rewrite dot_product_assign_left in Hin.
      nia.
Qed.
*)

Definition canPrecede n (pol1 pol2 proj2 : polyhedron) :=
  let g2 := filter (fun c => nth n (fst c) 0 <? 0) pol2 in
  isBottom (pol1 ++ proj2 ++ g2).

Lemma canPrecede_correct :
  forall n pol1 pol2 proj2,
    isExactProjection n pol2 proj2 ->
    If canPrecede n pol1 pol2 proj2 THEN
       forall p1 x, in_poly p1 pol1 = true -> in_poly (assign n x p1) pol2 = true -> nth n p1 0 < x.
Proof.
  intros n pol1 pol2 proj2 Hproj2 b Hprec.
  destruct b; simpl; [|auto].
  intros p1 x Hp1 Hpx.
  unfold canPrecede in Hprec. apply isBottom_correct_1 in Hprec; simpl in Hprec.
  specialize (Hprec p1). rewrite !in_poly_app in Hprec. reflect.
  rewrite Hp1 in Hprec.
  apply isExactProjection_weaken1 in Hproj2. eapply isExactProjection_assign_1 in Hproj2; [|exact Hpx].
  rewrite assign_assign, assign_id in Hproj2. rewrite Hproj2 in Hprec.
  destruct Hprec as [? | [? | Hprec]]; try congruence.
  assert (Hin : in_poly (assign n x p1) (filter (fun c => nth n (fst c) 0 <? 0) pol2) = true).
  - unfold in_poly in *; rewrite forallb_forall in *.
    intros c. rewrite filter_In. intros; apply Hpx; tauto.
  - rewrite <- Z.nle_gt. intros Hle.
    eapply eq_true_false_abs; [|exact Hprec].
    unfold in_poly in *; rewrite forallb_forall in *.
    intros c. rewrite filter_In. intros Hc.
    specialize (Hin c). rewrite filter_In in Hin. specialize (Hin Hc).
    destruct Hc as [Hcin Hc].
    unfold satisfies_constraint in *. reflect. rewrite dot_product_assign_left in Hin.
    nia.
Qed.

Module Proj := FourierMotzkinProject CoreAlarmed.
(* Module Canon := NaiveCanonizer CoreAlarmed. *)
Module Canon := VplCanonizer.
Module PO := PolyProjectImpl CoreAlarmed Canon Proj.
Import PO.

Global Opaque project.

(** * Generating the code *)

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

Definition make_affine_test n c := make_le (make_linear_expr n (fst c)) (Constant (snd c)).

Lemma make_affine_test_correct :
  forall env n c, length env = n -> eval_test env (make_affine_test n c) = satisfies_constraint (rev env) c.
Proof.
  intros. simpl in *. unfold make_affine_test. rewrite make_le_correct, make_linear_expr_correct; auto.
  rewrite dot_product_commutative. reflexivity.
Qed.

Fixpoint sequence {A : Type} (l : list (imp A)) : imp (list A) :=
  match l with
  | nil => pure nil
  | x :: l => BIND y <- x -; BIND l1 <- sequence l -; pure (y :: l1)
  end.

Definition fmap {A B : Type} (f : A -> B) (x : imp A) : imp B :=
  BIND y <- x -; pure (f y).

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
             (loop_semantics st env mem1 mem2 <-> iter_semantics (fun x => loop_semantics inner (x :: env)) lb ub mem1 mem2) /\
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
        -- intros Hsem. rewrite make_guard_correct, Htest1. inversion_clear Hsem; [|lia]. reflexivity.
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
        -- intros H; inversion_clear H; [auto|lia].
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
  induction pstmt.
  - intros n env mem1 mem2 st Hst Hsem Henv.
    simpl in *. bind_imp_destruct Hst inner Hinner.
    generalize (scan_dimension_sem _ _ _ _ Hst _ mem1 mem2 Henv).
    intros [lb [ub [H1 H2]]].
    econstructor; [exact H2|]. rewrite H1 in Hsem.
    eapply iter_semantics_map; [|exact Hsem].
    intros x mem3 mem4 Hx Hsem2. simpl in Hsem2. eapply IHpstmt; simpl; eauto.
  - intros n env mem1 mem2 st Hst Hsem Henv.
    simpl in *. apply mayReturn_pure in Hst. rewrite <- Hst in *.
    inversion_clear Hsem. constructor.
    rewrite map_map in H.
    unfold eval_affine_expr. erewrite map_ext; [exact H|].
    intros [k a]; simpl. rewrite make_div_correct, make_affine_expr_correct by auto. reflexivity.
  - intros n env mem1 mem2 st Hst Hsem Henv.
    simpl in *. apply mayReturn_pure in Hst; rewrite <- Hst in *.
    inversion_clear Hsem. econstructor; auto.
  - intros n env mem1 mem2 st Hst Hsem Henv.
    simpl in *.
    bind_imp_destruct Hst u1 Hu1. bind_imp_destruct Hst u2 Hu2.
    apply mayReturn_pure in Hst; rewrite <- Hst in *.
    inversion_clear Hsem; inversion_clear H0. replace mem2 with mem4 by (inversion_clear H2; auto).
    econstructor; [eapply IHpstmt1|eapply IHpstmt2]; eauto.
  - intros n env mem1 mem2 st Hst Hsem Henv.
    simpl in *. bind_imp_destruct Hst inner Hinner. apply mayReturn_pure in Hst; rewrite <- Hst in *.
    rewrite make_guard_correct in Hsem.
    rewrite make_poly_test_correct in Hsem by auto.
    destruct (in_poly (rev env) p) eqn:Htest.
    + apply PLGuardTrue; [|auto]. eapply IHpstmt; eauto.
    + rewrite Hsem; apply PLGuardFalse; auto.
Qed.

Fixpoint generate_loop (d : nat) (n : nat) (pi : Polyhedral_Instruction) : imp poly_stmt :=
  match d with
  | O => pure (PInstr pi.(pi_instr) (map (fun t => (1%positive, t)) pi.(pi_transformation)))
  | S d1 =>
    BIND proj <- project ((n - d1)%nat, pi.(pi_poly)) -;
    BIND inner <- generate_loop d1 n pi -;
    pure (PLoop (filter (fun c => negb (nth (n - d)%nat (fst c) 0 =? 0)) proj) inner)
  end.

Lemma env_scan_begin :
  forall polys env n p m, env_scan polys env n m p = true -> p =v= env ++ skipn (length env) p.
Proof.
  intros polys env n p m Hscan. unfold env_scan in Hscan. destruct (nth_error polys m); [|congruence].
  reflect. destruct Hscan as [[Heq1 Heq2] Heq3].
  apply same_length_eq in Heq1; [|rewrite resize_length; auto].
  rewrite Heq1 at 1.
  rewrite resize_skipn_eq; reflexivity.
Qed.
  
Lemma env_scan_single :
  forall polys env n p m, length env = n -> env_scan polys env n m p = true -> env =v= p.
Proof.
  intros polys env n p m Hlen Hscan.
  unfold env_scan in Hscan. destruct (nth_error polys m); [|congruence].
  reflect. destruct Hscan as [[Heq1 Heq2] Heq3]. rewrite Hlen in Heq1.
  rewrite Heq1. symmetry. auto.
Qed.

Lemma env_scan_split :
  forall polys env n p m, (length env < n)%nat -> env_scan polys env n m p = true <-> (exists x, env_scan polys (env ++ (x :: nil)) n m p = true).
Proof.
  intros polys env n p m Hlen.
  unfold env_scan. destruct (nth_error polys m); simpl; [|split; [intros; congruence|intros [x Hx]; auto]].
  split.
  - intros H. exists (nth (length env) p 0).
    reflect. destruct H as [[H1 H2] H3].
    split; [split|]; auto.
    rewrite app_length. simpl. rewrite <- resize_skipn_eq with (l := p) (d := length env) at 2.
    rewrite resize_app_le by (rewrite resize_length; lia).
    rewrite resize_length. rewrite <- is_eq_veq.
    rewrite is_eq_app by (rewrite resize_length; auto).
    reflect; split; auto.
    replace (length env + 1 - length env)%nat with 1%nat by lia.
    simpl. transitivity (nth 0 (skipn (length env) p) 0 :: nil).
    + rewrite nth_skipn. rewrite Nat.add_0_r. reflexivity.
    + destruct (skipn (length env) p); simpl; reflexivity.
  - intros [x Hx]. reflect. destruct Hx as [[H1 H2] H3].
    + split; [split|]; auto.
      rewrite app_length in H1. simpl in H1.
      rewrite <- is_eq_veq in H1. rewrite is_eq_app_left in H1.
      reflect; destruct H1 as [H1 H4]. rewrite resize_resize in H1 by lia. assumption.
Qed.

Lemma generate_loop_single_point :
  forall n pi env mem1 mem2,
    WHEN st <- generate_loop 0%nat n pi THEN
    poly_loop_semantics st env mem1 mem2 ->
    length env = n ->
    in_poly (rev env) pi.(pi_poly) = true ->
    env_poly_lex_semantics (rev env) n (pi :: nil) mem1 mem2.
Proof.
  intros n pi env mem1 mem2 st Hgen Hsem Hlen Henvsat. simpl in *.
  apply mayReturn_pure in Hgen.
  unfold env_poly_lex_semantics.
  eapply PolyLexProgress with (n := 0%nat) (p := rev env); [ |reflexivity| | | apply PolyLexDone].
  - unfold env_scan. simpl. reflect. split; [split|].
    + rewrite resize_eq; reflexivity.
    + rewrite resize_eq; [reflexivity | rewrite rev_length; lia].
    + auto.
  - intros n2 p2 Hcmp. apply not_true_iff_false; intros H.
    apply env_scan_single in H; [|rewrite rev_length; auto].
    rewrite H in Hcmp. rewrite lex_compare_reflexive in Hcmp. congruence.
  - rewrite <- Hgen in Hsem. inversion_clear Hsem.
    unfold affine_product in *. rewrite map_map in H.
    erewrite map_ext in H; [exact H|].
    intros; unfold eval_affine_expr; simpl. apply Z.div_1_r.
  - intros n1 p1. unfold scanned.
    destruct n1 as [|n1]; [|destruct n1; simpl; auto]. simpl.
    apply not_true_iff_false; intros H; reflect; destruct H as [H1 H2].
    apply env_scan_single in H1; [|rewrite rev_length; lia].
    rewrite H1 in H2; rewrite is_eq_reflexive in H2.
    destruct H2; congruence.
Qed.

Lemma env_scan_extend :
  forall d n pi lb ub env m p,
    length env = n ->
    (n < d)%nat ->
    WHEN proj <- project (S n, pi.(pi_poly)) THEN
    (forall x, (forall c, In c proj -> nth n (fst c) 0 <> 0 -> satisfies_constraint (rev (x :: env)) c = true) <-> lb <= x < ub) ->
    env_scan (pi :: nil) (rev env) d m p =
      existsb (fun x : Z => env_scan (pi :: nil) (rev env ++ x :: nil) d m p) (Zrange lb ub).
Proof.
  intros d n pi lb ub env m p Hlen Hnd proj Hproj Hlbub.
  rewrite eq_iff_eq_true. rewrite existsb_exists.
  rewrite env_scan_split by (rewrite rev_length; lia).
  split.
  - intros [x Hscan]; exists x; split; [|auto].
    rewrite Zrange_in. unfold env_scan in Hscan. destruct m; [|destruct m; simpl in Hscan; try congruence].
    simpl in Hscan. reflect.
    destruct Hscan as [[Hscan1 Hscan2] Hscan3].
    assert (Hinproj : in_poly (rev env ++ x :: nil) proj = true).
    {
      rewrite Hscan1. eapply project_inclusion; [apply Hscan3|].
      rewrite app_length; rewrite rev_length; rewrite Hlen; unfold length.
      replace (n + 1)%nat with (S n) by lia. apply Hproj.
    }
    rewrite <- Hlbub by eauto.
    unfold in_poly in Hinproj. rewrite forallb_forall in Hinproj.
    intros; auto.
  - intros [x [H1 H2]]; exists x; assumption.
Qed.

Lemma env_scan_inj_nth :
  forall pis env1 env2 n m p s, length env1 = length env2 -> (s < length env1)%nat ->
                           env_scan pis env1 n m p = true -> env_scan pis env2 n m p = true -> nth s env1 0 = nth s env2 0.
Proof.
  intros pis env1 env2 n m p s Hleneq Hs Henv1 Henv2.
  unfold env_scan in Henv1, Henv2. destruct (nth_error pis m) as [pi|]; [|congruence].
  reflect. rewrite Hleneq in Henv1. destruct Henv1 as [[Henv1 ?] ?]; destruct Henv2 as [[Henv2 ?] ?].
  rewrite <- Henv2 in Henv1. apply nth_eq; auto.
Qed.

Lemma env_scan_inj_rev :
  forall pis env n m x1 x2 p, env_scan pis (rev (x1 :: env)) n m p = true -> env_scan pis (rev (x2 :: env)) n m p = true -> x1 = x2.
Proof.
  intros pis env n m x1 x2 p H1 H2.
  replace x1 with (nth (length env) (rev (x1 :: env)) 0) by (simpl; rewrite app_nth2, rev_length, Nat.sub_diag; reflexivity || rewrite rev_length; lia).
  replace x2 with (nth (length env) (rev (x2 :: env)) 0) by (simpl; rewrite app_nth2, rev_length, Nat.sub_diag; reflexivity || rewrite rev_length; lia).
  eapply env_scan_inj_nth; [| |exact H1|exact H2]; rewrite !rev_length; simpl; lia.
Qed.

Lemma lex_app_not_gt :
  forall env x1 x2 l1 l2, lex_compare ((env ++ (x1 :: nil)) ++ l1) ((env ++ (x2 :: nil)) ++ l2) <> Gt -> x1 <= x2.
Proof.
  intros env x1 x2 l1 l2 H.
  rewrite !lex_compare_app, lex_compare_reflexive in H by (rewrite ?app_length; reflexivity).
  simpl in H. destruct (x1 ?= x2) eqn:H12; simpl; congruence.
Qed.

Theorem generate_loop_preserves_sem :
  forall d n pi env mem1 mem2,
    (d <= n)%nat ->
    WHEN st <- generate_loop d n pi THEN
    poly_loop_semantics st env mem1 mem2 ->
    length env = (n - d)%nat ->
    (forall c, In c pi.(pi_poly) -> fst c =v= resize n (fst c)) ->
    project_invariant (n - d)%nat pi.(pi_poly) (rev env) ->
    env_poly_lex_semantics (rev env) n (pi :: nil) mem1 mem2.
Proof.
  induction d.
  - intros n pi env mem1 mem2 Hnd st Hgen Hsem Hlen Hpilen Hinv.
    eapply generate_loop_single_point; eauto; try lia.
    eapply project_id; eauto.
    rewrite Nat.sub_0_r in Hinv. auto.
  - intros n pi env mem1 mem2 Hnd st Hgen Hsem Hlen Hpilen Hinv. simpl in *.
    bind_imp_destruct Hgen proj Hproj.
    bind_imp_destruct Hgen inner Hinner.
    apply mayReturn_pure in Hgen. rewrite <- Hgen in Hsem.
    apply PLLoop_inv_sem in Hsem.
    destruct Hsem as [lb [ub [Hlbub Hsem]]].
    unfold env_poly_lex_semantics in *.
    eapply poly_lex_semantics_extensionality.
    + apply poly_lex_concat_seq with (to_scans := fun x => env_scan (pi :: nil) (rev (x :: env)) n).
      * eapply iter_semantics_map; [|apply Hsem].
        intros x mem3 mem4 Hbounds Hloop. eapply IHd with (env := x :: env); simpl; eauto; try lia.
        replace (n - d)%nat with (S (n - S d))%nat in * by lia.
        eapply project_next_r_inclusion; [|exact Hproj|].
        -- rewrite project_invariant_resize, resize_app by (rewrite rev_length; auto).
           apply Hinv.
        -- intros c Hcin Hcnth. rewrite <- Hlbub in Hbounds.
           unfold in_poly in Hbounds; rewrite forallb_forall in Hbounds. apply Hbounds.
           rewrite filter_In; reflect; auto.
      * intros x. apply env_scan_proper.
      * intros x1 x2 m p. apply env_scan_inj_rev.
      * intros x1 n1 p1 x2 n2 p2 Hcmp H1 H2.
        apply env_scan_begin in H1; apply env_scan_begin in H2. simpl in *.
        rewrite H1, H2 in Hcmp. eapply lex_app_not_gt; rewrite Hcmp. congruence.
    + simpl. intros m p. rewrite env_scan_extend; eauto; try lia.
      * replace (S (n - S d)) with (n - d)%nat by lia. apply Hproj.
      * intros x; rewrite <- Hlbub. unfold in_poly; rewrite forallb_forall. apply forall_ext; intros c.
        split; intros H; intros; apply H; rewrite filter_In in *; reflect; tauto.
Qed.

Definition generate d n pi :=
  BIND st <- generate_loop d n pi -;
  BIND ctx <- project_invariant_export ((n - d)%nat, pi.(pi_poly)) -;
  pure (PGuard ctx st).

Theorem generate_preserves_sem :
  forall d n pi env mem1 mem2,
    (d <= n)%nat ->
    WHEN st <- generate d n pi THEN
    poly_loop_semantics st env mem1 mem2 ->
    length env = (n - d)%nat ->
    (forall c, In c pi.(pi_poly) -> fst c =v= resize n (fst c)) ->
    env_poly_lex_semantics (rev env) n (pi :: nil) mem1 mem2.
Proof.
  intros d n pi env mem1 mem2 Hd st Hgen Hloop Henv Hsize.
  bind_imp_destruct Hgen st1 H. bind_imp_destruct Hgen ctx Hctx.
  apply mayReturn_pure in Hgen.
  rewrite <- Hgen in *.
  apply PLGuard_inv_sem in Hloop.
  destruct (in_poly (rev env) ctx) eqn:Htest.
  - eapply generate_loop_preserves_sem; eauto.
    rewrite <- (project_invariant_export_correct _ _ _ _ Hctx); eauto.
  - rewrite Hloop. apply PolyLexDone. intros n0 p. unfold env_scan.
    destruct n0; simpl in *; [|destruct n0]; auto. reflect.
    rewrite rev_length; rewrite Henv.
    destruct (is_eq (rev env) (resize (n - d)%nat p)) eqn:Hpenv; auto.
    destruct (in_poly p pi.(pi_poly)) eqn:Hpin; auto. exfalso.
    eapply project_invariant_inclusion in Hpin.
    rewrite <- (project_invariant_export_correct _ _ _ _ Hctx) in Hpin.
    reflect. rewrite <- Hpenv in Hpin. congruence.
Qed.



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










(*
Definition generate es pi :=
  let n := list_max (map (fun c => length (fst c)) pi.(pi_poly)) in
  generate_loop (n - es) n pi.
*)
(*
Theorem generate_preserves_sem :
  forall pi es st env mem1 mem2,
    es = length env ->
    generate es pi = Ok st ->
    (forall c, In c pi.(pi_poly) -> fst c =v= resize es (fst c) -> satisfies_constraint (rev env) c = true) ->
    env_poly_lex_semantics 
 *)


