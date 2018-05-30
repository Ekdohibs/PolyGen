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

  

(*
(* TODO *)
Parameter split_polys : list polyhedron -> result (list (polyhedron * list nat)%type).

Definition poly_disjoint pol1 pol2 := forall p, in_poly p pol1 = false \/ in_poly p pol2 = false.

Fixpoint all_disjoint (l : list polyhedron) :=
  match l with
  | nil => True
  | p :: l => (forall p2, In p2 l -> poly_disjoint p p2) /\ all_disjoint l
  end.

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

Definition find_eq (n : nat) (p : polyhedron) :=
  let l1 := filter (fun c => 0 <? nth n (fst c) 0) p in
  let l2 := filter (fun c => nth n (fst c) 0 <? 0) p in
  let l12 := list_prod l1 l2 in
  match find (fun c12 => is_eq (fst (fst c12)) (mult_vector (-1) (fst (snd c12))) && (snd (fst c12) =? -snd (snd c12))) l12 with
  | None => None
  | Some (c1, c2) => Some c1
  end.

Theorem find_eq_in :
  forall n pol c, find_eq n pol = Some c -> In c pol.
Proof.
  intros n pol c Hfind. unfold find_eq in *.
  match goal with [ Hfind : context[match ?X with _ => _ end] |- _ ] => destruct X as [[c1 c2]|] eqn:Hfind1 end; [|congruence].
  injection Hfind as Hfind; rewrite <- Hfind.
  apply find_some in Hfind1; reflect; destruct Hfind1 as [Hfind1 [Heql Heqc]]. reflect; simpl in *.
  rewrite in_prod_iff, !filter_In in Hfind1. tauto.
Qed.

Theorem find_eq_correct :
  forall n pol c p t, 0 < t -> find_eq n pol = Some c ->
                 (forall c, In c pol -> nth n (fst c) 0 <> 0 -> satisfies_constraint p (mult_constraint_cst t c) = true) -> dot_product p (fst c) = t * snd c.
Proof.
  intros n pol c p t Ht Hfind Hin.
  unfold find_eq, in_poly, satisfies_constraint in *.
  match goal with [ Hfind : context[match ?X with _ => _ end] |- _ ] => destruct X as [[c1 c2]|] eqn:Hfind1 end; [|congruence].
  injection Hfind as Hfind; rewrite <- Hfind.
  apply find_some in Hfind1; reflect; destruct Hfind1 as [Hfind1 [Heql Heqc]]. reflect; simpl in *.
  rewrite in_prod_iff, !filter_In in Hfind1.
  destruct Hfind1 as [[Hin1 ?] [Hin2 ?]]. reflect.
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
  match goal with [ Hfind : context[match ?X with _ => _ end] |- _ ] => destruct X as [[c1 c2]|] eqn:Hfind1 end; [|congruence].
  injection Hfind as Hfind; rewrite <- Hfind.
  apply find_some in Hfind1; reflect; destruct Hfind1 as [Hfind1 [Heql Heqc]]. reflect; simpl in *.
  rewrite in_prod_iff, !filter_In in Hfind1.
  destruct Hfind1 as [[? ?] [? ?]]. reflect; auto.
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

End PolyProject.

Module PolyProjectSimple (Import Imp: FullAlarmedMonad) <: PolyProject Imp.

  Parameter untrusted_project : nat -> polyhedron -> (polyhedron * list witness)%type.

  Definition project (np : nat * polyhedron) : imp polyhedron :=
    let (n, p) := np in
    let (res, wits) := untrusted_project n p in
    if negb (length res =? length wits)%nat then
      alarm "Incorrect number of witnesses" p
    else if negb (forallb (fun c => is_eq (fst c) (resize n (fst c))) res) then
      alarm "Constraint too long" p
    else if negb (forallb (fun z => is_redundant (snd z) p (fst z)) (combine res wits)) then
      alarm "Witness checking failed" p
    else if negb (forallb (fun c => negb (is_eq (fst c) (resize n (fst c))) || existsb (fun c' => is_eq (fst c) (fst c') && (snd c =? snd c')) res) p) then
      alarm "Constraint removed in projection" p
    else
      pure res.

  Theorem project_inclusion :
    forall n p pol, in_poly p pol = true -> WHEN proj <- project (n, pol) THEN in_poly (resize n p) proj = true.
  Proof.
    intros n p pol Hin.
    unfold project.
    destruct (untrusted_project n pol) as [res wits].
    case_if eq Hlen; reflect; [xasimplify ltac:(eauto using mayReturn_alarm)|].
    case_if eq Hresize; reflect; [xasimplify ltac:(eauto using mayReturn_alarm)|].
    case_if eq Hwits; reflect; [xasimplify ltac:(eauto using mayReturn_alarm)|].
    case_if eq Hpreserve; reflect; [xasimplify ltac:(eauto using mayReturn_alarm)|].
    xasimplify eauto.
    assert (Hinres : in_poly p res = true).
    - unfold in_poly. rewrite forallb_forall. intros c Hc.
      apply in_l_combine with (l' := wits) in Hc; [|auto].
      destruct Hc as [wit Hwit].
      eapply is_redundant_correct; [|apply Hin].
      rewrite forallb_forall in Hwits.
      apply (Hwits (c, wit)); auto.
    - unfold in_poly in *. rewrite forallb_forall in *. intros c Hc.
      rewrite <- (Hinres c) by auto.
      unfold satisfies_constraint. f_equal. specialize (Hresize c Hc). reflect.
      rewrite Hresize.
      rewrite <- dot_product_resize_left with (t1 := p). rewrite resize_length. reflexivity.
  Qed.

  Definition project_invariant n pol p :=
    forall c, In c pol -> fst c =v= resize n (fst c) -> satisfies_constraint p c = true.

  Theorem project_reverse_inclusion :
    forall n pol c, In c pol -> fst c =v= resize n (fst c) -> WHEN proj <- project (n, pol) THEN (exists c', c =c= c' /\ In c' proj).
  Proof.
    intros n pol c Hin Heq.
    unfold project.
    destruct (untrusted_project n pol) as [res wits].
    case_if eq Hlen; reflect; [xasimplify ltac:(exfalso; eauto using mayReturn_alarm)|].
    case_if eq Hresize; reflect; [xasimplify ltac:(exfalso; eauto using mayReturn_alarm)|].
    case_if eq Hwits; reflect; [xasimplify ltac:(exfalso; eauto using mayReturn_alarm)|].
    case_if eq Hpreserve; reflect; [xasimplify ltac:(exfalso; eauto using mayReturn_alarm)|].
    xasimplify eauto.
    reflect_binders.
    specialize (Hpreserve c Hin).
    rewrite <- is_eq_veq in Heq; rewrite Heq in Hpreserve.
    destruct Hpreserve as [Hpreserve | [c' [Hin2 Heqc']]]; [congruence|].
    exists c'. auto.
  Qed.

  Theorem project_invariant_inclusion :
    forall n pol p, in_poly p pol = true -> project_invariant n pol (resize n p).
  Proof.
    intros n pol p Hin. unfold in_poly, project_invariant in *.
    rewrite forallb_forall in Hin; intros c Hinc Hlenc.
    specialize (Hin c Hinc).
    unfold satisfies_constraint in *.
    rewrite Hlenc in Hin. rewrite <- dot_product_resize_left in Hin.
    rewrite resize_length in Hin. rewrite Hlenc. auto.
  Qed.

  Theorem project_id :
    forall n pol p, (forall c, In c pol -> fst c =v= resize n (fst c)) -> project_invariant n pol p -> in_poly p pol = true.
  Proof.
    intros n pol p Hsize Hinv. unfold in_poly; rewrite forallb_forall. intros c Hc.
    apply Hinv; auto.
  Qed.

  Theorem project_next_r_inclusion :
    forall n pol p, project_invariant n pol p ->
               WHEN proj <- project (S n, pol) THEN
                 (forall c, In c proj -> nth n (fst c) 0 <> 0 -> satisfies_constraint p c = true) ->
                 project_invariant (S n) pol p.
  Proof.
    intros n pol p Hinv proj Hproj Hsat c Hcin Hclen.
    destruct (nth n (fst c) 0 =? 0) eqn:Hzero; reflect.
    - rewrite resize_succ in Hclen. rewrite Hzero in Hclen.
      setoid_replace (0 :: nil) with (@nil Z) using relation veq in Hclen by (rewrite <- is_eq_veq; auto).
      rewrite app_nil_r in Hclen.
      apply Hinv; auto.
    - destruct (project_reverse_inclusion (S n) pol c Hcin Hclen proj Hproj) as [c' [Heqc' Hc'in]].
      rewrite Heqc'. apply Hsat; auto. erewrite nth_eq; eauto. rewrite Heqc'; reflexivity.
  Qed.

  Theorem project_invariant_resize :
    forall n pol p, project_invariant n pol p <-> project_invariant n pol (resize n p).
  Proof.
    intros n pol p.
    unfold project_invariant; apply forall_ext.
    intros c. apply forall_ext. intros Hcin. apply forall_ext. intros Hclen.
    apply eq_iff_eq_true. unfold satisfies_constraint. f_equal.
    rewrite Hclen. rewrite <- dot_product_resize_left. rewrite resize_length; auto.
  Qed.

  Definition project_invariant_export (np : nat * polyhedron) : imp polyhedron :=
    pure (filter (fun c => is_eq (fst c) (resize (fst np) (fst c))) (snd np)).

  Theorem project_invariant_export_correct :
    forall n p pol, WHEN res <- project_invariant_export (n, pol) THEN in_poly p res = true <-> project_invariant n pol p.
  Proof.
    intros n p pol. xasimplify eauto.
    unfold project_invariant. unfold in_poly.
    rewrite forallb_forall. under_forall ((list Z * Z)%type) ltac:(fun x => rewrite filter_In; reflect).
    firstorder.
  Qed.

  Theorem project_constraint_size :
    forall n pol c, WHEN proj <- project (n, pol) THEN In c proj -> fst c =v= resize n (fst c).
  Proof.
    intros n pol c. unfold project.
    destruct (untrusted_project n pol) as [res wits].
    case_if eq Hlen; reflect; [xasimplify ltac:(exfalso; eauto using mayReturn_alarm)|].
    case_if eq Hresize; reflect; [xasimplify ltac:(exfalso; eauto using mayReturn_alarm)|].
    case_if eq Hwits; reflect; [xasimplify ltac:(exfalso; eauto using mayReturn_alarm)|].
    case_if eq Hpreserve; reflect; [xasimplify ltac:(exfalso; eauto using mayReturn_alarm)|].
    xasimplify eauto.
    reflect. intros Hin.
    rewrite forallb_forall in Hresize. specialize (Hresize c); reflect; eauto.
  Qed.

End PolyProjectSimple.

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

Module Type ProjectOperator (Import Imp: FullImpureMonad).

  Parameter project : (nat * polyhedron) -> imp polyhedron.

  Parameter project_projected :
    forall n pol, WHEN proj <- project (n, pol) THEN forall c, In c proj -> nth n (fst c) 0 = 0.

  Parameter project_no_new_var :
    forall n k pol, (forall c, In c pol -> nth k (fst c) 0 = 0) -> WHEN proj <- project (n, pol) THEN (forall c, In c proj -> nth k (fst c) 0 = 0).

  Parameter project_in_iff :
    forall n p pol s, 0 < s ->
                 WHEN proj <- project (n, pol) THEN
                      in_poly p (expand_poly s proj) = true <->
                 exists t k, 0 < t /\ in_poly (assign n k (mult_vector t p)) (expand_poly (s * t) pol) = true.

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
    forall n p pol s, 0 < s -> in_poly p (expand_poly s (pure_project n pol)) = true <->
                         exists t k, 0 < t /\ in_poly (assign n k (mult_vector t p)) (expand_poly (s * t) pol) = true.
  Proof.
    intros n p pol s Hs.
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
    forall n p pol s, 0 < s ->
                 WHEN proj <- project (n, pol) THEN
                      in_poly p (expand_poly s proj) = true <->
                 exists t k, 0 < t /\ in_poly (assign n k (mult_vector t p)) (expand_poly (s * t) pol) = true.
  Proof.
    intros n p pol s Hs proj Hproj.
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
        rewrite (Proj.project_in_iff _ _ _ _ Hst _ Hproja) in Hin.
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
        rewrite (Proj.project_in_iff _ _ _ _ Hst _ Hproja).
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

(*
Module PolyProjectSimplifier (Import Imp: FullImpureMonad) (Base : PolyProject Imp) <: PolyProject Imp.

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
    forall n pol p, in_poly p (simplify_poly n pol) = in_poly p pol.
  Proof.
    induction n.
    - intros; simpl; reflexivity.
    - intros pol p. simpl.
      set (nz := filter (fun c => negb (nth n (fst c) 0 =? 0)) pol).
      set (z := filter (fun c => nth n (fst c) 0 =? 0) pol).
      transitivity (in_poly p nz && in_poly p z).
      + destruct (find_eq n nz) as [c|] eqn:Hfindeq.
        * unfold in_poly in *. simpl. rewrite IHn. rewrite andb_assoc.
          replace (satisfies_constraint p c && satisfies_constraint p (mult_constraint (-1) c)) with (dot_product p (fst c) =? snd c)
            by (unfold satisfies_constraint, mult_constraint; simpl; rewrite eq_iff_eq_true, dot_product_mult_right; reflect; lia).
          assert (Hcnth : nth n (fst c) 0 <> 0) by (apply find_eq_nth in Hfindeq; lia).
          destruct (dot_product p (fst c) =? snd c) eqn:Heq; simpl; reflect.
          -- rewrite forallb_app, forallb_map. f_equal. apply forallb_ext.
             intros c1. rewrite make_constraint_with_eq_correct; auto.
          -- destruct (forallb (satisfies_constraint p) nz) eqn:Hin; simpl; [|reflexivity]. exfalso; apply Heq.
             rewrite forallb_forall in Hin.
             eapply find_eq_correct; eauto.
        * rewrite in_poly_app. rewrite IHn. reflexivity.
      + rewrite eq_iff_eq_true. reflect. unfold in_poly, nz, z; rewrite !forallb_forall.
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

  (*
  Lemma simplify_poly_correct_nz :
    forall n pol p, (forall c, In c pol -> nth n (fst c) 0 <> 0 -> satisfies_constraint p c = true) ->
               (forall c, In c (simplify_poly (S n) pol) -> nth n (fst c) 0 <> 0 -> satisfies_constraint p c = true).
  Proof.
    intros n pol p H c Hcin Hcn.
    simpl in Hcin.
    set (nz := filter (fun c => negb (nth n (fst c) 0 =? 0)) pol) in *.
    set (z := filter (fun c => nth n (fst c) 0 =? 0) pol) in *.
    destruct (find_eq n nz) as [c1|] eqn:Hfindeq.
    - simpl in Hcin.
      assert (Heq : dot_product p (fst c1) = snd c1)
        by (eapply find_eq_correct; [apply Hfindeq|]; intros c2 Hc2 Hcn2; unfold nz in Hc2; rewrite filter_In in Hc2; apply H; tauto).
      destruct Hcin as [Hcin | [Hcin | Hcin]]; [rewrite <- Hcin|rewrite <- Hcin|]; unfold satisfies_constraint; reflect;
        [lia|unfold mult_constraint; simpl; rewrite dot_product_mult_right; lia|].
      exfalso. apply Hcn. eapply simplify_poly_preserve_zeros; [|apply Hcin].
      intros c2 Hc2. rewrite in_app_iff, in_map_iff in Hc2.
      destruct Hc2 as [[c3 [Heq2 Hc3]] | Hc2]; [|unfold z in Hc2; rewrite filter_In in Hc2; reflect; tauto].
      rewrite <- Heq2. apply make_constraint_with_eq_nth. apply find_eq_nth in Hfindeq; lia.
    - rewrite in_app_iff in Hcin. destruct Hcin as [Hcin | Hcin].
      + apply H; [|auto]. unfold nz in Hcin; rewrite filter_In in Hcin; tauto.
      + exfalso; apply Hcn. eapply simplify_poly_preserve_zeros; [|apply Hcin].
        intros c1 Hc1; unfold z in Hc1; rewrite filter_In in Hc1; reflect; tauto.
  Qed.
   *)

  Lemma simplify_poly_correct_nz :
    forall n pol p, (forall c, In c pol -> nth n (fst c) 0 = 0 -> satisfies_constraint p c = true) ->
               (forall c, In c (simplify_poly (S n) pol) -> nth n (fst c) 0 <> 0 -> satisfies_constraint p c = true) ->
               (forall c, In c pol -> nth n (fst c) 0 <> 0 -> satisfies_constraint p c = true).
  Proof.
    intros n pol p Hz Hnz c Hcin Hcn.
    simpl in Hnz.
    set (nz := filter (fun c => negb (nth n (fst c) 0 =? 0)) pol) in *.
    set (z := filter (fun c => nth n (fst c) 0 =? 0) pol) in *.
    destruct (find_eq n nz) as [ceq|] eqn:Hfindeq.
    - assert (Hceqn : nth n (fst ceq) 0 <> 0) by (generalize (find_eq_nth _ _ _ Hfindeq); lia).
      assert (Heq : dot_product p (fst ceq) = snd ceq). {
        generalize (Hnz ceq); generalize (Hnz (mult_constraint (-1) ceq)).
        unfold mult_constraint, satisfies_constraint; simpl.
        rewrite mult_nth, dot_product_mult_right; reflect.
        clear Hnz Hz. firstorder.
      }
(*      specialize (Hnz (make_constraint_with_eq n ceq c) *) admit.
    - apply Hnz; [|auto]. rewrite in_app_iff; left. unfold nz.
      rewrite filter_In; reflect; auto.
  Admitted.

  Definition project np :=
    BIND r <- Base.project np -; pure (simplify_poly (fst np) r).

  Lemma project_inclusion :
    forall n p pol, in_poly p pol = true -> WHEN proj <- project (n, pol) THEN in_poly (resize n p) proj = true.
  Proof.
    intros n p pol Hin. do 3 xastep eauto. simpl.
    rewrite simplify_poly_correct.
    eapply Base.project_inclusion in Hexta; eauto.
  Qed.

  Definition project_invariant := Base.project_invariant.

  Lemma project_invariant_inclusion :
    forall n pol p, in_poly p pol = true -> project_invariant n pol (resize n p).
  Proof.
    apply Base.project_invariant_inclusion.
  Qed.

  Lemma project_id :
    forall n pol p, (forall c, In c pol -> fst c =v= resize n (fst c)) -> project_invariant n pol p -> in_poly p pol = true.
  Proof.
    apply Base.project_id.
  Qed.

  Axiom is_exact_projection :
    forall v p n, project_invariant n p v <-> exists t m, 0 < t /\ in_poly (resize n (mult_vector t v) ++ m) (expand_poly t p) = true.

  Lemma project_next_r_inclusion :
    forall n pol p, project_invariant n pol p ->
               WHEN proj <- project (S n, pol) THEN
               (forall c, In c proj -> nth n (fst c) 0 <> 0 -> satisfies_constraint p c = true) ->
                 project_invariant (S n) pol p.
  Proof.
    intros n pol p Hinv. do 3 xastep eauto.
    intros H. 
    eapply Base.project_next_r_inclusion in Hexta; eauto.
    apply Hexta. unfold project_invariant in Hinv.
    intros. eapply simplify_poly_correct_nz. ; [exact H| |auto].
    eapply simplify_poly_correct_nz in H.
    intros c Hc Hnc; apply H; [|apply Hnc].

  Parameter project_invariant_resize :
    forall n pol p, project_invariant n pol p <-> project_invariant n pol (resize n p).

  Parameter project_invariant_export : nat * polyhedron -> imp polyhedron.

  Parameter project_invariant_export_correct :
    forall n p pol, WHEN res <- project_invariant_export (n, pol) THEN in_poly p res = true <-> project_invariant n pol p.

  Parameter project_constraint_size :
    forall n pol c, WHEN proj <- project (n, pol) THEN In c proj -> fst c =v= resize n (fst c).

End PolyProject.
*)

Module CoreAlarmed := AlarmImpureMonad Vpl.ImpureConfig.Core.
Import CoreAlarmed.

(*
Module PPS := PolyProjectSimple CoreAlarmed.
Import PPS.
*)

Module Proj := FourierMotzkinProject CoreAlarmed.
Module Canon := NaiveCanonizer CoreAlarmed.
Module PO := PolyProjectImpl CoreAlarmed Canon Proj.
Import PO.

Global Opaque project.
Ltac bind_imp_destruct H id1 id2 :=
  apply mayReturn_bind in H; destruct H as [id1 [id2 H]].

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

Fixpoint and_all l :=
  match l with
  | nil => TConstantTest true
  | x :: l => make_and x (and_all l)
  end.

Theorem and_all_correct :
  forall l env, eval_test env (and_all l) = forallb (eval_test env) l.
Proof.
  induction l; simpl in *; [auto|].
  intros; rewrite make_and_correct, IHl; auto.
Qed.

Definition make_affine_test n c := make_le (make_linear_expr n (fst c)) (Constant (snd c)).

Lemma make_affine_test_correct :
  forall env n c, length env = n -> eval_test env (make_affine_test n c) = satisfies_constraint (rev env) c.
Proof.
  intros. simpl in *. unfold make_affine_test. rewrite make_le_correct, make_linear_expr_correct; auto.
  rewrite dot_product_commutative. reflexivity.
Qed.

Definition scan_dimension (n : nat) (inner : stmt) (p : polyhedron) : imp stmt :=
  match find_eq n p with
  | Some c =>
    let '(result, test) := solve_eq n c in
    let cstrs := map (fun c1 => make_affine_test n (make_constraint_with_eq n c c1)) (filter (fun c => negb (nth n (fst c) 0 =? 0)) p) in
    pure (Guard (make_and test (and_all cstrs)) (Loop result (Sum result (Constant 1)) inner))
  | None => 
    BIND lb <- res_to_alarm (Constant 0) (find_lower_bound n p) -;
    BIND ub <- res_to_alarm (Constant 0) (find_upper_bound n p) -;
    pure (Loop lb ub inner)
  end.

Lemma scan_dimension_sem :
  forall n inner pol,
    WHEN st <- scan_dimension n inner pol THEN
         forall env mem1 mem2,
           length env = n ->
           exists lb ub,
             (loop_semantics st env mem1 mem2 <-> iter_semantics (fun x => loop_semantics inner (x :: env)) lb ub mem1 mem2) /\
             (forall x, (forall c, In c pol -> nth n (fst c) 0 <> 0 -> satisfies_constraint (rev (x :: env)) c = true) <-> lb <= x < ub).
Proof.
  intros n inner pol st Hst env mem1 mem2 Henvlen.
  unfold scan_dimension in Hst.
  destruct (find_eq n pol) as [c|] eqn:Hfindeq.
  - destruct (solve_eq n c) as [result test] eqn:Hsolve. apply mayReturn_pure in Hst; rewrite <- Hst.
    match goal with [ Hst : Guard ?T _ = _ |- _ ] => set (test1 := T) end.
    assert (Hcnth : 0 < nth n (fst c) 0) by (eapply find_eq_nth; eauto).
    destruct (eval_test env test1) eqn:Htest1.
    + exists (eval_expr env result). exists (eval_expr env (Sum result (Constant 1))). split.
      * split.
        -- intros Hsem. inversion_clear Hsem; [|congruence]. inversion_clear H. auto.
        -- intros Hsem; constructor; [|auto]. constructor; auto.
      * intros x. simpl.
        unfold test1 in Htest1. rewrite make_and_correct in Htest1; reflect.
        rewrite and_all_correct in Htest1. destruct Htest1 as [Htest Hcstr].
        transitivity (eval_expr env (fst (solve_eq n c)) = x /\ eval_test env (snd (solve_eq n c)) = true); [|rewrite Hsolve; simpl; intuition lia].
        rewrite solve_eq_correct by (auto || lia).
        split.
        -- intros H. eapply find_eq_correct_1; eauto.
        -- intros H c1 Hc1in Hc1nth.
           rewrite forallb_map, forallb_forall in Hcstr. specialize (Hcstr c1).
           rewrite filter_In in Hcstr. reflect. rewrite make_affine_test_correct in Hcstr by auto.
           rewrite <- make_constraint_with_eq_correct_1 with (n := n) (c1 := c) by (auto || lia).
           rewrite <- Hcstr by auto.
           unfold satisfies_constraint. f_equal.
           rewrite <- dot_product_assign_left_zero with (k := n) (s := 0) by (apply make_constraint_with_eq_nth; lia).
           f_equiv. rewrite assign_app_ge by (rewrite rev_length; lia). rewrite rev_length, Henvlen, Nat.sub_diag.
           unfold assign. simpl.
           rewrite <- app_nil_r. f_equiv.
    + exists 0. exists 0. split.
      * split.
        -- intros Hsem. inversion_clear Hsem; [congruence|]. constructor; lia.
        -- intros Hsem. inversion_clear Hsem; [|lia]. apply LGuardFalse. auto.
      * split; [|lia]. intros H. exfalso.
        enough (eval_test env test1 = true) by congruence.
        unfold test1. rewrite make_and_correct, and_all_correct, forallb_map. reflect.
        assert (Heq : dot_product (rev (x :: env)) (fst c) = snd c) by (eapply find_eq_correct_1; eauto). simpl in Heq.
        split.
        -- rewrite <- solve_eq_correct in Heq; [|exact Henvlen|lia]. rewrite Hsolve in Heq; simpl in Heq; tauto.
        -- rewrite forallb_forall. intros c1 Hc1in. rewrite filter_In in Hc1in. reflect.
           rewrite make_affine_test_correct by auto. destruct Hc1in as [Hc1in Hc1n]. specialize (H c1 Hc1in Hc1n).
           rewrite <- make_constraint_with_eq_correct_1 with (n := n) (c1 := c) in H by (auto || lia).
           rewrite <- H. unfold satisfies_constraint. f_equal.
           rewrite <- dot_product_assign_left_zero with (k := n) (s := 0) (v1 := rev (x :: env)) by (apply make_constraint_with_eq_nth; lia).
           f_equiv. simpl. rewrite assign_app_ge by (rewrite rev_length; lia). rewrite rev_length, Henvlen, Nat.sub_diag.
           unfold assign. simpl. rewrite <- app_nil_r with (l := rev env) at 1. f_equiv.
  - bind_imp_destruct Hst lb Hlb. apply res_to_alarm_correct in Hlb.
    bind_imp_destruct Hst ub Hub. apply res_to_alarm_correct in Hub.
    exists (eval_expr env lb). exists (eval_expr env ub).
    apply mayReturn_pure in Hst. rewrite <- Hst.
    split.
    + split.
      * intros Hsem; inversion_clear Hsem; auto.
      * intros Hsem; constructor; auto.
    + intros x. rewrite find_bounds_correct; try reflexivity; auto.
Qed.


Fixpoint generate_loop (d : nat) (n : nat) (pi : Polyhedral_Instruction) : imp stmt :=
  match d with
  | O => pure (Instr pi.(pi_instr) (map (make_affine_expr n) pi.(pi_transformation)))
  | S d1 =>
    BIND proj <- project ((n - d1)%nat, pi.(pi_poly)) -;
    BIND inner <- generate_loop d1 n pi -;
    scan_dimension (n - d)%nat inner proj
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
    loop_semantics st env mem1 mem2 ->
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
    intros; apply make_affine_expr_correct; auto.
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
    loop_semantics st env mem1 mem2 ->
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
    apply scan_dimension_sem in Hgen. specialize (Hgen env mem1 mem2 Hlen).
    destruct Hgen as [lb [ub [Hsemgen Hlbub]]]. rewrite Hsemgen in Hsem.
    unfold env_poly_lex_semantics in *.
    eapply poly_lex_semantics_extensionality.
    + apply poly_lex_concat_seq with (to_scans := fun x => env_scan (pi :: nil) (rev (x :: env)) n).
      * eapply iter_semantics_map; [|apply Hsem].
        intros x mem3 mem4 Hbounds Hloop. eapply IHd with (env := x :: env); simpl; eauto; try lia.
        replace (n - d)%nat with (S (n - S d))%nat in * by lia.
        eapply project_next_r_inclusion; [|exact Hproj|rewrite (Hlbub x); auto].
        rewrite project_invariant_resize, resize_app by (rewrite rev_length; auto).
        apply Hinv.
      * intros x. apply env_scan_proper.
      * intros x1 x2 m p. apply env_scan_inj_rev.
      * intros x1 n1 p1 x2 n2 p2 Hcmp H1 H2.
        apply env_scan_begin in H1; apply env_scan_begin in H2. simpl in *.
        rewrite H1, H2 in Hcmp. eapply lex_app_not_gt; rewrite Hcmp. congruence.
    + simpl. intros m p. rewrite env_scan_extend; eauto; try lia.
      replace (S (n - S d)) with (n - d)%nat by lia. apply Hproj.
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

Definition generate d n pi :=
  BIND st <- generate_loop d n pi -;
  BIND ctx <- project_invariant_export ((n - d)%nat, pi.(pi_poly)) -;
  pure (Guard (make_poly_test (n - d)%nat ctx) st).

Theorem generate_preserves_sem :
  forall d n pi env mem1 mem2,
    (d <= n)%nat ->
    WHEN st <- generate d n pi THEN
    loop_semantics st env mem1 mem2 ->
    length env = (n - d)%nat ->
    (forall c, In c pi.(pi_poly) -> fst c =v= resize n (fst c)) ->
    env_poly_lex_semantics (rev env) n (pi :: nil) mem1 mem2.
Proof.
  intros d n pi env mem1 mem2 Hd st Hgen Hloop Henv Hsize.
  bind_imp_destruct Hgen st1 H. bind_imp_destruct Hgen ctx Hctx.
  apply mayReturn_pure in Hgen.
  rewrite <- Hgen in *. inversion_clear Hloop.
  - eapply generate_loop_preserves_sem; eauto.
    rewrite <- (project_invariant_export_correct _ _ _ _ Hctx) by eauto.
    erewrite <- make_poly_test_correct; [|apply Henv]. auto.
  - apply PolyLexDone. intros n0 p. unfold env_scan.
    destruct n0; simpl in *; [|destruct n0]; auto. reflect.
    rewrite rev_length; rewrite Henv.
    rewrite make_poly_test_correct in H0; auto.
    destruct (is_eq (rev env) (resize (n - d)%nat p)) eqn:Hpenv; auto.
    destruct (in_poly p pi.(pi_poly)) eqn:Hpin; auto. exfalso.
    eapply project_invariant_inclusion in Hpin.
    rewrite <- (project_invariant_export_correct _ _ _ _ Hctx) in Hpin.
    reflect. rewrite <- Hpenv in Hpin. congruence.
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


