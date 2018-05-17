Require Import String.

Require Import QArith.
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

Open Scope Z_scope.
Open Scope list_scope.

(** * Definition and properties of the [result] type *)
(** A result is the same as an option, but with an error message in case of failure *)

Inductive result (A : Type) :=
| Ok : A -> result A
| Err : string -> result A.

Arguments Ok {A}.
Arguments Err {A}.

Definition bind {A : Type} (a : result A) {B : Type} (f : A -> result B) :=
  match a with
  | Ok x => f x
  | Err s => Err s
  end.

Notation "a >>= f" := (bind a f) (at level 50, left associativity).
Notation "'do' a <- e ; c" := (e >>= (fun a => c)) (at level 60, right associativity).

Lemma result_right_unit :
  forall A (a : result A), a = bind a (@Ok A).
Proof.
  intros; destruct a; auto.
Qed.

Lemma result_left_unit :
  forall A (a : A) B (f : A -> result B), f a = bind (Ok a) f.
Proof.
  intros; reflexivity.
Qed.

Lemma result_associativity :
  forall A (a : result A) B f C (g : B -> result C), bind a (fun x => bind (f x) g) = bind (bind a f) g.
Proof.
  intros; destruct a; reflexivity.
Qed.

Lemma bind_ok :
  forall A B a (f : A -> result B) x, a >>= f = Ok x -> exists y, a = Ok y /\ f y = Ok x.
Proof.
  intros; destruct a as [a|]; simpl in *; eauto; congruence.
Qed.

Ltac bind_ok_destruct H id1 id2 :=
  apply bind_ok in H; destruct H as [id1 [id2 H]].
  

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
  | S n, x :: l => Sum (Mult x (Var n)) (make_linear_expr n l)
  end.

Lemma firstn_nth_app :
  forall A n (l : list A) d, (length l >= S n)%nat -> firstn (S n) l = firstn n l ++ (nth n l d :: nil).
Proof.
  intros A. induction n.
  - intros l d H; destruct l; simpl in *; [lia | auto].
  - intros l d H; destruct l; simpl in *; [lia |].
    erewrite IHn by lia. reflexivity.
Qed.

Theorem make_linear_expr_correct_aux :
  forall n l env, (length env >= n)%nat -> eval_expr env (make_linear_expr n l) = dot_product l (rev (firstn n env)).
Proof.
  induction n.
  - intros l env Hel. destruct env; destruct l; simpl in *; auto; lia.
  - intros l env Hel.
    destruct l as [|x l]; simpl in Hel; destruct (rev (firstn (S n) env)) as [|y ev] eqn:Hrev; auto; simpl; auto.
    + destruct env as [|e env]; simpl in *; [lia | destruct (rev (firstn n env)); simpl in *; congruence].
    + rewrite firstn_nth_app with (d := 0) in Hrev by auto. rewrite rev_unit in Hrev.
      injection Hrev as Hnth Hrev. rewrite IHn by lia. congruence.
Qed.

Theorem make_linear_expr_correct :
  forall n l env, length env = n -> eval_expr env (make_linear_expr n l) = dot_product l (rev env).
Proof.
  intros. rewrite make_linear_expr_correct_aux by lia. f_equal. f_equal. apply firstn_all2. lia.
Qed.

Definition make_affine_expr (n : nat) (e : (list Z * Z)%type) := Sum (make_linear_expr n (fst e)) (Constant (snd e)).

Theorem make_affine_expr_correct :
  forall n e env, length env = n -> eval_expr env (make_affine_expr n e) = dot_product (fst e) (rev env) + snd e.
Proof.
  intros. simpl in *. rewrite make_linear_expr_correct; auto.
Qed.

(** * Creating upper and lower bounds for a given variable in a constraint *)

Definition make_lower_bound n c :=
  Div (Sum (Constant ((- nth n (fst c) 0) - 1)) (make_affine_expr n (fst c, -(snd c)))) (-(nth n (fst c) 0)).
Lemma make_lower_bound_correct :
  forall n c env x, length env = n -> nth n (fst c) 0 < 0 -> (eval_expr env (make_lower_bound n c) <= x <-> satisfies_constraint (rev env ++ x :: nil) c = true).
Proof.
  intros n c env x Hlen Hneg.
  unfold satisfies_constraint. simpl.
  reflect.
  rewrite make_linear_expr_correct by auto.
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
  Div (Sum (Constant (nth n (fst c) 0)) (make_affine_expr n (mult_vector (-1) (fst c), snd c))) (nth n (fst c) 0).
Lemma make_upper_bound_correct :
  forall n c env x, length env = n -> 0 < nth n (fst c) 0 -> (x < eval_expr env (make_upper_bound n c) <-> satisfies_constraint (rev env ++ x :: nil) c = true).
Proof.
  intros n c env x Hlen Hpos.
  unfold satisfies_constraint. simpl.
  reflect.
  rewrite make_linear_expr_correct by auto. rewrite dot_product_mult_left.
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
               find_lower_bound_aux (Some (match e with Some e => Max e (make_lower_bound n c) | None => make_lower_bound n c end)) n p
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
      destruct e; simpl; [rewrite Z.max_lub_iff|]; rewrite make_lower_bound_correct by auto; split.
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
               find_upper_bound_aux (Some (match e with Some e => Min e (make_upper_bound n c) | None => make_upper_bound n c end)) n p
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
      destruct e; simpl; [rewrite Z.min_glb_lt_iff|]; rewrite make_upper_bound_correct by auto; split.
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

(*
Require Import Vpl.DomainInterfaces.
Require Import Vpl.ConsSet.
Require Import Vpl.PedraQ.
Require Import VplInterface.
 *)
Require Import Vpl.Impure.

(** * Polyhedral projection, using an untrusted oracle and a certificate *)

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

Ltac destruct_if H Heq :=
  lazymatch goal with
    | [ H : context[if ?X then _ else _] |- _ ] => destruct X eqn:Heq
  end.

Ltac destruct_if_g Heq :=
  lazymatch goal with
    | [ |- context[if ?X then _ else _] ] => destruct X eqn:Heq
  end.

Require Vpl.ImpureConfig.

Module CoreAlarmed := AlarmImpureMonad Vpl.ImpureConfig.Core.

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
    destruct_if_g Hlen; reflect; [xasimplify ltac:(eauto using mayReturn_alarm)|].
    destruct_if_g Hresize; reflect; [xasimplify ltac:(eauto using mayReturn_alarm)|].
    destruct_if_g Hwits; reflect; [xasimplify ltac:(eauto using mayReturn_alarm)|].
    destruct_if_g Hpreserve; reflect; [xasimplify ltac:(eauto using mayReturn_alarm)|].
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
    destruct_if_g Hlen; reflect; [xasimplify ltac:(exfalso; eauto using mayReturn_alarm)|].
    destruct_if_g Hresize; reflect; [xasimplify ltac:(exfalso; eauto using mayReturn_alarm)|].
    destruct_if_g Hwits; reflect; [xasimplify ltac:(exfalso; eauto using mayReturn_alarm)|].
    destruct_if_g Hpreserve; reflect; [xasimplify ltac:(exfalso; eauto using mayReturn_alarm)|].
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
    destruct_if_g Hlen; reflect; [xasimplify ltac:(exfalso; eauto using mayReturn_alarm)|].
    destruct_if_g Hresize; reflect; [xasimplify ltac:(exfalso; eauto using mayReturn_alarm)|].
    destruct_if_g Hwits; reflect; [xasimplify ltac:(exfalso; eauto using mayReturn_alarm)|].
    destruct_if_g Hpreserve; reflect; [xasimplify ltac:(exfalso; eauto using mayReturn_alarm)|].
    xasimplify eauto.
    reflect. intros Hin.
    rewrite forallb_forall in Hresize. specialize (Hresize c); reflect; eauto.
  Qed.

End PolyProjectSimple.

Require Import VplInterface.


Definition assign n x v :=
  resize n v ++ (x :: (skipn (S n) v)).

Definition mult_constraint_cst k (c : (list Z * Z)) := (fst c, k * snd c).

Definition expand_poly k pol := map (mult_constraint_cst k) pol.

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

Require Import QOrderedType.

Module FourierMotzkinProject (Import Imp: FullImpureMonad) <: ProjectOperator Imp.

  Definition merge_constraints n c1 c2 :=
    let '(g, (aa, bb)) := Z.ggcd (nth n (fst c1) 0) (nth n (fst c2) 0) in
    add_constraint (mult_constraint bb c1) (mult_constraint_cst (-aa) c2).

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
  

End FourierMotzkinProject.


Fixpoint list_max l :=
  match l with
  | nil => 0%nat
  | x :: l => Nat.max x (list_max l)
  end.

Theorem list_max_le :
  forall l n, (list_max l <= n -> (forall x, In x l -> x <= n))%nat.
Proof.
  induction l; simpl in *.
  - intros; exfalso; auto.
  - intros n H x [Ha | Hl].
    + lia.
    + apply IHl; auto; lia.
Qed.

Theorem list_le_max :
  forall l n, (forall x, In x l -> x <= n)%nat -> (list_max l <= n)%nat.
Proof.
  induction l; simpl in *.
  - intros; lia.
  - intros n H. apply Nat.max_lub.
    + apply H; auto.
    + apply IHl; intros; apply H; auto.
Qed.

Theorem list_max_def :
  forall l n, (list_max l <= n <-> (forall x, In x l -> x <= n))%nat.
Proof.
  intros l n; split; [apply list_max_le | apply list_le_max].
Qed.

Lemma mult_vector_1 :
  forall v, mult_vector 1 v = v.
Proof.
  induction v; simpl; auto; destruct a; auto.
Qed.

Lemma mult_constraint_1 :
  forall c, mult_constraint 1 c = c.
Proof.
  intros c; destruct c as [v x]; unfold mult_constraint.
  simpl in *; rewrite mult_vector_1.
  f_equal; destruct x; auto.
Qed.

Lemma mult_constraint_cst_1 :
  forall c, mult_constraint_cst 1 c = c.
Proof.
  intros c; destruct c as [v x]; destruct x; auto.
Qed.

Lemma expand_poly_1 :
  forall p, expand_poly 1 p = p.
Proof.
  intros p.
  unfold expand_poly. erewrite map_ext; [apply map_id|].
  apply mult_constraint_cst_1.
Qed.

Lemma mult_vector_resize :
  forall n k v, resize n (mult_vector k v) = mult_vector k (resize n v).
Proof.
  induction n.
  - intros; simpl in *; auto.
  - intros; simpl in *.
    destruct v; simpl in *; rewrite <- IHn; f_equal.
    lia.
Qed.

Lemma mult_vector_skipn :
  forall n k v, skipn n (mult_vector k v) = mult_vector k (skipn n v).
Proof.
  induction n.
  - intros; simpl in *; auto.
  - intros; destruct v; simpl in *; auto.
Qed.

Lemma mult_constraint_cst_eq :
  forall c k p, 0 < k -> satisfies_constraint (mult_vector k p) (mult_constraint_cst k c) = satisfies_constraint p c.
Proof.
  intros c k p Hk.
  unfold satisfies_constraint, mult_constraint_cst.
  rewrite dot_product_mult_left. simpl.
  apply eq_iff_eq_true. reflect.
  nia.
Qed.

Lemma expand_poly_eq :
  forall p k v, 0 < k -> in_poly (mult_vector k v) (expand_poly k p) = in_poly v p.
Proof.
  intros p k v Hk.
  unfold in_poly, expand_poly. rewrite forallb_map. apply forallb_ext.
  intros; apply mult_constraint_cst_eq; auto.
Qed.

Lemma mult_constraint_cst_comp :
  forall s t c, mult_constraint_cst s (mult_constraint_cst t c) = mult_constraint_cst (s * t) c.
Proof.
  intros. unfold mult_constraint_cst. simpl. f_equal.
  nia.
Qed.

Lemma expand_poly_comp :
  forall s t p, expand_poly s (expand_poly t p) = expand_poly (s * t) p.
Proof.
  intros. unfold expand_poly.
  rewrite map_map. apply map_ext.
  apply mult_constraint_cst_comp.
Qed.

Lemma mult_vector_comp :
  forall s t v, mult_vector s (mult_vector t v) = mult_vector (s * t) v.
Proof.
  intros s t v. unfold mult_vector. rewrite map_map; apply map_ext.
  intros; nia.
Qed.

Lemma mult_vector_app :
  forall s v1 v2, mult_vector s (v1 ++ v2) = mult_vector s v1 ++ mult_vector s v2.
Proof.
  intros s v1 v2. unfold mult_vector. apply map_app.
Qed.

Lemma resize_app_ge :
  forall n v1 v2, (n <= length v1)%nat -> resize n (v1 ++ v2) = resize n v1.
Proof.
  induction n.
  - intros; simpl in *; auto.
  - intros; destruct v1; simpl in *; [|rewrite IHn]; auto; lia.
Qed.

Lemma skipn_app_le :
  forall (A : Type) n (v1 v2 : list A), (length v1 <= n)%nat -> skipn n (v1 ++ v2) = skipn (n - length v1) v2.
Proof.
  intros A n; induction n.
  - intros; simpl in *.
    destruct v1; simpl in *; auto; lia.
  - intros v1 v2 H; destruct v1.
    + reflexivity.
    + simpl in *; apply IHn; lia.
Qed.

Lemma skipn_app_ge :
  forall (A : Type) n (v1 v2 : list A), (n <= length v1)%nat -> skipn n (v1 ++ v2) = skipn n v1 ++ v2.
Proof.
  intros A n; induction n.
  - intros; simpl; auto.
  - intros; destruct v1; simpl in *; [|apply IHn]; lia.
Qed.

Lemma assign_app_lt :
  forall n k v1 v2, (n < length v1)%nat -> assign n k (v1 ++ v2) = assign n k v1 ++ v2.
Proof.
  intros n k v1 v2 H. unfold assign.
  rewrite <- app_assoc. rewrite skipn_app_ge by lia. rewrite resize_app_ge by lia.
  reflexivity.
Qed.

Lemma assign_app_ge :
  forall n k v1 v2, (length v1 <= n)%nat -> assign n k (v1 ++ v2) = v1 ++ assign (n - length v1) k v2.
Proof.
  intros n k v1 v2 H. unfold assign.
  rewrite resize_app_le by lia. rewrite skipn_app_le by lia. rewrite <- app_assoc.
  f_equal. f_equal. f_equal. f_equal. lia.
Qed.

Lemma resize_length_eq :
  forall n l, length l = n -> resize n l = l.
Proof.
  induction n; intros; destruct l; simpl in *; auto; lia.
Qed.

Fixpoint nrlength l :=
  match l with
  | nil => 0%nat
  | x :: l => let n := nrlength l in if (x =? 0) && (n =? 0)%nat then 0%nat else S n
  end.

Lemma nrlength_zero_null :
  forall l, nrlength l = 0%nat -> is_null l = true.
Proof.
  induction l.
  - simpl in *; auto.
  - intros H; simpl in *.
    destruct (a =? 0); simpl in *; [|congruence].
    destruct (nrlength l); simpl in *; [auto|congruence].
Qed.

Lemma nrlength_null_zero :
  forall l, is_null l = true -> nrlength l = 0%nat.
Proof.
  induction l.
  - simpl; auto.
  - intros H; simpl in *; reflect; destruct H as [H1 H2]; rewrite IHl by auto; rewrite H1; reflexivity.
Qed.

Lemma nrlength_zero_null_iff :
  forall l, nrlength l = 0%nat <-> is_null l = true.
Proof.
  intros l; split; [apply nrlength_zero_null | apply nrlength_null_zero].
Qed.

Lemma nrlength_def :
  forall l n, resize n l =v= l <-> (nrlength l <= n)%nat.
Proof.
  induction l.
  - intros n; simpl in *. split; intros; [lia|].
    rewrite <- is_eq_veq. rewrite is_eq_nil_right. apply resize_nil_null.
  - intros n. rewrite <- is_eq_veq. destruct n.
    + simpl in *. destruct (a =? 0); simpl; [|split; intros; [congruence|lia]].
      rewrite <- nrlength_zero_null_iff.
      destruct (nrlength l); simpl in *; split; intros; lia.
    + simpl. rewrite Z.eqb_refl. simpl. rewrite is_eq_veq. rewrite IHl.
      destruct_if_g H; reflect; lia.
Qed.

Lemma nrlength_eq :
  forall l, resize (nrlength l) l =v= l.
Proof.
  intros; rewrite nrlength_def; lia.
Qed.

Lemma nrlength_def_impl :
  forall l n, (nrlength l <= n)%nat -> resize n l =v= l.
Proof.
  intros; rewrite nrlength_def; auto.
Qed.

Lemma dot_product_nrlength_right :
  forall v1 v2 n, (nrlength v1 <= n)%nat -> dot_product v1 (resize n v2) = dot_product v1 v2.
Proof.
  intros v1 v2 n H. rewrite <- (nrlength_def_impl v1 n) by auto.
  rewrite <- dot_product_resize_right with (t2 := v2). rewrite resize_length. reflexivity.
Qed.

Lemma dot_product_nrlength_left :
  forall v1 v2 n, (nrlength v2 <= n)%nat -> dot_product (resize n v1) v2 = dot_product v1 v2.
Proof.
  intros v1 v2 n H. rewrite dot_product_commutative. rewrite dot_product_nrlength_right by auto.
  apply dot_product_commutative.
Qed.

Lemma satisfies_constraint_nrlength :
  forall p c n, (nrlength (fst c) <= n)%nat -> satisfies_constraint (resize n p) c = satisfies_constraint p c.
Proof.
  intros p c n H. unfold satisfies_constraint.
  rewrite dot_product_nrlength_left; auto.
Qed.

Definition poly_nrl (pol : polyhedron) := list_max (map (fun c => nrlength (fst c)) pol).

Lemma in_poly_nrlength :
  forall p pol n, (poly_nrl pol <= n)%nat -> in_poly (resize n p) pol = in_poly p pol.
Proof.
  intros p pol n H.
  unfold in_poly. rewrite eq_iff_eq_true, !forallb_forall. apply forall_ext.
  intros c.
  enough (In c pol -> satisfies_constraint (resize n p) c = satisfies_constraint p c) by (intuition congruence).
  intros Hin. apply satisfies_constraint_nrlength.
  eapply list_max_le; [exact H|]. rewrite in_map_iff. exists c. auto.
Qed.

Lemma nrlength_mult :
  forall k v, k <> 0 -> nrlength (mult_vector k v) = nrlength v.
Proof.
  intros k. induction v.
  - simpl; auto.
  - intros; simpl. rewrite IHv by auto.
    replace (k * a =? 0) with (a =? 0); [reflexivity|].
    rewrite eq_iff_eq_true; reflect; nia.
Qed.

Lemma expand_poly_nrl :
  forall k p, k <> 0 -> poly_nrl (expand_poly k p) = poly_nrl p.
Proof.
  intros k p H. unfold poly_nrl, expand_poly.
  rewrite map_map. f_equal.
Qed.

Lemma poly_nrl_def :
  forall n pol, (forall c, In c pol -> fst c =v= resize n (fst c)) <-> (poly_nrl pol <= n)%nat.
Proof.
  intros n pol. unfold poly_nrl. rewrite list_max_def. split.
  - intros H x Hin. rewrite in_map_iff in Hin. destruct Hin as [c [Hlen Hin]].
    rewrite <- Hlen, <- nrlength_def. symmetry; auto.
  - intros H c Hin. symmetry; rewrite nrlength_def. apply H.
    rewrite in_map_iff; exists c; auto.
Qed.

Lemma nth_resize :
  forall n k v, nth k (resize n v) 0 = if (k <? n)%nat then nth k v 0 else 0.
Proof.
  induction n.
  - intros k v; destruct k; auto.
  - intros k v; destruct k; destruct v; simpl; auto;
      replace (S k <? S n)%nat with (k <? n)%nat by (rewrite eq_iff_eq_true; reflect; lia); rewrite IHn; destruct k; reflexivity.
Qed.

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

  Definition project (np : nat * polyhedron) : imp polyhedron :=
    let (n, p) := np in
    let k := poly_nrl p in
    do_project n (k - n)%nat p.

  Lemma project_in_iff :
    forall s n p pol, 0 < s -> WHEN proj <- project (n, pol) THEN
                              in_poly p (expand_poly s proj) = true <->
                         exists t m, 0 < t /\ in_poly (resize n (mult_vector t p) ++ m) (expand_poly (s * t) pol) = true.
  Proof.
    intros s n p pol Hs proj Hproj.
    unfold project in Hproj.
    remember (poly_nrl pol) as u.
    rewrite (do_project_in_iff _ _ _ _ _ Hs _ Hproj).
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
    apply vector_nth_veq. intros k.
    unfold project in Hproj.
    rewrite nth_resize.
    destruct (k <? n)%nat eqn:Hkn; reflect; [reflexivity|].
    destruct (k <? n + (poly_nrl pol - n))%nat eqn:Hkrl; reflect.
    - apply (do_project_constraints _ _ _ _ (conj Hkn Hkrl) _ Hproj); auto.
    - assert (Hnrl : (poly_nrl pol <= k)%nat) by lia.
      rewrite <- poly_nrl_def in Hnrl.
      assert (H : forall c, In c pol -> nth k (fst c) 0 = 0).
      + intros c1 Hin1; specialize (Hnrl c1 Hin1).
        apply nth_eq with (n := k) in Hnrl. rewrite nth_resize in Hnrl. destruct (k <? k)%nat eqn:Hkk; reflect; lia.
      + apply (do_project_no_new_var _ _ _ _  H _ Hproj _ Hin).
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
Module PolyProjectVPL (Dom : HasAssume QNum Cstr BasicD) <: PolyProject.

  Axiom extractImp : forall A, imp A -> A.

  Definition project n p := Ok p.

  Theorem project_inclusion :
    forall n p pol proj, project n pol = Ok proj -> in_poly p pol = true -> in_poly (resize n p) proj = true.
  Proof.
  Admitted.

  Definition project_invariant n pol p :=
    forall c, In c pol -> fst c =v= resize n (fst c) -> satisfies_constraint p c = true.

  Theorem project_invariant_inclusion :
    forall n pol p, in_poly p pol = true -> project_invariant n pol (resize n p).
  Proof.
  Admitted.

  Theorem project_id :
    forall n pol p, (forall c, In c pol -> fst c =v= resize n (fst c)) -> project_invariant n pol p -> in_poly p pol = true.
  Proof.
  Admitted.

  Theorem project_next_r_inclusion :
    forall n pol proj p, project (S n) pol = Ok proj -> project_invariant n pol p ->
                    (forall c, In c proj -> nth n (fst c) 0 <> 0 -> satisfies_constraint p c = true) -> project_invariant (S n) pol p.
  Proof.
  Admitted.

  Theorem project_invariant_resize :
    forall n pol p, project_invariant n pol p <-> project_invariant n pol (resize n p).
  Proof.
  Admitted.

  Definition project_invariant_export n (pol : polyhedron) :=
    Ok (filter (fun c => is_eq (fst c) (resize n (fst c))) pol).

  Theorem project_invariant_export_correct :
    forall n p pol res, project_invariant_export n pol = Ok res -> in_poly p res = true <-> project_invariant n pol p.
  Proof.
  Admitted.

  Theorem project_constraint_size :
    forall n pol proj c, project n pol = Ok proj -> In c proj -> fst c =v= resize n (fst c).
  Proof.
  Admitted.

End PolyProjectVPL.
 *)

Import CoreAlarmed.
Module PPS := PolyProjectSimple CoreAlarmed.
Import PPS.
Global Opaque project.
Ltac bind_imp_destruct H id1 id2 :=
  apply mayReturn_bind in H; destruct H as [id1 [id2 H]].

(*
Theorem project_id :
  forall n pol proj p, project n pol = Ok proj -> (forall c, In c pol -> fst c =v= resize n (fst c)) -> in_poly p proj = true -> in_poly p pol = true.
Proof.
  intros n pol proj p Hproj Hplen Hin.
  unfold project in Hproj.
  destruct (untrusted_project n pol) as [res wits].
  destruct_if Hproj Hlen; [congruence|].
  destruct_if Hproj Hresize; [congruence|].
  destruct_if Hproj Hwits; [congruence|].
  destruct_if Hproj Hpreserve; [congruence|].
  injection Hproj as Hproj; rewrite Hproj in *.
  reflect. unfold in_poly in *. reflect_binders.
  intros c Hc; specialize (Hpreserve c Hc). specialize (Hplen c Hc).
  rewrite <- Hplen in Hpreserve. rewrite is_eq_reflexive in Hpreserve.
  destruct Hpreserve as [Hpreserve | [x  [H1 [H2 H3]]]]; [congruence|].
  unfold satisfies_constraint. rewrite H2; rewrite H3. apply Hin; auto.
Qed.

Theorem project_next_r_inclusion :
  forall n pol proj1 proj2 p, project n pol = Ok proj1 -> project (S n) pol = Ok proj2 -> in_poly p proj1 = true ->
                         (forall c, In c proj2 -> nth n (fst c) 0 <> 0 -> satisfies_constraint p c = true) -> in_poly p proj2 = true.
Proof.
  intros n pol proj1 proj2 p Hproj1 Hproj2 Hinp1 Hsat.
Admitted.
*)


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

Fixpoint generate_loop (d : nat) (n : nat) (pi : Polyhedral_Instruction) : imp stmt :=
  match d with
  | O => pure (Instr pi.(pi_instr) (map (make_affine_expr n) pi.(pi_transformation)))
  | S d1 =>
    BIND proj <- project ((n - d1)%nat, pi.(pi_poly)) -;
    BIND lb <- res_to_alarm (Constant 0) (find_lower_bound (n - d)%nat proj) -;
    BIND ub <- res_to_alarm (Constant 0) (find_upper_bound (n - d)%nat proj) -;
    BIND inner <- generate_loop d1 n pi -;
    pure (Loop lb ub inner)
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
    find_lower_bound n proj = Ok lb ->
    find_upper_bound n proj = Ok ub ->
    env_scan (pi :: nil) (rev env) d m p =
      existsb (fun x : Z => env_scan (pi :: nil) (rev env ++ x :: nil) d m p) (Zrange (eval_expr env lb) (eval_expr env ub)).
Proof.
  intros d n pi lb ub env m p Hlen Hnd proj Hproj Hlb Hub.
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
    rewrite find_bounds_correct by eauto.
    unfold in_poly in Hinproj. rewrite forallb_forall in Hinproj.
    intros; auto.
  - intros [x [H1 H2]]; exists x; assumption.
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
    bind_imp_destruct Hgen lb Hlb. apply res_to_alarm_correct in Hlb.
    bind_imp_destruct Hgen ub Hub. apply res_to_alarm_correct in Hub.
    bind_imp_destruct Hgen inner Hinner.
    apply mayReturn_pure in Hgen. rewrite <- Hgen in Hsem.
    inversion_clear Hsem.
    unfold env_poly_lex_semantics in *.
    eapply poly_lex_semantics_extensionality.
    + apply poly_lex_concat_seq with (to_scans := fun x => env_scan (pi :: nil) (rev (x :: env)) n).
      * eapply iter_semantics_map; [|apply H]. simpl.
        intros x mem3 mem4 Hbounds Hloop. eapply IHd with (env := x :: env); simpl; eauto; try lia.
        replace (n - d)%nat with (S (n - S d))%nat in * by lia.
        eapply project_next_r_inclusion; [|exact Hproj|].
        -- rewrite project_invariant_resize. rewrite resize_app by (rewrite rev_length; auto).
           apply Hinv.
        -- rewrite <- find_bounds_correct; eauto.
      * intros x. apply env_scan_proper.
      * intros x1 x2 m p H1 H2. apply env_scan_begin in H1. apply env_scan_begin in H2.
        assert (Heq : resize (length (rev (x1 :: env))) p = resize (length (rev (x2 :: env))) p).
        { simpl. rewrite !app_length; simpl. auto. }
        rewrite H1 in Heq at 1. rewrite H2 in Heq at 2.
        rewrite !resize_app in Heq by auto.
        assert (Heq2: rev (rev (x1 :: env)) = rev (rev (x2 :: env))) by (f_equal; auto).
        rewrite !rev_involutive in Heq2; congruence.
      * intros x1 n1 p1 x2 n2 p2 Hcmp H1 H2.
        apply env_scan_begin in H1; apply env_scan_begin in H2.
        rewrite H1 in Hcmp; rewrite H2 in Hcmp.
        rewrite lex_compare_app in Hcmp by (rewrite !rev_length; simpl; auto).
        simpl in Hcmp. rewrite lex_compare_app in Hcmp by auto.
        rewrite lex_compare_reflexive in Hcmp. simpl in Hcmp.
        destruct (x2 ?= x1) eqn:Hcmpx; reflect; [lia | lia | congruence].
    + simpl. intros m p. erewrite env_scan_extend; eauto; try lia.
      replace (S (n - S d)) with (n - d)%nat by lia. apply Hproj.
Qed.

Fixpoint and_all l :=
  match l with
  | nil => EQ (Constant 0) (Constant 0)
  | x :: l => And x (and_all l)
  end.

Theorem and_all_correct :
  forall l env, eval_test env (and_all l) = forallb (eval_test env) l.
Proof.
  induction l; simpl in *; [auto|].
  intros; rewrite IHl; auto.
Qed.

Definition make_affine_test n c := LE (make_linear_expr n (fst c)) (Constant (snd c)).

Lemma make_affine_test_correct :
  forall env n c, length env = n -> eval_test env (make_affine_test n c) = satisfies_constraint (rev env) c.
Proof.
  intros. simpl in *. rewrite make_linear_expr_correct; auto.
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

(*
Import ListNotations.
Axiom dummy : instr.
Definition test_pi := {|
   pi_instr := dummy ;
   pi_poly := [ ([0; 0; -1; 0], 0); ([0; 0; 0; -1], 0); ([-1; 0; 1; 0], 0); ([0; -1; 0; 1], 0) ] ;
   pi_schedule := [([0; 0; 0; 1], 0); ([0; 0; 1; 0], 0)] ;
   pi_transformation := [([0; 0; 1; 0], 0); ([0; 0; 0; 1], 0)] ;
|}.

Definition test_pi_lex := pi_elim_schedule 2%nat 2%nat test_pi.
Eval cbv in test_pi_lex.
 *)