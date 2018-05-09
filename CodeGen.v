Require Import String.

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


(** * Polyhedral projection, using an untrusted oracle and a certificate *)

Module Type PolyProject.
  Parameter project : nat -> polyhedron -> result polyhedron.

  Parameter project_inclusion :
    forall n p pol proj, project n pol = Ok proj -> in_poly p pol = true -> in_poly (resize n p) proj = true.

  Parameter project_invariant : nat -> polyhedron -> list Z -> Prop.

  Parameter project_invariant_inclusion :
    forall n pol p, in_poly p pol = true -> project_invariant n pol (resize n p).

  Parameter project_id :
    forall n pol p, (forall c, In c pol -> fst c =v= resize n (fst c)) -> project_invariant n pol p -> in_poly p pol = true.

  Parameter project_next_r_inclusion :
    forall n pol proj p, project (S n) pol = Ok proj -> project_invariant n pol p ->
                    (forall c, In c proj -> nth n (fst c) 0 <> 0 -> satisfies_constraint p c = true) -> project_invariant (S n) pol p.

  Parameter project_invariant_resize :
    forall n pol p, project_invariant n pol p <-> project_invariant n pol (resize n p).

  Parameter project_invariant_export : nat -> polyhedron -> result polyhedron.

  Parameter project_invariant_export_correct :
    forall n p pol res, project_invariant_export n pol = Ok res -> in_poly p res = true <-> project_invariant n pol p.

  Parameter project_constraint_size :
    forall n pol proj c, project n pol = Ok proj -> In c proj -> fst c =v= resize n (fst c).

End PolyProject.

Ltac destruct_if H Heq :=
  lazymatch goal with
    | [ H : context[if ?X then _ else _] |- _ ] => destruct X eqn:Heq
  end.

Module PolyProjectSimple <: PolyProject.

  Parameter untrusted_project : nat -> polyhedron -> (polyhedron * list witness)%type.

  Definition project n p :=
    let (res, wits) := untrusted_project n p in
    if negb (length res =? length wits)%nat then
      Err "Incorrect number of witnesses"
    else if negb (forallb (fun c => is_eq (fst c) (resize n (fst c))) res) then
      Err "Constraint too long"
    else if negb (forallb (fun z => is_redundant (snd z) p (fst z)) (combine res wits)) then
      Err "Witness checking failed"
    else if negb (forallb (fun c => negb (is_eq (fst c) (resize n (fst c))) || existsb (fun c' => is_eq (fst c) (fst c') && (snd c =? snd c')) res) p) then
      Err "Constraint removed in projection"
    else
      Ok res.

  Theorem project_inclusion :
    forall n p pol proj, project n pol = Ok proj -> in_poly p pol = true -> in_poly (resize n p) proj = true.
  Proof.
    intros n p pol proj Hok Hin.
    unfold project in Hok.
    destruct (untrusted_project n pol) as [res wits].
    destruct_if Hok Hlen; reflect; [congruence|].
    destruct_if Hok Hresize; reflect; [congruence|].
    destruct_if Hok Hwits; reflect; [congruence|].
    destruct_if Hok Hpreserve; reflect; [congruence|].
    injection Hok as Hok; rewrite Hok in *.
    assert (Hinproj : in_poly p proj = true).
    - unfold in_poly. rewrite forallb_forall. intros c Hc.
      apply in_l_combine with (l' := wits) in Hc; [|auto].
      destruct Hc as [wit Hwit].
      eapply is_redundant_correct; [|apply Hin].
      rewrite forallb_forall in Hwits.
      apply (Hwits (c, wit)); auto.
    - unfold in_poly in *. rewrite forallb_forall in *. intros c Hc.
      rewrite <- (Hinproj c) by auto.
      unfold satisfies_constraint. f_equal. specialize (Hresize c Hc). reflect.
      rewrite Hresize.
      rewrite <- dot_product_resize_left with (t1 := p). rewrite resize_length. reflexivity.
  Qed.

  Definition project_invariant n pol p :=
    forall c, In c pol -> fst c =v= resize n (fst c) -> satisfies_constraint p c = true.

  Theorem project_reverse_inclusion :
    forall n pol proj c, project n pol = Ok proj -> In c pol -> fst c =v= resize n (fst c) -> (exists c', c =c= c' /\ In c' proj).
  Proof.
    intros n pol proj c Hok Hin Heq.
    unfold project in Hok.
    destruct (untrusted_project n pol) as [res wits].
    destruct_if Hok Hlen; reflect; [congruence|].
    destruct_if Hok Hresize; reflect; [congruence|].
    destruct_if Hok Hwits; reflect; [congruence|].
    destruct_if Hok Hpreserve; reflect; [congruence|].
    injection Hok as Hok; rewrite Hok in *.
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
    forall n pol proj p, project (S n) pol = Ok proj -> project_invariant n pol p ->
                    (forall c, In c proj -> nth n (fst c) 0 <> 0 -> satisfies_constraint p c = true) -> project_invariant (S n) pol p.
  Proof.
    intros n pol proj p Hproj Hinv Hsat c Hcin Hclen.
    destruct (nth n (fst c) 0 =? 0) eqn:Hzero; reflect.
    - rewrite resize_succ in Hclen. rewrite Hzero in Hclen.
      setoid_replace (0 :: nil) with (@nil Z) in Hclen by (rewrite <- is_eq_veq; auto).
      rewrite app_nil_r in Hclen.
      apply Hinv; auto.
    - destruct (project_reverse_inclusion (S n) pol proj c Hproj Hcin Hclen) as [c' [Heqc' Hc'in]].
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

  Definition project_invariant_export n (pol : polyhedron) :=
    Ok (filter (fun c => is_eq (fst c) (resize n (fst c))) pol).

  Theorem project_invariant_export_correct :
    forall n p pol res, project_invariant_export n pol = Ok res -> in_poly p res = true <-> project_invariant n pol p.
  Proof.
    intros n p pol res Heq. unfold project_invariant_export in Heq; injection Heq as Heq.
    rewrite <- Heq in *. unfold project_invariant. unfold in_poly.
    rewrite forallb_forall. under_forall ((list Z * Z)%type) ltac:(fun x => rewrite filter_In; reflect).
    firstorder.
  Qed.

  Theorem project_constraint_size :
    forall n pol proj c, project n pol = Ok proj -> In c proj -> fst c =v= resize n (fst c).
  Proof.
    intros n pol proj c Hproj Hin.
    unfold project in Hproj.
    destruct (untrusted_project n pol) as [res wits].
    destruct_if Hproj Hlen; [congruence|].
    destruct_if Hproj Hresize; [congruence|].
    destruct_if Hproj Hwits; [congruence|].
    destruct_if Hproj Hpreserve; [congruence|].
    injection Hproj as Hproj; rewrite Hproj in *.
    reflect. rewrite forallb_forall in Hresize. specialize (Hresize c); reflect; eauto.
  Qed.

End PolyProjectSimple.

Require Import Vpl.DomainInterfaces.
Require Import Vpl.ConsSet.
Require Import Vpl.PedraQ.
Require Import VplInterface.

Module PolyProjectVPL (Dom : HasAssume QNum Cstr BasicD) <: PolyProject.

  Axiom extractImp : forall A, imp A -> A.

  Definition project n p := Ok p.

  Theorem project_inclusion :
    forall n p pol proj, project n pol = Ok proj -> in_poly p pol = true -> in_poly (resize n p) proj = true.
  Proof.
  Qed.

  Definition project_invariant n pol p :=
    forall c, In c pol -> fst c =v= resize n (fst c) -> satisfies_constraint p c = true.

  Theorem project_reverse_inclusion :
    forall n pol proj c, project n pol = Ok proj -> In c pol -> fst c =v= resize n (fst c) -> (exists c', c =c= c' /\ In c' proj).
  Proof.
  Qed.

  Theorem project_invariant_inclusion :
    forall n pol p, in_poly p pol = true -> project_invariant n pol (resize n p).
  Proof.
  Qed.

  Theorem project_id :
    forall n pol p, (forall c, In c pol -> fst c =v= resize n (fst c)) -> project_invariant n pol p -> in_poly p pol = true.
  Proof.
  Qed.

  Theorem project_next_r_inclusion :
    forall n pol proj p, project (S n) pol = Ok proj -> project_invariant n pol p ->
                    (forall c, In c proj -> nth n (fst c) 0 <> 0 -> satisfies_constraint p c = true) -> project_invariant (S n) pol p.
  Proof.
  Qed.

  Theorem project_invariant_resize :
    forall n pol p, project_invariant n pol p <-> project_invariant n pol (resize n p).
  Proof.
  Qed.

  Definition project_invariant_export n (pol : polyhedron) :=
    Ok (filter (fun c => is_eq (fst c) (resize n (fst c))) pol).

  Theorem project_invariant_export_correct :
    forall n p pol res, project_invariant_export n pol = Ok res -> in_poly p res = true <-> project_invariant n pol p.
  Proof.
  Qed.

  Theorem project_constraint_size :
    forall n pol proj c, project n pol = Ok proj -> In c proj -> fst c =v= resize n (fst c).
  Proof.
  Qed.

End PolyProjectVPL.

Import PolyProjectSimple.

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

Fixpoint generate_loop (d : nat) (n : nat) (pi : Polyhedral_Instruction) : result stmt :=
  match d with
  | O => Ok (Instr pi.(pi_instr) (map (make_affine_expr n) pi.(pi_transformation)))
  | S d1 =>
    do proj <- project (n - d1)%nat pi.(pi_poly) ;
    do lb <- find_lower_bound (n - d)%nat proj ;
    do ub <- find_upper_bound (n - d)%nat proj ;
    do inner <- generate_loop d1 n pi ;
    Ok (Loop lb ub inner)
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
  forall n pi st env mem1 mem2,
    generate_loop 0%nat n pi = Ok st ->
    loop_semantics st env mem1 mem2 ->
    length env = n ->
    in_poly (rev env) pi.(pi_poly) = true ->
    env_poly_lex_semantics (rev env) n (pi :: nil) mem1 mem2.
Proof.
  intros n pi st env mem1 mem2 Hgen Hsem Hlen Henvsat. simpl in *.
  injection Hgen as Hgen.
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

(*
Lemma satisfies_extend :
  forall n pol proj lb ub env x,
    length env = n ->
    (forall c, In c pol -> fst c =v= resize n (fst c) -> satisfies_constraint (rev env) c = true) ->
    project (S n) pol = Ok proj ->
    find_lower_bound n proj = Ok lb ->
    find_upper_bound n proj = Ok ub ->
    eval_expr env lb <= x < eval_expr env ub ->
    (forall c, In c pol -> fst c =v= resize (S n) (fst c) -> satisfies_constraint (rev env ++ x :: nil) c = true).
Proof.
  intros n pol proj lb ub env x Hlen Hsat Hproj Hlb Hub Hx c Hin Hsize.
  destruct (project_reverse_inclusion (S n) pol proj c Hproj Hin Hsize) as [c' [Heqc' Hinc']].
  rewrite resize_succ in Hsize.
  destruct (nth n (fst c) 0 =? 0) eqn:Hzero; reflect.
  - rewrite Hzero in Hsize.
    setoid_replace (0 :: nil) with (@nil Z) in Hsize by (rewrite <- is_eq_veq; auto).
    unfold satisfies_constraint. rewrite Hsize.
    rewrite dot_product_app by (rewrite rev_length, resize_length; auto). simpl.
    rewrite Z.add_0_r. rewrite app_nil_r in Hsize.
    rewrite <- Hsize. apply Hsat; auto.
  - rewrite Heqc'. rewrite find_bounds_correct in Hx by eauto.
    apply Hx; auto. erewrite nth_eq in Hzero; [exact Hzero|].
    rewrite Heqc'; reflexivity.
Qed.
 *)

Lemma env_scan_extend :
  forall d n pi proj lb ub env m p,
    length env = n ->
    (n < d)%nat ->
    project (S n) pi.(pi_poly) = Ok proj ->
    find_lower_bound n proj = Ok lb ->
    find_upper_bound n proj = Ok ub ->
    env_scan (pi :: nil) (rev env) d m p =
      existsb (fun x : Z => env_scan (pi :: nil) (rev env ++ x :: nil) d m p) (Zrange (eval_expr env lb) (eval_expr env ub)).
Proof.
  intros d n pi proj lb ub env m p Hlen Hnd Hproj Hlb Hub.
  rewrite eq_iff_eq_true. rewrite existsb_exists.
  rewrite env_scan_split by (rewrite rev_length; lia).
  split.
  - intros [x Hscan]; exists x; split; [|auto].
    rewrite Zrange_in. unfold env_scan in Hscan. destruct m; [|destruct m; simpl in Hscan; try congruence].
    simpl in Hscan. reflect.
    destruct Hscan as [[Hscan1 Hscan2] Hscan3].
    assert (Hinproj : in_poly (rev env ++ x :: nil) proj = true).
    {
      rewrite Hscan1. eapply project_inclusion; [|apply Hscan3].
      rewrite app_length; rewrite rev_length; rewrite Hlen; simpl.
      rewrite <- Hproj. f_equal. lia.
    }
    rewrite find_bounds_correct by eauto.
    unfold in_poly in Hinproj. rewrite forallb_forall in Hinproj.
    intros; auto.
  - intros [x [H1 H2]]; exists x; assumption.
Qed.

Theorem generate_loop_preserves_sem :
  forall d n pi st env mem1 mem2,
    (d <= n)%nat ->
    generate_loop d n pi = Ok st ->
    loop_semantics st env mem1 mem2 ->
    length env = (n - d)%nat ->
    (forall c, In c pi.(pi_poly) -> fst c =v= resize n (fst c)) ->
    project_invariant (n - d)%nat pi.(pi_poly) (rev env) ->
    env_poly_lex_semantics (rev env) n (pi :: nil) mem1 mem2.
Proof.
  induction d.
  - intros n pi st env mem1 mem2 Hnd Hgen Hsem Hlen Hpilen Hinv.
    eapply generate_loop_single_point; eauto; try lia.
    eapply project_id; eauto.
    rewrite Nat.sub_0_r in Hinv. auto.
  - intros n pi st env mem1 mem2 Hnd Hgen Hsem Hlen Hpilen Hinv. simpl in *.
    bind_ok_destruct Hgen proj Hproj. bind_ok_destruct Hgen lb Hlb. bind_ok_destruct Hgen ub Hub. bind_ok_destruct Hgen inner Hinner.
    injection Hgen as Hgen. rewrite <- Hgen in Hsem.
    inversion_clear Hsem.
    unfold env_poly_lex_semantics in *.
    eapply poly_lex_semantics_extensionality.
    + apply poly_lex_concat_seq with (to_scans := fun x => env_scan (pi :: nil) (rev (x :: env)) n).
      * eapply iter_semantics_map; [|apply H]. simpl.
        intros x mem3 mem4 Hbounds Hloop. eapply IHd with (env := x :: env); simpl; eauto; try lia.
        replace (n - d)%nat with (S (n - S d))%nat in * by lia.
        eapply project_next_r_inclusion; [exact Hproj| |].
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
      rewrite <- Hproj; f_equal; lia.
Qed.

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

Fixpoint and_all l :=
  match l with
  | nil => EQ (Constant 0) (Constant 0)
  | x :: l => And x (and_all l)
  end.

Theorem and_all_correct :
  forall l env, eval_test env (and_all l) = forallb (eval_test env) l.
Proof.
  induction l; simpl in *; auto.
(*  intros; rewrite IHl; auto. *)
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

(*
Definition make_smalldims_test d n poly :=
  and_all (map (make_affine_test n) (filter (fun c => is_eq (fst c) (resize d (fst c))) poly)).

Lemma make_smalldims_test_correct :
  forall d n poly env, length env = n ->
                  eval_test env (make_smalldims_test d n poly) = true <->
                  (forall c, In c poly -> fst c =v= resize d (fst c) -> satisfies_constraint (rev env) c = true).
Proof.
  intros d n poly env Hlen.
  unfold make_smalldims_test. rewrite and_all_correct. rewrite forallb_map. rewrite forallb_forall.
  apply forall_ext. intros c. rewrite make_affine_test_correct by auto.
  rewrite filter_In. tauto.
Qed.
 *)

Definition generate d n pi :=
  do st <- generate_loop d n pi ;
  do ctx <- project_invariant_export (n - d)%nat pi.(pi_poly) ;
  Ok (Guard (make_poly_test (n - d)%nat ctx) st).

Theorem generate_preserves_sem :
  forall d n pi st env mem1 mem2,
    (d <= n)%nat ->
    generate d n pi = Ok st ->
    loop_semantics st env mem1 mem2 ->
    length env = (n - d)%nat ->
    (forall c, In c pi.(pi_poly) -> fst c =v= resize n (fst c)) ->
    env_poly_lex_semantics (rev env) n (pi :: nil) mem1 mem2.
Proof.
  intros d n pi st env mem1 mem2 Hd Hgen Hloop Henv Hsize.
  bind_ok_destruct Hgen st1 H. bind_ok_destruct Hgen ctx Hctx. injection Hgen as Hgen.
  rewrite <- Hgen in *. inversion_clear Hloop.
  - eapply generate_loop_preserves_sem; eauto.
    rewrite <- project_invariant_export_correct by eauto.
    erewrite <- make_poly_test_correct; [|apply Henv]. auto.
  - apply PolyLexDone. intros n0 p. unfold env_scan.
    destruct n0; simpl in *; [|destruct n0]; auto. reflect.
    rewrite rev_length; rewrite Henv.
    rewrite make_poly_test_correct in H0; auto.
    destruct (is_eq (rev env) (resize (n - d)%nat p)) eqn:Hpenv; auto.
    destruct (in_poly p pi.(pi_poly)) eqn:Hpin; auto. exfalso.
    eapply project_invariant_inclusion in Hpin.
    rewrite <- project_invariant_export_correct in Hpin; [|exact Hctx].
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