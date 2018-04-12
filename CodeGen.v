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

Ltac destruct_if H Heq :=
  lazymatch goal with
    | [ H : context[if ?X then _ else _] |- _ ] => destruct X eqn:Heq
  end.

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

Lemma resize_succ :
  forall n l, resize (S n) l = resize n l ++ nth n l 0 :: nil.
Proof.
  induction n.
  - intros; destruct l; simpl; auto.
  - intros; destruct l; simpl in *; f_equal.
    + rewrite (IHn nil). destruct n; auto.
    + apply IHn.
Qed.

Theorem nth_eq :
  forall n l1 l2, l1 =v= l2 -> nth n l1 0 = nth n l2 0.
Proof.
  induction n.
  - intros l1 l2 H. rewrite <- is_eq_veq in H.
    destruct l1; destruct l2; simpl in *; reflect; auto; destruct H; auto.
  - intros l1 l2 H. rewrite <- is_eq_veq in H.
    destruct l1; destruct l2; simpl in *; reflect; auto; destruct H; auto.
    + specialize (IHn nil l2). rewrite <- is_eq_veq in IHn. rewrite <- IHn by (destruct l2; auto). destruct n; auto.
    + specialize (IHn l1 nil). rewrite <- is_eq_veq in IHn. rewrite IHn by (destruct l1; auto). destruct n; auto.
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
    (forall c, In c pi.(pi_poly) -> fst c =v= resize (n - d)%nat (fst c) -> satisfies_constraint (rev env) c = true) ->
    env_poly_lex_semantics (rev env) n (pi :: nil) mem1 mem2.
Proof.
  induction d.
  - intros n pi st env mem1 mem2 Hnd Hgen Hsem Hlen Hpilen Henvsat.
    eapply generate_loop_single_point; eauto; try lia.
    unfold in_poly. rewrite forallb_forall. intros c Hin.
    apply Henvsat; auto. rewrite Nat.sub_0_r. auto.
  - intros n pi st env mem1 mem2 Hnd Hgen Hsem Hlen Hpilen Henvsat. simpl in *.
    bind_ok_destruct Hgen proj Hproj. bind_ok_destruct Hgen lb Hlb. bind_ok_destruct Hgen ub Hub. bind_ok_destruct Hgen inner Hinner.
    injection Hgen as Hgen. rewrite <- Hgen in Hsem.
    inversion_clear Hsem.
    unfold env_poly_lex_semantics in *.
    eapply poly_lex_semantics_extensionality.
    + apply poly_lex_concat_seq with (to_scans := fun x => env_scan (pi :: nil) (rev (x :: env)) n).
      * eapply iter_semantics_map; [|apply H]. simpl.
        intros x mem3 mem4 Hbounds Hloop. eapply IHd with (env := x :: env); simpl; eauto; try lia.
        replace (n - d)%nat with (S (n - S d))%nat in * by lia.
        eapply satisfies_extend; eauto.
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