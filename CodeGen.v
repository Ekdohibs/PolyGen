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

Parameter instr : Type.
Parameter mem : Type.
Parameter instr_semantics : instr -> list Z -> mem -> mem -> Prop.

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

Fixpoint zero_after (n : nat) (l : list Z) :=
  match n, l with
  | O, _ => is_null l
  | _, nil => true
  | S n', x :: l' => zero_after n' l'
  end.

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

Definition make_affine_expr (n : nat) (e : (vector * Z)%type) := Sum (make_linear_expr n (fst e)) (Constant (snd e)).

Theorem make_affine_expr_correct :
  forall n e env, length env = n -> eval_expr env (make_affine_expr n e) = dot_product (fst e) (rev env) + snd e.
Proof.
  intros. simpl in *. rewrite make_linear_expr_correct; auto.
Qed.

Parameter project : nat -> polyhedron -> result polyhedron.
Parameter find_lower_bound : nat -> polyhedron -> result expr.
Parameter find_upper_bound : nat -> polyhedron -> result expr.

Axiom project_inclusion :
  forall n p pol proj, project n pol = Ok proj -> in_poly p pol = true -> in_poly (resize n p) proj = true.
Axiom project_reverse_inclusion :
  forall n pol proj c, project n pol = Ok proj -> In c pol -> fst c =v= resize n (fst c) -> (exists c', c =c= c' /\ In c' proj).

Axiom find_lower_bound_correct :
  forall n pol env x lb, find_lower_bound n pol = Ok lb -> length env = n ->
                    eval_expr env lb <= x <-> (forall c, In c pol -> nth n (fst c) 0 < 0 -> satisfies_constraint (rev env ++ x :: nil) c = true).
Axiom find_upper_bound_correct :
  forall n pol env x ub, find_upper_bound n pol = Ok ub -> length env = n ->
                    x < eval_expr env ub <-> (forall c, In c pol -> nth n (fst c) 0 > 0 -> satisfies_constraint (rev env ++ x :: nil) c = true).

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

Lemma nth_skipn :
  forall A n m (l : list A) d, nth n (skipn m l) d = nth (m + n) l d.
Proof.
  induction m.
  - intros. simpl. reflexivity.
  - intros. simpl.
    destruct l; simpl.
    + destruct n; reflexivity.
    + apply IHm.
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
  - intros n pi st env mem1 mem2 Hnd Hgen Hsem Hlen Hpilen Henvsat. simpl in *.
    injection Hgen as Hgen.
    unfold env_poly_lex_semantics.
    eapply PolyLexProgress with (n := 0%nat) (p := rev env); [ |reflexivity| | | apply PolyLexDone].
    + unfold env_scan. simpl. reflect. split; [split|].
      * rewrite resize_eq; reflexivity.
      * rewrite resize_eq; [reflexivity | rewrite rev_length; lia].
      * unfold in_poly. rewrite forallb_forall. intros c Hin.
        apply Henvsat; auto. rewrite Nat.sub_0_r. auto.
    + intros n2 p2 Hcmp.
      apply not_true_iff_false; intros H; apply env_scan_single in H; [|rewrite rev_length; lia].
      rewrite H in Hcmp. rewrite lex_compare_reflexive in Hcmp. congruence.
    + rewrite <- Hgen in Hsem. inversion_clear Hsem.
      unfold affine_product in *. rewrite map_map in H.
      erewrite map_ext in H; [exact H|].
      intros; apply make_affine_expr_correct. lia.
    + intros n1 p1. unfold scanned.
      destruct n1 as [|n1]; [|destruct n1; simpl; auto]. simpl.
      apply not_true_iff_false; intros H; reflect; destruct H as [H1 H2]; apply env_scan_single in H1; [|rewrite rev_length; lia].
      rewrite H1 in H2; rewrite is_eq_reflexive in H2. destruct H2; congruence.
  - intros n pi st env mem1 mem2 Hnd Hgen Hsem Hlen Hpilen Henvsat. simpl in *.
    bind_ok_destruct Hgen proj Hproj. bind_ok_destruct Hgen lb Hlb. bind_ok_destruct Hgen ub Hub. bind_ok_destruct Hgen inner Hinner.
    injection Hgen as Hgen. rewrite <- Hgen in Hsem.
    inversion_clear Hsem.
    unfold env_poly_lex_semantics in *.
    eapply poly_lex_semantics_extensionality.
    + apply poly_lex_concat_seq with (to_scans := fun x => env_scan (pi :: nil) (rev (x :: env)) n).
      * eapply iter_semantics_map; [|apply H]. simpl.
        intros x mem3 mem4 Hbounds Hloop. eapply IHd with (env := x :: env); simpl; eauto.
        -- lia.
        -- lia.
        -- intros c Hin Heq.
           destruct (project_reverse_inclusion (n - d)%nat (pi_poly pi) proj c Hproj Hin Heq) as [c' [Heqc' Hinc']].
           replace (n - d)%nat with (S (n - S d))%nat in Heq by lia.
           rewrite resize_succ in Heq.
           destruct (nth (n - S d) (fst c) 0 =? 0) eqn:Hzero; reflect.
           ++ rewrite Hzero in Heq.
              setoid_replace (0 :: nil) with (@nil Z) in Heq by (rewrite <- is_eq_veq; auto).
              unfold satisfies_constraint. rewrite Heq.
              rewrite dot_product_app by (rewrite rev_length, resize_length; auto). simpl.
              rewrite Z.add_0_r. rewrite app_nil_r in Heq. rewrite <- Heq.
              apply Henvsat; auto.
           ++ rewrite Heqc'. rewrite find_bounds_correct in Hbounds by eauto.
              apply Hbounds; auto. erewrite nth_eq in Hzero; [exact Hzero|].
              rewrite Heqc'; reflexivity.
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
    + simpl. intros m p.
      rewrite eq_iff_eq_true. rewrite existsb_exists.
      rewrite env_scan_split by (rewrite rev_length; lia).
      split.
      * intros [x [H1 H2]]; exists x; assumption.
      * intros [x Hscan]; exists x; split; [|auto].
        rewrite Zrange_in. unfold env_scan in Hscan. destruct m; [|destruct m; simpl in Hscan; congruence].
        simpl in Hscan. reflect.
        destruct Hscan as [[Hscan1 Hscan2] Hscan3].
        assert (Hinproj : in_poly (rev env ++ x :: nil) proj = true).
        { rewrite Hscan1. eapply project_inclusion; [|apply Hscan3].
          rewrite app_length; rewrite rev_length; rewrite Hlen; simpl.
          rewrite <- Hproj. f_equal. lia.
        }
        rewrite find_bounds_correct by eauto.
        unfold in_poly in Hinproj. rewrite forallb_forall in Hinproj.
        intros; auto.
Qed.
