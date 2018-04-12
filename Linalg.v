Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Psatz.
Require Import Setoid Morphisms.
Require Import RelationPairs.

Require Import Misc.

Open Scope Z_scope.
Open Scope list_scope.
Open Scope vector_scope.

(** * Equality on vectors *)

(** Two vectors are equal iff they are so up to trailing zeros. *)

Definition is_null xs := forallb (fun x => x =? 0) xs.
Transparent is_null.
Hint Unfold is_null.

Fixpoint is_eq (xs ys : list Z) :=
  match xs, ys with
  | nil, nil => true
  | nil, ys => is_null ys
  | xs, nil => is_null xs
  | x :: xs, y :: ys => (x =? y) && is_eq xs ys
  end.

Lemma veq_def xs ys : {P | P <-> is_eq xs ys = true}.
Proof.
  exists (is_eq xs ys = true). reflexivity.
Qed.

(* Definition veq xs ys := proj1_sig (veq_def xs ys). *)

Definition veq xs ys := is_eq xs ys = true.
Infix "=v=" := veq (at level 70) : vector_scope.

Lemma is_eq_veq :
  forall xs ys, is_eq xs ys = true <-> xs =v= ys.
Proof.
  intros. unfold veq. (* destruct (veq_def xs ys). simpl.
  symmetry. assumption. *) reflexivity.
Qed.
Hint Rewrite is_eq_veq : reflect.
Opaque veq.

Lemma is_eq_reflexive :
  forall xs, is_eq xs xs = true.
Proof.
  induction xs; simpl; auto.
  reflect. auto.
Qed.
Hint Immediate is_eq_reflexive.

Lemma veq_refl :
  forall xs, xs =v= xs.
Proof.
  intros. rewrite <- is_eq_veq. apply is_eq_reflexive.
Qed.

Lemma is_eq_commutative :
  forall xs ys, is_eq xs ys = is_eq ys xs.
Proof.
  induction xs.
  - destruct ys; auto.
  - destruct ys; simpl in *; auto.
    f_equal; [apply Z.eqb_sym | auto].
Qed.

Lemma veq_sym :
  forall xs ys, xs =v= ys -> ys =v= xs.
Proof.
  intros. rewrite <- is_eq_veq in *.
  rewrite is_eq_commutative. auto.
Qed.

Lemma is_eq_nil_left :
  forall xs, is_eq nil xs = is_null xs.
Proof.
  destruct xs; auto.
Qed.
Lemma is_eq_nil_right :
  forall xs, is_eq xs nil = is_null xs.
Proof.
  destruct xs; auto.
Qed.
Hint Immediate is_eq_nil_left is_eq_nil_right.
Hint Rewrite is_eq_nil_left is_eq_nil_right : vector.

Lemma is_null_eq_compat :
  forall xs ys, is_eq xs ys = true -> is_null xs = is_null ys.
Proof.
  induction xs.
  - destruct ys; auto.
  - destruct ys; auto. intro Heq. simpl in *.
    reflect; rewrite <- is_eq_veq in *. destruct Heq.
    f_equal; [congruence|auto].
Qed.

Lemma is_eq_is_null_left :
  forall xs ys, is_null xs = true -> is_eq xs ys = is_null ys.
Proof.
  induction xs.
  - destruct ys; auto.
  - destruct ys; auto. simpl. reflect. intros [Ha Heq].
    f_equal.
    + rewrite Ha. apply Z.eqb_sym.
    + auto.
Qed.

Lemma is_eq_is_null_right :
  forall xs ys, is_null ys = true -> is_eq xs ys = is_null xs.
Proof.
  intros. rewrite is_eq_commutative. apply is_eq_is_null_left. auto.
Qed.

Lemma is_eq_is_eq_left :
  forall xs ys zs, is_eq xs ys = true -> is_eq xs zs = is_eq ys zs.
Proof.
  induction xs.
  - intros ys zs Heq. rewrite is_eq_nil_left in *. rewrite is_eq_is_null_left; auto.
  - destruct ys; destruct zs; auto; autorewrite with vector.
    + intros. apply is_eq_is_null_left; auto.
    + intros. apply is_null_eq_compat; auto.
    + simpl in *. reflect. rewrite <- is_eq_veq in *. intros [Ha Heq]. f_equal; [congruence|auto].
Qed.

Lemma is_eq_is_eq_right :
  forall xs ys zs, is_eq ys zs = true -> is_eq xs ys = is_eq xs zs.
Proof.
  intros xs ys zs Heq.
  rewrite is_eq_commutative. erewrite is_eq_is_eq_left; [apply is_eq_commutative|]; auto.
Qed.

Lemma veq_transitive :
  forall xs ys zs, xs =v= ys -> ys =v= zs -> xs =v= zs.
Proof.
  intros xs ys zs H1 H2. rewrite <- is_eq_veq in *.
  erewrite is_eq_is_eq_left; eauto.
Qed.

Instance veq_Equiv : Equivalence veq.
Proof.
  split; [exact veq_refl | exact veq_sym | exact veq_transitive].
Qed.

Instance is_null_proper : Proper (veq ==> eq) is_null.
Proof.
  intros xs1 xs2 Hxs. rewrite <- is_eq_veq in Hxs.
  apply is_null_eq_compat; auto.
Qed.

Instance is_eq_proper : Proper (veq ==> veq ==> eq) is_eq.
Proof.
  intros xs1 xs2 H1 ys1 ys2 H2.
  erewrite is_eq_is_eq_left; [|rewrite is_eq_veq; exact H1].
  apply is_eq_is_eq_right; rewrite is_eq_veq; exact H2.
Qed.

Instance cons_proper : Proper (eq ==> veq ==> veq) cons.
Proof.
  intros x1 x2 Hx xs1 xs2 Hxs.
  rewrite <- is_eq_veq in *. simpl. rewrite Hx. rewrite Z.eqb_refl. auto.
Qed.

Lemma is_eq_app :
  forall l1 l2 l3 l4, length l1 = length l3 -> is_eq (l1 ++ l2) (l3 ++ l4) = is_eq l1 l3 && is_eq l2 l4.
Proof.
  induction l1.
  - intros l2 l3 l4 H. destruct l3; simpl in *; auto; lia.
  - intros l2 l3 l4 H. destruct l3; simpl in *; try lia.
    rewrite IHl1; try lia. destruct (a =? z); auto.
Qed.

Lemma repeat_zero_is_null :
  forall n, is_null (repeat 0 n) = true.
Proof.
  induction n; auto.
Qed.

Lemma same_length_eq :
  forall xs ys, length xs = length ys -> xs =v= ys -> xs = ys.
Proof.
  induction xs.
  - intros ys Hlen Heq. rewrite <- is_eq_veq in Heq. destruct ys; simpl in *; congruence.
  - intros ys Hlen Heq. rewrite <- is_eq_veq in Heq. destruct ys; simpl in *; [congruence|].
    reflect. destruct Heq; f_equal; auto.
Qed.

Instance app_proper : Proper (eq ==> veq ==> veq) (@app Z).
Proof.
  intros l1 l2 Hl r1 r2 Hr.
  rewrite Hl. rewrite <- is_eq_veq.
  rewrite is_eq_app by reflexivity. rewrite is_eq_reflexive; simpl.
  rewrite is_eq_veq; assumption.
Qed.

(** * Dot product *)

Fixpoint dot_product (xs ys : list Z) :=
  match xs, ys with
  | _, nil | nil, _ => 0
  | x :: xs, y :: ys => x * y + dot_product xs ys
  end.

Lemma dot_product_nil_left : forall xs, dot_product nil xs = 0.
Proof.
  intros; destruct xs; auto.
Qed.
Lemma dot_product_nil_right : forall xs, dot_product xs nil = 0.
Proof.
  intros; destruct xs; auto.
Qed.
Hint Immediate dot_product_nil_left dot_product_nil_right.
Hint Rewrite dot_product_nil_left dot_product_nil_right : vector.

Lemma dot_product_commutative : forall xs ys, dot_product xs ys = dot_product ys xs.
Proof.
  induction xs.
  - intro ys; destruct ys; auto.
  - intro ys; destruct ys; [auto|simpl; rewrite IHxs; ring].
Qed.

Lemma dot_product_null_left :
  forall xs ys, is_null xs = true -> dot_product xs ys = 0.
Proof.
  induction xs; auto.
  intros ys Hnull; destruct ys; auto.
  simpl in *; reflect; destruct Hnull as [Hzero Hnull].
  rewrite IHxs; [nia | auto].
Qed.

Lemma dot_product_null_right :
  forall xs ys, is_null ys = true -> dot_product xs ys = 0.
Proof.
  intros xs ys Hnull; rewrite dot_product_commutative; auto using dot_product_null_left.
Qed.

Lemma dot_product_eq_compat_left :
  forall xs ys zs, is_eq xs ys = true -> dot_product xs zs = dot_product ys zs.
Proof.
  induction xs.
  - destruct ys; destruct zs; auto.
    intros. repeat (rewrite dot_product_null_left); auto.
  - destruct ys.
    + destruct zs; intros; repeat (rewrite dot_product_null_left); auto.
    + destruct zs; simpl; auto. reflect; rewrite <- is_eq_veq. intros [Ha Heq].
      f_equal; [congruence | auto].
Qed.

Lemma dot_product_eq_compat_right :
  forall xs ys zs, is_eq ys zs = true -> dot_product xs ys = dot_product xs zs.
Proof.
  intros xs ys zs Heq. rewrite dot_product_commutative.
  erewrite dot_product_eq_compat_left; eauto using dot_product_commutative.
Qed.

Instance dot_product_proper : Proper (veq ==> veq ==> eq) dot_product.
Proof.
  intros xs1 xs2 H1 ys1 ys2 H2.
  erewrite dot_product_eq_compat_left; [|rewrite is_eq_veq; exact H1].
  apply dot_product_eq_compat_right; rewrite is_eq_veq; exact H2.
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
Hint Rewrite dot_product_repeat_zero_left dot_product_repeat_zero_right : vector.

Lemma dot_product_app :
  forall l1 l2 l3 l4, length l1 = length l3 -> dot_product (l1 ++ l2) (l3 ++ l4) = dot_product l1 l3 + dot_product l2 l4.
Proof.
  induction l1.
  - intros l2 l3 l4 H. destruct l3; simpl in *; auto; lia.
  - intros l2 l3 l4 H. destruct l3; simpl in *; try lia. rewrite IHl1; lia.
Qed.


(** * Constraints and polyhedra *)

Definition constraint := (list Z * Z)%type.

Definition satisfies_constraint p c := dot_product p (fst c) <=? (snd c).
Transparent satisfies_constraint.
Hint Unfold satisfies_constraint.

Definition ceq := (veq * @eq Z)%signature.
Transparent ceq.
Infix "=c=" := ceq (at level 70) : vector_scope.

Instance satisfies_constraint_proper : Proper (veq ==> ceq ==> eq) satisfies_constraint.
Proof.
  intros p1 p2 H1 c1 c2 H2.
  unfold satisfies_constraint. rewrite H1. rewrite H2. reflexivity.
Qed.

Definition polyhedron := list constraint.

Definition in_poly p pol := forallb (satisfies_constraint p) pol.
Instance in_poly_proper : Proper (veq ==> eq ==> eq) in_poly.
Proof.
  intros p1 p2 H1 pol1 pol2 H2.
  rewrite H2. unfold in_poly.
  apply forallb_ext. intros. rewrite H1. reflexivity.
Qed.

Lemma in_poly_app :
  forall p pol1 pol2, in_poly p (pol1 ++ pol2) = in_poly p pol1 && in_poly p pol2.
Proof.
  intros. unfold in_poly. apply forallb_app.
Qed.

Definition empty_poly (pol : polyhedron) :=
  forall p, in_poly p pol = false.
Definition empty_constraint : constraint := (nil, -1).
Definition null_constraint : constraint := (nil, 0).
Transparent empty_poly empty_constraint null_constraint.
Hint Unfold empty_poly empty_constraint null_constraint.

Lemma empty_constraint_empty : forall p, satisfies_constraint p empty_constraint = false.
Proof.
  intros. autounfold; simpl; autorewrite with vector. auto.
Qed.
Lemma null_constraint_trivial : forall p, satisfies_constraint p null_constraint = true.
Proof.
  intros. autounfold; simpl; autorewrite with vector. auto.
Qed.





(** * Multiplying a vector by a constant *)

Definition mult_vector k xs := map (fun x => k * x) xs.
Definition mult_constraint (k : Z) (c : constraint) :=
  (mult_vector k (fst c), k * snd c).
Transparent mult_constraint.
Hint Unfold mult_constraint.

Lemma mult_vector_null :
  forall k xs, is_null xs = true -> is_null (mult_vector k xs) = true.
Proof.
  intros k. induction xs; auto.
  simpl. reflect.
  intros [Ha Hnull]. split; [nia | auto].
Qed.

Lemma mult_vector_eq_compat :
  forall k xs ys, is_eq xs ys = true -> is_eq (mult_vector k xs) (mult_vector k ys) = true.
Proof.
  intros k. induction xs.
  - intros ys Heq. rewrite is_eq_nil_left in *. apply mult_vector_null; auto.
  - destruct ys.
    + intros Heq. rewrite is_eq_nil_right in *. apply mult_vector_null; auto.
    + simpl. reflect. repeat (rewrite <- is_eq_veq in *).
      intros [Ha Heq]. split; [congruence | apply IHxs; auto].
Qed.

Instance mult_vector_proper : Proper (eq ==> veq ==> veq) mult_vector.
Proof.
  intros k1 k2 Hk xs1 xs2 Hx.
  rewrite Hk. rewrite <- is_eq_veq in *.
  apply mult_vector_eq_compat; auto.
Qed.

Instance mult_constraint_proper : Proper (eq ==> ceq ==> ceq) mult_constraint.
Proof.
  intros k1 k2 Hk c1 c2 Hc.
  rewrite Hk. unfold mult_constraint.
  rewrite Hc. reflexivity.
Qed.

Lemma dot_product_mult_left :
  forall k xs ys, dot_product (mult_vector k xs) ys = k * dot_product xs ys.
Proof.
  intros k. induction xs.
  - intro ys. repeat (rewrite dot_product_nil_left). ring.
  - intro ys. destruct ys.
    + repeat (rewrite dot_product_nil_right). ring.
    + simpl. rewrite IHxs. ring.
Qed.

Lemma dot_product_mult_right :
  forall k xs ys, dot_product xs (mult_vector k ys) = k * dot_product xs ys.
Proof.
  intros.
  rewrite dot_product_commutative.
  rewrite dot_product_mult_left.
  rewrite dot_product_commutative.
  auto.
Qed.
Hint Rewrite dot_product_mult_left dot_product_mult_right : vector.

Lemma mult_constraint_eq :
  forall k c p, k > 0 -> satisfies_constraint p (mult_constraint k c) = satisfies_constraint p c.
Proof.
  intros k c p Hpos.
  destruct (satisfies_constraint p c) eqn:Heq; autounfold in *; simpl in *; rewrite dot_product_mult_right; reflect; nia.
Qed.

Lemma mult_constraint_zero :
  forall c p, satisfies_constraint p (mult_constraint 0 c) = true.
Proof.
  intros c p. autounfold; simpl; rewrite dot_product_mult_right.
  reflect; lia.
Qed.

Lemma mult_constraint_pos_satisfy :
  forall k c p, k >= 0 -> satisfies_constraint p c = true -> satisfies_constraint p (mult_constraint k c) = true.
Proof.
  intros k c p Hpos Hsat. destruct (Z.lt_total k 0) as [Hk | [Hk | Hk]].
  - lia.
  - rewrite Hk; apply mult_constraint_zero.
  - rewrite mult_constraint_eq; auto; lia.
Qed.

Lemma mult_vector_length :
  forall k v, length (mult_vector k v) = length v.
Proof.
  intros. apply map_length.
Qed.


(** * Adding two vectors *)

Fixpoint add_vector xs ys :=
  match xs, ys with
  | nil, nil => nil
  | nil, ys => ys
  | xs, nil => xs
  | x :: xs, y :: ys => (x + y) :: add_vector xs ys
  end.

Lemma add_vector_nil_left :
  forall xs, add_vector nil xs = xs.
Proof.
  intro xs; destruct xs; auto.
Qed.
Lemma add_vector_nil_right :
  forall xs, add_vector xs nil = xs.
Proof.
  intro xs; destruct xs; auto.
Qed.
Hint Immediate add_vector_nil_left add_vector_nil_right.
Hint Rewrite add_vector_nil_left add_vector_nil_right : vector.

Lemma add_vector_commutative :
  forall xs ys, add_vector xs ys = add_vector ys xs.
Proof.
  induction xs.
  - intro ys; destruct ys; auto.
  - intro ys; destruct ys; auto.
    simpl; f_equal; [ring | auto].
Qed.

Lemma add_vector_null_left :
  forall xs ys, is_null xs = true -> is_eq (add_vector xs ys) ys = true.
Proof.
  induction xs.
  - intros ys Heq. rewrite add_vector_nil_left. apply is_eq_reflexive.
  - intros ys Heq. destruct ys; auto.
    simpl in *; reflect; rewrite <- is_eq_veq in *.
    destruct Heq as [Ha Heq]; split; [lia | apply IHxs; auto].
Qed.

Lemma add_vector_null_right :
  forall xs ys, is_null ys = true -> is_eq (add_vector xs ys) xs = true.
Proof.
  intros xs ys Heq. rewrite add_vector_commutative. apply add_vector_null_left. auto.
Qed.

Lemma add_vector_eq_compat_left :
  forall xs ys zs, is_eq xs ys = true -> is_eq (add_vector xs zs) (add_vector ys zs) = true.
Proof.
  induction xs.
  - intros ys zs Heq. destruct ys; destruct zs; auto using is_eq_reflexive.
    rewrite add_vector_nil_left. rewrite is_eq_commutative. apply add_vector_null_left. auto.
  - intros ys zs Heq. destruct ys; destruct zs; auto.
    + rewrite add_vector_nil_left. apply add_vector_null_left. auto.
    + simpl in *; reflect; rewrite <- is_eq_veq in *.
      destruct Heq as [Ha Heq]; split; [lia | apply IHxs; auto].
Qed.

Lemma add_vector_eq_compat_right :
  forall xs ys zs, is_eq ys zs = true -> is_eq (add_vector xs ys) (add_vector xs zs) = true.
Proof.
  intros xs ys zs Heq. rewrite add_vector_commutative with (ys := ys).
  rewrite add_vector_commutative with (ys := zs). apply add_vector_eq_compat_left; auto.
Qed.

Instance add_vector_proper : Proper (veq ==> veq ==> veq) add_vector.
Proof.
  intros xs1 xs2 Hx ys1 ys2 Hy.
  transitivity (add_vector xs2 ys1).
  - rewrite <- is_eq_veq in *; erewrite add_vector_eq_compat_left; [reflexivity|exact Hx].
  - rewrite <- is_eq_veq in *; apply add_vector_eq_compat_right. exact Hy.
Qed.

Lemma add_vector_mult_distr :
  forall k xs ys, mult_vector k (add_vector xs ys) = add_vector (mult_vector k xs) (mult_vector k ys).
Proof.
  induction xs.
  - intro ys; destruct ys; auto.
  - intro ys; destruct ys; auto.
    simpl; f_equal; [ring | auto].
Qed.

Lemma add_vector_dot_product_distr_left :
  forall xs ys zs, dot_product (add_vector xs ys) zs = dot_product xs zs + dot_product ys zs.
Proof.
  induction xs.
  - intros ys zs; destruct ys; destruct zs; auto.
  - intros ys zs; destruct ys; destruct zs; simpl; try rewrite IHxs; ring.
Qed.

Lemma add_vector_dot_product_distr_right :
  forall xs ys zs, dot_product xs (add_vector ys zs) = dot_product xs ys + dot_product xs zs.
Proof.
  intros xs ys zs. rewrite dot_product_commutative. rewrite add_vector_dot_product_distr_left.
  f_equal; apply dot_product_commutative.
Qed.

(** * Adding constraints *)

Definition add_constraint c1 c2 := (add_vector (fst c1) (fst c2), snd c1 + snd c2).
Transparent add_constraint.
Hint Unfold add_constraint.

Instance add_constraint_proper : Proper (ceq ==> ceq ==> ceq) add_constraint.
Proof.
  intros c1 c2 Hc d1 d2 Hd.
  unfold add_constraint.
  rewrite Hc. rewrite Hd. reflexivity.
Qed.

Lemma add_constraint_satisfy :
  forall p c1 c2, satisfies_constraint p c1 = true -> satisfies_constraint p c2 = true ->
             satisfies_constraint p (add_constraint c1 c2) = true.
Proof.
  intros p c1 c2 Hs1 Hs2.
  autounfold in *. simpl; reflect. rewrite add_vector_dot_product_distr_right. lia.
Qed.


(** * Certificates for polyhedral operations *)

Definition same_polyhedron pol1 pol2 := forall p, in_poly p pol1 = in_poly p pol2.

Fixpoint combine_constraints comb pol :=
  match comb, pol with
  | nil, _ | _, nil => null_constraint
  | c :: comb, p :: pol => add_constraint (mult_constraint c p) (combine_constraints comb pol)
  end.

Lemma combine_constraints_satisfy :
  forall p comb pol, forallb (fun w => 0 <=? w) comb = true -> forallb (satisfies_constraint p) pol = true ->
                satisfies_constraint p (combine_constraints comb pol) = true.
Proof.
  intros p. induction comb.
  - intros pol Hcomb Hsat. destruct pol; simpl; apply null_constraint_trivial.
  - intros pol Hcomb Hsat. destruct pol; simpl in *.
    + apply null_constraint_trivial.
    + reflect. destruct Hcomb as [Ha Hcomb]. destruct Hsat as [Hc Hsat].
      apply add_constraint_satisfy.
      * apply mult_constraint_pos_satisfy; [lia | auto].
      * apply IHcomb; auto.
Qed.

Definition constraint_entails (c1 c2 : constraint) := is_eq (fst c1) (fst c2) && (snd c1 <=? snd c2).
Hint Unfold constraint_entails.

Lemma constraint_entails_correct :
  forall c1 c2 p, constraint_entails c1 c2 = true -> satisfies_constraint p c1 = true -> satisfies_constraint p c2 = true.
Proof.
  intros c1 c2 p Hent Hsat.
  autounfold in *.
  reflect; destruct Hent as [Heq Hcmp].
  rewrite Heq in Hsat. lia.
Qed.

Definition witness := (list Z * Z)%type.

Definition is_redundant (wit : witness) (pol : polyhedron) (c : constraint) :=
  (0 <? snd wit) &&
    forallb (fun w => 0 <=? w) (fst wit) &&
    constraint_entails (combine_constraints (fst wit) pol) (mult_constraint (snd wit) c).
Transparent is_redundant.
Hint Unfold is_redundant.

Lemma is_redundant_correct :
  forall wit pol c p, is_redundant wit pol c = true -> forallb (satisfies_constraint p) pol = true ->
                 satisfies_constraint p c = true.
Proof.
  intros wit pol c p Hred Hinpoly.
  unfold is_redundant in Hred. reflect.
  destruct Hred as [[Hpos Hcpos] Hent].
  erewrite <- mult_constraint_eq.
  - eapply constraint_entails_correct; eauto.
    apply combine_constraints_satisfy; auto.
  - lia.
Qed.

Definition is_empty (wit : witness) (pol : polyhedron) := is_redundant wit pol empty_constraint.
Transparent is_empty.
Hint Unfold is_empty.

Lemma is_empty_correct :
  forall wit pol, is_empty wit pol = true -> empty_poly pol.
Proof.
  intros wit pol Hemp p.
  assert (~ (in_poly p pol = true)); [|destruct (in_poly p pol); congruence]. intro Hin.
  assert (satisfies_constraint p empty_constraint = true).
  - eapply is_redundant_correct; eauto.
  - rewrite empty_constraint_empty in *; congruence.
Qed.





(** * Lexicographical ordering of vectors *)

Fixpoint lex_compare_nil t :=
  match t with
  | nil => Eq
  | x :: t => match 0 ?= x with Eq => lex_compare_nil t | c => c end
  end.

Lemma lex_compare_nil_is_null :
  forall t, is_null t = true -> lex_compare_nil t = Eq.
Proof.
  induction t; auto.
  intros H; simpl in *. reflect. destruct H as [Ha Hn].
  rewrite Ha; auto.
Qed.

Lemma lex_compare_nil_eq :
  forall t1 t2, is_eq t1 t2 = true -> lex_compare_nil t1 = lex_compare_nil t2.
Proof.
  induction t1.
  - intros t2 H. simpl. rewrite lex_compare_nil_is_null; auto. rewrite is_eq_nil_left in H; auto.
  - intros t2 H. destruct t2.
    + rewrite lex_compare_nil_is_null; auto.
    + simpl in H. reflect. rewrite <- is_eq_veq in *. destruct H as [Ha Hn]. rewrite Ha.
      simpl. destruct z; auto.
Qed.

Fixpoint lex_compare t1 t2 :=
  match t1, t2 with
  | nil, nil => Eq
  | _, nil => CompOpp (lex_compare_nil t1)
  | nil, _ => lex_compare_nil t2
  | x :: t1, y :: t2 => match x ?= y with Eq => lex_compare t1 t2 | c => c end
  end.

Lemma lex_compare_antisym :
  forall t1 t2, lex_compare t1 t2 = CompOpp (lex_compare t2 t1).
Proof.
  induction t1.
  - destruct t2; simpl; auto using CompOpp_involutive.
  - destruct t2; simpl; auto.
    rewrite Z.compare_antisym.
    rewrite IHt1. destruct (z ?= a); auto.
Qed.

Lemma lex_compare_null_left :
  forall t1 t2, is_null t1 = true -> lex_compare t1 t2 = lex_compare_nil t2.
Proof.
  induction t1.
  - intros; destruct t2; auto.
  - intros t2 H; destruct t2; simpl in *; reflect; destruct H as [Ha Hn]; rewrite Ha.
    + rewrite lex_compare_nil_is_null; auto.
    + rewrite IHt1; auto.
Qed.

Lemma lex_compare_nil_left :
  forall t, lex_compare nil t = lex_compare_nil t.
Proof.
  intros; destruct t; auto.
Qed.

Lemma lex_compare_nil_right :
  forall t, lex_compare t nil = CompOpp (lex_compare_nil t).
Proof.
  intros; destruct t; auto.
Qed.

Lemma lex_compare_left_eq :
  forall t1 t2 t3, is_eq t1 t2 = true -> lex_compare t1 t3 = lex_compare t2 t3.
Proof.
  induction t1.
  - intros t2 t3 H. rewrite lex_compare_nil_left. rewrite lex_compare_null_left; auto. rewrite is_eq_nil_left in H; auto.
  - intros t2 t3 H. destruct t2.
    + rewrite lex_compare_nil_left. rewrite lex_compare_null_left; auto. 
    + simpl in H. reflect. rewrite <- is_eq_veq in *. destruct H as [Ha Hn]. rewrite Ha.
      destruct t3.
      * simpl in *. erewrite lex_compare_nil_eq; eauto.
      * simpl. erewrite IHt1; auto.
Qed.

Lemma lex_compare_right_eq :
  forall t1 t2 t3, is_eq t2 t3 = true -> lex_compare t1 t2 = lex_compare t1 t3.
Proof.
  intros t1 t2 t3 H.
  rewrite lex_compare_antisym.
  erewrite lex_compare_left_eq; [|apply H]. rewrite <- lex_compare_antisym. auto.
Qed.

Instance lex_compare_proper : Proper (veq ==> veq ==> eq) lex_compare.
Proof.
  intros s1 s2 Hs t1 t2 Ht.
  transitivity (lex_compare s1 t2).
  - apply lex_compare_right_eq; rewrite is_eq_veq; exact Ht.
  - apply lex_compare_left_eq; rewrite is_eq_veq; exact Hs.
Qed.

Lemma lex_compare_app :
  forall t1 t2 t3 t4, length t1 = length t3 ->
                 lex_compare (t1 ++ t2) (t3 ++ t4) = match lex_compare t1 t3 with Eq => lex_compare t2 t4 | c => c end.
Proof.
  induction t1.
  - intros t2 t3 t4 H. destruct t3; simpl in *; auto; lia.
  - intros t2 t3 t4 H. destruct t3; simpl in *; auto; try lia.
    rewrite IHt1; try lia.
    destruct (a ?= z); auto.
Qed.

Lemma lex_compare_reflexive :
  forall t, lex_compare t t = Eq.
Proof.
  induction t; simpl; try rewrite Z.compare_refl; auto.
Qed.



(** * Product of an affine matrix with a vector *)

Definition affine_product mat p := map (fun t => dot_product (fst t) p + (snd t)) mat.

Instance affine_product_proper : Proper (eq ==> veq ==> eq) affine_product.
Proof.
  intros m1 m2 Hm x1 x2 Hx.
  unfold affine_product. rewrite Hm. apply map_ext. intros. rewrite Hx. reflexivity.
Qed.




(** * Resizing a vector to a fixed size *)

Fixpoint resize (d : nat) (l : list Z) :=
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
Hint Rewrite resize_length : vector.

Theorem resize_nil_null :
  forall d, is_null (resize d nil) = true.
Proof.
  induction d; auto.
Qed.
Hint Immediate resize_nil_null.
Hint Rewrite resize_nil_null : vector.

Theorem resize_eq :
  forall d l, (length l <= d)%nat -> resize d l =v= l.
Proof.
  induction d.
  - intros l H; destruct l; simpl in *; [reflexivity | lia].
  - intros l H; destruct l; simpl in *.
    + rewrite <- is_eq_veq. apply resize_nil_null.
    + rewrite IHd; [reflexivity | lia].
Qed.

Theorem resize_skipn_eq :
  forall d l, resize d l ++ skipn d l =v= l.
Proof.
  induction d.
  - intros l; reflexivity.
  - intros l; destruct l; simpl in *.
    + rewrite app_nil_r; rewrite <- is_eq_veq; apply resize_nil_null.
    + rewrite IHd. reflexivity.
Qed.

Lemma resize_app :
  forall n p q, length p = n -> resize n (p ++ q) = p.
Proof.
  induction n.
  - intros; destruct p; simpl in *; auto; lia.
  - intros p q Hlength; destruct p; simpl in *.
    + lia.
    + rewrite IHn; auto.
Qed.

Lemma resize_app_le :
  forall n p q, (length p <= n)%nat -> resize n (p ++ q) = p ++ resize (n - length p)%nat q.
Proof.
  induction n.
  - intros p q H. destruct p; simpl in *; [auto | lia].
  - intros p q H. destruct p; simpl in *; [|rewrite IHn by lia]; reflexivity.
Qed.

Lemma resize_null_repeat :
  forall n l, is_null l = true -> resize n l = repeat 0 n.
Proof.
  induction n.
  - intros; simpl; auto.
  - intros l H; destruct l; simpl in *.
    + rewrite IHn; auto.
    + reflect. destruct H.
      rewrite IHn; [congruence | auto].
Qed.

Lemma resize_eq_compat :
  forall n l1 l2, is_eq l1 l2 = true -> resize n l1 = resize n l2.
Proof.
  induction n.
  - intros; simpl; auto.
  - intros l1 l2 H.
    destruct l1; destruct l2; simpl in *; reflect; auto; destruct H as [H1 H2]; rewrite <- ?is_eq_veq in H2; 
      f_equal; auto; apply IHn; [rewrite is_eq_nil_left | rewrite is_eq_nil_right]; auto.
Qed.

Instance resize_proper : Proper (eq ==> veq ==> eq) resize.
Proof.
  intros n1 n2 Hn l1 l2 Hl. rewrite Hn. apply resize_eq_compat. rewrite is_eq_veq. auto.
Qed.

Lemma resize_resize :
  forall n m l, (n <= m)%nat -> resize n (resize m l) = resize n l.
Proof.
  induction n.
  - intros m l H. reflexivity.
  - intros m l H. destruct m as [|m]; [lia|].
    destruct l; simpl; rewrite IHn by lia; reflexivity.
Qed.


(** Alternative formulation of previous results that used [++] on both sides *)

Lemma dot_product_app_left :
  forall l1 l2 l3, dot_product (l1 ++ l2) l3 = dot_product l1 (resize (length l1) l3) + dot_product l2 (skipn (length l1) l3).
Proof.
  intros.
  erewrite <- resize_skipn_eq with (l := l3) at 1.
  rewrite dot_product_app; [reflexivity|rewrite resize_length; auto].
Qed.

Lemma dot_product_app_right :
  forall l1 l2 l3, dot_product l1 (l2 ++ l3) = dot_product (resize (length l2) l1) l2 + dot_product (skipn (length l2) l1) l3.
Proof.
  intros. rewrite dot_product_commutative. rewrite dot_product_app_left.
  f_equal; apply dot_product_commutative.
Qed.

Lemma is_eq_app_left :
  forall l1 l2 l3, is_eq (l1 ++ l2) l3 = is_eq l1 (resize (length l1) l3) && is_eq l2 (skipn (length l1) l3).
Proof.
  intros.
  erewrite <- resize_skipn_eq with (l := l3) at 1.
  rewrite is_eq_app; [reflexivity|rewrite resize_length; auto].
Qed.

Lemma is_eq_app_right :
  forall l1 l2 l3, is_eq l1 (l2 ++ l3) = is_eq (resize (length l2) l1) l2 && is_eq (skipn (length l2) l1) l3.
Proof.
  intros. rewrite is_eq_commutative. rewrite is_eq_app_left.
  f_equal; apply is_eq_commutative.
Qed.
