Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Psatz.
Open Scope Z_scope.
Open Scope list_scope.

Definition vector := list Z.

Fixpoint dot_product (xs ys : vector) :=
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

Lemma dot_product_commutative : forall xs ys, dot_product xs ys = dot_product ys xs.
Proof.
  induction xs.
  - intro ys; destruct ys; auto.
  - intro ys; destruct ys; [auto|simpl; rewrite IHxs; ring].
Qed.

Definition constraint := (vector * Z)%type.

Definition satisfies_constraint (p : vector) (c : constraint) :=
  dot_product p (fst c) <=? (snd c).

Hint Unfold satisfies_constraint.

Definition polyhedron := list constraint.

Definition in_poly (p : vector) (pol : polyhedron) :=
  forallb (satisfies_constraint p) pol.

Definition empty_poly (pol : polyhedron) :=
  forall p, Is_true (negb (in_poly p pol)).

Definition empty_constraint : constraint := (nil, -1).
Definition null_constraint : constraint := (nil, 0).
Hint Unfold empty_constraint null_constraint.
Lemma empty_constraint_empty : forall p, satisfies_constraint p empty_constraint = false.
Proof.
  intros. autounfold; simpl. rewrite dot_product_nil_right; auto.
Qed.
Lemma null_constraint_trivial : forall p, satisfies_constraint p null_constraint = true.
Proof.
  intros. autounfold; simpl. rewrite dot_product_nil_right; auto.
Qed.

Definition mult_vector (k : Z) (xs : vector) := map (fun x => k * x) xs.

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

Definition mult_constraint (k : Z) (c : constraint) :=
  (mult_vector k (fst c), k * snd c).
Hint Unfold mult_constraint.

Lemma mult_constraint_eq :
  forall k c p, k > 0 -> satisfies_constraint p (mult_constraint k c) = satisfies_constraint p c.
Proof.
  intros k c p Hpos.
  destruct (satisfies_constraint p c) eqn:Heq; autounfold in *; simpl in *; rewrite dot_product_mult_right.
  - rewrite Z.leb_le in *. nia.
  - rewrite Z.leb_gt in *. nia.
Qed.

Lemma mult_constraint_zero :
  forall c p, satisfies_constraint p (mult_constraint 0 c) = true.
Proof.
  intros c p. autounfold; simpl; rewrite dot_product_mult_right.
  rewrite Z.leb_le. lia.
Qed.

Lemma mult_constraint_pos_satisfy :
  forall k c p, k >= 0 -> satisfies_constraint p c = true -> satisfies_constraint p (mult_constraint k c) = true.
Proof.
  intros k c p Hpos Hsat. destruct (Z.lt_total k 0) as [Hk | [Hk | Hk]].
  - lia.
  - rewrite Hk; apply mult_constraint_zero.
  - rewrite mult_constraint_eq; auto; lia.
Qed.

Fixpoint add_vector (xs ys : vector) :=
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

Lemma add_vector_commutative :
  forall xs ys, add_vector xs ys = add_vector ys xs.
Proof.
  induction xs.
  - intro ys; destruct ys; auto.
  - intro ys; destruct ys; auto.
    simpl; f_equal; [ring | auto].
Qed.

Lemma add_vector_mult_distr :
  forall k xs ys, mult_vector k (add_vector xs ys) = add_vector (mult_vector k xs) (mult_vector k ys).
Proof.
  induction xs.
  - intro ys; destruct ys; auto.
  - intro ys; destruct ys; auto.
    simpl; f_equal; [ring | auto].
Qed.

Lemma add_vector_dot_product_dist_left :
  forall xs ys zs, dot_product (add_vector xs ys) zs = dot_product xs zs + dot_product ys zs.
Proof.
  induction xs.
  - intros ys zs; destruct ys; destruct zs; auto.
  - intros ys zs; destruct ys; destruct zs; simpl; try rewrite IHxs; ring.
Qed.

Lemma add_vector_dot_product_dist_right :
  forall xs ys zs, dot_product xs (add_vector ys zs) = dot_product xs ys + dot_product xs zs.
Proof.
  intros xs ys zs. rewrite dot_product_commutative. rewrite add_vector_dot_product_dist_left.
  f_equal; apply dot_product_commutative.
Qed.

Definition add_constraint c1 c2 := (add_vector (fst c1) (fst c2), snd c1 + snd c2).
Hint Unfold add_constraint.

Lemma add_constraint_satisfy :
  forall p c1 c2, satisfies_constraint p c1 = true -> satisfies_constraint p c2 = true ->
             satisfies_constraint p (add_constraint c1 c2) = true.
Proof.
  intros p c1 c2 Hs1 Hs2.
  autounfold in *. simpl; rewrite Z.leb_le in *. rewrite add_vector_dot_product_dist_right. lia.
Qed.

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
    + rewrite andb_true_iff in *. destruct Hcomb as [Ha Hcomb]. destruct Hsat as [Hc Hsat].
      apply add_constraint_satisfy.
      * apply mult_constraint_pos_satisfy; auto.
        rewrite Z.leb_le in Ha. lia.
      * apply IHcomb; auto.
Qed.

Definition is_null xs := forallb (fun x => x =? 0) xs.
Hint Unfold is_null.

Fixpoint is_eq (xs ys : vector) :=
  match xs, ys with
  | nil, nil => true
  | nil, ys => is_null ys
  | xs, nil => is_null xs
  | x :: xs, y :: ys => (x =? y) && is_eq xs ys
  end.

Lemma is_eq_reflexive :
  forall xs, is_eq xs xs = true.
Proof.
  induction xs; simpl; auto.
  rewrite andb_true_iff; split; auto.
  rewrite Z.eqb_eq; auto.
Qed.

Lemma is_eq_commutative :
  forall xs ys, is_eq xs ys = is_eq ys xs.
Proof.
  induction xs.
  - destruct ys; auto.
  - destruct ys; simpl in *; auto.
    f_equal; [apply Z.eqb_sym | auto].
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

Lemma dot_product_null_left :
  forall xs ys, is_null xs = true -> dot_product xs ys = 0.
Proof.
  induction xs; auto.
  intros ys Hnull; destruct ys; auto.
  simpl in *; rewrite andb_true_iff in Hnull; destruct Hnull as [Hzero Hnull].
  rewrite IHxs.
  - rewrite Z.eqb_eq in Hzero; nia.
  - auto.
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
    + destruct zs; simpl; auto.
      rewrite andb_true_iff. intros [Ha Heq].
      f_equal; [rewrite Z.eqb_eq in Ha; congruence | auto].
Qed.

Lemma dot_product_eq_compat_right :
  forall xs ys zs, is_eq ys zs = true -> dot_product xs ys = dot_product xs zs.
Proof.
  intros xs ys zs Heq. rewrite dot_product_commutative.
  erewrite dot_product_eq_compat_left; eauto using dot_product_commutative.
Qed.

Lemma mult_vector_null :
  forall k xs, is_null xs = true -> is_null (mult_vector k xs) = true.
Proof.
  intros k. induction xs; auto.
  simpl. repeat (rewrite andb_true_iff).
  intros [Ha Hnull]. split; auto.
  rewrite Z.eqb_eq in *; nia.
Qed.

Lemma mult_vector_eq_compat :
  forall k xs ys, is_eq xs ys = true -> is_eq (mult_vector k xs) (mult_vector k ys) = true.
Proof.
  intros k. induction xs.
  - intros ys Heq. rewrite is_eq_nil_left in *. apply mult_vector_null; auto.
  - destruct ys.
    + intros Heq. rewrite is_eq_nil_right in *. apply mult_vector_null; auto.
    + simpl. repeat (rewrite andb_true_iff). intros [Ha Heq].
      split; auto. rewrite Z.eqb_eq in *. congruence.
Qed.

Lemma add_vector_null_left :
  forall xs ys, is_null xs = true -> is_eq (add_vector xs ys) ys = true.
Proof.
  induction xs.
  - intros ys Heq. rewrite add_vector_nil_left. apply is_eq_reflexive.
  - intros ys Heq. destruct ys; auto.
    simpl in *; rewrite andb_true_iff in *. destruct Heq as [Ha Heq].
    rewrite Z.eqb_eq in *. split; auto. lia.
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
    + simpl in *. rewrite andb_true_iff in *. destruct Heq as [Ha Heq].
      rewrite Z.eqb_eq in *. split; auto. lia.
Qed.

Lemma add_vector_eq_compat_right :
  forall xs ys zs, is_eq ys zs = true -> is_eq (add_vector xs ys) (add_vector xs zs) = true.
Proof.
  intros xs ys zs Heq. rewrite add_vector_commutative with (ys := ys).
  rewrite add_vector_commutative with (ys := zs). apply add_vector_eq_compat_left; auto.
Qed.

Definition constraint_entails (c1 c2 : constraint) := is_eq (fst c1) (fst c2) && (snd c1 <=? snd c2).
Hint Unfold constraint_entails.

Lemma constraint_entails_correct :
  forall c1 c2 p, constraint_entails c1 c2 = true -> satisfies_constraint p c1 = true -> satisfies_constraint p c2 = true.
Proof.
  intros c1 c2 p Hent Hsat.
  autounfold in *.
  rewrite andb_true_iff in Hent; destruct Hent as [Heq Hcmp].
  rewrite Z.leb_le in *. erewrite <- dot_product_eq_compat_right; [|eauto]. lia.
Qed.

Definition witness := (vector * Z)%type.

Definition is_redundant (wit : witness) (pol : polyhedron) (c : constraint) :=
  (0 <? snd wit) &&
    forallb (fun w => 0 <=? w) (fst wit) &&
    constraint_entails (combine_constraints (fst wit) pol) (mult_constraint (snd wit) c).
Hint Unfold is_redundant.

Lemma is_redundant_correct :
  forall wit pol c p, is_redundant wit pol c = true -> forallb (satisfies_constraint p) pol = true ->
                 satisfies_constraint p c = true.
Proof.
  intros wit pol c p Hred Hinpoly.
  unfold is_redundant in Hred. repeat (rewrite andb_true_iff in Hred).
  destruct Hred as [[Hpos Hcpos] Hent].
  erewrite <- mult_constraint_eq.
  - eapply constraint_entails_correct; eauto.
    apply combine_constraints_satisfy; auto.
  - rewrite Z.ltb_lt in Hpos. lia.
Qed.

Definition is_empty (wit : witness) (pol : polyhedron) := is_redundant wit pol empty_constraint.
Hint Unfold is_empty.

Lemma is_empty_correct :
  forall wit pol, is_empty wit pol = true -> empty_poly pol.
Proof.
  intros wit pol Hemp p.
  apply negb_prop_intro. intro Hin. apply Is_true_eq_true in Hin.
  assert (satisfies_constraint p empty_constraint = true).
  - eapply is_redundant_correct; eauto.
  - rewrite empty_constraint_empty in *; congruence.
Qed.

