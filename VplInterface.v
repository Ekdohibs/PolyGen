Require Import Vpl.LinTerm.
Require Import Vpl.CstrC.
Require Import Linalg.
Require Import ZArith.
Require Import Vpl.PositiveMapAddOn.
Require Import BinPos.
Require Import List.
Require Import Psatz.
Require Import Misc.
Require Import Vpl.ConsSet.

Fixpoint vector_to_LinQ_rec (n : positive) (v : list Z) : LinQ.t :=
  match v with
  | nil => @PositiveMap.empty QNum.t
  | x :: v => if (x =? 0)%Z then
               vector_to_LinQ_rec (Pos.succ n) v
             else
               PositiveMap.add n (ZtoQ.ofZ x) (vector_to_LinQ_rec (Pos.succ n) v)
  end.

Definition vector_to_LinQ := vector_to_LinQ_rec xH.

Lemma vector_to_LinQ_rec_free :
  forall v n m, (m < n)%positive -> LinQ.isFree m (vector_to_LinQ_rec n v) = true.
Proof.
  induction v.
  - intros. simpl. destruct m; reflexivity.
  - intros n m Hmn. simpl. destruct (a =? 0)%Z eqn:Ha.
    + apply IHv. lia.
    + unfold LinQ.isFree.
      rewrite PositiveMap.mem_find, PositiveMapAdditionalFacts.gsspec.
      destruct (PositiveMap.E.eq_dec m n) as [e | e]. rewrite e in Hmn. lia.
      rewrite <- PositiveMap.mem_find. apply IHv. lia.
Qed.

Lemma vector_to_LinQ_rec_nil :
  forall n, vector_to_LinQ_rec n nil = LinQ.nil.
Proof.
  reflexivity.
Qed.

Lemma absEval_ext :
  forall l m1 m2, (forall x, m1 x = m2 x) -> LinQ.absEval l m1 = LinQ.absEval l m2.
Proof.
  induction l; intros; simpl; auto.
Qed.

Lemma eval_ext :
  forall l m1 m2, (forall x, m1 x = m2 x) -> LinQ.eval l m1 = LinQ.eval l m2.
Proof.
  intros; unfold LinQ.eval; erewrite absEval_ext; auto.
Qed.

Lemma remove_eval :
  forall x l m c, PositiveMap.find x l = Some c -> LinQ.eval l m = QNum.add (QNum.mul (m x) c) (LinQ.eval (PositiveMap.remove x l) m).
Proof.
  intros x l m c Hc.
  generalize (LinQ.rename_correct x x l m). intros H.
  unfold LinQ.rename in H. rewrite Hc in H. unfold LinQ.rename in H.
  rewrite LinQ.Add_correct, LinQ.single_correct in H. rewrite H.
  apply eval_ext. intros; rewrite Mem.assign_id; auto.
Qed.

Lemma remove_free_eval :
  forall x l m, PositiveMap.find x l = None -> LinQ.eval l m = LinQ.eval (PositiveMap.remove x l) m.
Proof.
  intros x l m Hnone.
  unfold LinQ.eval. rewrite elements_remove.
  f_equal. symmetry. apply CoqAddOn.filter_triv_true. rewrite CoqAddOn.Forall_ListForIn.
  intros [y my] Hin. apply PositiveMap.elements_complete in Hin. unfold eq_key; simpl.
  destruct (Pos.eq_dec x y); [congruence | reflexivity].
Qed.

Lemma PositiveMap_ext_merge :
  forall (A : Type) (l1 l2 : PositiveMap.t A), (forall x, PositiveMap.find x l1 = PositiveMap.find x l2) -> PositiveMap.Empty (merge (fun n1 n2 => None) l1 l2).
Proof.
  intros A l1 l2 Heq.
  rewrite PositiveMap.Empty_alt. intros x.
  rewrite find_merge. rewrite Heq. destruct (PositiveMap.find x l2); simpl; auto.
Qed.

Lemma empty_elements :
  forall (A : Type) (l : PositiveMap.t A), PositiveMap.Empty l -> PositiveMap.elements l = nil.
Proof.
  intros A l Hempty.
  destruct (PositiveMap.elements l) eqn:Helem; auto.
  rewrite PositiveMap.Empty_alt in Hempty; specialize (Hempty (fst p)).
  assert (PositiveMap.find (fst p) l = Some (snd p)); [|congruence].
  rewrite <- elements_spec. rewrite Helem. unfold In; left. destruct p; auto.
Qed.

Lemma inMerge_nil_eq :
  forall (A : Type) (l1 l2 : list (positive * A)) w, inMerge (fun _ _ => None) l1 l2 w -> w = nil -> (forall p x y, In (p, x) l1 -> In (p, y) l2 -> x = y) -> l1 = l2.
Proof.
  intros A l1 l2 w Hmerge. induction Hmerge; try (intros; congruence).
  intros Hnil Hin. f_equal.
  - f_equal. eapply Hin; left; reflexivity.
  - apply IHHmerge; [auto|].
    intros p u v Hin1 Hin2; apply (Hin p); right; auto.
Qed.

Lemma Positive_map_elements_ext :
  forall (A : Type) (l1 l2 : PositiveMap.t A), (forall x, PositiveMap.find x l1 = PositiveMap.find x l2) -> PositiveMap.elements l1 = PositiveMap.elements l2.
Proof.
  intros A l1 l2 Heq.
  generalize (PositiveMap_ext_merge A l1 l2 Heq). intros Hmerge.
  generalize (elements_merge (fun _ _ => None) l1 l2). intros Hinmerge.
  rewrite (empty_elements _ _ Hmerge) in Hinmerge.
  eapply inMerge_nil_eq; [exact Hinmerge|reflexivity|].
  intros p x y Hx Hy. rewrite elements_spec in Hx, Hy. specialize (Heq p); congruence.
Qed.

Lemma remove_add_elements :
  forall x l (c : QNum.t), PositiveMap.find x l = None -> PositiveMap.elements (PositiveMap.remove x (PositiveMap.add x c l)) = PositiveMap.elements l.
Proof.
  intros x l c Hfind.
  apply Positive_map_elements_ext. intros y.
  destruct (Pos.eq_dec x y) as [Hxy | Hxy].
  - rewrite Hxy in *. rewrite Hfind. apply PositiveMap.grs.
  - rewrite PositiveMap.gro by auto. apply PositiveMap.gso; auto.
Qed.

Lemma vector_to_LinQ_rec_add :
  forall x v n, LinQ.Eq (vector_to_LinQ_rec n (x :: v)) (LinQ.add (LinQ.single n (ZtoQ.ofZ x)) (vector_to_LinQ_rec (Pos.succ n) v)).
Proof.
  intros x v n.
  simpl. destruct (x =? 0)%Z eqn:Hx.
  - reflect. rewrite Hx. simpl. intro m; reflexivity.
  - intros m. rewrite LinQ.Add_correct. rewrite LinQ.single_correct.
    rewrite remove_eval with (x := n) (c := ZtoQ.ofZ x).
    + f_equal. unfold LinQ.eval. rewrite remove_add_elements; [auto|].
      generalize (vector_to_LinQ_rec_free v (Pos.succ n) n (Pos.lt_succ_diag_r n)). unfold LinQ.isFree.
      rewrite PositiveMap.mem_find.
      destruct (PositiveMap.find n (vector_to_LinQ_rec (Pos.succ n) v)); intros; simpl in *; congruence.
    + rewrite PositiveMap.gss. reflexivity.
Qed.

Definition vector_to_memQ v := fun p => ZtoQ.ofZ (nth (Nat.pred (Pos.to_nat p)) v 0%Z).

Fixpoint vector_memQ_product v m n :=
  match v with
  | nil => QNum.z
  | x :: v => QNum.add (QNum.mul (ZtoQ.ofZ x) (m n)) (vector_memQ_product v m (Pos.succ n))
  end.

Theorem dot_product_to_memQ_rec :
  forall v1 v2 n, ZtoQ.ofZ (dot_product v1 (skipn n v2)) = vector_memQ_product v1 (vector_to_memQ v2) (Pos.of_succ_nat n).
Proof.
  intros v1. induction v1.
  - intros v2 n. simpl in *. destruct (skipn n v2); simpl; apply ZtoQ.ofZ_zero.
  - intros v2 n.
    replace (a :: v1) with ((a :: nil) ++ v1) by auto.
    rewrite dot_product_app_left. unfold length. rewrite resize_succ. rewrite skipn_skipn.
    autorewrite with num. rewrite IHv1. simpl. f_equal. autorewrite with num. unfold vector_to_memQ.
    replace (ZtoQ.ofZ 0) with QNum.z by (symmetry; apply ZtoQ.ofZ_zero). rewrite QNum.AddZR.
    f_equal. f_equal. rewrite nth_skipn. f_equal. lia.
Qed.

Lemma vector_to_LinQ_memQ_product :
  forall v n m, vector_memQ_product v m n = LinQ.eval (vector_to_LinQ_rec n v) m.
Proof.
  induction v.
  - intros. simpl. rewrite LinQ.NilEval. reflexivity.
  - intros n m. rewrite vector_to_LinQ_rec_add.
    rewrite LinQ.Add_correct. simpl. rewrite LinQ.single_correct.
    f_equal.
    + apply QNum.MulComm.
    + apply IHv.
Qed.

Lemma vector_to_LinQ_correct :
  forall v1 v2, LinQ.eval (vector_to_LinQ v1) (vector_to_memQ v2) = ZtoQ.ofZ (dot_product v1 v2).
Proof.
  intros v1 v2.
  unfold vector_to_LinQ. rewrite <- vector_to_LinQ_memQ_product.
  symmetry. apply (dot_product_to_memQ_rec v1 v2 0%nat).
Qed.

Definition constraint_to_Cstr c :=
  Cstr.upperOrEqualsToCstr (vector_to_LinQ (fst c)) (ZtoQ.ofZ (snd c)).

Lemma constraint_to_Cstr_correct :
  forall c v, Cstr.sat (constraint_to_Cstr c) (vector_to_memQ v) <-> (satisfies_constraint v c = true).
Proof.
  intros c v.
  unfold constraint_to_Cstr, Cstr.upperOrEqualsToCstr, Cstr.sat; simpl.
  rewrite vector_to_LinQ_correct. unfold satisfies_constraint. reflect.
  rewrite dot_product_commutative.
  rewrite <- ZtoQ.LeCommutes. reflexivity.
Qed.

Definition poly_to_Cs p := map constraint_to_Cstr p.

Lemma poly_to_Cs_correct :
  forall p v, Cs.sat (poly_to_Cs p) (vector_to_memQ v) <-> (in_poly v p = true).
Proof.
  induction p.
  - intros v; simpl; split; auto.
  - intros v; simpl. rewrite constraint_to_Cstr_correct. rewrite IHp. reflect.
    tauto.
Qed.