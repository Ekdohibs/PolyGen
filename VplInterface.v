Require Import Vpl.LinTerm.
Require Import Vpl.CstrC.
Require Import Linalg.
Require Import QArith.
Require Import Qcanon.
Require Import Qround.
Require Import ZArith.
Require Import Vpl.PositiveMapAddOn.
Require Import BinPos.
Require Import List.
Require Import Psatz.
Require Import Misc.
Require Import Vpl.ConsSet.
Require Import Setoid.

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

Fixpoint fun_to_vector {A : Type} (f : positive -> A) k n :=
  match n with
  | 0%nat => nil
  | S n => f k :: fun_to_vector f (Pos.succ k) n
  end.

Lemma fun_to_vector_def_rec :
  forall A (f : positive -> A) n k t d,
    nth t (fun_to_vector f k n) d = if (t <? n)%nat then f (Pos.of_nat (t + Pos.to_nat k)) else d.
Proof.
  intros A f n. induction n.
  - intros k t d; simpl. destruct t; auto.
  - intros k t d; simpl. destruct t as [|t].
    + simpl. rewrite Pos2Nat.id. reflexivity.
    + rewrite IHn.
      replace (S t <? S n)%nat with (t <? n)%nat by reflexivity.
      destruct (t <? n)%nat; [|reflexivity].
      f_equal. f_equal. lia. 
Qed.

Lemma fun_to_vector_def :
  forall A (f : positive -> A) n t d,
    nth t (fun_to_vector f xH n) d = if (t <? n)%nat then f (Pos.of_succ_nat t) else d.
Proof.
  intros A f n t d. rewrite fun_to_vector_def_rec.
  destruct (t <? n)%nat; [|reflexivity].
  f_equal. rewrite Pos.of_nat_succ. f_equal. lia.
Qed.

Lemma fun_to_vector_nth_small :
  forall A (f : positive -> A) n t d,
    (t < n)%nat -> nth t (fun_to_vector f xH n) d = f (Pos.of_succ_nat t).
Proof.
  intros A f n t d H. rewrite fun_to_vector_def.
  replace (t <? n)%nat with true by (symmetry; reflect; auto).
  reflexivity.
Qed.

Lemma fun_to_vector_nth_large :
  forall A (f : positive -> A) k n t d,
    (n <= t)%nat -> nth t (fun_to_vector f k n) d = d.
Proof.
  intros A f k n t d H.
  rewrite fun_to_vector_def_rec. replace (t <? n)%nat with false by (symmetry; reflect; auto).
  reflexivity.
Qed.

Fixpoint list_max l :=
  match l with
  | nil => 0%nat
  | x :: l => Nat.max x (list_max l)
  end.

Lemma list_max_correct :
  forall l x, In x l -> (x <= list_max l)%nat.
Proof.
  induction l.
  - intros; simpl in *; tauto.
  - intros x H; simpl in *; destruct H as [H | H]; [|specialize (IHl x H)]; lia.
Qed.

Definition max_binding {A : Type} (l : PositiveMap.t A) :=
  list_max (map (fun x => Pos.to_nat (fst x)) (PositiveMap.elements l)).

Theorem max_binding_correct :
  forall (A : Type) (l : PositiveMap.t A) x v, PositiveMap.find x l = Some v -> (Pos.to_nat x <= max_binding l)%nat.
Proof.
  intros A l x v H.
  unfold max_binding.
  apply list_max_correct.
  rewrite in_map_iff. exists (x, v).
  simpl. split; [auto|].
  apply PositiveMap.elements_correct; auto.
Qed.

Definition flip_ggcd (gg : positive * (positive * positive)) := (fst gg, (snd (snd gg), fst (snd gg))).

Lemma ggcdn_comm :
  forall n a b, Pos.ggcdn n b a = flip_ggcd (Pos.ggcdn n a b).
Proof.
  induction n.
  - intros; simpl; auto.
  - intros; destruct a; destruct b; simpl; try reflexivity;
      [rewrite Pos.compare_antisym; destruct (a ?= b)%positive eqn:Hab| | |];
      try (rewrite IHn; simpl; destruct Pos.ggcdn as (g,(u,v)); simpl; reflexivity).
    simpl.
    apply Pos.compare_eq in Hab; rewrite Hab; reflexivity.
Qed.

Lemma ggcd_comm :
  forall a b, Pos.ggcd b a = flip_ggcd (Pos.ggcd a b).
Proof.
  intros a b. unfold Pos.ggcd. rewrite <- ggcdn_comm.
  f_equal. lia.
Qed.

Lemma divide_mul_cancel_l p q r : (p * q | p * r)%positive -> (q | r)%positive.
Proof.
  intros [x H]. exists x. nia.
Qed.

Lemma divide_mul2_l p q r : (q | r)%positive -> (p * q | p * r)%positive.
Proof.
  intros [x H]. exists x. nia.
Qed.

Lemma divide_mul_cancel_r p q r : (q * p | r * p)%positive -> (q | r)%positive.
Proof.
  intros [x H]. exists x. nia.
Qed.

Lemma divide_mul2_r p q r : (q | r)%positive -> (q * p | r * p)%positive.
Proof.
  intros [x H]. exists x. nia.
Qed.

Lemma divide_mul_cancel_l_iff p q r : (p * q | p * r)%positive <-> (q | r)%positive.
Proof.
  split; [apply divide_mul_cancel_l | apply divide_mul2_l].
Qed.

Lemma divide_mul_cancel_r_iff p q r : (q * p | r * p)%positive <-> (q | r)%positive.
Proof.
  split; [apply divide_mul_cancel_r | apply divide_mul2_r].
Qed.

Lemma divide_antisym p q : (p | q)%positive -> (q | p)%positive -> p = q.
Proof.
  intros [a Ha] [b Hb]. nia.
Qed.

Lemma divide_refl p : (p | p)%positive.
Proof.
  exists 1%positive. lia.
Qed.

Lemma divide_trans p q r : (p | q)%positive -> (q | r)%positive -> (p | r)%positive.
Proof.
  intros [x Hx] [y Hy]; exists (x * y)%positive; nia.
Qed.

Lemma gcd_spec a b p : (forall q, ((q | a)%positive /\ (q | b)%positive) <-> (q | p)%positive) <-> p = Pos.gcd a b.
Proof.
  split.
  - intros Hg. 
    apply divide_antisym.
    + generalize (divide_refl p). intros H; rewrite <- Hg in H; destruct H. apply Pos.gcd_greatest; auto.
    + apply Hg; split; [apply Pos.gcd_divide_l | apply Pos.gcd_divide_r].
  - intros Hp; rewrite Hp. intros q. split.
    + intros [Ha Hb]; apply Pos.gcd_greatest; auto.
    + intros Hd; split; eapply divide_trans; [exact Hd | apply Pos.gcd_divide_l | exact Hd | apply Pos.gcd_divide_r].
Qed.

Lemma gcd_mul_k k a b : (Pos.gcd (k * a) (k * b) = k * Pos.gcd a b)%positive.
Proof.
  generalize (Pos.gcd_greatest (k * a) (k * b) k)%positive. intros H; destruct H.
  - exists a; nia.
  - exists b; nia.
  - rewrite H; rewrite Pos.mul_comm. f_equal.
    symmetry in H. rewrite Pos.mul_comm in H. rewrite <- gcd_spec in H.
    rewrite <- gcd_spec. intros q. specialize (H (k * q)%positive).
    rewrite !divide_mul_cancel_l_iff in H. auto.
Qed.

Lemma gcd_greatest_mul a b k p : (p | k * a)%positive -> (p | k * b)%positive -> (p | k * Pos.gcd a b)%positive.
Proof.
  rewrite <- gcd_mul_k.
  apply Pos.gcd_greatest.
Qed.

Definition lcm a b := let '(g, (aa, bb)) := Pos.ggcd a b in (aa * b)%positive.

Lemma lcm_comm a b : lcm a b = lcm b a.
Proof.
  unfold lcm.
  generalize (Pos.ggcd_correct_divisors a b).
  rewrite ggcd_comm with (a := a) (b := b); destruct Pos.ggcd as (g, (u, v)).
  simpl. nia.
Qed.

Lemma divide_lcm_r a b : (b | lcm a b)%positive.
Proof.
  unfold lcm.
  remember (Pos.ggcd a b) as u.
  destruct u as [g [aa bb]].
  exists aa. reflexivity.
Qed.

Lemma divide_lcm_l a b : (a | lcm a b)%positive.
Proof.
  rewrite lcm_comm. apply divide_lcm_r.
Qed.

Lemma lcm_gcd_mul a b : (lcm a b * Pos.gcd a b = a * b)%positive.
Proof.
  unfold lcm.
  generalize (Pos.ggcd_correct_divisors a b).
  rewrite <- Pos.ggcd_gcd.
  destruct Pos.ggcd as (g, (u, v)); intros [Hu Hv]. simpl.
  nia.
Qed.

Lemma lcm_smallest : forall a b p, (a | p)%positive -> (b | p)%positive -> (lcm a b | p)%positive.
Proof.
  intros a b p [x Hx] [y Hy].
  apply divide_mul_cancel_r with (p := Pos.gcd a b).
  rewrite lcm_gcd_mul.
  apply gcd_greatest_mul; [exists y; rewrite Hy | exists x; rewrite Hx]; nia.
Qed.

Lemma lcm_one : forall a, lcm 1%positive a = a.
Proof.
  intros a. unfold lcm. reflexivity.
Qed.

Fixpoint list_lcm l :=
  match l with
  | nil => 1%positive
  | x :: l => lcm x (list_lcm l)
  end.

Lemma list_lcm_correct :
  forall x l, In x l -> (x | list_lcm l)%positive.
Proof.
  intros x l. induction l.
  - intros; simpl in *; tauto.
  - intros [Ha | Hl]; simpl in *.
    + rewrite Ha. apply divide_lcm_l.
    + eapply divide_trans; [apply IHl; auto|apply divide_lcm_r].
Qed.

Definition LinQ_to_vector l :=
  let d := Zpos (list_lcm (map (fun u => (snd u).(this).(Qden)) (PositiveMap.elements l))) in
  (d, fun_to_vector (fun u => match PositiveMap.find u l with Some x => Qfloor (x * ZtoQ.ofZ d) | None => 0 end) xH (max_binding l)).

Lemma LinQ_to_vector_positive_multiple :
  forall l, 0 < fst (LinQ_to_vector l).
Proof.
  intros; simpl. reflexivity.
Qed.

Lemma LinQ_vector_eq :
  forall x l,
    QNum.mul (ZtoQ.ofZ (fst (LinQ_to_vector l))) (match PositiveMap.find (Pos.of_succ_nat x) l with Some a => a | None => QNum.z end) =
     ZtoQ.ofZ (nth x (snd (LinQ_to_vector l)) 0).
Proof.
  intros x l.
  remember (fst (LinQ_to_vector l)) as d.
  unfold LinQ_to_vector in *. simpl in *. rewrite <- Heqd.
  rewrite fun_to_vector_def.
  destruct (PositiveMap.find (Pos.of_succ_nat x) l) as [w|] eqn:Hfind.
  - assert (Hdiv : (Qden w | Z.to_pos d)%positive).
    {
      rewrite Heqd; simpl.
      apply list_lcm_correct.
      apply in_map_iff. exists (Pos.of_succ_nat x, w). split; [reflexivity|].
      apply PositiveMap.elements_correct. auto.
    }
    apply max_binding_correct in Hfind.
    replace (x <? max_binding l)%nat with true by (symmetry; reflect; lia). unfold QNum.mul. unfold ZtoQ.ofZ.
    unfold "*"%Qc. unfold "*"%Q. rewrite <- Qop.QOp.Q2Qc_this_eq.
    rewrite Q2Qc_eq_iff. simpl. unfold inject_Z. unfold "==". simpl.
    destruct Hdiv as [u Hu]. destruct d as [|d|d]; try congruence. simpl in Hu.
    rewrite Hu. zify. ring_simplify. ring_simplify (' Qden w * 1).
    rewrite <- Znumtheory.Zdivide_Zdiv_eq; try lia. exists ('u * Qnum w); nia.
  - transitivity QNum.z.
    + rewrite QNum.MulComm. apply QNum.MulZL.
    + destruct (x <? max_binding l)%nat; simpl; symmetry; apply ZtoQ.ofZ_zero.
Qed.

Lemma vector_LinQ_eq_rec :
  forall l n x, match PositiveMap.find (Pos.of_nat (x + Pos.to_nat n)) (vector_to_LinQ_rec n l) with Some a => a | None => QNum.z end =
           ZtoQ.ofZ (nth x l 0).
Proof.
  induction l.
  - intros n x. simpl in *.
    rewrite PositiveMap.gempty. destruct x; symmetry; apply ZtoQ.ofZ_zero.
  - intros n x. simpl.
    destruct (a =? 0) eqn:Ha.
    + reflect. rewrite Ha.
      destruct x as [|x].
      * simpl. rewrite Pos2Nat.id.
        replace (PositiveMap.find n (vector_to_LinQ_rec (Pos.succ n) l)) with (@None Qc); [symmetry; apply ZtoQ.ofZ_zero|].
        generalize (vector_to_LinQ_rec_free l (Pos.succ n) n); intros H.
        unfold LinQ.isFree in H. rewrite PositiveMap.mem_find in H.
        destruct PositiveMap.find; auto. simpl in *.
        assert (false = true) by (apply H; lia).
        congruence.
      * rewrite <- IHl with (n := Pos.succ n).
        replace (S x + Pos.to_nat n)%nat with (x + Pos.to_nat (Pos.succ n))%nat by lia. reflexivity.
    + destruct x as [|x].
      * simpl. rewrite Pos2Nat.id.
        rewrite PositiveMap.gss. reflexivity.
      * rewrite PositiveMap.gso.
        -- rewrite <- IHl with (n := Pos.succ n).
           replace (S x + Pos.to_nat n)%nat with (x + Pos.to_nat (Pos.succ n))%nat by lia. reflexivity.
        -- rewrite <- Pos2Nat.inj_iff, Nat.add_succ_l, <- Pos.of_nat_succ, SuccNat2Pos.id_succ.
           lia.
Qed.

Lemma vector_LinQ_eq :
  forall x l, match PositiveMap.find (Pos.of_succ_nat x) (vector_to_LinQ l) with Some a => a | None => QNum.z end =
         ZtoQ.ofZ (nth x l 0).
Proof.
  intros x l.
  rewrite <- vector_LinQ_eq_rec with (n := xH). unfold vector_to_LinQ.
  replace (Pos.of_nat (x + Pos.to_nat xH)) with (Pos.of_succ_nat x); [reflexivity|].
  rewrite Pos.of_nat_succ. f_equal. lia.
Qed.

Lemma find_map :
  forall (A B : Type) (f : A -> B) l x, PositiveMap.find x (PositiveMapAddOn.map f l) = match PositiveMap.find x l with Some y => Some (f y) | None => None end.
Proof.
  intros A B f l. induction l.
  - intros; simpl; destruct x; auto. 
  - intros; destruct x; simpl; [rewrite IHl2|rewrite IHl1|]; auto.
Qed.

Lemma absEval_null :
  forall m l, (forall x c, In (x, c) l -> c = QNum.z) -> LinQ.absEval l m = QNum.z.
Proof.
  intros m; induction l.
  - intros; simpl; auto.
  - intros H; simpl in *.
    rewrite IHl by (intros; eapply H; eauto).
    rewrite QNum.AddZL. rewrite QNum.MulComm.
    replace (snd a) with QNum.z; [apply QNum.MulZL|].
    symmetry. apply (H (fst a) (snd a)).
    left; destruct a; auto.
Qed.

Lemma LinQ_null :
  forall l m, (forall x c, PositiveMap.find x l = Some c -> c = QNum.z) -> LinQ.eval l m = QNum.z.
Proof.
  intros l m H. unfold LinQ.eval.
  apply absEval_null.
  intros x c Hin.
  apply (H x c). apply PositiveMap.elements_complete. auto.
Qed.

Add Ring QRing : QNum.Ring.

Lemma LinQ_Eq :
  forall l1 l2, (forall x, match PositiveMap.find x l1 with Some a => a | None => QNum.z end = match PositiveMap.find x l2 with Some a => a | None => QNum.z end) ->
           LinQ.Eq l1 l2.
Proof.
  intros l1 l2 H m.
  remember (LinQ.add l1 (LinQ.opp l2)) as l3.
  enough (H1 : LinQ.eval l3 m = QNum.z).
  - rewrite Heql3, LinQ.Add_correct, LinQ.Opp_correct in H1.
    replace (LinQ.eval l1 m) with (QNum.add (QNum.add (LinQ.eval l1 m) (QNum.opp (LinQ.eval l2 m))) (LinQ.eval l2 m)) by ring.
    rewrite H1; ring.
  - apply LinQ_null. intros x c Hfind.
    rewrite Heql3 in Hfind. unfold LinQ.add, LinQ.opp in Hfind.
    rewrite find_merge, find_map in Hfind.
    specialize (H x).
    remember (PositiveMap.find x l1) as u1. remember (PositiveMap.find x l2) as u2.
    destruct u1 as [u1|]; destruct u2 as [u2|]; simpl in *; try congruence.
    + rewrite H, QNum.AddOpp in Hfind; simpl in *; congruence.
    + rewrite <- H, QNum.OppZ in Hfind. congruence.
Qed.

Lemma LinQ_vector_LinQ :
  forall (l : PositiveMap.t QNum.t), LinQ.Eq (LinQ.mul (ZtoQ.ofZ (fst (LinQ_to_vector l))) l) (vector_to_LinQ (snd (LinQ_to_vector l))).
Proof.
  intros l.
  apply LinQ_Eq.
  intros x. remember (fst (LinQ_to_vector l)) as d.
  transitivity ((QNum.mul (ZtoQ.ofZ d) (match PositiveMap.find x l with Some a => a | None => QNum.z end)) : QNum.t).
  - unfold LinQ.mul, LinQ.opp, LinQ.nil.
    generalize (QNum.mulDiscr_correct (ZtoQ.ofZ d)); destruct (QNum.mulDiscr (ZtoQ.ofZ d)); simpl;
      rewrite ?find_map, ?PositiveMap.gempty; destruct (PositiveMap.find x l); intro H; try (rewrite H); ring.
  - replace x with (Pos.of_succ_nat (Nat.pred (Pos.to_nat x))) by lia.
    rewrite vector_LinQ_eq, <- LinQ_vector_eq.
    auto.
Qed.

Lemma LinQ_to_vector_correct :
  forall l v, ZtoQ.ofZ (dot_product (snd (LinQ_to_vector l)) v) = QNum.mul (ZtoQ.ofZ (fst (LinQ_to_vector l))) (LinQ.eval l (vector_to_memQ v)).
Proof.
  intros l v.
  rewrite <- vector_to_LinQ_correct. rewrite <- LinQ_vector_LinQ. rewrite LinQ.Mul_correct. reflexivity.
Qed.
