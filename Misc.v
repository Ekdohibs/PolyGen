Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Psatz.
Require Import Setoid.

Open Scope Z_scope.

(** * More properties of lists that are missing from the Coq library *)

Lemma forallb_map :
  forall A B f (g : A -> B) l, forallb f (map g l) = forallb (fun x => f (g x)) l.
Proof.
  intros. induction l; simpl; auto; congruence.
Qed.

Lemma forallb_ext :
  forall A f g (l : list A), (forall x, f x = g x) -> forallb f l = forallb g l.
Proof.
  intros. induction l; simpl; auto; congruence.
Qed.

Lemma forallb_exists :
  forall A f (l : list A), forallb f l = false <-> exists x, In x l /\ f x = false.
Proof.
  intros A f. induction l.
  - intros; simpl. split; [congruence | intros [x Hx]; tauto].
  - simpl. rewrite andb_false_iff, IHl.
    destruct (f a) eqn:Hfa; firstorder congruence.
Qed.

Lemma existsb_forall :
  forall A f (l : list A), existsb f l = false <-> forall x, In x l -> f x = false.
Proof.
  intros A f. induction l.
  - simpl; tauto.
  - simpl. rewrite orb_false_iff, IHl.
    destruct (bool_dec (f a) false); firstorder congruence. 
Qed.

Lemma skipn_skipn :
  forall A n m (l : list A), skipn n (skipn m l) = skipn (n + m)%nat l.
Proof.
  induction m.
  - simpl. rewrite Nat.add_0_r; auto.
  - rewrite Nat.add_succ_r. destruct l; simpl.
    + destruct n; auto.
    + auto.
Qed.

Lemma skipn_app :
  forall A n (p q : list A), length p = n -> skipn n (p ++ q) = q.
Proof.
  induction n.
  - intros; destruct p; simpl in *; auto; lia.
  - intros; destruct p; simpl in *; auto; lia.
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

Lemma firstn_nth_app :
  forall A n (l : list A) d, (length l >= S n)%nat -> firstn (S n) l = firstn n l ++ (nth n l d :: nil).
Proof.
  intros A. induction n.
  - intros l d H; destruct l; simpl in *; [lia | auto].
  - intros l d H; destruct l; simpl in *; [lia |].
    erewrite IHn by lia. reflexivity.
Qed.

Lemma map_nth_error_none :
  forall A B n (f : A -> B) l, nth_error l n = None -> nth_error (map f l) n = None.
Proof.
  intros; rewrite nth_error_None in *; rewrite map_length; auto.
Qed.

Lemma nth_error_map_iff :
  forall A B (f : A -> B) n l x, nth_error (map f l) n = Some x <-> (exists y, nth_error l n = Some y /\ x = f y).
Proof.
  intros A B f. induction n.
  - intros [|y l] x; simpl.
    + split; [congruence|firstorder congruence].
    + split; intros; [exists y|]; firstorder congruence.
  - intros [|y l] x; simpl.
    + split; [|intros [y Hy]]; intuition congruence.
    + apply IHn.
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

Theorem nth_error_combine :
  forall (A B : Type) (n : nat) (l : list A) (l' : list B) x y,
    nth_error (combine l l') n = Some (x, y) <-> nth_error l n = Some x /\ nth_error l' n = Some y.
Proof.
  induction n.
  - intros l l' x y; destruct l; destruct l'; simpl in *; split; (intros [H1 H2] || (intros H; split)); congruence.
  - intros l l' x y; destruct l; destruct l'; simpl in *; split; (intros [H1 H2] || (intros H; split)); try congruence.
    + rewrite IHn in H; destruct H; auto.
    + rewrite IHn in H; destruct H; auto.
    + rewrite IHn; auto.
Qed.

Theorem in_l_combine :
  forall (A B : Type) (l : list A) (l': list B) x,
    length l = length l' -> In x l -> (exists y, In (x, y) (combine l l')).
Proof.
  intros A B l l' x Hlen Hin. apply In_nth_error in Hin.
  destruct Hin as [n Hin].
  destruct (nth_error l' n) as [y|] eqn:Heq.
  - exists y. apply nth_error_In with (n := n). rewrite nth_error_combine. auto.
  - rewrite nth_error_None in Heq.
    assert (n < length l)%nat by (rewrite <- nth_error_Some; congruence).
    lia.
Qed.

Fixpoint flatten {A : Type} (l : list (list A)) :=
  match l with
  | nil => nil
  | a :: l => a ++ (flatten l)
  end.

Lemma flatten_forallb :
  forall (A : Type) (l : list (list A)) (P : A -> bool),
    forallb (forallb P) l = forallb P (flatten l).
Proof.
  induction l.
  - intros; simpl; auto.
  - intros; simpl. rewrite IHl. rewrite forallb_app. reflexivity.
Qed.

Lemma flatten_In :
  forall (A : Type) (x : A) l, In x (flatten l) <-> exists u, In x u /\ In u l.
Proof.
  intros A x l. induction l.
  - simpl; firstorder.
  - simpl. rewrite in_app_iff.
    split.
    + intros [H | H]; [exists a; auto|]. rewrite IHl in H; destruct H as [u Hu]; exists u; tauto.
    + intros [u [Hxu [Hau | Hul]]]; [left; congruence|]. right; rewrite IHl; exists u; tauto.
Qed.

(** * Tactics for rewriting under binders *)

Definition helper_lemma : forall P Q, P -> Q -> Q :=
  fun P Q _ Q_proof => Q_proof.

Ltac under_binder vartype tacr tac :=
  let f := fresh "f" in
  let H := fresh "H" in
  let var := fresh "x" in
  evar (f : vartype -> Prop);
  tacr f; [|intro var; tac var; match goal with |- ?P <-> ?Q => apply (helper_lemma (Q -> P)) end; [intro H; pattern var; exact H|]; reflexivity];
  unfold f in *;
  clear f.

Lemma forall_ext :
  forall (A : Type) (P Q : A -> Prop), (forall x, P x <-> Q x) -> (forall x, P x) <-> (forall x, Q x).
Proof.
  intros A P Q H; split; intros; [rewrite <- H|rewrite H]; auto.
Qed.

Lemma exists_ext :
  forall (A : Type) (P Q : A -> Prop), (forall x, P x <-> Q x) -> (exists x, P x) <-> (exists x, Q x).
Proof.
  intros A P Q H; split; intros [x Hx]; exists x; [rewrite <- H|rewrite H]; auto.
Qed.

Ltac under_forall vartype tac :=
  under_binder vartype ltac:(fun f => rewrite forall_ext with (Q := f)) tac.
Ltac under_exists vartype tac :=
  under_binder vartype ltac:(fun f => rewrite exists_ext with (Q := f)) tac.
Ltac under_forall_in H vartype tac :=
  under_binder vartype ltac:(fun f => rewrite forall_ext with (Q := f) in H) tac.
Ltac under_exists_in H vartype tac :=
  under_binder vartype ltac:(fun f => rewrite exists_ext with (Q := f) in H) tac.


(** * The [reflect] tactic *)

Hint Rewrite andb_true_iff andb_false_iff orb_true_iff orb_false_iff negb_true_iff negb_false_iff: reflect.
Hint Rewrite Z.eqb_eq Z.leb_le Z.eqb_neq Z.leb_gt Z.ltb_lt Z.ltb_ge Z.gtb_ltb Z.geb_leb Z.compare_eq_iff Z.compare_lt_iff Z.compare_gt_iff : reflect.
Hint Rewrite Nat.eqb_eq Nat.leb_le Nat.eqb_neq Nat.leb_gt Nat.ltb_lt Nat.ltb_ge : reflect.

Ltac reflect := autorewrite with reflect in *.
Ltac reflect_binders :=
  repeat (
      autorewrite with reflect in *;
      try match goal with
          | [ |- context [forallb ?f1 ?l1 = true] ] =>
            (rewrite forallb_forall with (f := f1) (l := l1);
             let typ := match (type of f1) with (?A -> bool) => A end in
             under_forall typ ltac:(fun _ => reflect_binders)
            )
          | [ H : context [forallb ?f1 ?l1 = true] |- _] =>
            (rewrite forallb_forall with (f := f1) (l := l1) in H;
             let typ := match (type of f1) with (?A -> bool) => A end in
             under_forall_in H typ ltac:(fun _ => reflect_binders)
            )
          | [ |- context [existsb ?f1 ?l1 = true] ] =>
            (rewrite existsb_exists with (f := f1) (l := l1);
             let typ := match (type of f1) with (?A -> bool) => A end in
             under_exists typ ltac:(fun _ => reflect_binders)
            )
          | [ H : context [existsb ?f1 ?l1 = true] |- _] =>
            (rewrite existsb_exists with (f := f1) (l := l1) in H;
             let typ := match (type of f1) with (?A -> bool) => A end in
             under_exists_in H typ ltac:(fun _ => reflect_binders)
            )
          end
    ).


Lemma test1:
  forall l, (forallb (fun x => x =? 0) l = true <-> (forall x, In x l -> x = 0)).
Proof.
  intros l.
  reflect_binders.
  reflexivity.
Qed.

Lemma test2:
  (forall (x y : Z), (x =? y) = true) <-> (forall (x y : Z), x = y).
Proof.
  under_forall Z ltac:(fun _ => under_forall Z ltac:(fun _ => reflect)).
  reflexivity.
Qed.

Lemma test3:
  forall l1 l2, forallb (fun x => existsb (fun y => x =? y) l1) l2 = true <->
           forall x, In x l2 -> exists y, In y l1 /\ x = y.
Proof.
  intros l1 l2.
  reflect_binders. reflexivity.
Qed.

(** * Handlings [if]s *)

Tactic Notation "case_if" "in" hyp(H) :=
  lazymatch goal with
    | [ H : context[if ?X then _ else _] |- _ ] => destruct X
  end.

Tactic Notation "case_if" "in" hyp(H) "as" simple_intropattern(Has) :=
  lazymatch goal with
    | [ H : context[if ?X then _ else _] |- _ ] => destruct X as Has
  end.

Tactic Notation "case_if" "in" hyp(H) "eq" ident(Heq) :=
  lazymatch goal with
    | [ H : context[if ?X then _ else _] |- _ ] => destruct X eqn:Heq
  end.

Tactic Notation "case_if" "in" hyp(H) "as" simple_intropattern(Has) "eq" ident(Heq) :=
  lazymatch goal with
    | [ H : context[if ?X then _ else _] |- _ ] => destruct X as Has eqn:Heq
  end.

Tactic Notation "case_if" :=
  lazymatch goal with
    | [ |- context[if ?X then _ else _] ] => destruct X
  end.

Tactic Notation "case_if" "as" simple_intropattern(Has) :=
  lazymatch goal with
    | [ |- context[if ?X then _ else _] ] => destruct X as Has
  end.

Tactic Notation "case_if" "eq" ident(Heq) :=
  lazymatch goal with
    | [ |- context[if ?X then _ else _] ] => destruct X eqn:Heq
  end.

Tactic Notation "case_if" "as" simple_intropattern(Has) "eq" ident(Heq) :=
  lazymatch goal with
    | [ |- context[if ?X then _ else _] ] => destruct X as Has eqn:Heq
  end.

(** * Integer ranges *)

Fixpoint n_range (n : nat) :=
  match n with
  | O => nil
  | S n => (n_range n) ++ (n :: nil)
  end.

Lemma n_range_in :
  forall n m, In m (n_range n) <-> (m < n)%nat.
Proof.
  induction n.
  - intros. simpl in *. split; [intro; exfalso; auto | apply Nat.nlt_0_r].
  - intros m. simpl in *. split.
    + intros H. apply in_app_or in H. destruct H as [H | H].
      * rewrite IHn in H. lia.
      * simpl in H. destruct H; [lia | exfalso; auto].
    + intros H. apply in_or_app. destruct (Nat.eq_dec n m).
      * right; simpl; auto.
      * left; rewrite IHn; lia.
Qed.

Lemma n_range_begin :
  forall n, n_range (S n) = 0%nat :: (map S (n_range n)).
Proof.
  induction n.
  - simpl in *. auto.
  - simpl in *. rewrite IHn at 1. simpl.
    f_equal. rewrite map_app. simpl. reflexivity.
Qed.

Lemma n_range_length :
  forall n, length (n_range n) = n.
Proof.
  induction n.
  - simpl; auto.
  - simpl; rewrite app_length, IHn; simpl; lia.
Qed.

Lemma n_range_nth_error :
  forall n m x, nth_error (n_range n) m = Some x <-> ((m < n)%nat /\ x = m).
Proof.
  induction n.
  - intros; simpl. destruct m; simpl; split; (congruence || lia).
  - intros m x; simpl.
    destruct ((m <? n)%nat) eqn:Hnm; reflect.
    + rewrite nth_error_app1 by (rewrite n_range_length; lia). rewrite IHn; lia.
    + rewrite nth_error_app2 by (rewrite n_range_length; lia). rewrite n_range_length.
      destruct (m - n)%nat as [|u] eqn:Hmn; simpl.
      * replace m with n by lia. intuition (congruence || lia).
      * destruct u; simpl; intuition (congruence || lia).
Qed.

Definition Zrange lb ub := map (fun n => lb + Z.of_nat n) (n_range (Z.to_nat (ub - lb))).

Lemma Zrange_empty :
  forall lb ub, lb >= ub -> Zrange lb ub = nil.
Proof.
  intros lb ub H. unfold Zrange.
  assert (H1 : Z.to_nat (ub - lb) = 0%nat).
  { destruct (ub - lb) eqn:Hdiff; (reflexivity || lia). }
  rewrite H1. reflexivity.
Qed.

Lemma Zrange_begin :
  forall lb ub, lb < ub -> Zrange lb ub = lb :: Zrange (lb + 1) ub.
Proof.
  intros lb ub H. unfold Zrange.
  assert (H1 : Z.to_nat (ub - lb) = S (Z.to_nat (ub - (lb + 1)))).
  { rewrite <- Z2Nat.inj_succ by lia. f_equal. lia. }
  rewrite H1. rewrite n_range_begin. simpl. f_equal.
  - lia.
  - rewrite map_map; apply map_ext. intro; lia.
Qed.

Lemma Zrange_end :
  forall lb ub, lb < ub -> Zrange lb ub = Zrange lb (ub - 1) ++ ((ub - 1) :: nil).
Proof.
  intros lb ub H. unfold Zrange.
  assert (H1 : Z.to_nat (ub - lb) = S (Z.to_nat (ub - (lb + 1)))).
  { rewrite <- Z2Nat.inj_succ by lia. f_equal. lia. }
  rewrite H1. simpl. rewrite map_app. simpl. f_equal.
  - f_equal. f_equal. f_equal. lia.
  - f_equal. rewrite Z2Nat.id; lia.
Qed.

Lemma Zrange_in :
  forall lb ub n, In n (Zrange lb ub) <-> lb <= n < ub.
Proof.
  intros lb ub n.
  unfold Zrange. rewrite in_map_iff. split.
  - intros [x [Hx1 Hx2]]; rewrite n_range_in in Hx2.
    apply Nat2Z.inj_lt in Hx2.
    rewrite Z2Nat.id in Hx2; [lia|].
    destruct (ub - lb); simpl in *; lia.
  - intros H. exists (Z.to_nat (n - lb)). split.
    + rewrite Z2Nat.id; lia.
    + rewrite n_range_in. apply Z2Nat.inj_lt; lia.
Qed.

Lemma Zrange_nth_error :
  forall n x lb ub, nth_error (Zrange lb ub) n = Some x <-> (lb <= x < ub /\ x = lb + Z.of_nat n).
Proof.
  intros n x lb ub. unfold Zrange.
  rewrite nth_error_map_iff.
  under_exists nat ltac:(fun _ => rewrite n_range_nth_error).
  setoid_replace (n < Z.to_nat (ub - lb))%nat with (Z.of_nat n < ub - lb) using relation iff; [firstorder lia|].
  destruct (ub - lb); simpl; lia.
Qed.

(** * Results on integer division *)

Lemma div_lt_iff :
  forall x y z, 0 < y -> x / y < z <-> x < y * z.
Proof.
  intros x y z Hy; split; intro H.
  - apply Z.nle_gt; intro H2. apply Z.div_le_lower_bound in H2; lia.
  - apply Z.div_lt_upper_bound; auto.
Qed.

Lemma div_le_iff :
  forall x y z, 0 < y -> x / y <= z <-> x <= y * z + y - 1.
Proof.
  intros x y z Hy. rewrite <- Z.lt_succ_r. rewrite div_lt_iff by lia. nia.
Qed.

Lemma div_ge_iff :
  forall x y z, 0 < z -> x <= y / z <-> x * z <= y.
Proof.
  intros x y z Hz. rewrite <- !Z.nlt_ge. apply not_iff_compat. rewrite div_lt_iff by lia. nia.
Qed.

Lemma div_gt_iff :
  forall x y z, 0 < z -> x < y / z <-> x * z + z - 1 < y.
Proof.
  intros x y z Hz. rewrite <- !Z.nle_gt. apply not_iff_compat. rewrite div_le_iff by lia. nia.
Qed.

(** * Maximum of lists of [nat] *)

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

Theorem list_max_le_iff :
  forall l n, (list_max l <= n <-> (forall x, In x l -> x <= n))%nat.
Proof.
  intros l n; split; [apply list_max_le | apply list_le_max].
Qed.

Lemma list_max_ge :
  forall l x, In x l -> (x <= list_max l)%nat.
Proof.
  induction l.
  - intros; simpl in *; tauto.
  - intros x H; simpl in *; destruct H as [H | H]; [|specialize (IHl x H)]; lia.
Qed.

(** * Extra results on [gcd] on [positive] *)

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


(** * gcd of lists of [Z] *)

Fixpoint list_gcd l :=
  match l with
  | nil => 0
  | x :: l => Z.gcd x (list_gcd l)
  end.

Lemma list_gcd_nonneg :
  forall l, 0 <= list_gcd l.
Proof.
  destruct l.
  - simpl; lia.
  - simpl. apply Z.gcd_nonneg.
Qed.

Lemma list_gcd_div :
  forall l x, In x l -> (list_gcd l | x).
Proof.
  induction l.
  - intros; simpl in *; tauto.
  - intros x [Ha | Hx].
    + rewrite <- Ha. simpl. apply Z.gcd_divide_l.
    + transitivity (list_gcd l).
      * simpl; apply Z.gcd_divide_r.
      * auto.
Qed.

(** * lcm of lists of [positive] *)

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
