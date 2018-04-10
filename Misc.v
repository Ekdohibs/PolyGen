Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Psatz.

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

Lemma map_nth_error_none :
  forall A B n (f : A -> B) l, nth_error l n = None -> nth_error (map f l) n = None.
Proof.
  intros; rewrite nth_error_None in *; rewrite map_length; auto.
Qed.

Hint Rewrite andb_true_iff andb_false_iff orb_true_iff orb_false_iff negb_true_iff negb_false_iff: reflect.
Hint Rewrite Z.eqb_eq Z.leb_le Z.eqb_neq Z.leb_gt Z.ltb_lt Z.ltb_ge Z.compare_eq_iff Z.compare_lt_iff Z.compare_gt_iff : reflect.
Hint Rewrite Nat.eqb_eq Nat.leb_le Nat.eqb_neq Nat.leb_gt Nat.ltb_lt Nat.ltb_ge : reflect.
Ltac reflect := autorewrite with reflect in *.
