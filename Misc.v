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
Hint Rewrite Z.eqb_eq Z.leb_le Z.eqb_neq Z.leb_gt Z.ltb_lt Z.ltb_ge Z.gtb_ltb Z.geb_leb Z.compare_eq_iff Z.compare_lt_iff Z.compare_gt_iff : reflect.
Hint Rewrite Nat.eqb_eq Nat.leb_le Nat.eqb_neq Nat.leb_gt Nat.ltb_lt Nat.ltb_ge : reflect.

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

Ltac under_forall vartype tac :=
  under_binder vartype ltac:(fun f => rewrite forall_ext with (Q := f)) tac.
Ltac under_exists vartype tac :=
  under_binder vartype ltac:(fun f => rewrite exists_ext with (Q := f)) tac.
Ltac under_forall_in H vartype tac :=
  under_binder vartype ltac:(fun f => rewrite forall_ext with (Q := f) in H) tac.
Ltac under_exists_in H vartype tac :=
  under_binder vartype ltac:(fun f => rewrite exists_ext with (Q := f) in H) tac.

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
  (forall (x y : nat), (x =? y) = true) <-> (forall (x y : nat), x = y).
Proof.
  under_forall nat ltac:(fun _ => under_forall nat ltac:(fun _ => reflect)).
  reflexivity.
Qed.

Lemma test3:
  forall l1 l2, forallb (fun x => existsb (fun y => x =? y) l1) l2 = true <->
           forall x, In x l2 -> exists y, In y l1 /\ x = y.
Proof.
  intros l1 l2.
  reflect_binders. reflexivity.
Qed.