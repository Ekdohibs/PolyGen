Require Import String.

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Psatz.

Require Import Linalg.
Require Import Loop.
Require Import PolyLang.

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

Definition make_affine_expr (n : nat) (e : (vector * Z)%type) := Sum (make_linear_expr n (fst e)) (Constant (snd e)).

Parameter project : nat -> polyhedron -> result polyhedron.
Parameter find_lower_bound : nat -> polyhedron -> result expr.
Parameter find_upper_bound : nat -> polyhedron -> result expr.

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

Theorem generate_loop_preserves_sem :
  forall st env mem1 mem2,
    loop_semantics st env mem1 mem2 ->
    forall pi d n,
      generate_loop d n pi = Ok st ->
      length env = (n - d)%nat ->
      (forall c, In c pi.(pi_poly) -> (length (fst c) <= n)%nat) ->
      env_poly_lex_semantics (rev env) n (pi :: nil) mem1 mem2.
Proof.
  intros st env mem1 mem2 Hsem. induction Hsem.
  - intros pi d n Hgen Hlen Hpilen.
    destruct d; simpl in *; inversion Hgen.
    + unfold env_poly_lex_semantics.
      eapply PolyLexProgress with (n := 0%nat) (p := rev env); [ |reflexivity| | | apply PolyLexDone].
      * admit.
      * admit.
    + bind_ok_destruct Hgen proj Hproj.
      bind_ok_destruct Hgen lb Hlb.
      bind_ok_destruct Hgen ub Hub.
      bind_ok_destruct Hgen inner Hinner.
      inversion Hgen.
  - intros pi d n Hgen Hlen; destruct d; simpl in *; [inversion Hgen|].
    bind_ok_destruct Hgen proj Hproj.
    bind_ok_destruct Hgen lb Hlb.
    bind_ok_destruct Hgen ub Hub.
    bind_ok_destruct Hgen inner Hinner.
    inversion Hgen.
  - admit.
Admitted.
