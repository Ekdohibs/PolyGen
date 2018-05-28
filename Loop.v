Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Psatz.
Open Scope Z_scope.
Open Scope list_scope.

Require Import Instr.

(** * The semantics of the Loop language *)

Inductive expr :=
| Constant : Z -> expr
| Sum : expr -> expr -> expr
| Mult : Z -> expr -> expr
| Div : expr -> Z -> expr
| Mod : expr -> Z -> expr
| Var : nat -> expr
| Max : expr -> expr -> expr
| Min : expr -> expr -> expr.

Fixpoint eval_expr (env : list Z) (e : expr) :=
  match e with
  | Constant c => c
  | Sum e1 e2 => eval_expr env e1 + eval_expr env e2
  | Mult k e => k * eval_expr env e
  | Div e k => eval_expr env e / k
  | Mod e k => (eval_expr env e) mod k
  | Var n => nth n env 0
  | Max e1 e2 => Z.max (eval_expr env e1) (eval_expr env e2)
  | Min e1 e2 => Z.min (eval_expr env e1) (eval_expr env e2)
  end.

Ltac destruct_match :=
  match goal with
  | [ |- context[match ?X with _ => _ end] ] => destruct X
  end.

Definition make_sum e1 e2 :=
  match e1, e2 with
  | Constant n, Constant m => Constant (n + m)
  | Constant 0, e2 => e2
  | e1, Constant 0 => e1
  | e1, e2 => Sum e1 e2
  end.

Lemma make_sum_correct :
  forall env e1 e2, eval_expr env (make_sum e1 e2) = eval_expr env e1 + eval_expr env e2.
Proof.
  intros env e1 e2; unfold make_sum; repeat destruct_match; simpl; try reflexivity; lia.
Qed.

Definition make_mult n e :=
  match n, e with
  | _, Constant m => Constant (n * m)
  | 0, _ => Constant 0
  | 1, e => e
  | n, e => Mult n e
  end.

Lemma make_mult_correct :
  forall env n e, eval_expr env (make_mult n e) = n * eval_expr env e.
Proof.
  intros env n e; unfold make_mult; repeat (destruct_match; simpl); try reflexivity; lia.
Qed.

Definition make_div e n :=
  match e, n with
  | Constant m, _ => Constant (m / n)
  | _, 0 => Constant 0
  | e, 1 => e
  | e, n => Div e n
  end.

Lemma make_div_correct :
  forall env e n, eval_expr env (make_div e n) = eval_expr env e / n.
Proof.
  intros env e n; unfold make_div; repeat (destruct_match; simpl); try reflexivity; rewrite ?Zdiv_0_r, ?Z.div_1_r; reflexivity.
Qed.


Inductive test :=
| LE : expr -> expr -> test
| EQ : expr -> expr -> test
| And : test -> test -> test
| Or : test -> test -> test
| Not : test -> test
| TConstantTest : bool -> test.

Fixpoint eval_test (env : list Z) (t : test) :=
  match t with
  | LE e1 e2 => eval_expr env e1 <=? eval_expr env e2
  | EQ e1 e2 => eval_expr env e1 =? eval_expr env e2
  | And t1 t2 => eval_test env t1 && eval_test env t2
  | Or t1 t2 => eval_test env t1 || eval_test env t2
  | Not t => negb (eval_test env t)
  | TConstantTest b => b
  end.

Definition make_le e1 e2 :=
  match e1, e2 with
  | Constant n, Constant m => TConstantTest (n <=? m)
  | e1, e2 => LE e1 e2
  end.

Lemma make_le_correct :
  forall env e1 e2, eval_test env (make_le e1 e2) = (eval_expr env e1 <=? eval_expr env e2).
Proof.
  intros env e1 e2; unfold make_le; repeat (destruct_match; simpl); reflexivity.
Qed.

Definition make_eq e1 e2 :=
  match e1, e2 with
  | Constant n, Constant m => TConstantTest (n =? m)
  | e1, e2 => EQ e1 e2
  end.

Lemma make_eq_correct :
  forall env e1 e2, eval_test env (make_eq e1 e2) = (eval_expr env e1 =? eval_expr env e2).
Proof.
  intros env e1 e2; unfold make_eq; repeat (destruct_match; simpl); reflexivity.
Qed.

Definition make_and t1 t2 :=
  match t1, t2 with
  | TConstantTest true, t | t, TConstantTest true => t
  | TConstantTest false, _ | _, TConstantTest false => TConstantTest false
  | t1, t2 => And t1 t2
  end.

Lemma make_and_correct :
  forall env t1 t2, eval_test env (make_and t1 t2) = eval_test env t1 && eval_test env t2.
Proof.
  intros env t1 t2; unfold make_and; repeat (destruct_match; simpl); try reflexivity;
    repeat (match goal with [ |- context[?X && ?Y]] => destruct X; simpl end); auto.
Qed.

Definition make_or t1 t2 :=
  match t1, t2 with
  | TConstantTest false, t | t, TConstantTest false => t
  | TConstantTest true, _ | _, TConstantTest true => TConstantTest true
  | t1, t2 => Or t1 t2
  end.

Lemma make_or_correct :
  forall env t1 t2, eval_test env (make_or t1 t2) = eval_test env t1 || eval_test env t2.
Proof.
  intros env t1 t2; unfold make_or; repeat (destruct_match; simpl); try reflexivity;
    repeat (match goal with [ |- context[?X || ?Y]] => destruct X; simpl end); auto.
Qed.

Definition make_not t :=
  match t with
  | TConstantTest b => TConstantTest (negb b)
  | t => Not t
  end.

Lemma make_not_correct :
  forall env t, eval_test env (make_not t) = negb (eval_test env t).
Proof.
  intros env t; unfold make_not; repeat (destruct_match; simpl); reflexivity.
Qed.


Inductive stmt :=
| Loop : expr -> expr -> stmt -> stmt
| Instr : instr -> list expr -> stmt
| Seq : list stmt -> stmt
| Guard : test -> stmt -> stmt.

Inductive loop_semantics : stmt -> list Z -> mem -> mem -> Prop :=
| LInstr : forall i es env mem1 mem2,
    instr_semantics i (map (eval_expr env) es) mem1 mem2 ->
    loop_semantics (Instr i es) env mem1 mem2
| LSeqEmpty : forall env mem, loop_semantics (Seq nil) env mem mem
| LSeq : forall env st sts mem1 mem2 mem3,
    loop_semantics st env mem1 mem2 ->
    loop_semantics (Seq sts) env mem2 mem3 ->
    loop_semantics (Seq (st :: sts)) env mem1 mem3
| LGuardTrue : forall env t st mem1 mem2,
    loop_semantics st env mem1 mem2 ->
    eval_test env t = true ->
    loop_semantics (Guard t st) env mem1 mem2
| LGuardFalse : forall env t st mem,
    eval_test env t = false -> loop_semantics (Guard t st) env mem mem
| LLoop : forall env lb ub st mem1 mem2,
    iter_semantics (fun x => loop_semantics st (x :: env)) (eval_expr env lb) (eval_expr env ub) mem1 mem2 ->
    loop_semantics (Loop lb ub st) env mem1 mem2.
