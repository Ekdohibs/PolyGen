Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Psatz.
Open Scope Z_scope.
Open Scope list_scope.

Inductive expr :=
| Constant : Z -> expr
| Sum : expr -> expr -> expr
| Mult : Z -> expr -> expr
| Div : expr -> Z -> expr
| Mod : expr -> Z -> expr
| Var : nat -> expr.

Fixpoint eval_expr (env : list Z) (e : expr) :=
  match e with
  | Constant c => c
  | Sum e1 e2 => eval_expr env e1 + eval_expr env e2
  | Mult k e => k * eval_expr env e
  | Div e k => eval_expr env e / k
  | Mod e k => (eval_expr env e) mod k
  | Var n => nth n env 0
  end.

Parameter instr : Type.
Parameter mem : Type.
Parameter instr_semantics : instr -> list Z -> mem -> mem -> Prop.

Inductive test :=
| LE : expr -> expr -> test
| EQ : expr -> expr -> test
| And : test -> test -> test
| Or : test -> test -> test
| Not : test -> test.

Fixpoint eval_test (env : list Z) (t : test) :=
  match t with
  | LE e1 e2 => eval_expr env e1 <=? eval_expr env e2
  | EQ e1 e2 => eval_expr env e1 =? eval_expr env e2
  | And t1 t2 => eval_test env t1 && eval_test env t2
  | Or t1 t2 => eval_test env t1 || eval_test env t2
  | Not t => negb (eval_test env t)
  end.

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
| LLoopDone : forall env lb ub st mem,
    eval_expr env ub <= eval_expr env lb -> loop_semantics (Loop lb ub st) env mem mem
| LLoopProgress : forall env lb ub st mem1 mem2 mem3,
    eval_expr env lb < eval_expr env ub ->
    loop_semantics st (eval_expr env lb :: env) mem1 mem2 ->
    loop_semantics (Loop (Sum lb (Constant 1)) ub st) env mem2 mem3 ->
    loop_semantics (Loop lb ub st) env mem1 mem3.

