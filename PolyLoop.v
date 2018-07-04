Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Psatz.

Require Import Linalg.
Require Import Misc.
Require Import Semantics.
Require Import Instr.

Open Scope Z_scope.

Notation affine_expr := (positive * (list Z * Z))%type.
Definition eval_affine_expr env (e : affine_expr) :=
  (dot_product (fst (snd e)) (rev env) + snd (snd e)) / (Zpos (fst e)).
Definition affine_expr_ok env (e : affine_expr) :=
  ((dot_product (fst (snd e)) (rev env) + snd (snd e)) mod (Zpos (fst e)) =? 0).

Inductive poly_stmt :=
| PLoop : polyhedron -> poly_stmt -> poly_stmt
| PInstr : instr -> list affine_expr -> poly_stmt
| PSkip : poly_stmt
| PSeq : poly_stmt -> poly_stmt -> poly_stmt
| PGuard : polyhedron -> poly_stmt -> poly_stmt.

Inductive poly_loop_semantics : poly_stmt -> list Z -> mem -> mem -> Prop :=
| PLInstr : forall i es env mem1 mem2,
(*    forallb (affine_expr_ok env) es = true -> *)
    instr_semantics i (map (eval_affine_expr env) es) mem1 mem2 ->
    poly_loop_semantics (PInstr i es) env mem1 mem2
| PLSkip : forall env mem, poly_loop_semantics PSkip env mem mem
| PLSeq : forall env st1 st2 mem1 mem2 mem3,
    poly_loop_semantics st1 env mem1 mem2 ->
    poly_loop_semantics st2 env mem2 mem3 ->
    poly_loop_semantics (PSeq st1 st2) env mem1 mem3
| PLGuardTrue : forall env t st mem1 mem2,
    poly_loop_semantics st env mem1 mem2 ->
    in_poly (rev env) t = true ->
    poly_loop_semantics (PGuard t st) env mem1 mem2
| PLGuardFalse : forall env t st mem,
    in_poly (rev env) t = false -> poly_loop_semantics (PGuard t st) env mem mem
| PLLoop : forall env p lb ub st mem1 mem2,
    (forall x, in_poly (rev (x :: env)) p = true <-> lb <= x < ub) ->
    iter_semantics (fun x => poly_loop_semantics st (x :: env)) (Zrange lb ub) mem1 mem2 ->
    poly_loop_semantics (PLoop p st) env mem1 mem2.

Lemma PLInstr_inv_sem :
  forall i es env mem1 mem2,
    poly_loop_semantics (PInstr i es) env mem1 mem2 ->
    instr_semantics i (map (eval_affine_expr env) es) mem1 mem2.
Proof.
  intros i es env mem1 mem2 Hsem. inversion_clear Hsem. auto.
Qed.

Lemma PLLoop_inv_sem :
  forall env p st mem1 mem2,
    poly_loop_semantics (PLoop p st) env mem1 mem2 ->
    exists lb ub, (forall x, in_poly (rev (x :: env)) p = true <-> lb <= x < ub) /\ iter_semantics (fun x => poly_loop_semantics st (x :: env)) (Zrange lb ub) mem1 mem2.
Proof.
  intros env p st mem1 mem2 H. inversion_clear H.
  eexists; eexists; eauto.
Qed.

Lemma PLGuard_inv_sem :
  forall env p st mem1 mem2,
    poly_loop_semantics (PGuard p st) env mem1 mem2 ->
    if in_poly (rev env) p then poly_loop_semantics st env mem1 mem2 else mem1 = mem2.
Proof.
  intros env p st mem1 mem2 H.
  inversion_clear H.
  - rewrite H1; simpl; auto.
  - rewrite H0; simpl; auto.
Qed.

Lemma PLSeq_inv_sem :
  forall env st1 st2 mem1 mem3,
    poly_loop_semantics (PSeq st1 st2) env mem1 mem3 ->
    exists mem2, poly_loop_semantics st1 env mem1 mem2 /\ poly_loop_semantics st2 env mem2 mem3.
Proof.
  intros env p st mem1 mem3 H.
  inversion_clear H. exists mem2; auto.
Qed.
