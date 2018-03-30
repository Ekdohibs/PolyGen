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
