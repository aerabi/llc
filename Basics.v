(* Quantifiers : Linear & Unrestricted *)
Inductive q : Type :=
  | qlin : q
  | qun : q.

(* Boolean Literal : True & False *)
Inductive b : Type :=
  | btrue : b
  | bfalse : b.

(* Names of the Variables *)
Inductive id : Type :=
  | Id : nat -> id.

(* Type and Pretype *)
Reserved Notation "'qty'" (at level 10).

Inductive ty : Type :=
  | ty_bool : qty
  | ty_pair : ty -> ty -> qty
  | ty_arrow : ty -> ty -> qty

where "'qty'" := (q -> ty).

Notation "T ** T'" := (ty_pair T T') (at level 20, left associativity).

Notation "T --> T'" := (ty_arrow T T') (at level 40, left associativity).

(* Terms *)
Inductive tm : Type :=
  | tmvar : id -> tm
  | tmbool : q -> b -> tm
  | tmif : tm -> tm -> tm -> tm
  | tmpair : q -> tm -> tm -> tm
  | tmsplit : tm -> id -> id -> tm -> tm
  | tmabs : q -> id -> ty -> tm -> tm
  | tmapp : tm -> tm -> tm.