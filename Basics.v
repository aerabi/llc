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

(* Term Variable Replacement *)
Fixpoint nat_eq ( m : nat ) ( n : nat ) : bool :=
  match m, n with
  | O, O => true
  | S _, O => false
  | O, S _ => false
  | S m', S n' => nat_eq m' n'
  end.

Definition var_eq ( x : id ) ( y : id ) : bool :=
  match x, y with
  | Id m, Id n => nat_eq m n
  end.

Definition rpv ( x' : id ) ( x : id ) ( y : id ) : id :=
  if var_eq x x' then y else x'.

Fixpoint rp ( t : tm ) ( x : id ) ( y : id ) : tm :=
  match t with
  | tmvar x' => tmvar (rpv x' x y)
  | tmbool qi bi => tmbool qi bi
  | tmif t1 t2 t3 => tmif (rp t1 x y) (rp t2 x y) (rp t3 x y)
  | tmpair qi t1 t2 => tmpair qi (rp t1 x y) (rp t2 x y)
  | tmsplit t1 x1 x2 t2 => tmsplit (rp t1 x y) (rpv x1 x y) (rpv x2 x y) (rp t2 x y)
  | tmabs qi x' T t => tmabs qi (rpv x' x y) T (rp t x y)
  | tmapp t1 t2 => tmapp (rp t1 x y) (rp t2 x y)
  end.

(* Values and PreValues *)
Reserved Notation "'pv'" (at level 10).

Inductive v : Type :=
  | pvbool : b -> pv
  | pvpair : id -> id -> pv
  | pvabs : id -> ty -> tm -> pv

where "'pv'" := (q -> v).

Fixpoint tmv (t : v) : tm :=
  match t with
  | pvbool bi qi => tmbool qi bi
  | pvpair x y qi => tmpair qi (tmvar x) (tmvar y)
  | pvabs x ti t' qi => tmabs qi x ti t'
  end.
