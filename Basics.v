(* Quantifiers : Linear & Unrestricted [Figure 1-3, q] *)
Inductive q : Type :=
  | qlin : q  (* [Figure 1-3, lin] *)
  | qun : q.  (* [Figure 1-3, un] *)

(* Boolean Literal : True & False [Figure 1-3, b] *)
Inductive b : Type :=
  | btrue : b    (* [Figure 1-3, true] *)
  | bfalse : b.  (* [Figure 1-3, false] *)

(* Names of the Variables, [See Figure 1-3, x] *)
Inductive id : Type :=
  | Id : nat -> id.

(* Type and Pretype *)
Reserved Notation "'qty'" (at level 10).  (* [Figure 1-3, P] *)

Inductive ty : Type :=  (* Figure 1-3, T] *)
  | ty_bool : qty               (* [Figure 1-3, Bool] *)
  | ty_pair : ty -> ty -> qty   (* [Figure 1-3, T*T] *)
  | ty_arrow : ty -> ty -> qty  (* [Figure 1-3, T->T] *)

where "'qty'" := (q -> ty).

Notation "T ** T'" := (ty_pair T T') (at level 20, left associativity).

Notation "T --> T'" := (ty_arrow T T') (at level 40, left associativity).

(* Terms [Figure 1-3, t] *)
Inductive tm : Type :=
  | tmvar : id -> tm                       (* [Figure 1-3, x] *)
  | tmbool : q -> b -> tm                  (* [Figure 1-3, q b] *)
  | tmif : tm -> tm -> tm -> tm            (* [Figure 1-3, if t then t else t] *)
  | tmpair : q -> tm -> tm -> tm           (* [Figure 1-3, q <t, t>] *)
  | tmsplit : tm -> id -> id -> tm -> tm   (* [Figure 1-3, split t as x, y in t] *)
  | tmabs : q -> id -> ty -> tm -> tm      (* [Figure 1-3, q λx:T.t] *)
  | tmapp : tm -> tm -> tm.                (* [Figure 1-3, t t] *)

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

Definition rpv ( x' : id ) ( x : id ) ( y : id ) : id :=  (* [x->y]x' *)
  if var_eq x x' then y else x'.

Fixpoint rp ( t : tm ) ( x : id ) ( y : id ) : tm :=  (* [x->y]t *)
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
Reserved Notation "'pv'" (at level 10).  (* [Figure 1-7, w] *)

Inductive v : Type :=  (* [Figure 1-7, v] *)
  | pvbool : b -> pv              (* [Figure 1-7, b] *)
  | pvpair : id -> id -> pv       (* [Figure 1-7, <x, y>] *)
  | pvabs : id -> ty -> tm -> pv  (* [Figure 1-7, λx:T.t] *)

where "'pv'" := (q -> v).

Fixpoint tmv (t : v) : tm :=
  match t with
  | pvbool bi qi => tmbool qi bi
  | pvpair x y qi => tmpair qi (tmvar x) (tmvar y)
  | pvabs x ti t' qi => tmabs qi x ti t'
  end.
