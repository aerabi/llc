Require Import SetCtx.
Require Import DeclarativeTyping.

Module OperationalSemantics 
    ( kvs : SetCtx.KeyValueSet ) 
    ( dt : DeclarativeTyping.DeclarativeTyping ).

(* Quantifiers : Linear & Unrestricted *)
Definition q : Type := kvs.Q.
Definition qun := kvs.qun.
Definition qlin := kvs.qlin.

(* Boolean Literal : True & False *)
Inductive b : Type :=
  | btrue : b
  | bfalse : b.

(* Type and Pretype *)
Definition ty : Type := kvs.V.
Definition ty_bool := kvs.ty_bool.
Definition ty_pair := kvs.ty_pair.
Definition ty_arrow := kvs.ty_arrow.
Definition qty : Type := (q -> ty).

Notation "T ** T'" := (ty_pair T T') (at level 20, left associativity).

Notation "T --> T'" := (ty_arrow T T') (at level 40, left associativity).

(* Names of the Variables *)
Definition id : Type := kvs.K.

(* Terms *)  (* Duplicated *)
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
  | kvs.Id m, kvs.Id n => nat_eq m n
  end.

Definition rpv ( x' : id ) ( x : id ) ( y : id ) : id :=
  if var_eq x x' then y else x'.

Example rpv_test_1 : rpv (kvs.Id 0) (kvs.Id 1) (kvs.Id 2) = kvs.Id 0.
Proof. compute. reflexivity. Qed.

Example rpv_test_2 : rpv (kvs.Id 0) (kvs.Id 0) (kvs.Id 2) = kvs.Id 2.
Proof. compute. reflexivity. Qed.

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

Example tp_test_1 : rp ( tmif ( tmvar (kvs.Id 0) ) (tmbool qlin bfalse) (tmbool qun bfalse) ) (kvs.Id 0) (kvs.Id 1) = 
  tmif ( tmvar (kvs.Id 1) ) (tmbool qlin bfalse) (tmbool qun bfalse).
Proof. compute. reflexivity. Qed.

(* Values and PreValues *)
Reserved Notation "'pv'" (at level 10).

Inductive v : Type :=
  | pvbool : b -> pv
  | pvpair : id -> id -> pv
  | pvabs : id -> ty -> tm -> pv

where "'pv'" := (q -> v).

(* Stores *)
Inductive store : Type :=
  | empty_store : store
  | update_store : store -> id -> v -> store.

Axiom store_comm : forall S x v x' v',
  update_store (update_store S x v) x' v' = update_store (update_store S x' v') x v.

Axiom store_no_duplicate : forall S x v,
  update_store (update_store S x v) x v = update_store S x v.

(* Store as a Function *)
Inductive sval : store -> id -> v -> Prop :=
  | S_Val : forall S x v, sval (update_store S x v) x v.
  

(* Evaluation Context *)
Inductive ec : Type :=
  | echole : ec
  | ecif : ec -> tm -> tm -> ec
  | ecpair1 : ec -> tm -> ec
  | ecpair2 : id -> ec -> ec
  | ecsplit : ec -> id -> id -> tm -> ec
  | ecfun : ec -> tm -> ec
  | ecarg : id -> ec -> ec.

(* Small Context Evaluation Relation *)
Fixpoint scer ( qu : q ) ( S : store ) ( x : id ) : store :=
  match qu, S, x with
  | qlin, update_store S' x' v', x'' => 
    match x' = x'' with
    | True => S'
    end
  | qun, S', _ => S'
  | _, _, _ => empty_store
  end.

Example test_scer_1 : forall S x v, scer qlin (update_store S x v) x = S.
Proof. intros. simpl. reflexivity. Qed.

Example test_scer_2 : forall S x v x' v', 
  scer qlin (update_store (update_store S x v) x' v') x = update_store S x' v'.
Proof. intros. rewrite -> store_comm. simpl. reflexivity. Qed.

(* Evaluation *)
Inductive semev : store -> tm -> store -> tm : Prop :=
  | E_Bool : forall
      


End OperationalSemantics.