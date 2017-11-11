(* Quantifiers : Linear & Unrestricted [Figure 1-3, q] *)
Inductive q : Type :=
  | qlin : q  (* [Figure 1-3, lin] *)
  | qun : q.  (* [Figure 1-3, un] *)

Definition q_eq ( x : q ) ( y : q ) : bool :=
  match x, y with
  | qun, qun => true
  | qlin, qlin => true
  | _, _ => false
  end.

Example q_eq_test : q_eq qun qlin = false.
Proof. simpl. reflexivity. Qed.

(* Boolean Literal : True & False [Figure 1-3, b] *)
Inductive b : Type :=
  | btrue : b    (* [Figure 1-3, true] *)
  | bfalse : b.  (* [Figure 1-3, false] *)

Definition b_eq ( x : b ) ( y : b ) : bool :=
  match x, y with
  | btrue, btrue => true
  | bfalse, bfalse => true
  | _, _ => false
  end.

Example b_eq_test : b_eq btrue bfalse = false.
Proof. simpl. reflexivity. Qed.

(* Names of the Variables, [See Figure 1-3, x] *)
Inductive id : Type :=
  | Id : nat -> id.

Fixpoint nat_eq ( m : nat ) ( n : nat ) : bool :=
  match m, n with
  | O, O => true
  | S _, O => false
  | O, S _ => false
  | S m', S n' => nat_eq m' n'
  end.

Lemma nat_eq_to_eq : forall m n, nat_eq m n = true -> m = n.
Proof.
  intros m. induction m; induction n; intros H.
  - reflexivity.
  - compute in H. inversion H.
  - compute in H. inversion H.
  - simpl in H. apply IHm in H. rewrite -> H. reflexivity.
Qed.

Definition var_eq ( x : id ) ( y : id ) : bool :=
  match x, y with
  | Id m, Id n => nat_eq m n
  end.

Lemma var_eq_to_eq : forall x y, var_eq x y = true -> x = y.
Proof.
  intros. destruct x. destruct y. inversion H. apply nat_eq_to_eq in H1.
  rewrite -> H1. reflexivity.
Qed.

(* Type and Pretype *)
Reserved Notation "'qty'" (at level 10).  (* [Figure 1-3, P] *)

Inductive ty : Type :=  (* Figure 1-3, T] *)
  | ty_bool : qty               (* [Figure 1-3, Bool] *)
  | ty_pair : ty -> ty -> qty   (* [Figure 1-3, T*T] *)
  | ty_arrow : ty -> ty -> qty  (* [Figure 1-3, T->T] *)

where "'qty'" := (q -> ty).

Notation "T ** T'" := (ty_pair T T') (at level 20, left associativity).

Notation "T --> T'" := (ty_arrow T T') (at level 40, left associativity).

Fixpoint ty_eq ( T1 : ty ) ( T2 : ty ) : bool :=
  match T1, T2 with
  | ty_bool q1, ty_bool q2 => q_eq q1 q2
  | ty_pair TT1 TT2 Q, ty_pair TT'1 TT'2 Q' => 
    andb (q_eq Q Q') (andb (ty_eq TT1 TT'1) (ty_eq TT2 TT'2))
  | ty_arrow TT1 TT2 Q, ty_arrow TT'1 TT'2 Q' => 
    andb (q_eq Q Q') (andb (ty_eq TT1 TT'1) (ty_eq TT2 TT'2))
  | _, _ => false
  end.

(* Pointer *)
Inductive pnt : Type :=
  | Pnt : nat -> pnt.

(* Terms [Figure 1-3, t] *)
Inductive tm : Type :=
  | tmvar : id -> tm                       (* [Figure 1-3, x] *)
  | tmbool : q -> b -> tm                  (* [Figure 1-3, q b] *)
  | tmif : tm -> tm -> tm -> tm            (* [Figure 1-3, if t then t else t] *)
  | tmpair : q -> tm -> tm -> tm           (* [Figure 1-3, q <t, t>] *)
  | tmsplit : tm -> id -> id -> tm -> tm   (* [Figure 1-3, split t as x, y in t] *)
  | tmabs : q -> id -> ty -> tm -> tm      (* [Figure 1-3, q λx:T.t] *)
  | tmapp : tm -> tm -> tm                 (* [Figure 1-3, t t] *)
  | tmpointer : pnt -> tm.

Fixpoint tm_eq ( t1 : tm ) ( t2 : tm ) : bool :=
  match t1, t2 with
  | tmvar x, tmvar y => var_eq x y
  | tmbool q1 x, tmbool q2 y => andb (q_eq q1 q2) (b_eq x y)
  | tmif t1 t2 t3, tmif t'1 t'2 t'3 =>
    andb (tm_eq t1 t'1) (andb (tm_eq t2 t'2) (tm_eq t3 t'3))
  | tmpair q1 t1 t2, tmpair q'1 t'1 t'2 =>
    andb (q_eq q1 q'1) (andb (tm_eq t1 t'1) (tm_eq t2 t'2))
  | tmsplit t1 x y t2, tmsplit t'1 x' y' t'2 =>
    andb (andb (var_eq x x') (var_eq y y')) (andb (tm_eq t1 t'1) (tm_eq t2 t'2))
  | tmabs Q x T t, tmabs Q' x' T' t' =>
    andb (andb (q_eq Q Q') (ty_eq T T')) (andb (var_eq x x') (tm_eq t t'))
  | tmapp t1 t2, tmapp t'1 t'2 => andb (tm_eq t1 t'1) (tm_eq t2 t'2)
  | tmpointer (Pnt n1), tmpointer (Pnt n2) => nat_eq n1 n2
  | _, _ => false
  end.

Example tm_eq_test_1 : tm_eq (tmvar (Id 0)) (tmvar (Id 0)) = true.
Proof. simpl. reflexivity. Qed.

Example tm_eq_test_2 : forall x y g,
  x = tmvar (Id 0) ->
  y = tmvar (Id 0) ->
  g = tmbool qun bfalse ->
  tm_eq (tmif g x y) (tmif g y x) = true.
Proof. intros. rewrite -> H. rewrite -> H0. rewrite -> H1. 
  simpl. reflexivity. Qed.

(* Term Variable Replacement *)
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
  | _ => t
  end.

(* Replace Variable by Pointer *)
Fixpoint rpp ( t : tm ) ( x : id ) ( y : pnt ) : tm :=  (* [x->y]t *)
  match t with
  | tmvar x' => if var_eq x x' then tmpointer y else t
  | tmif t1 t2 t3 => tmif (rpp t1 x y) (rpp t2 x y) (rpp t3 x y)
  | tmpair qi t1 t2 => tmpair qi (rpp t1 x y) (rpp t2 x y)
  | tmsplit t1 x1 x2 t2 => 
      if orb (var_eq x x1) (var_eq x x2)
        then tmsplit (rpp t1 x y) x1 x2 t2
        else tmsplit (rpp t1 x y) x1 x2 (rpp t2 x y)
  | tmabs qi x' T t' => if var_eq x x' then t else tmabs qi x' T (rpp t' x y)
  | tmapp t1 t2 => tmapp (rpp t1 x y) (rpp t2 x y)
  | _ => t
  end.

(* Term Replacement *)
Definition tmp : id := Id 999.

Fixpoint rpt ( t : tm ) ( x : tm ) ( y : tm ) : tm :=
  if tm_eq t x then y else
  match t with
  | tmif t1 t2 t3 => tmif (rpt t1 x y) (rpt t2 x y) (rpt t3 x y)
  | tmpair qi t1 t2 => tmpair qi (rpt t1 x y) (rpt t2 x y)
  | tmsplit t1 x1 x2 t2 => tmsplit (rpt t1 x y) x1 x2 (rpt t2 x y)
  | tmabs qi x' T t => tmabs qi x' T (rp (rpt t (rp x x' tmp) y) tmp x')
  | tmapp t1 t2 => tmapp (rpt t1 x y) (rpt t2 x y)
  | _ => t
  end.

Example rpt_test_1 : forall x y X Y f qi T,
  x = Id 0 ->
  X = tmvar x ->
  y = Id 1 ->
  Y = tmvar y ->
  f = tmabs qi x T (tmvar x) ->
  rpt f X Y = f.
Proof.
  intros x y X Y f qi T Hx HX Hy HY Hf.
  rewrite -> Hf.
  rewrite -> HX.
  rewrite -> HY.
  rewrite -> Hx.
  rewrite -> Hy.
  simpl. compute. reflexivity.
Qed.

Example rpt_test_2 : forall x y X Y f qi T,
  x = Id 0 ->
  X = tmvar x ->
  y = Id 1 ->
  Y = tmvar y ->
  f = tmabs qi x T (tmabs qi y T (tmpair qi X Y)) ->
  rpt f (tmpair qi X Y) (tmpair qi Y X) = f.
Proof.
  intros x y X Y f qi T Hx HX Hy HY Hf.
  rewrite -> Hf.
  rewrite -> HX.
  rewrite -> HY.
  rewrite -> Hx.
  rewrite -> Hy.
  simpl.
  assert (H : andb (q_eq qi qi) false = false).
  { destruct qi; simpl; reflexivity. }
  rewrite -> H. simpl. compute. reflexivity.
Qed.

(* Values and PreValues *)
Reserved Notation "'pv'" (at level 10).  (* [Figure 1-7, w] *)

Inductive v : Type :=  (* [Figure 1-7, v] *)
  | pvbool : b -> pv              (* [Figure 1-7, b] *)
  | pvpair : pnt -> pnt -> pv     (* [Figure 1-7, <x, y>] *)
  | pvabs : id -> ty -> tm -> pv  (* [Figure 1-7, λx:T.t] *)

where "'pv'" := (q -> v).

Fixpoint tmv (t : v) : tm :=
  match t with
  | pvbool bi qi => tmbool qi bi
  | pvpair x y qi => tmpair qi (tmpointer x) (tmpointer y)
  | pvabs x ti t' qi => tmabs qi x ti t'
  end.
