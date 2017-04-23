Require Import SetCtx.

Module NewLLC ( kvs : SetCtx.KeyValueSet ).

(* Context *)
Definition ctx : Type := kvs.T.
Definition empty_ctx : ctx := kvs.empty.
Definition update_ctx := kvs.append.
Definition concat_ctx := kvs.concat.

Notation "'Ø'" := (empty_ctx).
Notation "G '∷' x T" := (update_ctx G x T) (at level 15, left associativity).
Notation "G1 '∪' G2" := (concat_ctx G1 G2) (at level 20, left associativity).

(* Quantifiers : Linear & Unrestricted *)
Definition q : Type := kvs.Q.
Definition qun := kvs.qun.
Definition qlin := kvs.qlin.

(* Boolean Literal : True & False *)
Inductive b : Type :=
  | btrue : b
  | bfalse : b.

(* Names of the Variables *)
Definition id : Type := kvs.K.

(* Type and Pretype *)
Definition ty : Type := kvs.V.
Definition ty_bool := kvs.ty_bool.
Definition ty_pair := kvs.ty_pair.
Definition ty_arrow := kvs.ty_arrow.
Definition qty : Type := (q -> ty).

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

Inductive ctx_split : ctx -> ctx -> ctx -> Prop :=
  | M_Empty : ctx_split empty_ctx empty_ctx empty_ctx
  | M_Un : forall G G1 G2 x P,
      ctx_split G G1 G2 -> 
      ctx_split (update_ctx G x (P qun)) (update_ctx G1 x (P qun)) (update_ctx G2 x (P qun))
  | M_Lin1 : forall G G1 G2 x P,
      ctx_split G G1 G2 ->
      ctx_split (update_ctx G x (P qlin)) (update_ctx G1 x (P qlin)) G2
  | M_Lin2 : forall G G1 G2 x P,
      ctx_split G G1 G2 ->
      ctx_split (update_ctx G x (P qlin)) G1 (update_ctx G2 x (P qlin)).

Reserved Notation "Q1 '<<' Q2" (at level 70).

Inductive q_rel : q -> q -> Prop :=
  | Q_Ref : forall Q, Q << Q
  | Q_Axiom : qlin << qun

where "Q1 '<<' Q2" := (q_rel Q1 Q2).

Lemma q_rel_trans : forall Q Q' Q'', Q << Q' -> Q' << Q'' -> Q << Q''.
Proof.
  induction Q; induction Q'; induction Q''; intros H H';
  try inversion H; try inversion H'; try apply Q_Ref; try apply Q_Axiom.
Qed.

Inductive q_rel' : q -> ty -> Prop :=
  | Q_Rel_Type : forall Q Q' P, Q << Q' -> q_rel' Q (P Q').

Reserved Notation "Q '((' G '))'" (at level 30).

Inductive q_rel'' : q -> ctx -> Prop :=
  | Q_Rel_Ctx_Empty : forall Q, Q (( empty_ctx ))
  | Q_Rel_Ctx_Update : forall Q G x T, 
      q_rel' Q T ->
      Q (( G )) ->
      Q (( update_ctx G x T ))

where "Q '((' G '))'" := (q_rel'' Q G).

Lemma q_rel''_concat_ctx : forall Q G1 G2,
  Q (( G1 )) ->
  Q (( G2 )) ->
  Q (( G1 ∪ G2 )).
Proof. Admitted.

Lemma q_rel''_concat_ctx' : forall G1 G2 Q,
  Q (( G1 ∪ G2 )) -> Q (( G1 )) /\ Q (( G2 )).
Proof. Admitted.

Reserved Notation "G '|-' t '|' T" (at level 60).

Inductive ctx_ty : ctx -> tm -> ty -> Prop :=
  | T_Var : forall G1 G2 x T,
      qun (( concat_ctx G1 G2 )) ->
      (concat_ctx (update_ctx G1 x T) G2) |- (tmvar x) | T
  | T_Bool : forall G (Q : q) (B : b),
      qun (( G )) ->
      G |- (tmbool Q B) | ty_bool Q
  | T_If : forall G1 G2 t1 t2 t3 Q T,
      G1 |- t1 | ty_bool Q ->
      G2 |- t2 | T ->
      G2 |- t3 | T ->
      concat_ctx G1 G2 |- tmif t1 t2 t3 | T
  | T_Pair : forall G1 G2 t1 t2 T1 T2 Q,
      G1 |- t1 | T1 ->
      G2 |- t2 | T2 ->
      q_rel' Q T1 ->
      q_rel' Q T2 ->
      concat_ctx G1 G2 |- tmpair Q t1 t2 | (T1 ** T2) Q
  | T_Split : forall G1 G2 t1 t2 T1 T2 T x y Q,
      G1 |- t1 | (T1 ** T2) Q ->
      update_ctx (update_ctx G2 x T1) y T2 |- t2 | T ->
      concat_ctx G1 G2 |- tmsplit t1 x y t2 | T
  | T_Abs : forall Q G t2 T1 T2 x,
      Q (( G )) ->
      update_ctx G x T1 |- t2 | T2 ->
      G |- tmabs Q x T1 t2 | (T1 --> T2) Q
  | T_App : forall G1 G2 t1 t2 T11 T12 Q,
      G1 |- t1 | (T11 --> T12) Q ->
      G2 |- t2 | T11 ->
      concat_ctx G1 G2 |- tmapp t1 t2 | T12

where "G '|-' t '|' T" := (ctx_ty G t T).

Hint Constructors ctx_ty.

Lemma exchange : forall t x1 x2 T1 T2 T G1 G2,
  concat_ctx (update_ctx (update_ctx G1 x1 T1) x2 T2) G2 |- t | T ->
  concat_ctx (update_ctx (update_ctx G1 x2 T2) x1 T1) G2 |- t | T.
Proof.
  intros.
  assert (H' : (update_ctx (update_ctx G1 x1 T1) x2 T2) ∪ G2 = (update_ctx (update_ctx G1 x2 T2) x1 T1) ∪ G2).
    { apply kvs.exchange. }
  rewrite <- H'. apply H.
Qed.

Lemma unrestricted_weakening : forall G t x T P,
  G |- t | T ->
  update_ctx G x (P qun) |- t | T.
Proof.
  assert (concat_to_concat : forall G1 G2, kvs.concat G1 G2 = G1 ∪ G2). { intros. reflexivity. }
  assert (append_to_append : forall G k v, kvs.append G k v = update_ctx G k v). { intros. reflexivity. }
  intros. generalize dependent G. generalize dependent T. induction t.
  - intros. inversion H. subst. rewrite -> kvs.append_to_concat. rewrite -> kvs.assoc. repeat rewrite -> concat_to_concat.
    apply T_Var with ( G2 := G2 ∪ ( kvs.append kvs.empty x (P qun) ) ). apply q_rel''_concat_ctx' in H2.
    inversion H2 as [H2l H2r]. apply q_rel''_concat_ctx; try apply H2l. apply q_rel''_concat_ctx; try apply H2r.
    eapply Q_Rel_Ctx_Update; try apply Q_Rel_Ctx_Empty. apply Q_Rel_Type. apply Q_Ref.
  - intros. inversion H. subst. apply T_Bool. apply Q_Rel_Ctx_Update; try apply H4. apply Q_Rel_Type. apply Q_Ref.
  - intros. inversion H. subst. rewrite -> kvs.append_to_concat. rewrite -> kvs.assoc. rewrite -> concat_to_concat.
    eapply T_If.
    + apply H4.
    + rewrite <- kvs.append_to_concat. rewrite -> append_to_append. apply IHt2. apply H6.
    + rewrite <- kvs.append_to_concat. rewrite -> append_to_append. apply IHt3. apply H7.
  - intros. inversion H. subst. rewrite -> kvs.append_to_concat. rewrite -> kvs.assoc. rewrite <- kvs.append_to_concat. 
    rewrite -> append_to_append. rewrite -> concat_to_concat. apply T_Pair; try apply H3; try apply H7; try apply H8.
    apply IHt2. apply H5.
  - intros. inversion H. subst. rewrite -> kvs.append_to_concat. rewrite -> kvs.assoc. rewrite <- kvs.append_to_concat. 
    rewrite -> append_to_append. rewrite -> concat_to_concat. eapply T_Split. inversion H. subst.
    + apply H6.
    + assert ( H' : update_ctx (update_ctx (update_ctx G2 x (P qun) ) i T1) i0 T2 = 
        kvs.concat ( kvs.concat ( kvs.concat G2 (kvs.append kvs.empty x (P qun) ) ) (kvs.append kvs.empty i T1) ) (kvs.append kvs.empty i0 T2) ).
      { repeat rewrite <- kvs.append_to_concat. reflexivity. }
      rewrite -> H'. rewrite -> kvs.set_exchange.
      assert ( weak_set_exchange : forall A B C, kvs.concat (kvs.concat A B) C = kvs.concat (kvs.concat A C) B ).
      { intros. rewrite <- kvs.id_right. rewrite -> kvs.set_exchange. rewrite -> kvs.id_right. reflexivity. }
      rewrite -> weak_set_exchange. repeat rewrite <- kvs.append_to_concat. apply IHt2. apply H7.
  - intros. inversion H. subst. apply T_Abs.
    + rewrite -> kvs.append_to_concat. apply q_rel''_concat_ctx; try apply H6. apply Q_Rel_Ctx_Update; try apply Q_Rel_Ctx_Empty.
      apply Q_Rel_Type. destruct q0; try apply Q_Axiom. apply Q_Ref.
    + assert ( H' : update_ctx (update_ctx G x (P qun) ) i t = 
        kvs.concat ( kvs.concat G ( kvs.append kvs.empty x (P qun) ) ) (kvs.append kvs.empty i t) ).
      { repeat rewrite <- kvs.append_to_concat. reflexivity. }
      assert ( weak_set_exchange : forall A B C, kvs.concat (kvs.concat A B) C = kvs.concat (kvs.concat A C) B ).
      { intros. rewrite <- kvs.id_right. rewrite -> kvs.set_exchange. rewrite -> kvs.id_right. reflexivity. }
      rewrite -> H'. rewrite -> weak_set_exchange. repeat rewrite <- kvs.append_to_concat. apply IHt. apply H7.
  - intros. inversion H. subst. rewrite -> kvs.append_to_concat. rewrite -> kvs.assoc. rewrite <- kvs.append_to_concat.
    eapply T_App.
    + apply H3.
    + apply IHt2. apply H5.
Qed.

Lemma unrestricted_contraction : forall G t x1 x2 x3 T P,
  update_ctx (update_ctx G x2 (P qun) ) x3 (P qun) |- t | T ->
  x2 = x1 ->
  x3 = x1 ->
  update_ctx G x1 (P qun) |- t | T.
Proof.
  assert (append_to_append : forall G k v, kvs.append G k v = update_ctx G k v). { intros. reflexivity. }
  intros. subst.
  assert ( H' : kvs.contains ( update_ctx G x1 (P qun) ) x1 (P qun) ).
  { eapply kvs.contains_append. reflexivity. }
  apply kvs.unique_append in H'. rewrite -> append_to_append in H'. rewrite -> H' in H. apply H.
Qed.
