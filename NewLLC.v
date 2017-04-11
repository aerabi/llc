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