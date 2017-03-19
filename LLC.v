Module LinearLambdaCalculus.

Inductive q : Type :=
  | qlin : q
  | qun : q.

Inductive b : Type :=
  | btrue : b
  | bfalse : b.

Inductive id : Type :=
  | Id : nat -> id.

Reserved Notation "'qty'" (at level 10).

Inductive ty : Type :=
  | ty_bool : qty
  | ty_pair : ty -> ty -> qty
  | ty_arrow : ty -> ty -> qty

where "'qty'" := (q -> ty).

Notation "T ** T'" := (ty_pair T T') (at level 20, left associativity).

Notation "T --> T'" := (ty_pair T T') (at level 40, left associativity).

Inductive tm : Type :=
  | tmvar : id -> tm
  | tmbool : q -> b -> tm
  | tmif : tm -> tm -> tm -> tm
  | tmpair : q -> tm -> tm -> tm
  | tmsplit : tm -> id -> id -> tm -> tm
  | tmabs : q -> id -> ty -> tm -> tm
  | tmapp : tm -> tm -> tm.

Inductive ctx : Type :=
  | empty_ctx : ctx
  | update_ctx : ctx -> id -> ty -> ctx.

Fixpoint update_l_ctx x T G :=
  match G with
  | empty_ctx => update_ctx empty_ctx x T
  | update_ctx G' x' T' => update_ctx (update_l_ctx x T G') x' T'
  end.

Lemma ctx_singleton : forall x T,
  update_ctx empty_ctx x T = update_l_ctx x T empty_ctx.
Proof.
  intros. simpl. reflexivity.
Qed.

Definition singleton_ctx x T := update_ctx empty_ctx x T.

Lemma ctx_lr : forall x x' T T',
  update_ctx (singleton_ctx x T) x' T' = update_l_ctx x T (singleton_ctx x' T').
Proof.
  intros. simpl. unfold singleton_ctx. reflexivity.
Qed.

Fixpoint concat_ctx (G1 : ctx) (G2 : ctx) : ctx :=
  match G1 with
  | empty_ctx => G2
  | update_ctx G1' x T => concat_ctx G1' (update_l_ctx x T G2)
  end.

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
