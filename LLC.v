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

Notation "T --> T'" := (ty_arrow T T') (at level 40, left associativity).

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

Notation "'[]'" := empty_ctx (at level 10).

Notation "G '::' x T" := (update_ctx G x T) (at level 15, left associativity).

Proposition update_ctx_unique : forall G G' x x' T T',
  update_ctx G x T = update_ctx G' x' T' -> G = G' /\ x = x' /\ T = T'.
Proof.
  induction G; induction G'; intros; inversion H; split; auto.
Qed.

Fixpoint update_l_ctx x T G :=
  match G with
  | [] => update_ctx ([]) x T
  | update_ctx G' x' T' => update_ctx (update_l_ctx x T G') x' T'
  end.

Notation "x T '::' G" := (update_l_ctx x T G) (at level 14, right associativity).

Lemma ctx_singleton : forall x T,
  update_ctx ([]) x T = update_l_ctx x T ([]).
Proof.
  intros. simpl. reflexivity.
Qed.

Notation "'[' x T ']'" := (update_ctx ([]) x T) (at level 10).

Lemma ctx_lr : forall x x' T T',
  update_ctx (update_ctx empty_ctx x T) x' T' = update_l_ctx x T (update_ctx empty_ctx x' T').
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma ctx_lr' : forall G x x' T T',
  update_ctx (update_l_ctx x T G) x' T' = update_l_ctx x T (update_ctx G x' T').
Proof.
  induction G.
  - intros. simpl. reflexivity.
  - intros. rewrite <- IHG. simpl. reflexivity.
Qed.

Reserved Notation "G1 'o' G2" (at level 20).

Fixpoint concat_ctx (G1 : ctx) (G2 : ctx) : ctx :=
  match G1 with
  | [] => G2
  | update_ctx G1' x T => G1' o (update_l_ctx x T G2)
  end

where "G1 'o' G2" := (concat_ctx G1 G2).

Proposition concat_ctx_update : forall G1 G2 i T,
  G1 o (update_ctx G2 i T) = update_ctx (G1 o G2) i T.
Proof.
  induction G1. induction G2.
  - intros. simpl. reflexivity.
  - intros i' T. simpl. reflexivity.
  - intros G2 i' T.
    assert (Hlr : (update_ctx G1 i t) o G2 = G1 o (update_l_ctx i t G2)). { reflexivity. }
    rewrite -> Hlr. apply IHG1 with (G2 := update_l_ctx i t G2).
Qed.

Corollary concat_ctx_null_r : forall G, G o [] = G.
Proof.
  induction G.
  - simpl. reflexivity.
  - simpl. assert (H : update_ctx G i t = update_ctx (G o []) i t). { rewrite -> IHG. reflexivity. }
    rewrite -> H. apply concat_ctx_update.
Qed.

Corollary concat_ctx_singleton : forall G i T, G o (update_ctx ([]) i T) = update_ctx G i T.
Proof.
  induction G.
  - intros. simpl. reflexivity.
  - intros i' T. simpl. rewrite -> concat_ctx_update. rewrite -> IHG. reflexivity.
Qed.

Example concat_ctx_update_lr : forall G1 G2 x T,
  (update_ctx G1 x T) o G2 = G1 o (update_l_ctx x T G2).
Proof. reflexivity. Qed.

Proposition concat_ctx_assoc : forall G1 G2 G3, (G1 o G2) o G3 = G1 o (G2 o G3).
Proof.
  intros. admit.
Qed.

Fixpoint ctx_contains (G : ctx) (i : id) (T : ty) : Prop :=
  match G with
  | [] => False
  | update_ctx G' i' T' => ((i = i') /\ (T = T')) \/ (ctx_contains G' i T)
  end.

Example ctx_contains_test_1 : forall x T, ctx_contains (update_ctx ([]) x T) x T.
Proof. intros. simpl. left. split; reflexivity. Qed.

Example ctx_contains_test_2 : forall G x T, ctx_contains (update_ctx G x T) x T.
Proof. intros. simpl. left. split; reflexivity. Qed.

Proposition ctx_contains_concat : forall G1 G2 x T, 
  ctx_contains ((update_ctx G1 x T) o G2) x T.
Proof.
  intros. induction G2.
  - simpl. rewrite -> concat_ctx_singleton. simpl. left. split; reflexivity.
  - rewrite -> concat_ctx_update. simpl. right. simpl in IHG2. apply IHG2.
Qed.

Proposition ctx_contains_concat' : 
  forall G x T, ctx_contains G x T ->
  exists G1 G2, G = (update_ctx G1 x T) o G2.
Proof.
  intros. induction G.
  - inversion H.
  - simpl in H. inversion H.
    + inversion H0. subst. exists G. exists ([]). simpl. rewrite -> concat_ctx_singleton. reflexivity.
    + apply IHG in H0. inversion H0 as [G']. inversion H1 as [G''].
      exists G'. exists (update_ctx G'' i t). rewrite -> H2. rewrite -> concat_ctx_update. reflexivity.
Qed.

Proposition ctx_contains_concat'' : forall G1 G2 x T x' T',
  ctx_contains ( (update_ctx G1 x' T') o G2 ) x T ->
  (ctx_contains G1 x T) \/ (x = x' /\ T = T') \/ (ctx_contains G2 x T).
Proof.
  intros. induction G2.
  - simpl in H. rewrite -> concat_ctx_singleton in H. simpl in H. inversion H.
    + right. left. apply H0.
    + left. apply H0.
  - rewrite -> concat_ctx_update in H. simpl in H. inversion H.
    + right. right. simpl. left. apply H0.
    + simpl in IHG2. apply IHG2 in H0. inversion H0; try (left; apply H1).
      inversion H1; try (right; left; apply H2). right. right. simpl. right. apply H2.
Qed.

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

Proposition q_rel'_qlin : forall T, q_rel' qlin T.
Proof.
  induction T; induction q0; apply Q_Rel_Type; try apply Q_Ref; try apply Q_Axiom.
Qed.

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
  Q (( G1 o G2 )).
Proof.
  intros Q G1 G2 H H'. induction G2.
  - simpl. rewrite -> concat_ctx_null_r. apply H.
  - inversion H'. subst. apply IHG2 in H5. rewrite -> concat_ctx_update. apply Q_Rel_Ctx_Update.
    + apply H3.
    + apply H5.
Qed.

Proposition q_rel''_update_l_ctx : forall G Q x T,
  Q (( update_l_ctx x T G )) -> q_rel' Q T /\ Q (( G )).
Proof.
  induction G.
  - intros. rewrite <- ctx_singleton in H. inversion H. subst. split; try apply H3; try apply H5.
  - intros. rewrite <- ctx_lr' in H. inversion H. subst. apply IHG in H5. split.
    + inversion H5. apply H0.
    + apply Q_Rel_Ctx_Update; try apply H3. inversion H5. apply H1.
Qed.

Lemma q_rel''_concat_ctx' : forall G1 G2 Q,
  Q (( G1 o G2 )) -> Q (( G1 )) /\ Q (( G2 )).
Proof.
  induction G1. induction G2.
  - intros. split; apply Q_Rel_Ctx_Empty.
  - intros. split; try apply Q_Rel_Ctx_Empty. simpl in H. apply H.
  - intros.
    assert (Hlr : (update_ctx G1 i t) o G2 = G1 o (update_l_ctx i t G2) ). { reflexivity. }
    rewrite -> Hlr in H. apply IHG1 in H. inversion H as [H1 H2]. apply q_rel''_update_l_ctx in H2.
    inversion H2 as [H21 H22]. split; try apply H22. apply Q_Rel_Ctx_Update; try apply H21; try apply H1.
Qed.

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
  induction t.
  - intros. inversion H. subst.
    assert (Hc : ctx_contains ( (update_ctx G0 i T) o G3 ) i T).
    { apply ctx_contains_concat. }
    simpl in Hc. rewrite -> H0 in Hc. rewrite <- concat_ctx_update_lr in Hc. 
    apply ctx_contains_concat'' in Hc. inversion Hc.
    { apply ctx_contains_concat' in H1. inversion H1 as [G']. inversion H3 as [G'']. subst.
      rewrite -> concat_ctx_update_lr. rewrite -> concat_ctx_update_lr. rewrite -> concat_ctx_assoc.
      apply T_Var.
    
    apply ctx_contains_concat' in Hc. 
    inversion Hc as [G']. inversion H1 as [G'']. simpl. 
  - admit.
  - intros. inversion H. subst.
Qed.
