Require Import Basics.
Require Import ListCtx.

Require Import Coq.Bool.Bool.

(* Define new ModuleType for id and ty, for later using them as key-value types of the
   Key-Value Set. *)

Module Type ModuleTy <: ValModuleType.

  Definition T := ty.
  Definition equal : T -> T -> bool := ty_eq.

  Definition eq_refl : forall t, equal t t = true.
  Proof.
    intros. apply ty_eq_refl.
  Qed.

End ModuleTy.

(* Now, here is the Declarative Typing using a ListContext. *)

Module Type DeclarativeTyping
    ( mid : ModuleId )
    ( mty : ModuleTy )
    ( kvs : ListCtx.ListCtx mid mty ).

Import kvs.

(* Context *)
Notation "'Ø'" := (empty).
Notation "G '∷' x T" := (append G x T) (at level 29, left associativity).
Notation "G1 '∪' G2" := (mult G1 G2) (at level 40, left associativity).

Definition ctx : Type := kvs.T.

(* Context Split (see Figure 1-4) *)
Reserved Notation "G '≜' G1 '∘' G2" (at level 80).

Inductive split' : T -> T -> T -> Prop :=
  | M_Empty : empty ≜ empty ∘ empty
  | M_Un : forall G G1 G2 x P,
      G ≜ G1 ∘ G2 -> (append G x (P qun)) ≜ (append G1 x (P qun)) ∘ (append G2 x (P qun))
  | M_Lin1 : forall G G1 G2 x P, 
      G ≜ G1 ∘ G2 -> (append G x (P qlin)) ≜ (append G1 x (P qlin)) ∘ G2
  | M_Lin2 : forall G G1 G2 x P,
      G ≜ G1 ∘ G2 -> (append G x (P qlin)) ≜ G1 ∘ (append G2 x (P qlin))

where "G '≜' G1 '∘' G2" := (split' G G1 G2).

(* Context Split Axioms, TODO *)
Parameter unr : T -> T.
Parameter split_id_l : forall G, G ≜ (unr G) ∘ G.
Parameter split_id_r : forall G, G ≜ G ∘ (unr G).
Parameter unr_members : forall G x P Q, contains (unr G) x (P Q) -> Q = qun.

Axiom split_comm : forall G G1 G2, G ≜ G1 ∘ G2 -> G ≜ G2 ∘ G1.
Axiom split_contains : forall G G1 G2 k v,
    G ≜ G1 ∘ G2 ->
    contains G2 k v ->
    contains G k v.

(* Relations between Quantifiers and Types *)
Reserved Notation "Q1 '<<' Q2" (at level 70).  (* Q1 ⊑ Q2 *)

Inductive q_rel : q -> q -> Prop :=
  | Q_Ref : forall Q, Q << Q
  | Q_Axiom : qlin << qun

where "Q1 '<<' Q2" := (q_rel Q1 Q2).

Lemma q_rel_trans : forall Q Q' Q'', Q << Q' -> Q' << Q'' -> Q << Q''.
Proof.
  induction Q; induction Q'; induction Q''; intros H H';
  try inversion H; try inversion H'; try apply Q_Ref; try apply Q_Axiom.
Qed.

Inductive q_rel' : q -> ty -> Prop :=  (* q(T) *)
  | Q_Rel_Type : forall Q Q' P, Q << Q' -> q_rel' Q (P Q').

Reserved Notation "Q '〔' G '〕'" (at level 30).  (* q(Γ) *)

Inductive q_rel'' : q -> ctx -> Prop :=
  | Q_Rel_Ctx_Empty : forall Q, Q 〔empty〕
  | Q_Rel_Ctx_Update : forall Q G x T, 
      q_rel' Q T ->
      Q 〔G〕 ->
      Q 〔append G x T〕

where "Q '〔' G '〕'" := (q_rel'' Q G).

Lemma q_rel''_unr : forall G Q, Q 〔unr G〕.
Proof. Admitted.

Lemma q_rel''_concat_ctx : forall Q G1 G2,
  Q 〔G1〕 ->
  Q 〔G2〕 ->
  Q 〔G1 ∪ G2〕.
Proof. Admitted.

Lemma q_rel''_concat_ctx' : forall G1 G2 Q,
  Q 〔G1 ∪ G2〕 -> Q 〔G1〕 /\ Q 〔G2〕.
Proof. Admitted.

(* Declarative Typing [Figure 1-5] *)
Reserved Notation "G '|-' t '|' T" (at level 60).  (* G ⊢ t : T *)

Inductive ctx_ty : ctx -> tm -> ty -> Prop :=
  | T_Var : forall G1 G2 x T,
      qun 〔G1 ∪ G2〕 ->
      ( (append G1 x T) ∪ G2 ) |- (tmvar x) | T
  | T_Bool : forall G (Q : q) (B : b),
      qun 〔G〕 ->
      G |- (tmbool Q B) | ty_bool Q
  | T_If : forall G G1 G2 t1 t2 t3 Q T,
      G1 |- t1 | ty_bool Q ->
      G2 |- t2 | T ->
      G2 |- t3 | T ->
      G ≜ G1 ∘ G2 ->
      G |- tmif t1 t2 t3 | T
  | T_Pair : forall G G1 G2 t1 t2 T1 T2 Q,
      G1 |- t1 | T1 ->
      G2 |- t2 | T2 ->
      q_rel' Q T1 ->
      q_rel' Q T2 ->
      G ≜ G1 ∘ G2 ->
      G |- tmpair Q t1 t2 | (T1 ** T2) Q
  | T_Split : forall G G1 G2 t1 t2 T1 T2 T x y Q,
      G1 |- t1 | (T1 ** T2) Q ->
      append (append G2 x T1) y T2 |- t2 | T ->
      G ≜ G1 ∘ G2 ->
      G |- tmsplit t1 x y t2 | T
  | T_Abs : forall Q G t2 T1 T2 x,
      Q 〔G〕 ->
      append G x T1 |- t2 | T2 ->
      G |- tmabs Q x T1 t2 | (T1 --> T2) Q
  | T_App : forall G G1 G2 t1 t2 T11 T12 Q,
      G1 |- t1 | (T11 --> T12) Q ->
      G2 |- t2 | T11 ->
      G ≜ G1 ∘ G2 ->
      G |- tmapp t1 t2 | T12

where "G '|-' t '|' T" := (ctx_ty G t T).

Hint Constructors ctx_ty.

(* Three Lemmas *)
Lemma exchange_lemma : forall t x1 x2 T1 T2 T G1 G2,
  (append (append G1 x1 T1) x2 T2) ∪ G2 |- t | T ->
  (append (append G1 x2 T2) x1 T1) ∪ G2 |- t | T.
Proof.
  intros.
  assert (H' : (append (append G1 x1 T1) x2 T2) ∪ G2 = (append (append G1 x2 T2) x1 T1) ∪ G2).
    { rewrite -> append_to_concat with (k := x2). 
      rewrite -> append_to_concat with (k := x1).
      rewrite -> append_to_concat with (s' := append G1 x2 T2).
      rewrite -> append_to_concat with (s' := G1).
      apply exchange. }
  rewrite <- H'. apply H.
Qed.

Lemma unrestricted_weakening : forall G t x T P,
  G |- t | T ->
  append G x (P qun) |- t | T.
Proof.
  intros. generalize dependent G. generalize dependent T0. induction t; intros; inversion H; subst.
  - rewrite -> append_to_concat. rewrite -> assoc. eapply T_Var. apply q_rel''_concat_ctx' in H2.
    inversion H2 as [H2l H2r]. apply q_rel''_concat_ctx; try apply H2l. apply q_rel''_concat_ctx; try apply H2r.
    eapply Q_Rel_Ctx_Update; try apply Q_Rel_Ctx_Empty. apply Q_Rel_Type. apply Q_Ref.
  - apply T_Bool. apply Q_Rel_Ctx_Update; try apply H4. apply Q_Rel_Type. apply Q_Ref.
  - eapply T_If.
    + apply IHt1 in H3. apply H3.
    + apply IHt2 in H5. apply H5.
    + apply IHt3 in H7. apply H7.
    + apply M_Un with (x := x) (P := P) in H8. apply H8.
  - apply T_Pair with (G1 := append G1 x (P qun)) (G2 := append G2 x (P qun)); try apply H6; try apply H8.
    + apply IHt1 in H3. apply H3.
    + apply IHt2 in H4. apply H4.
    + apply M_Un with (x := x) (P := P) in H9. apply H9.
  - eapply T_Split.
    + apply IHt1 in H6. apply H6.
    + assert ( H' : forall G x ti x' ti' x'' ti'', append (append (append G x ti ) x' ti') x'' ti'' =
        G ∪ (append empty x ti) ∪ (append empty x' ti') ∪ (append empty x'' ti'') ).
      { intros. repeat rewrite <- append_to_concat. reflexivity. }
      assert ( weak_set_exchange : forall A B C, A ∪ B ∪ C = A ∪ C ∪ B ).
      { intros. rewrite <- id_r. rewrite <- id_r with (m := A ∪ B ∪ C). apply exchange. }
      rewrite -> H'. rewrite -> exchange. rewrite -> weak_set_exchange. repeat rewrite <- kvs.append_to_concat.
      apply IHt2. apply H7.
    + apply M_Un with (x := x) (P := P) in H8. apply H8.
  - apply T_Abs.
    + rewrite -> append_to_concat. apply q_rel''_concat_ctx; try apply H6. apply Q_Rel_Ctx_Update; try apply Q_Rel_Ctx_Empty.
      apply Q_Rel_Type. destruct q; try apply Q_Axiom. apply Q_Ref.
    + assert ( H' : append (append G x (P qun)) i t = G ∪ (append empty x (P qun)) ∪ (append empty i t) ).
      { repeat rewrite <- append_to_concat. reflexivity. }
      assert ( weak_set_exchange : forall A B C, A ∪ B ∪ C = A ∪ C ∪ B ).
      { intros. rewrite <- id_r. rewrite -> exchange. rewrite -> id_r. reflexivity. }
      rewrite -> H'. rewrite -> weak_set_exchange. repeat rewrite <- append_to_concat. apply IHt. apply H7.
  - eapply T_App.
    + apply IHt1 in H2. apply H2.
    + apply IHt2 in H4. apply H4.
    + apply M_Un with (x := x) (P := P) in H6. apply H6.
Qed.

Lemma unrestricted_contraction : forall G t x1 x2 x3 T P,
  append (append G x2 (P qun) ) x3 (P qun) |- t | T ->
  append G x1 (P qun) |- rpi (rpi t x2 x1) x3 x1 | T.
Proof.
Admitted.

End DeclarativeTyping.
