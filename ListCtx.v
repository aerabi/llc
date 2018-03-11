Require Import SetCtx.

Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.

Module Type ModuleType.

  Parameter T : Type.
  Parameter equal : T -> T -> bool.

End ModuleType.

Module Type ListCtx  
  ( KM : ModuleType ) 
  ( VM : ModuleType ).

  Definition K : Type := KM.T.
  Definition V : Type := VM.T.

  (* Inductive Definition of Key-Value List *)
  Inductive T : Type :=
  | empty : T
  | append : T -> K -> V -> T.

  Example unittest_T : forall k v, append empty k v <> empty.
  Proof.
    intros. unfold not. intros. inversion H.
  Qed.

  Proposition decide_append_empty : forall s k v, 
    empty = append s k v -> False.
  Proof.
    intros. inversion H.
  Qed.

  Definition null : T := empty.

  (* Equality *)
  Lemma equal_commut : forall (m1 m2 : T), m1 = m2 -> m2 = m1.
  Proof.
    intros. rewrite -> H. reflexivity.
  Qed.

  (* List Concat *)
  Fixpoint mult (s s' : T) : T :=
    match s, s' with
    | _, empty => s
    | empty, _ => s'
    | _, append t' k' v' => append (mult s t') k' v'
    end.

  Example unittest_mult : forall k k' v v',
    append (append empty k v) k' v' = mult (append empty k v) (append empty k' v').
  Proof.
    intros. simpl. reflexivity.
  Qed.

  (* Notations *)
  Notation "s1 'o' s2" := (mult s1 s2) (at level 20, left associativity).

  (* Append and Concat *)
  Proposition id_r : forall m, m o null = m.
  Proof.
    intros. induction m; simpl; reflexivity.
  Qed.

  Proposition id_l : forall m, null o m = m.
  Proof.
    intros. induction m; simpl; reflexivity.
  Qed.

  Proposition append_to_concat : forall s' k v, 
    append s' k v = s' o (append empty k v).
  Proof.
    intros s. induction s.
    - intros. rewrite -> id_l. reflexivity.
    - intros k' v'. simpl. reflexivity.
  Qed.

  Proposition append_concat : forall s1 s2 s' k v, 
    s2 = append s' k v -> 
    s1 o s2 = append (s1 o s') k v.
  Proof.
    intros s1. induction s1.
    - intros. rewrite -> id_l. rewrite -> id_l. apply H.
    - intros s2 s' k' v' H. subst s2. simpl. reflexivity.
  Qed.

  (* Associativity of Concat *)
  Lemma assoc : forall m1 m2 m3, (m1 o m2) o m3 = m1 o (m2 o m3).
  Proof.
    intros m1; induction m1; intros m2; induction m2; intros m3; induction m3; simpl; try reflexivity.
    rewrite <- IHm3. simpl. reflexivity.
  Qed.

  (* Membership *)
  Inductive contains : T -> K -> V -> Prop :=
  | contains_append : forall s s' k v, s = append s' k v -> contains s k v
  | contains_append_set : forall s' k v k' v',
    contains s' k' v' -> contains (append s' k v) k' v'.

  Example unittest_contains_overwrite : forall s k k' v v' v'',
    k <> k' ->
    s = append (append (append empty k v) k' v') k v'' ->
    contains s k v. (* We must not be able to prove this. *)
  Proof.
    intros. rewrite -> H0. try apply contains_append. apply contains_append_set.
  Abort.

  Example unittest_contains_overwrite' : forall s k k' v v' v'',
    k <> k' ->
    s = append (append (append empty k' v) k' v') k v'' ->
    contains s k' v. (* We must not be able to prove this. *)
  Proof.
    intros. rewrite -> H0. try apply contains_append. apply contains_append_set; try apply H.
    try apply contains_append. apply contains_append_set. 
  Abort.

  (* Union *)
  Lemma union_l : forall (B C : T) (k : K) (v : V), 
    contains B k v -> contains (B o C) k v.
  Proof.
    intros. induction C.
    - rewrite -> id_r. apply H.
    - assert (HX : B o append C k0 v0 = append (B o C) k0 v0).
      { apply append_concat. reflexivity. } rewrite -> HX.
      apply contains_append_set. apply IHC.
  Qed.

  Lemma union_r : forall (B C : T) (k : K) (v : V),
    contains C k v -> contains (B o C) k v.
  Proof.
    intros. induction H.
    - rewrite -> H.
      assert (HX : B o append s' k v = append (B o s') k v).
      { apply append_concat. reflexivity. } rewrite -> HX.
      eapply contains_append. reflexivity.
    - assert (HX : B o append s' k v = append (B o s') k v).
      { apply append_concat. reflexivity. } rewrite -> HX.
      apply contains_append_set. apply IHcontains. 
  Qed.

  Lemma reunion : forall (B C : T) (k : K) (v : V),
    contains (B o C) k v -> contains B k v \/ contains C k v.
  Proof.
    intros. induction C.
    - left. rewrite -> id_r in H. apply H.
    - assert (HX : B o append C k0 v0 = append (B o C) k0 v0).
      { apply append_concat. reflexivity. } rewrite -> HX in H.
      inversion H.
      + subst k1 v1. inversion H0. subst k0 v0 s'.
        right. eapply contains_append. reflexivity.
      + subst s' k1 v1 k' v'. apply IHC in H5. inversion H5.
        * left. apply H0.
        * right. apply contains_append_set. apply H0.
  Qed.

  (* Equivalence *)
  Definition subseteq (A B : T) : Prop := 
    forall (k : K) (v : V), contains A k v -> contains B k v.

  Definition eq (s s' : T) : Prop := subseteq s s' /\ subseteq s' s.

  Notation "s1 '≡' s2" := (eq s1 s2) (at level 82, left associativity).

  (* Equivalence Relation Axioms *)
  Proposition subseteq_reflexivity : forall m, subseteq m m.
  Proof.
    intros. unfold subseteq. intros k v. intros H. apply H.
  Qed.

  Proposition subseteq_transitivity : forall m1 m2 m3,
    subseteq m1 m2 -> subseteq m2 m3 -> subseteq m1 m3.
  Proof.
    intros m1 m2 m3 H H'. unfold subseteq in H. unfold subseteq in H'.
    unfold subseteq. intros k' v'. intros H''. apply H in H''.
    apply H' in H''. apply H''.
  Qed.

  Proposition eq_reflexivity : forall m, m ≡ m.
  Proof.
    intros. split; apply subseteq_reflexivity.
  Qed.

  Proposition eq_symmetry : forall m1 m2, m1 ≡ m2 -> m2 ≡ m1.
  Proof.
    intros. inversion H. split; try apply H0; try apply H1.
  Qed.

  Proposition eq_transitivity : forall m1 m2 m3,
    m1 ≡ m2 -> m2 ≡ m3 -> m1 ≡ m3.
  Proof.
    intros m1 m2 m3 H H'. inversion H. inversion H'.
    apply subseteq_transitivity with (m1 := m1) (m2 := m2) (m3 := m3) in H0.
    apply subseteq_transitivity with (m1 := m3) (m2 := m2) (m3 := m1) in H3.
    - split; try apply H0; try apply H3.
    - apply H1.
    - apply H2.
  Qed.

  (* Commutativity *)
  Lemma eq_commut : forall (B C : T), B o C ≡ C o B.
  Proof.
    intros B C. unfold eq. split.
    - unfold subseteq. intros. apply reunion in H. inversion H.
      + apply union_r. apply H0.
      + apply union_l. apply H0.
    - unfold subseteq. intros. apply reunion in H. inversion H.
      + apply union_r. apply H0.
      + apply union_l. apply H0.
  Qed.

  (* Axioms of Extionsionality *)
  Axiom extensionality : forall (A B : T), eq A B -> A = B.

  Lemma extensionality_converse : forall (A B : T), A = B -> eq A B.
  Proof.
    intros. rewrite <- H. apply eq_reflexivity.
  Qed.

  Lemma extensionality_inverse : forall (A B : T), ~ eq A B -> A <> B.
  Proof.
    intros. unfold not. intros Hf. apply extensionality_converse in Hf.
    apply H in Hf. apply Hf.
  Qed.

  Lemma extensionality_contraposition : forall (A B : T), A <> B -> ~ eq A B.
  Proof.
    intros. unfold not. intros Hf. apply extensionality in Hf.
    unfold not in H. apply H in Hf. apply Hf.
  Qed.

  (* Commutativity *)
  Lemma commut : forall (B C : T), B o C = C o B.
  Proof.
    intros. apply extensionality. apply eq_commut.
  Qed.

  (* Exchange *)
  Lemma exchange : forall A B C D, A o B o C o D = A o C o B o D.
  Proof.
    intros.
    assert (H : B o C = C o B). { apply commut. }
    assert (H' : B o (C o D) = C o (B o D)). 
      { repeat rewrite <- assoc. rewrite -> H. reflexivity. }
    repeat rewrite -> assoc. rewrite -> H'. reflexivity.
  Qed.

  (* Contains Key *)
  Inductive contains_key : T -> K -> Prop :=
    contains_key_contains : forall (A : T) (k : K) (v : V),
      contains A k v -> contains_key A k.

  (* Duplicate Keys *)
  Inductive duplicated : T -> Prop :=
    duplicate_keys : forall (A : T) (k : K) (v v' : V),
      contains A k v -> contains A k v' -> v <> v' -> duplicated A.

  Definition well_defined (A : T) : Prop := ~ duplicated A.

  Lemma contains_unique : forall (A : T) (k : K),
    well_defined A -> contains_key A k -> (exists! (v : V), contains A k v).
  Proof.
    intros A k H H'. inversion H'. subst A0 k0. exists v. unfold unique. split.
    - apply H0.
    - intros v'. unfold well_defined in H. unfold not in H. intros.
      (* reductio ad absurdum *)
      assert (Hx : v = v' \/ v <> v'). { apply classic. }
      inversion Hx; try apply H2. assert (Hf : duplicated A). 
      { eapply duplicate_keys. apply H0. apply H1. apply H2. }
      apply H in Hf. inversion Hf.
  Qed.

  Fixpoint to_function (A : T) (none : V) (k : K) : V :=
    match A with
    | append B k' v' => if KM.equal k k' then v' else to_function B none k
    | empty => none
    end.

  (* Pair Uniqueness *)
  Lemma unique_append : forall (A : T) (k : K) (v : V), 
    contains A k v -> append A k v = A.
  Proof.
    intros. apply extensionality. unfold eq. split; unfold subseteq; intros k' v'.
    - intros H'. inversion H'.
      + subst k0 v0. inversion H0. subst s' k' v'. apply H.
      + subst k0 v0 s' k'0 v'0. apply H5.
    - intros H'. apply contains_append_set. apply H'.
  Qed.

  (* Allocate *)
  

End ListCtx.