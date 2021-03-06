Require Import Axioms.
Require Import Types.

(* This file contains the definition of an Abelian Monoid, 
   and then, an axiomatic definition of a Key-Value Set, as an Abelian Monoid, with more
   axioms and properties.
   The Key-Value Set uses generic types for its keys and values, so in order to use it,
   you must plug-in the module types of type ModuleType (see Types.v). *)

Module Type AbelianMonoid.

  (* Type of Abelian Monoid *)
  Parameter T : Type.

  (* Constructors *)
  Parameter null : T.
  Parameter mult : T -> T -> T.

  (* Notations *)
  Notation "s1 'o' s2" := (mult s1 s2) (at level 20, left associativity).

  (* Decision *)
  Parameter decide_empty : forall (s : T), { s = null }+{ s <> null }.

  (* Axioms of Monoid *)
  Parameter assoc : forall m1 m2 m3, (m1 o m2) o m3 = m1 o (m2 o m3).
  
  Parameter id_l : forall m, null o m = m.
  Parameter id_r : forall m, m o null = m.

  (* The Axiom of Commutativity *)
  Parameter commut : forall m1 m2, m1 o m2 = m2 o m1.

  Lemma equal_commut : forall (m1 m2 : T), m1 = m2 -> m2 = m1.
  Proof.
    intros. rewrite -> H. reflexivity.
  Qed.

  Lemma exchange : forall A B C D, A o B o C o D = A o C o B o D.
  Proof.
    intros.
    assert (H : B o C = C o B). { apply commut. }
    assert (H' : B o (C o D) = C o (B o D)). 
      { repeat rewrite <- assoc. rewrite -> H. reflexivity. }
    repeat rewrite -> assoc. rewrite -> H'. reflexivity.
  Qed.

End AbelianMonoid.

Module Type KeyValueSet ( M : AbelianMonoid ) ( KM : Types.ModuleType ) ( VM : Types.ModuleType ).

  (* The Type *)
  Definition T : Type := M.T.

  Definition K : Type := KM.T.
  Definition V : Type := VM.T.

  (* Constructors *)
  Parameter append : T -> K -> V -> T.
  
  Definition empty := M.null.

  Notation "'[' k v ']'" := (append empty k v) (at level 15).

  Parameter alloc : T -> K.

  (* Decision *)  
  Parameter decide_append : forall (s : T), 
      s <> empty -> 
      exists s' k v, s = append s' k v.

  Parameter decide_append_empty : forall s' k v, empty = append s' k v -> False.

  Lemma empty_union : forall s1 s2, M.mult s1 s2 = empty -> s1 = empty /\ s2 = empty.
  Proof. Admitted.

  Proposition decide_append_iff : forall (s : T),
      s <> empty <->
      exists s' k v, s = append s' k v.
  Proof.
    split.
    - apply decide_append.
    - intros. inversion H; subst. inversion H0; subst. inversion H1; subst.
      unfold not. intros H'. eapply decide_append_empty. rewrite <- H'. reflexivity.
  Qed.
      
  (* Relation between Append and Concat *)
  Notation "s1 'o' s2" := (M.mult s1 s2) (at level 20, left associativity).

  Parameter append_concat : forall s1 s2 s' k v, 
      s2 = append s' k v -> 
      s1 o s2 = append (s1 o s') k v.

  Proposition append_to_concat : forall s' k v, 
      append s' k v = s' o (append empty k v).
  Proof.
    intros. erewrite -> append_concat with (s' := empty) (k := k) (v := v); try reflexivity.
    rewrite -> M.id_r. reflexivity.
  Qed.

  Proposition append_commut : forall s k v k' v',
      append (append s k v) k' v' = append (append s k' v') k v.
  Proof.
    intros. rewrite -> append_to_concat. rewrite -> append_to_concat.
    rewrite <- M.id_r with (m := s o (append empty k v) o (append empty k' v')).
    rewrite -> M.exchange. rewrite -> M.id_r. repeat rewrite <- append_to_concat.
    reflexivity.
  Qed.

  (* Remove *)
  Parameter remove : T -> K -> T.

  Parameter remove_append : forall s k v, remove (append s k v) k = s.

  (* Membership *)
  Inductive contains : T -> K -> V -> Prop :=
  | contains_append : forall s s' k v, s = append s' k v -> contains s k v
  | contains_append_set : forall s' k v k' v', k <> k' -> contains s' k' v' -> contains (append s' k v) k' v'.

  Proposition empty_contains : forall k v, contains empty k v -> False.
  Proof.
    intros. inversion H; subst.
    - apply decide_append_empty in H0. apply H0.
    - assert (H' : empty = append s' k0 v0). { rewrite <- H0. reflexivity. }
      apply decide_append_empty in H'. apply H'.
  Qed.

  (* Key Membership *)
  Inductive contains_key : T -> K -> Prop :=
  | contains_key_append : forall s s' k v, s = append s' k v -> contains_key s k
  | contains_key_append_set : forall s' k v k', k <> k' -> 
    contains_key s' k' -> contains_key (append s' k v) k'.

  Proposition empty_contains_key : forall k, contains_key empty k -> False.
  Proof.
    intros. inversion H.
    - apply decide_append_empty in H0. apply H0.
    - apply M.equal_commut in H0. apply decide_append_empty in H0. apply H0.
  Qed.

  Parameter remove_not_contained : forall s k, 
    ~ contains_key s k -> remove s k = s.

  Lemma contains_exists : forall (S S' : M.T) k v,
    contains S k v ->
    exists S', S = append S' k v.
  Proof.
    intros. induction H.
    - exists s'. subst. reflexivity.
    - inversion IHcontains as [s'']. subst s'. exists (append s'' k v). apply append_commut.
  Qed.

  Proposition remove_empty : forall k, remove empty k = empty.
  Proof.
    intros. apply remove_not_contained. unfold not. intros. 
    eapply empty_contains_key. apply H.
  Qed.

  Parameter decide_cross_append : forall s s' k k' v v',
    append s k' v' = append s' k v ->
    (k = k' /\ v = v' /\ s = s') \/ (k <> k' /\ contains s k v /\ contains s' k' v').

  Parameter contains_contains_key : forall S k, 
    (exists v, contains S k v) <-> contains_key S k.

  Lemma contains_set_append_law : forall s k v k' v',
    contains (append s k' v') k v ->
    (k = k' /\ v = v') \/ contains s k v.
  Proof.
    intros. remember H as H'. clear HeqH'. inversion H; subst.
    - apply decide_cross_append in H0. inversion H0 as [H1 | H1].
      + inversion H1. inversion H3. left. split; try apply H2; try apply H4.
      + inversion H1. right. inversion H3. apply H4.
    - remember H0 as H0'. clear HeqH0'. apply decide_cross_append in H0. inversion H0.
      + right. inversion H3 as [H3' H3'']. inversion H3'' as [H3''' H3'''']. 
        subst k0 v0 s'. apply H2.
      + assert (exclusi : {(k = k' /\ v = v')} + {~(k = k' /\ v = v')}).
        { apply principium_tertii_exclusi with (P := (k = k' /\ v = v')). }
        admit.
  Qed.

  (* No Duplications *)
  Parameter unique_append : forall s' k v, contains s' k v -> append s' k v = s'.

  Lemma contains_unique : forall s' k v v', 
      contains s' k v -> contains s' k v' -> v = v'.
  Proof.
  Admitted.

  (* Theorems *)
  Proposition factor : forall s1 s2 k v k' v',
      (append (append s1 k v) k' v') o s2 = s1 o (append empty k v) o (append empty k' v') o s2.
  Proof.
    intros. rewrite -> append_to_concat. rewrite -> append_to_concat. reflexivity.
  Qed.

  Lemma exchange : forall s1 s2 k v k' v',
      (append (append s1 k v) k' v') o s2 = (append (append s1 k' v') k v) o s2.
  Proof.
    intros. repeat rewrite -> factor. apply M.exchange.
  Qed.

End KeyValueSet.

Module Test ( M : AbelianMonoid ) ( m_nat : Types.ModuleNat ) ( kvs : KeyValueSet M m_nat m_nat ).
  Import kvs.
  
  Definition test_set : kvs.T := append (append empty 1 2) 2 3.

  Example test_set_contains : contains test_set 1 2.
  Proof.
    compute. apply contains_append_set. 
    - auto.
    - eapply contains_append. reflexivity.
  Qed.

End Test.
