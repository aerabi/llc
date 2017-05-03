Require Import Types.

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

  (* Decision *)  
  Parameter decide_append : forall (s : T), 
      s <> empty -> 
      exists s' k v, s = append s' k v.

  Parameter decide_append_empty : forall s' k v, empty = append s' k v -> False.

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

  (* Membership *)
  Inductive contains : T -> K -> V -> Prop :=
  | contains_append : forall s s' k v, s = append s' k v -> contains s k v
  | contains_append_set : forall s' k v k' v', contains s' k' v' -> contains (append s' k v) k' v'.

  Proposition empty_contains : forall k v, contains empty k v -> False.
  Proof.
    intros. inversion H; subst.
    - apply decide_append_empty in H0. apply H0.
    - assert (H' : empty = append s' k0 v0). { rewrite <- H0. reflexivity. }
      apply decide_append_empty in H'. apply H'.
  Qed.

  (* No Duplications *)
  Parameter unique_append : forall s' k v, contains s' k v -> append s' k v = s'.

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
    compute. apply contains_append_set. eapply contains_append. reflexivity.
  Qed.

End Test.
