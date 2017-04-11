Module Type KeyValueSet.

  (* The class of all KeyValueSets is an Abelian Monoid. To define KeyValueSets, we must
     furthermore define axioms on accessing the elements of each set,
     and an axiom avoiding duplicated elements. The first part is related with the Monoid. *)

  (* Type of Abelian Monoid *)
  Parameter T : Type.

  (* Constructors *)
  Parameter empty : T.
  Parameter concat : T -> T -> T.

  (* Notations *)
  Notation "s1 'o' s2" := (concat s1 s2) (at level 20, left associativity).

  (* Decision *)
  Parameter decide_empty : forall (s : T), { s = empty }+{ s <> empty }.

  (* Axioms of Monoid *)
  Parameter assoc : forall m1 m2 m3, concat (concat m1 m2) m3 = concat m1 (concat m2 m3).
  
  Parameter id_left : forall m, concat empty m = m.
  Parameter id_right : forall m, concat m empty = m.

  (* The Axiom of Commutativity *)
  Parameter commut : forall m1 m2, concat m1 m2 = concat m2 m1.

  Lemma set_exchange : forall A B C D, A o B o C o D = A o C o B o D.
  Proof.
    intros.
    assert (H : B o C = C o B). { apply commut. }
    assert (H' : B o (C o D) = C o (B o D)). 
      { repeat rewrite <- assoc. rewrite -> H. reflexivity. }
    repeat rewrite -> assoc. rewrite -> H'. reflexivity.
  Qed.

  (* The rest of the definition is associated with access to key-value elements of each set. *)
  
  (* Quantifiers : Linear & Unrestricted *)
  Inductive Q : Type :=
    | qlin : Q
    | qun : Q.

  (* Names of the Variables *)
  Inductive K : Type :=
    | Id : nat -> K.

  (* Type and Pretype *)
  Reserved Notation "'P'" (at level 10).

  Inductive V : Type :=
    | ty_bool : P
    | ty_pair : V -> V -> P
    | ty_arrow : V -> V -> P

  where "'P'" := (Q -> V).

  (* Constructors *)
  Parameter append : T -> K -> V -> T.

  Notation "'[' k v ']'" := (append empty k v) (at level 15).

  (* Decision *)  
  Parameter decide_append : forall (s : T), 
      s <> empty -> 
      exists s' k v, s = append s' k v.

  Parameter decide_append_empty : forall s' k v, empty = append s' k v -> False.

  (* Relation between Append and Concat *)
  Parameter append_concat : forall s1 s2 s' k v, 
      s2 = append s' k v -> 
      s1 o s2 = append (s1 o s') k v.

  Proposition append_to_concat : forall s' k v, 
      append s' k v = s' o (append empty k v).
  Proof.
    intros. erewrite -> append_concat with (s' := empty) (k := k) (v := v); try reflexivity.
    rewrite -> id_right. reflexivity.
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
    intros. repeat rewrite -> factor. apply set_exchange.
  Qed.

End KeyValueSet.
