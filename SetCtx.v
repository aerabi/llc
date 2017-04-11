Module Type AbelianMonoid.

  (* Type of Abelian Monoid *)
  Parameter T : Type.

  (* Constructors *)
  Parameter empty : T.
  Parameter concat : T -> T -> T.

  Parameter decide_empty : forall (s : T), { s = empty }+{ s <> empty }.

  (* Axioms of Monoid *)
  Parameter assoc : forall m1 m2 m3, concat (concat m1 m2) m3 = concat m1 (concat m2 m3).
  
  Parameter id_left : forall m, concat empty m = m.
  Parameter id_right : forall m, concat m empty = m.

  (* The Axiom of Commutativity *)
  Parameter commut : forall m1 m2, concat m1 m2 = concat m2 m1.

End AbelianMonoid.

Module Type SetCtx ( monoid : AbelianMonoid ).
  
  (* Types of Keys and Values *)
  Parameter K : Type.
  Parameter V : Type.

  (* Constructors *)
  Parameter append : monoid.T -> K -> V -> monoid.T.
  
  Parameter decide_append : forall (s : monoid.T), 
      s <> monoid.empty -> 
      exists s' k v, s = append s' k v.

  Parameter decide_append_empty : forall s' k v, monoid.empty = append s' k v -> False.

  (* Relation between Append and Concat *)
  Parameter append_concat : forall s1 s2 s' k v, 
      s2 = append s' k v -> 
      monoid.concat s1 s2 = append (monoid.concat s1 s') k v.

  Proposition append_to_concat : forall s' k v, 
      append s' k v = monoid.concat s' (append monoid.empty k v).
  Proof.
    intros. erewrite -> append_concat with (s' := monoid.empty) (k := k) (v := v); try reflexivity.
    rewrite -> monoid.id_right. reflexivity.
  Qed.

  (* Membership *)
  Inductive contains : monoid.T -> K -> V -> Prop :=
  | contains_append : forall s s' k v, s = append s' k v -> contains s k v
  | contains_append_set : forall s' k v k' v', contains s' k' v' -> contains (append s' k v) k' v'.

  Proposition empty_contains : forall k v, contains monoid.empty k v -> False.
  Proof.
    intros. inversion H; subst.
    - apply decide_append_empty in H0. apply H0.
    - assert (H' : monoid.empty = append s' k0 v0). { rewrite <- H0. reflexivity. }
      apply decide_append_empty in H'. apply H'.
  Qed.

  (* Notations *)
  Notation "s1 'o' s2" := (monoid.concat s1 s2) (at level 20, left associativity).

  Notation "'[' k v ']'" := (append monoid.empty k v) (at level 15).

  (* No Duplications *)
  Parameter unique_append : forall s' k v, contains s' k v -> append s' k v = s'.

  (* Theorems *)
  Proposition factor : forall s1 s2 k v k' v',
      (append (append s1 k v) k' v') o s2 = s1 o (append monoid.empty k v) o (append monoid.empty k' v') o s2.
  Proof.
    intros. rewrite -> append_to_concat. rewrite -> append_to_concat. reflexivity.
  Qed.

  Lemma set_exchange : forall A B C D, A o B o C o D = A o C o B o D.
  Proof.
    intros.
    assert (H : B o C = C o B). { apply monoid.commut. }
    assert (H' : B o (C o D) = C o (B o D)). 
      { repeat rewrite <- monoid.assoc. rewrite -> H. reflexivity. }
    repeat rewrite -> monoid.assoc. rewrite -> H'. reflexivity.
  Qed.

  Lemma exchange : forall s1 s2 k v k' v',
      monoid.concat (append (append s1 k v) k' v') s2 = monoid.concat (append (append s1 k' v') k v) s2.
  Proof.
    intros. repeat rewrite -> factor. apply set_exchange.
  Qed.

End SetCtx.
