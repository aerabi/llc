Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.

Require Import Types.
Require Import Ensembles.


Module Type MapCtxMonoid  
  ( KM : Types.ModuleType ) 
  ( VM : Types.ModuleType ).

  Definition K : Type := KM.T.
  Definition V : Type := VM.T.

  Definition T : Type := K -> V -> Prop.

  Definition contains (A : T) (k : K) (v : V) : Prop := A k v.

  Definition subseteq (A B : T) : Prop := 
    forall (k : K) (v : V), contains A k v -> contains B k v.

  (* Equivalence, Equality, and Extionsionality *)
  Definition eq (A B : T) : Prop := subseteq A B /\ subseteq B A.
  
  Lemma eq_refl : forall A : T, eq A A.
  Proof.
    intros. unfold eq. assert (H : subseteq A A).
    { unfold subseteq. intros. apply H. } split; apply H.
  Qed.

  Axiom extensionality : forall (A B : T), eq A B -> A = B.

  Lemma extensionality_converse : forall (A B : T), A = B -> eq A B.
  Proof.
    intros. rewrite <- H. apply eq_refl.
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

  (* Empty, Singleton, Union *)
  Inductive empty : T := .

  Inductive singleton (k : K) (v : V) : T :=
    singleton_contains : contains (singleton k v) k v.

  Inductive union (B C : T) : T :=
  | union_l : forall (k : K) (v : V), contains B k v -> contains (union B C) k v
  | union_r : forall (k : K) (v : V), contains C k v -> contains (union B C) k v.

  Lemma commut : forall (B C : T), union B C = union C B.
  Proof.
    intros B C. apply extensionality. unfold eq. split.
    - unfold subseteq. intros. inversion H.
      + apply union_r. apply H0.
      + apply union_l. apply H0.
    - unfold subseteq. intros. inversion H.
      + apply union_r. apply H0.
      + apply union_l. apply H0.
  Qed.

  (* Notations *)
  Notation "s1 'o' s2" := (union s1 s2) (at level 20, left associativity).
  Notation "'Ø'" := (empty).

  (* Empty Union *)
  Lemma empty_union : forall A B : T, A o B = Ø -> A = Ø /\ B = Ø.
  Proof.
    intros. apply extensionality_converse in H. inversion H as [Hl Hr].
    unfold subseteq in Hl. split.
    - apply extensionality. unfold eq. split.
      + unfold subseteq. intros. apply Hl. apply union_l. apply H0.
      + unfold subseteq. intros. inversion H0.
    - apply extensionality. unfold eq. split.
      + unfold subseteq. intros. apply Hl. apply union_r. apply H0.
      + unfold subseteq. intros. inversion H0.
  Qed.

  (* Associativity of Union *)
  Lemma assoc : forall A B C : T, (A o B) o C = A o (B o C).
  Proof.
    intros. apply extensionality. unfold eq. split; unfold subseteq.
    - intros. inversion H.
      + inversion H0.
        * apply union_l. apply H3.
        * apply union_r. apply union_l. apply H3.
      + apply union_r. apply union_r. apply H0.
    - intros. inversion H.
      + apply union_l. apply union_l. apply H0.
      + inversion H0.
        * apply union_l. apply union_r. apply H3.
        * apply union_r. apply H3.
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

  (* Identity Element of Union *)
  Lemma id_l : forall A : T, Ø o A = A.
  Proof.
    intros. apply extensionality. unfold eq. split; unfold subseteq.
    - intros. inversion H.
      + inversion H0.
      + apply H0.
    - intros. apply union_r. apply H.
  Qed.

  Lemma id_r : forall A : T, A o Ø = A.
  Proof.
    intros. apply extensionality. unfold eq. split; unfold subseteq.
    - intros. inversion H.
      + apply H0.
      + inversion H0.
    - intros. apply union_l. apply H.
  Qed.

  (* Append *)
  Definition append (A : T) (k : K) (v : V) : T := union A (singleton k v).

  (* Set Minus *)
  Inductive setminus (B C : T) : T :=
    contains_setminus : forall (k : K) (v : V),
      contains B k v /\ ~ contains C k v -> contains (setminus B C) k v.

  (* Remove *)
  Definition subtract (B : T) (k : K) (v : V) : T := setminus B (singleton k v).

  Lemma append_subtract : forall (B : T) (k : K) (v : V),
    contains B k v -> append (subtract B k v) k v = B.
  Proof.
    intros. apply extensionality. unfold eq. split; unfold subseteq.
    - intros k' v' H'. inversion H'.
      + inversion H0. apply H3.
      + inversion H0. subst k0 v0 k' v'. apply H.
    - intros k' v' H'. unfold append. unfold subtract.
      assert (H'' : (k = k' /\ v = v') \/ ~ (k = k' /\ v = v')).
      { apply classic. } inversion H'' as [H''l | H''r].
      + inversion H''l as [Hk Hv]. subst k' v'.
        apply union_r. apply singleton_contains.
      + apply union_l. apply contains_setminus. split; try apply H'.
        unfold not. intros Hf. inversion Hf. subst k' v'. unfold not in H''r.
        assert (Ht : k = k /\ v = v). { split; reflexivity. }
        apply H''r in Ht. apply Ht.
  Qed.

  Lemma decide_contains_subtract : forall (B : T) (k : K) (v : V),
    contains B k v -> exists A, append A k v = B /\ A = subtract B k v.
  Proof.
    intros. exists (subtract B k v). split; try reflexivity.
    apply append_subtract. apply H.
  Qed.

  Lemma decide_append : forall (B : T), 
    B <> Ø -> 
    exists (A : T) (k : K) (v : V), B = append A k v.
  Proof.
    intros. apply extensionality_contraposition in H. unfold eq in H.
    apply not_and_or in H. inversion H as [Hl | Hr].
    - unfold subseteq in Hl. apply not_all_ex_not in Hl.
      inversion Hl as [k Hl']. apply not_all_ex_not in Hl'.
      inversion Hl' as [v Hl'']. apply imply_to_and in Hl''.
      inversion Hl'' as [H' H'']. apply decide_contains_subtract in H'.
      inversion H' as [A HA]. inversion HA as [HAl HAr].
      exists A. exists k. exists v. rewrite -> HAl. reflexivity.
    - unfold subseteq in Hr. apply not_all_ex_not in Hr.
      inversion Hr as [k Hr']. apply not_all_ex_not in Hr'.
      inversion Hr' as [v Hr'']. apply not_imply_elim in Hr''.
      inversion Hr''.
  Qed.
