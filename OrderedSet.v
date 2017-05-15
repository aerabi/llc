Require Import Axioms.
Require Import SetCtx.
Require Import Types.

Module Type AbelianMap 
    ( KM : Types.ModuleType ) 
    ( VM : Types.ModuleType ) 
    ( rsl : Types.Resolver VM )
  <: AbelianMonoid.

  Inductive Option : Type :=
  | None : Option
  | Some : VM.T -> Option.

  Definition T : Type := KM.T -> Option.

  Definition null (k : KM.T) : Option := None.
  Definition mult (m1 m2 : T) (k : KM.T) : Option := 
  match (m1 k), (m2 k) with
  | None, None => None
  | None, Some v' => Some v'
  | Some v, None => Some v
  | Some v, Some v' => Some (rsl.rsl v v')
  end.

  Lemma decide_empty : forall (s : T), { s = null }+{ s <> null }.
  Proof.
    intros. apply Axioms.principium_tertii_exclusi with (P := (s = null)).
  Qed.

  Notation "s1 'o' s2" := (mult s1 s2) (at level 20, left associativity).

  Lemma assoc : forall m1 m2 m3, (m1 o m2) o m3 = m1 o (m2 o m3).
  Proof.
    assert (H : forall m1 m2 m3 k, ((m1 o m2) o m3) k = (m1 o (m2 o m3)) k).
    { intros.
      assert (Hm : forall (m : T), exists op, m k = op).
      { intros. exists (m k). reflexivity. }
      assert (Hm1 : exists op, m1 k = op). { apply Hm. }
      assert (Hm2 : exists op, m2 k = op). { apply Hm. }
      assert (Hm3 : exists op, m3 k = op). { apply Hm. }
      inversion Hm1 as [o1 H1]. inversion Hm2 as [o2 H2]. inversion Hm3 as [o3 H3].
      induction o1; induction o2; induction o3; compute;
      rewrite -> H1; rewrite -> H2; rewrite -> H3; try reflexivity.
      rewrite -> rsl.assoc_rsl. reflexivity. }
    intros.
    apply Axioms.functional_extensionality with (f := (m1 o m2) o m3) (g := m1 o (m2 o m3)) in H. apply H.
  Qed.

  Lemma id_l : forall m, null o m = m.
  Proof.
    assert (H : forall m k, (null o m) k = m k).
    { intros.
      assert (Hm : exists op, m k = op). { exists (m k). reflexivity. }
      inversion Hm as [op Hop]. compute. induction op; rewrite -> Hop; reflexivity. }
    intros. apply Axioms.functional_extensionality with (f := null o m) (g := m) in H. apply H.
  Qed.

  Lemma id_r : forall m, m o null = m.
  Proof.
    assert (H : forall m k, (m o null) k = m k).
    { intros.
      assert (Hm : exists op, m k = op). { exists (m k). reflexivity. }
      inversion Hm as [op Hop]. compute. induction op; rewrite -> Hop; reflexivity. }
    intros. apply Axioms.functional_extensionality with (f := m o null) (g := m) in H. apply H.
  Qed.

  Lemma commut : forall m1 m2, m1 o m2 = m2 o m1.
  Proof.
    assert (H : forall m1 m2 k, (m1 o m2) k = (m2 o m1) k).
    { intros.
      assert (Hm1 : exists o1, m1 k = o1). { exists (m1 k). reflexivity. }
      assert (Hm2 : exists o2, m2 k = o2). { exists (m2 k). reflexivity. }
      inversion Hm1 as [o1 H1]. inversion Hm2 as [o2 H2].
      induction o1; induction o2; compute; rewrite -> H1; rewrite -> H2; try reflexivity.
      rewrite -> rsl.comm_rsl. reflexivity. }
    intros.
    apply Axioms.functional_extensionality with (f := m1 o m2) (g := m2 o m1) in H. apply H.
  Qed.

  Lemma exchange : forall A B C D, A o B o C o D = A o C o B o D.
  Proof.
    intros.
    assert (H : B o C = C o B). { apply commut. }
    assert (H' : B o (C o D) = C o (B o D)). 
      { repeat rewrite <- assoc. rewrite -> H. reflexivity. }
    repeat rewrite -> assoc. rewrite -> H'. reflexivity.
  Qed.

End AbelianMap.