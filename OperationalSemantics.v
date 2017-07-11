Require Import Types.
Require Import Basics.
Require Import SetCtx.
Require Import DeclarativeTyping.

Module Type ModuleVal <: ModuleType.

  Definition T := v.

End ModuleVal.

Module OperationalSemantics
    ( M : SetCtx.AbelianMonoid )
    ( mid : ModuleId )
    ( mty : ModuleTy )
    ( mv : ModuleVal )
    ( kvs : SetCtx.KeyValueSet M mid mv ) 
    ( ctx : SetCtx.KeyValueSet M mid mty ) 
    ( dt : DeclarativeTyping.DeclarativeTyping M mid mty ctx ).

(* Stores *)
Import kvs.
Notation "'Ø'" := (empty).
Notation "G '∷' x T" := (append G x T) (at level 29, left associativity).
Notation "G1 '∪' G2" := (M.mult G1 G2) (at level 40, left associativity).

(* Store as a Function *)
Inductive sval : T -> id -> v -> Prop :=
  | S_Val : forall S x v, sval (append S x v) x v.

(* Evaluation Context *)
Inductive ec : Type :=
  | echole : ec
  | ecif : ec -> tm -> tm -> ec
  | ecpair1 : q -> ec -> tm -> ec
  | ecpair2 : q -> id -> ec -> ec
  | ecsplit : ec -> id -> id -> tm -> ec
  | ecfun : ec -> tm -> ec
  | ecarg : id -> ec -> ec.

Fixpoint eceval (E : ec) (t : tm) : tm :=
  match E with
  | echole => t
  | ecif E' t1 t2 => tmif (eceval E' t) t1 t2
  | ecpair1 qi E' t' => tmpair qi (eceval E' t) t'
  | ecpair2 qi x E' => tmpair qi (tmvar x) (eceval E' t)
  | ecsplit E' x y t' => tmsplit (eceval E' t) x y t'
  | ecfun E' t' => tmapp (eceval E' t) t'
  | ecarg x E' => tmapp (tmvar x) (eceval E' t)
  end.

(* Small Context Evaluation Relation: the Tilde with quantifier on it *)
Inductive scer' : q -> T -> id -> T -> Prop :=
  | Tilde_Lin : forall S1 S2 x V,
      scer' qlin ((append S1 x V) ∪ S2) x (S1 ∪ S2)
  | Tilde_Un : forall S x, scer' qun S x S.

(* Small-Step Evaluation *)
Inductive semev : T -> tm -> T -> tm -> Prop :=
  | E_Bool : forall S x Q (B : b),
    semev S (tmbool Q B) (append S x (pvbool B Q)) (tmvar x)
  | E_If_T : forall S S' x Q t1 t2,
    sval S x (pvbool btrue Q) ->
    scer' Q S x S' ->
    semev S (tmif (tmvar x) t1 t2) S' t1
  | E_If_F : forall S S' x Q t1 t2,
    sval S x (pvbool bfalse Q) ->
    scer' Q S x S' ->
    semev S (tmif (tmvar x) t1 t2) S' t2
  | E_Pair : forall S x y z Q,
    semev S (tmpair Q (tmvar y) (tmvar z)) (append S x (pvpair y z Q)) (tmvar x)
  | E_Split : forall S S' x y y1 z z1 Q t,
    sval S x (pvpair y1 z1 Q) ->
    scer' Q S x S' ->
    semev S (tmsplit (tmvar x) y z t) S' (rp (rp t y y1) z z1)
  | E_Fun : forall S x y t ti Q,
    semev S (tmabs Q y ti t) (append S x (pvabs y ti t Q)) (tmvar x)
  | E_App : forall S S' x1 x2 y t ti Q,
    sval S x1 (pvabs y ti t Q) ->
    scer' Q S x1 S' ->
    semev S (tmapp (tmvar x1) (tmvar x2)) S' (rp t y x2).

Hint Constructors semev.

(* Top-Level Evaluation *)
Inductive tlsemev : T -> tm -> T -> tm -> Prop :=
  | E_Ctxt : forall S S' E t t',
    semev S t S' t' ->
    tlsemev S (eceval E t) S' (eceval E t').

(* Lemmas *)
Proposition tlsemev_semev : forall S S' t t',
  semev S t S' t' ->
  tlsemev S t S' t'.
Proof.
  intros. apply E_Ctxt with (E := echole) in H. simpl in H. apply H.
Qed.

(* Tests *)
Example test_bool_1 :
  semev empty (tmbool qlin btrue) (append empty (Id 0) (pvbool btrue qlin)) (tmvar (Id 0)).
Proof. eapply E_Bool. Qed.

Example test_bool_2 :
  tlsemev empty (tmbool qlin btrue) (append empty (Id 0) (pvbool btrue qlin)) (tmvar (Id 0)).
Proof. apply tlsemev_semev. apply test_bool_1. Qed.

(* Store Typing *)
Notation "G '≜' G1 '∘' G2" := (dt.split' G G1 G2) (at level 20, left associativity).
Notation "G '|-' t '|' T" := (dt.ctx_ty G t T) (at level 60).

(* Store Typing and Program Typing *)

Inductive stty : T -> ctx.T -> Prop :=
  | T_EmptyS : stty empty ctx.empty
  | T_NextlinS : forall S G G1 G2 (w : pv) ti x,
    G ≜ G1 ∘ G2 ->
    stty S G ->
    G1 |- tmv (w qlin) | ti ->
    stty (append S x (w qlin)) (ctx.append G2 x ti)
  | T_NextunS : forall S G G1 G2 (w : pv) ti x,
    G ≜ G1 ∘ G2 ->
    stty S G ->
    G1 |- tmv (w qun) | ti ->
    stty (append S x (w qun)) (ctx.append G2 x ti).

Inductive stty' : T -> ctx.T -> Prop :=
  | T_EmptyS' : stty' empty ctx.empty
  | T_NextS' : forall S G G1 G2 ti tt x,
    G ≜ G1 ∘ G2 ->
    stty' S G ->
    G1 |- tmv tt | ti ->
    stty' (append S x tt) (ctx.append G2 x ti).

Inductive prty : T -> tm -> Prop :=
  | T_Prog : forall S G t ti,
    stty S G ->
    G |- t | ti ->
    prty S t.

Inductive prty' : T -> tm -> Prop :=
  | T_Prog' : forall S G t ti,
    stty' S G ->
    G |- t | ti ->
    prty' S t.

Inductive in' : T -> id -> Prop :=
  | S_Contains : forall S x vi,
    contains S x vi ->
    in' S x.

Proposition prty'_in' : forall S x,
  prty' S (tmvar x) -> in' S x.
Proof.
  Admitted.

Lemma subsemantic : forall S G G1 G2,
  stty' S G ->
  G ≜ G1 ∘ G2 ->
  (exists S1, stty' S1 G1 /\ (exists S2, S = S1 ∪ S2)).
Proof. Admitted.

(* Alternative Definition : Small-Step Semantic Evaluation, SSSE *)
Inductive ssse : T -> tm -> T -> tm -> Prop :=
  | SSSE_Bool : forall S x Q (B : b),
    ssse S (tmbool Q B) (append S x (pvbool B Q)) (tmvar x)
  | SSSE_If_Eval : forall S S' t t' t1 t2,
    ssse S t S' t' ->
    ssse S (tmif t t1 t2) S' (tmif t' t1 t2)
  | SSSE_If_T : forall S S' x Q t1 t2,
    sval S x (pvbool btrue Q) ->
    scer' Q S x S' ->
    ssse S (tmif (tmvar x) t1 t2) S' t1
  | SSSE_If_F : forall S S' x Q t1 t2,
    sval S x (pvbool bfalse Q) ->
    scer' Q S x S' ->
    ssse S (tmif (tmvar x) t1 t2) S' t2
  | SSSE_Pair_Eval_Fst : forall S S' y Q t1 t2, 
    ssse S t1 S' (tmvar y) ->
    ssse S (tmpair Q t1 t2) S' (tmpair Q (tmvar y) t2)
  | SSSE_Pair_Eval_Snd : forall S S' y z Q t2,
    ssse S t2 S' (tmvar z) ->
    ssse S (tmpair Q (tmvar y) t2) S' (tmpair Q (tmvar y) (tmvar z))
  | SSSE_Pair : forall S x y z Q,
    ssse S (tmpair Q (tmvar y) (tmvar z)) (append S x (pvpair y z Q)) (tmvar x)
  | SSSE_Split_Eval : forall S S' x y z t t',
    ssse S t S' (tmvar x) ->
    ssse S (tmsplit t y z t') S' (tmsplit (tmvar x) y z t')
  | SSSE_Split : forall S S' x y y1 z z1 Q t,
    sval S x (pvpair y1 z1 Q) ->
    scer' Q S x S' ->
    ssse S (tmsplit (tmvar x) y z t) S' (rp (rp t y y1) z z1)
  | SSSE_Fun : forall S x y t ti Q,
    ssse S (tmabs Q y ti t) (append S x (pvabs y ti t Q)) (tmvar x)
  | SSSE_App_Eval_Fun : forall S S' x1 t1 t2, 
    ssse S t1 S' (tmvar x1) ->
    ssse S (tmapp t1 t2) S' (tmapp (tmvar x1) t2)
  | SSSE_App_Eval_Arg : forall S S' x1 x2 t2,
    ssse S t2 S' (tmvar x2) ->
    ssse S (tmapp (tmvar x1) t2) S' (tmapp (tmvar x1) (tmvar x2))
  | SSSE_App : forall S S' x1 x2 y t ti Q,
    sval S x1 (pvabs y ti t Q) ->
    scer' Q S x1 S' ->
    ssse S (tmapp (tmvar x1) (tmvar x2)) S' (rp t y x2).

(* Lemmas *)
Lemma ssse_weakening : forall (S S' S1 S2 : T) (t t' : tm),
    ssse S1 t S' t' ->
    S = S1 ∪ S2 ->
    ssse S t (S' ∪ S2) t'.
Proof.
  Admitted.

(* TODO: relation between S and G *)

Proposition context_store_bool : forall S G Q x vi,
  G |- tmvar x | ty_bool Q ->
  contains S x vi ->
  exists (bi : b), vi = pvbool bi Q.
Proof.
  Admitted.

Lemma progress' : forall S t,
  prty' S t -> (exists S' t', ssse S t S' t') \/ (exists x, t = tmvar x /\ in' S x).
Proof.
  intros S t. generalize dependent S. induction t.
  - intros. right. exists i. apply prty'_in' in H. split. reflexivity. apply H.
  - intros. left. eexists. eexists. apply SSSE_Bool.
  - intros. inversion H; subst. inversion H1; subst.
    apply subsemantic with (G1 := G1) (G2 := G2) in H0; try apply H10. inversion H0 as [S1 HS1].
    inversion HS1 as [HS1l HS1r]. inversion HS1r as [S2 HS1r'].
    apply T_Prog' with (t := t1) (ti := (ty_bool Q)) in HS1l; try apply H5. apply IHt1 in HS1l.
    inversion HS1l.
    + left. inversion H2 as [S1' H2']. inversion H2' as [t1' H2'']. 
      eapply SSSE_If_Eval with (t1 := t2) (t2 := t3) in H2''.
      apply ssse_weakening with (S := S) (S2 := S2) in H2''. Focus 2. apply HS1r'. 
      exists (S1' ∪ S2). exists (tmif t1' t2 t3). apply H2''.
    + left. inversion H2 as [x H2']. inversion H2' as [H2'l H2'r]. subst t1.
      inversion H2'r. subst S0 x0. apply context_store_bool with (S := S1) (vi := vi) in H5.
      Focus 2. apply H3. inversion H5 as [bi H5']. apply kvs.contains_exists in H3; auto.
      inversion H3 as [S1' H3'].
      assert (Hval : sval S x (pvbool bi Q)).
      { subst S1 S. rewrite -> M.commut. rewrite -> kvs.append_to_concat. rewrite <- M.assoc.
        rewrite <- kvs.append_to_concat. rewrite <- H5'. apply S_Val. }
      destruct bi; destruct Q.
      * exists (S1' ∪ S2). exists t2. eapply SSSE_If_T with (Q := qlin); try apply Hval.
        subst S1 S. apply Tilde_Lin.
      * exists S. exists t2. eapply SSSE_If_T with (Q := qun); try apply Hval. apply Tilde_Un.
      * exists (S1' ∪ S2). exists t3. eapply SSSE_If_F with (Q := qlin); try apply Hval.
        subst S1 S. apply Tilde_Lin.
      * exists S. exists t3. eapply SSSE_If_F with (Q := qun); try apply Hval. apply Tilde_Un.
  - intros. left. inversion H; subst. inversion H1; subst.
    apply subsemantic with (G1 := G1) (G2 := G2) in H0; try apply H11. inversion H0 as [S1 HS1].
    inversion HS1 as [HS1l HS1r]. inversion HS1r as [S2 HS1r'].
    apply T_Prog' with (t := t1) (ti := T1) in HS1l; try apply H5. apply IHt1 in HS1l.
    inversion HS1l.
    + 
Qed.

Lemma preservation : forall S t S' t',
  prty S t ->
  ssse S t S' t' ->
  prty S' t'.
Proof.
  intros S t S' t' H H'. generalize dependent H. induction H'; intros HH; inversion HH; subst.
  - eapply T_Prog.
    + destruct Q.
      * eapply T_NextlinS. Focus 3. simpl. apply H0. Focus 2. apply H. apply dt.split_id_r.
      * eapply T_NextunS. Focus 3. simpl. apply H0. Focus 2. apply H. apply dt.split_id_r.
    + assert (X : forall G, ctx.append G x ti = M.mult (ctx.append G x ti) ctx.empty).
      { intros. rewrite -> M.id_r. reflexivity. }
      rewrite -> X. eapply dt.T_Var. rewrite -> M.id_r. apply dt.q_rel''_unr.
  - inversion H0. subst. assert (X : stty S G1). { eapply stty_split. apply H9. apply H. }
    eapply T_Prog in X. Focus 2. apply H4. apply IHH' in X. inversion X. subst.
    eapply T_Prog. apply H1. eapply dt.T_If. Focus 2. apply H6. Focus 2. apply H8.
    inversion H2. subst T0. subst x0.
Qed.


End OperationalSemantics.