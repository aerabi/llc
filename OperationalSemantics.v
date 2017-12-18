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
    semev S (tmsplit (tmvar x) y z t) S' (rpi (rpi t y y1) z z1)
  | E_Fun : forall S x y t ti Q,
    semev S (tmabs Q y ti t) (append S x (pvabs y ti t Q)) (tmvar x)
  | E_App : forall S S' x1 x2 y t ti Q,
    sval S x1 (pvabs y ti t Q) ->
    scer' Q S x1 S' ->
    semev S (tmapp (tmvar x1) (tmvar x2)) S' (rpi t y x2).

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
Notation "Q '〔' G '〕'" := (dt.q_rel'' Q G) (at level 30).

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

Lemma scer'_ex : forall S x Q,
  in' S x ->
  exists S', scer' Q S x S'.
Proof. Admitted.

Lemma subsemantic : forall S G G1 G2,
  stty' S G ->
  G ≜ G1 ∘ G2 ->
  (exists S1, stty' S1 G1 /\ (exists S2, S = S1 ∪ S2)).
Proof. Admitted.

(* Alternative Definition : Small-Step Semantic Evaluation, SSSE *)
Inductive ssse : T -> tm -> T -> tm -> Prop :=
  | SSSE_Bool : forall S x Q (B : b),
    x = alloc S ->  (* x : pointer *)
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
  | SSSE_Pair_Eval_Fst : forall S S' Q t1 t1' t2, 
    ssse S t1 S' t1' ->
    ssse S (tmpair Q t1 t2) S' (tmpair Q t1' t2)
  | SSSE_Pair_Eval_Snd : forall S S' y Q t2 t2',
    ssse S t2 S' t2' ->
    ssse S (tmpair Q (tmvar y) t2) S' (tmpair Q (tmvar y) t2')
  | SSSE_Pair : forall S x y z Q,
    x = alloc S ->
    ssse S (tmpair Q (tmvar y) (tmvar z)) (append S x (pvpair y z Q)) (tmvar x)
  | SSSE_Split_Eval : forall S S' y z t t' t'',
    ssse S t S' t' ->
    ssse S (tmsplit t y z t'') S' (tmsplit t' y z t'')
  | SSSE_Split : forall S S' x y y1 z z1 Q t,
    sval S x (pvpair y1 z1 Q) ->
    scer' Q S x S' ->
    ssse S (tmsplit (tmvar x) y z t) S' (rpi (rpi t y y1) z z1)
  | SSSE_Fun : forall S x y t ti Q,
    x = alloc S ->
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
    ssse S (tmapp (tmvar x1) (tmvar x2)) S' (rpi t y x2).

Inductive full_eval : T -> tm -> T -> K -> Prop :=
  | FuEv_Final : forall S S' t x,
    ssse S t S' (tmvar x) -> full_eval S t S' x
  | FuEv_Step  : forall S S' S'' t t' x,
    ssse S t S' t' ->
    ~(exists x', t' = tmvar x') ->
    full_eval S' t' S'' x ->
    full_eval S t S'' x.

(* Test *)
Example ssse_test_1 : forall p S x,
  p = tmif (tmbool qlin btrue) (tmbool qlin bfalse) (tmbool qlin btrue) ->
  full_eval Ø p S x ->
  sval S x (pvbool bfalse qlin).
Proof.
  intros p S x H' H. subst p. 
  inversion H as [SØ SS t x' Hf | SØ S' SS t t' x' H'].
  { inversion Hf. }
  subst SØ SS x' t. 
  inversion H' as [| SØ SS' t tt' t1 t2 Hbool | | | | | | | | | | |].
  subst SØ SS' t t1 t2. subst t'.
  inversion Hbool as [SØ y Q B Hy | | | | | | | | | | | |].
  subst SØ Q B S' tt'. clear H' H0. 
  inversion H1 as [SØ SS t x' Hf | Sy S' SS t t' x' H'].
  { inversion Hf. }
  subst Sy t SS x'. 
  inversion H' as [| | Sy SS' y' Q t1 t2 Hyval Hscer | | | | | | | | | |].
  { inversion H9. }
  { subst Sy y' t1 t2 SS'. inversion Hscer as [S1 S2 y' V HQ Hlin |].
    - subst y'. assert (HS' : S' = Ø). { admit. }
      subst S'. rewrite -> HS' in H2. subst t' Q. clear Hlin Hscer H' HS' S1 S2 V.
      clear Hyval H0 H1. inversion H2 as [SØ SS t x' Ht | SØ S' SS t t' x' Hf].
      + subst SØ t SS x'. inversion Ht. subst S0 Q B S x0. apply S_Val.
      + subst SØ t SS x'. inversion Hf as [SØ z Q B Hz | | | | | | | | | | | |].
        subst SØ Q B S' t'. unfold not in H0.
        assert (H0c : exists x' : id, tmvar z = tmvar x').
        { exists z. reflexivity. }
        apply H0 in H0c. inversion H0c.
    - subst Q. inversion Hyval. subst x1 v.
      assert (Hf : pvbool btrue qun = pvbool btrue qlin).
      { eapply contains_unique with (s' := append S1 y (pvbool btrue qun)) (k := y).
        - eapply contains_append. reflexivity.
        - rewrite -> H7. eapply contains_append. reflexivity. }
      inversion Hf. }
  { subst S0 x0 t1 t2 S'0 t'. inversion H9. subst x0 v. admit. }
Qed.

(* Lemmas *)
Lemma ssse_weakening : forall (S S' S1 S2 : T) (t t' : tm),
    ssse S1 t S' t' ->
    S = S1 ∪ S2 ->
    ssse S t (S' ∪ S2) t'.
Proof.
  Admitted.

Lemma sval_weakening : forall S S1 S2 x T,
  sval S1 x T ->
  S = S1 ∪ S2 ->
  sval S x T.
Proof. Admitted.

Lemma in'_weakening : forall S S1 S2 x,
  in' S1 x ->
  S = S1 ∪ S2 ->
  in' S x.
Proof. Admitted.

(* TODO: relation between S and G *)

Proposition substitution_lemma : forall tt G G1 G2 x y Tx Ttt,
  G ≜ G1 ∘ (ctx.append G2 y Tx) ->
  ctx.append G1 x Tx |- tt | Ttt ->
  qun 〔G2〕 ->
  G |- (rpi tt x y) | Ttt.
Proof. 
Admitted.

Proposition context_store_bool : forall S G Q x vi,
  G |- tmvar x | ty_bool Q ->
  contains S x vi ->
  exists (bi : b), vi = pvbool bi Q.
Proof.
  Admitted.

(* TODO: try doing the induction on the typing *)
Lemma progress' : forall S t,
  prty' S t -> (exists S' t', ssse S t S' t') \/ (exists x, t = tmvar x /\ in' S x).
Proof.
  intros S t. generalize dependent S. induction t.
  - intros. right. exists i. apply prty'_in' in H. split. reflexivity. apply H.
  - intros. left. eexists. eexists. apply SSSE_Bool. reflexivity.
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
    assert (Hstty : stty' S G). { apply H0. }
    apply subsemantic with (G1 := G1) (G2 := G2) in H0; try apply H11. inversion H0 as [S1 HS1].
    inversion HS1 as [HS1l HS1r]. inversion HS1r as [S2 HS1r'].
    apply T_Prog' with (t := t1) (ti := T1) in HS1l; try apply H5. apply IHt1 in HS1l.
    inversion HS1l.
    + inversion H2 as [S1' H2']. inversion H2' as [t1' H2''].
      exists (S1' ∪ S2). exists (tmpair q t1' t2). eapply SSSE_Pair_Eval_Fst.
      apply ssse_weakening with (S := S) (S2 := S2) in H2''; try apply HS1r'. apply H2''.
    + inversion H2 as [x H2']. inversion H2' as [H2'l H2'r]. subst t1.
      inversion H2'r. subst S0 x0. apply dt.split_comm in H11. 
      apply subsemantic with (G1 := G2) (G2 := G1) in Hstty; try apply H11.
      inversion Hstty as [Sx2 HSx2]. inversion HSx2 as [HSx2l HSx2r]. 
      inversion HSx2r as [Sx1 HSx2r']. eapply T_Prog' in HSx2l; try apply H6.
      apply IHt2 in HSx2l. inversion HSx2l.
      * inversion H4 as [Sx2' H4']. inversion H4' as [t2' H4'']. 
        exists (Sx2' ∪ Sx1). exists (tmpair q (tmvar x) t2'). eapply SSSE_Pair_Eval_Snd.
        apply ssse_weakening with (S := S) (S2 := Sx1) in H4''; try apply HSx2r'. apply H4''.
      * inversion H4 as [y H4']. inversion H4' as [H4'l H4'r]. subst t2.
        exists (append S (alloc S) (pvpair x y q)). exists (tmvar (alloc S)). apply SSSE_Pair. 
        reflexivity.
  - intros. left. inversion H; subst. remember H0 as H0'. clear HeqH0'. inversion H1; subst.
    apply subsemantic with (G1 := G1) (G2 := G2) in H0; try apply H10. inversion H0 as [S1 HS1].
    inversion HS1 as [HS1l HS1r]. inversion HS1r as [S2 HS1r'].
    apply T_Prog' with (t := t1) (ti := (T1 ** T2) Q) in HS1l; try apply H8. apply IHt1 in HS1l.
    inversion HS1l.
    + inversion H2 as [S1' H2']. inversion H2' as [t1' H2''].
      exists (S1' ∪ S2). exists (tmsplit t1' i i0 t2). eapply SSSE_Split_Eval.
      apply ssse_weakening with (S := S) (S2 := S2) in H2''; try apply HS1r'. apply H2''.
    + inversion H2 as [x H2']. inversion H2' as [H2'l H2'r]. subst t1.
      inversion H8. subst x0 T0.
      assert (Hval: exists y', exists z', sval S1 x (pvpair y' z' Q)). { admit. }
      inversion Hval as [y' Hval']. inversion Hval' as [z' Hval''].
      apply sval_weakening with (S := S) (S2 := S2) in Hval''; try apply HS1r'.
      remember H2'r as H2'rr. clear HeqH2'rr. eapply in'_weakening in H2'rr; try apply HS1r'.
      apply scer'_ex with (Q := Q) in H2'rr. inversion H2'rr as [S' H2'rr'].
      eapply SSSE_Split in Hval''; try apply H2'rr'.
      exists S'. exists (rpi (rpi t2 i y') i0 z'). apply Hval''.
    - admit.
    - admit.
Qed.

Lemma preservation : forall S t S' t',
  prty S t ->
  ssse S t S' t' ->
  prty S' t'.
Proof.
  intros S t S' t' H H'. generalize dependent H. induction H'; intros HH; inversion HH; subst.
  - eapply T_Prog.
    + destruct Q.
      * eapply T_NextlinS. Focus 3. simpl. apply H1. Focus 2. apply H0. apply dt.split_id_r.
      * eapply T_NextunS. Focus 3. simpl. apply H1. Focus 2. apply H0. apply dt.split_id_r.
    + assert (X : forall G, ctx.append G (alloc S) ti = M.mult (ctx.append G (alloc S) ti) ctx.empty).
      { intros. rewrite -> M.id_r. reflexivity. }
      rewrite -> X. eapply dt.T_Var. rewrite -> M.id_r. apply dt.q_rel''_unr.
  - inversion H0. subst. assert (X : stty S G1). { admit. }
    eapply T_Prog in X. Focus 2. apply H4. apply IHH' in X. inversion X. subst.
    eapply T_Prog. apply H1. eapply dt.T_If. Focus 2. apply H6. Focus 2. apply H8.
    inversion H2. subst T0. subst x0.
Qed.


End OperationalSemantics.