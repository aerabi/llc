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

(* Top-Level Evaluation *)
Inductive tlsemev : T -> tm -> T -> tm -> Prop :=
  | E_Ctxt : forall S S' E t t',
    semev S t S' t' ->
    tlsemev S (eceval E t) S' (eceval E t').

(* Store Typing *)
Notation "G '≜' G1 '∘' G2" := (dt.split' G G1 G2) (at level 20, left associativity).
Notation "G '|-' t '|' T" := (dt.ctx_ty G t T) (at level 60).

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

Inductive prty : T -> tm -> Prop :=
  | T_Prog : forall S G t ti,
    stty S G ->
    G |- t | ti ->
    prty S t.

(* Lemmas *)
Lemma preservation : forall S t S' t',
  prty S t ->
  tlsemev S t S' t' ->
  prty S' t'.
Proof.
  intros S t S' t' H H'.  inversion H'. subst S0. subst S'0. generalize dependent t.
  generalize dependent t'. generalize dependent S. generalize dependent S'.
  generalize dependent t0. generalize dependent t'0. induction E;
  intros tt' tt S' S Hsemev ti' HH ti Hprty Htlsemev HH'; simpl.
  - admit.
  - eapply T_Prog.
  Focus 2. eapply T_Prog. inversion H. subst S0. subst t3. inversion H0.
  intros S t S' t' H H'. inversion H; subst. inversion H'. subst S0. subst S. 
  eapply T_Prog with (G := G); try apply H0. subst. induction E. inversion H2. inversion H0.
  - simpl. simpl in H1. subst t0. subst t'0. subst G. subst S'. subst S.
    rewrite -> Tcomm in H5. apply decide_append_empty in H5.
Qed.


End OperationalSemantics.