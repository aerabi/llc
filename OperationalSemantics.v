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
Parameter scer : q -> T -> id -> T.
Parameter scer_lin : forall S1 S2 x V, 
  scer qlin ((append S1 x V) ∪ S2) x = S1 ∪ S2.
Parameter scer_un : forall S x, scer qun S x = S.

Example test_scer_1 : forall S x v, scer qlin (append S x v) x = S.
Proof.
  intros. assert ( H : (append S x v) ∪ Ø = (append S x v) ). { apply M.id_r. }
  rewrite <- H. rewrite <- M.id_r. apply scer_lin.
Qed.

(* Small-Step Evaluation *)
Inductive semev : T -> tm -> T -> tm -> Prop :=
  | E_Bool : forall S x Q (B : b),
    semev S (tmbool Q B) (append S x (pvbool B Q)) (tmvar x)
  | E_If_T : forall S x Q t1 t2,
    sval S x (pvbool btrue Q) ->
    semev S (tmif (tmvar x) t1 t2) (scer Q S x) t1
  | E_If_F : forall S x Q t1 t2,
    sval S x (pvbool bfalse Q) ->
    semev S (tmif (tmvar x) t1 t2) (scer Q S x) t2.

(* Top-Level Evaluation *)
Inductive tlsemev : T -> tm -> T -> tm -> Prop :=
  | E_Ctxt : forall S E t t',
    semev S t S t' ->
    tlsemev S (eceval E t) S (eceval E t').

(* Store Typing *)
Notation "G1 '⊔' G2" := (dt.split G1 G2) (at level 20, left associativity).
Notation "G '|-' t '|' T" := (dt.ctx_ty G t T) (at level 60).

Inductive stty : T -> ctx.T -> Prop :=
  | T_EmptyS : stty empty ctx.empty
  | T_NextlinS : forall S G1 G2 (w : pv) ti x,
    stty S (G1 ⊔ G2) ->
    G1 |- tmv (w qlin) | ti ->
    stty (append S x (w qlin)) (ctx.append G2 x ti)
  | T_NextunS : forall S G1 G2 (w : pv) ti x,
    stty S (G1 ⊔ G2) ->
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

Qed.


End OperationalSemantics.