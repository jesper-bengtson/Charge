Require Import RelationClasses Setoid Morphisms.
Require Import ILogic ILEmbed ILQuantTac.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Section ILogic_Pre.
  Context T (ord: relation T) {HPre : PreOrder ord}.
  Context {A : Type} `{IL: ILogic A}.

  Record ILPreFrm := mkILPreFrm {
    ILPreFrm_pred :> T -> A;
    ILPreFrm_closed: forall t t': T, ord t t' ->
      ILPreFrm_pred t |-- ILPreFrm_pred t'
  }.

  Notation "'mk'" := @mkILPreFrm.

  Global Instance ILPreFrm_m (P: ILPreFrm): Proper (ord ++> lentails) P.
  Proof.
    intros t t' Ht. apply ILPreFrm_closed; assumption.
  Qed.

  Local Obligation Tactic :=
    repeat match goal with
    | |- ord _ _ -> _ => intros Hord; try setoid_rewrite Hord; reflexivity
    | |- _ => intro
    end.

  Program Definition ILPre_Ops : ILogicOps ILPreFrm := {|
    lentails P Q := forall t:T, P t |-- Q t;
    ltrue        := mk (fun t => ltrue) _;
    lfalse       := mk (fun t => lfalse) _;
    limpl    P Q := mk (fun t => Forall t', Forall Ht' : ord t t', P t' -->> Q t') _;
    land     P Q := mk (fun t => P t //\\ Q t) _;
    lor      P Q := mk (fun t => P t \\// Q t) _;
    lforall  A P := mk (fun t => Forall a, P a t) _;
    lexists  A P := mk (fun t => Exists a, P a t) _
  |}. 
  Next Obligation.
    lforallR t'' Ht'. lforallL t''.
    assert (ord t t'') as Ht'' by (transitivity t'; assumption).
    lforallL Ht''; reflexivity.
  Qed.

  Local Existing Instance ILPre_Ops.

  Program Definition ILPre_ILogic : ILogic ILPreFrm.
  Proof.
    split; unfold lentails; simpl; intros.
    - split; red; [reflexivity|].
      intros P Q R HPQ HQR t. 
      transitivity (Q t); [apply HPQ | apply HQR].
    - apply ltrueR.
    - apply lfalseL.
    - lforallL x; apply H. 
    - lforallR x; apply H. 
    - lexistsL x; apply H. 
    - lexistsR x; apply H. 
    - apply landL1; eapply H; assumption.
    - apply landL2; eapply H; assumption.
    - apply lorR1; eapply H; assumption.
    - apply lorR2; eapply H; assumption.
    - apply landR; [eapply H | eapply H0]; assumption.
    - apply lorL; [eapply H | eapply H0]; assumption.
    - apply landAdj.
      etransitivity; [apply H|]. apply lforallL with t.
      apply lforallL; reflexivity.
    - lforallR t' Hord. apply limplAdj.
      rewrite ->Hord; eapply H; assumption.
  Qed.

  Global Instance ILPreFrm_pred_m {H : PreOrder ord}:
    Proper (lentails ++> ord ++> lentails) ILPreFrm_pred.
  Proof.
    intros P P' HPt t t' Ht. rewrite ->Ht. apply HPt.
  Qed.

  Global Instance ILPreFrm_pred_equiv_m:
    Equivalence ord ->
    Proper (lequiv ++> ord ++> lequiv) ILPreFrm_pred.
  Proof.
    intros Hord P P' HPt t t' Ht. split.
    - rewrite ->Ht. apply HPt. 
    - symmetry in Ht. rewrite <-Ht. apply HPt. 
  Qed.

  Program Definition ILPreAtom {HPre : PreOrder ord} (t: T) :=
    mk (fun t' => Exists x : ord t t', ltrue) _.
  Next Obligation.
    lexistsL H1.
    apply lexistsR; [transitivity t0; assumption | apply ltrueR].
  Qed.

  Lemma ILPreFrm_fold_entails x y P Q (Hord : ord x y) (H : P |-- Q) :
    P x |-- Q y.
  Proof.
    etransitivity.
    apply ILPreFrm_closed.
    eassumption.
    apply H.
  Qed.
                                  
End ILogic_Pre.

Implicit Arguments ILPreFrm [[T] [ILOps]].
Implicit Arguments mkILPreFrm [[T] [ord] [A] [ILOps]].


Section Embed_ILogic_Pre.
  Context T (ord: relation T) {HPre : PreOrder ord}.
  Context {A : Type} `{ILA: ILogic A}.
  Context {B : Type} `{ILB: ILogic B}.
  Context {HEmbOp : EmbedOp A B} {HEmb : Embed A B}.

  Program Instance EmbedILPreDropOp : EmbedOp A (ILPreFrm ord B) := {
     embed := fun a => mkILPreFrm (fun x => embed a) _
  }.

  Local Existing Instance ILPre_Ops.

  Instance EmbedILPreDrop : Embed A (ILPreFrm ord B).
  Proof.
    split; intros.
    + simpl; intros. apply embed_sound; assumption.
    + split; intros t; simpl; apply embedlforall.
    + split; intros t; simpl; apply embedlexists.
    + split; intros t; simpl. 
      * lforallL t. apply lforallL; [reflexivity | apply embedImpl].
      * lforallR x H. apply embedImpl.
  Qed.
        
  Program Instance EmbedILPreOp : EmbedOp (ILPreFrm ord A) (ILPreFrm ord B) := {
     embed := fun a => mkILPreFrm (fun x => embed (a x)) _
  }.
  Next Obligation.
    intros.
    apply embed_sound.
    rewrite H; reflexivity.
  Qed.

  Instance EmbedILPre : Embed (ILPreFrm ord A) (ILPreFrm ord B).
  Proof.
    split; intros.
    + simpl; intros. apply embed_sound; apply H.
    + split; intros t; simpl; apply embedlforall.
    + split; intros t; simpl; apply embedlexists.
    + split; intros t; simpl;
      do 2 setoid_rewrite <- embedlforall; 
      lforallR t' H; lforallL t' H; apply embedImpl.
  Qed.
        


End Embed_ILogic_Pre.

(** If [Frm] is a ILogic, then the function space [T -> Frm] is also an ilogic,
    for any type [T]. All connectives are just pointwise liftings. *)

Section ILogic_Fun.
  Context (T: Type).
  Context {A : Type} `{IL: ILogic A}.

  Program Definition ILFun_Ops : ILogicOps (T -> A) := {|
    lentails P Q := forall t:T, P t |-- Q t;
    ltrue        := fun t => ltrue;
    lfalse       := fun t => lfalse;
    limpl    P Q := fun t => P t -->> Q t;
    land     P Q := fun t => P t //\\ Q t;
    lor      P Q := fun t => P t \\// Q t;
    lforall  A P := fun t => Forall a, P a t;
    lexists  A P := fun t => Exists a, P a t
  |}.
  
  Local Existing Instance ILFun_Ops.

  Program Definition ILFun_ILogic : ILogic (T -> A). 
  Proof.
    split; unfold lentails; simpl; intros.
    - split; red; [reflexivity|].
      intros P Q R HPQ HQR t. transitivity (Q t); [apply HPQ | apply HQR].
    - apply ltrueR.
    - apply lfalseL.
    - apply lforallL with x; apply H.
    - apply lforallR; intros; apply H.
    - apply lexistsL; intros; apply H.
    - apply lexistsR with x; apply H.
    - apply landL1; intuition.
    - apply landL2; intuition.
    - apply lorR1; intuition.
    - apply lorR2; intuition.
    - apply landR; intuition.
    - apply lorL; intuition.
    - apply landAdj; intuition.
    - apply limplAdj; intuition.
  Qed.

  Lemma ILFun_fold_entails x P Q (H : P |-- Q) :
    P x |-- Q x.
  Proof.
    apply H.
  Qed.

End ILogic_Fun.



Section Embed_ILogic_Fun.
  Context {A : Type} `{ILA: ILogic A}.
  Context {B : Type} `{ILB: ILogic B}.
  Context {HEmbOp : EmbedOp A B} {HEmb : Embed A B}.

  Program Instance EmbedILFunDropOp {T} : EmbedOp A (T -> B) := {
     embed := fun a t => embed a
  }.

  Local Existing Instance ILFun_Ops.

  Instance EmbedILFunDrop {T} : Embed A (T -> B).
  Proof.
    split; intros.
    + simpl; intros. apply embed_sound; assumption.
    + split; intros t; simpl; apply embedlforall.
    + split; intros t; simpl; apply embedlexists.
    + split; intros t; simpl; apply embedImpl.
  Qed.
        
  Program Instance EmbedILFunOp {T} : EmbedOp (T -> A) (T -> B) := {
     embed := fun a x => embed (a x)
  }.

  Instance EmbedILFun {T} : Embed (T -> A) (T -> B).
  Proof.
    split; intros.
    + simpl; intros. apply embed_sound; apply H.
    + split; intros t; simpl; apply embedlforall.
    + split; intros t; simpl; apply embedlexists.
    + split; intros t; simpl; apply embedImpl.
  Qed.
        


End Embed_ILogic_Fun.

(* Coq tends to unfold lentails on [simpl], which triggers unfolding of
   several other connectives. When that happens, the goal can become quite
   unreadable. The workaround is to make the definition of entailment and
   connectives opaque. If a module wants to unfold those definitions, it should
   do [Transparent IL?_Ops], where ? is Pre or Fun. *)

Global Opaque ILPre_Ops.
Global Opaque EmbedILPreDropOp.
Global Opaque EmbedILPreOp.

Global Opaque ILFun_Ops.
Global Opaque EmbedILFunDropOp.
Global Opaque EmbedILFunOp.