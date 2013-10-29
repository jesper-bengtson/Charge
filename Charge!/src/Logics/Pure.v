Require Import ILogic ILInsts BILogic BILInsts ILEmbed ILQuantTac.
Require Import Setoid.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Section Pure.

  Context {A : Type} {ILOPs : ILogicOps A} {BILOps : BILOperators A}.

(* This version of Pure will not work for classical separation logics as that 
   requires a negative occurrence of a recursive call for the rule that states that
   P ** Q |-- P //\\ Q (both P and Q must be pure). This is most likely solvable,
   and is true even for non-pure predicates in intuitionistic separation logic,
   but I want to do it in a nice way. *)

  Class Pure (P : A) := {
    pureandscL  : (forall Q, P //\\ Q |-- P ** Q);
    pureandscR  : (forall Q, Q //\\ P |-- Q ** P);
	pureandscD  : (forall Q R, (Q //\\ P) ** R -|- (Q ** R) //\\ P);
    puresiimpl  : (forall Q, P -* Q |-- P -->> Q)
  }.
  
End Pure.

Section EmbedPropPure.

  Context {A : Type} `{HIL: ILogic A} {HPropOp: EmbedOp Prop A} {HProp: Embed Prop A}.
  Context {BILOPA : BILOperators A} {BILA : BILogic A}. 

  Instance EmbedPropPure (P : Prop) : Pure (embed P).
  Proof.
  	split; intros.
  	+ etransitivity; [rewrite embedPropExists |rewrite <- (embedPropExistsL P empSP)];
  		[reflexivity|].
  	  lexistsL Hp. rewrite sepSPC, <- bilexistsscL.
  	  lexistsR Hp. rewrite empSPR. apply landL2. reflexivity.
  	+ etransitivity; [rewrite embedPropExists |rewrite <- (embedPropExistsL P empSP)];
  		[reflexivity|].
  	  lexistsL Hp. rewrite <- bilexistsscL.
  	  lexistsR Hp. rewrite empSPR. apply landL1. reflexivity.
    + split.
      * apply landR.
        - apply bilsep. apply landL1. reflexivity.
        - rewrite <- embedPropExists', landC, landexistsDL, sepSPC, bilexistsscR.
          lexistsL Hp; lexistsR Hp; apply ltrueR.
      * rewrite <- embedPropExists'.
      	lexistsL Hp. apply landL1. apply bilsep. apply landR; 
      	  [reflexivity | lexistsR Hp; apply ltrueR].
	+ apply limplAdj. rewrite <- embedPropExists'.
	  lexistsL Hp. apply landL1.
	  rewrite siexistsE. lforallL Hp.
	  transitivity ((ltrue -* Q) ** empSP); [apply empSPR|].
	  apply wandSPL. apply ltrueR. reflexivity.
  Qed.
  
End EmbedPropPure.

Section PureBILogicFun.
  Context {A : Type} `{ILA: ILogic A}.
  Context {B : Type} `{BILB: BILogic B} {ILB : ILogic B}.
  Context {HEmbOp : EmbedOp A B} {HEmb : Embed A B}.

  Local Existing Instance EmbedILFunDropOp.
  Local Existing Instance EmbedILFunDrop.
  Local Existing Instance ILFun_Ops.
  Local Existing Instance BILFun_Ops.
  Transparent ILFun_Ops.
  Transparent BILFun_Ops.
  
  Instance PureFunDrop {T : Type} (P : A) {H : @Pure B _ _ (embed P)} : 
  	@Pure (T -> B) _ _ (embed P).
  Proof.
  	split.
  	+ intros Q s; simpl; apply pureandscL.
  	+ intros Q s; simpl; apply pureandscR.
  	+ intros Q R; split; intro s; simpl; apply pureandscD. 
  	+ intros Q s; simpl; apply puresiimpl.
  Qed.
  
  Local Existing Instance EmbedILFunOp.

  Instance PureFun {T : Type} (P : (T -> A)) {H : forall x, @Pure B _ _ (embed (P x))} : 
  	@Pure (T -> B) _ _ (embed P).
  Proof.
  	split.
  	+ intros Q s; simpl; apply pureandscL.
  	+ intros Q s; simpl; apply pureandscR.
  	+ intros Q R; split; intro s; simpl; apply pureandscD. 
  	+ intros Q s; simpl; apply puresiimpl.
  Qed.

End PureBILogicFun.

Section PureBILogicPre.

  Context T (ord: relation T) {HPre: PreOrder ord}.
  Context {A : Type} `{ILA: ILogic A}.
  Context {B : Type} `{BILB: BILogic B} {ILB : ILogic B}.
  Context {HEmbOp : EmbedOp A B} {HEmb : Embed A B}.


  Local Existing Instance EmbedILPreDropOpNeq.
  Local Existing Instance ILPre_Ops.
  Local Existing Instance BILPre_Ops.
  Transparent ILPre_Ops.
  Transparent BILPre_Ops.

  Instance PurePreDrop (P : A) {H : @Pure B _ _ (embed P)} : 
  	@Pure (ILPreFrm ord B) _ _ (embed P).
  Proof.
  	split.
  	+ intros Q s; simpl. apply pureandscL.
  	+ intros Q s; simpl; apply pureandscR.
  	+ intros Q R; split; intro s; simpl; apply pureandscD. 
  	+ intros Q s; simpl; lforallR t' Ht; lforallL t' Ht.
  	  apply puresiimpl.
  Qed.
  
  Local Existing Instance EmbedILPreOp.

  Instance PurePre (P : ILPreFrm ord A) {H : forall x, @Pure B _ _ (embed (P x))} : 
  	@Pure (ILPreFrm ord B) _ _ (embed P).
  Proof.
  	split.
  	+ intros Q s; simpl; apply pureandscL.
  	+ intros Q s; simpl; apply pureandscR.
  	+ intros Q R; split; intro s; simpl; apply pureandscD. 
  	+ intros Q s; simpl; lforallR t' Ht; lforallL t' Ht; apply puresiimpl.
  Qed.

End PureBILogicPre.

Check PurePre.