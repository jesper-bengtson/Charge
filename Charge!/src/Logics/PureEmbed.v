Add Rec LoadPath "/Users/jebe/git/Charge/Charge!/bin".
Add Rec LoadPath "/Users/jebe/git/mirror-core/src/" as MirrorCore.

Require Import ILogic ILInsts BILInsts BILogic ILEmbed ILQuantTac.
Require Import Setoid Morphisms Pure.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.


Section EmbedPropPure.

  Context {A : Type} `{HIL: ILogic A} {HPropOp: EmbedOp Prop A} {HProp: Embed Prop A}.
  Context {BILOPA : BILOperators A} {BILA : BILogic A}.
  Context (po : PureOp) (pur : Pure po).

  Instance embed_prop_pure (p : Prop) : pure (embed p).
  Proof.
    eapply pure_axiom; repeat split; intros.
    + etransitivity; [rewrite embedPropExists|rewrite  <- (embedPropExistsL p empSP)];
      [reflexivity|].
      lexistsL Hp. rewrite sepSPC, <- bilexistsscL.
      lexistsR Hp. rewrite empSPR. apply landL2. reflexivity.
    + rewrite <- embedPropExists', sepSPC, bilexistsscR.
      lexistsL Hp; lexistsR Hp. rewrite landC. eapply purescand; auto using pure_ltrue.
    + rewrite <- embedPropExists'. apply landR.
      * apply wandSepSPAdj. apply landL1.
        lexistsL Hp. apply wandSepSPAdj.
        lexistsR Hp. apply ltrueR.
      * apply bilsep. apply landL2. reflexivity.
    + rewrite <- embedPropExists'; rewrite landexistsDL; lexistsL Hp.
      apply landL2. apply bilsep. apply landR; [|reflexivity].
      lexistsR Hp. apply ltrueR.
    + rewrite <- embedPropExists', siexistsE.
      apply limplAdj. rewrite landC, landexistsDL.
      lexistsL Hp. apply landL2. lforallL Hp.
      transitivity ((ltrue -* Q) ** empSP); [apply empSPR|].
      apply wandSPL; [apply ltrueR | reflexivity].
    + apply wandSepSPAdj. rewrite <- embedPropExists', bilexistsscR.
      lexistsL Hp. apply wandSepSPAdj.
      rewrite limplexistsE. lforallL Hp.
      transitivity ((ltrue -->> Q) //\\ ltrue); [apply landR; [reflexivity | apply ltrueR]|].
      apply limplL; [apply ltrueR|apply landL1].
      rewrite <- pureimplsi; auto using pure_ltrue.
      apply limplAdj. apply landL1; reflexivity. assumption.
  Qed.
  
End EmbedPropPure.

Section PureBILogicFun.
  Context {A : Type} `{ILA: ILogic A}.
  Context {B : Type} `{BILB: BILogic B} {ILB : ILogic B}.
  Context {HEmbOp : EmbedOp A B} {HEmb : Embed A B}.
  Context (poB : PureOp) (prB : Pure poB) {prE : forall a : A, pure (embed a)}.

  Local Existing Instance ILFun_Ops.
  Local Existing Instance BILFun_Ops.
  Transparent ILFun_Ops.
  Transparent BILFun_Ops.
  Transparent EmbedILFunDropOp.
  Transparent EmbedILFunOp.

  Local Existing Instance EmbedILFunDropOp.
  Local Existing Instance EmbedILFunDrop.
  Local Existing Instance PureBILFunOp.
  Local Existing Instance PureBILFun.
  Local Existing Instance EmbedILFunOp.

  Instance PureEmbedFunDrop {T : Type} (p : A) : 
    pure (@embed A (T -> B) _ p).
  Proof.
    eapply pure_axiom. 
    unfold parameter_pure; repeat split; intros; intros t; simpl;
    apply prB; try apply prE; apply H.
  Qed.

  Instance PureEmbedFun {T : Type} (p : (T -> A)) : 
    pure (@embed (T -> A) (T -> B) _ p).
  Proof.
    eapply pure_axiom. 
    unfold parameter_pure; repeat split; intros; intros t; simpl;
    apply prB; try apply prE; apply H.
  Qed.

End PureBILogicFun.

Section PureBILogicPre.

  Context T (ord: relation T) {HPre: PreOrder ord}.
  Context {A : Type} `{ILA: ILogic A}.
  Context {B : Type} `{BILB: BILogic B} {ILB : ILogic B}.
  Context {HEmbOp : EmbedOp A B} {HEmb : Embed A B}.
  Context (poB : PureOp) (prB : Pure poB) {prE : forall a : A, pure (embed a)}.

  Local Existing Instance EmbedILPreDropOpNeq.
  Local Existing Instance ILPre_Ops.
  Local Existing Instance BILPre_Ops.
  Local Existing Instance PureBILPreOp.
  Local Existing Instance PureBILPre.
  Local Existing Instance EmbedILPreOp.

  Transparent ILPre_Ops.
  Transparent BILPre_Ops.
  Transparent EmbedILPreDropOpNeq.
  Transparent EmbedILPreOp.

  Instance PureEmbedPreDrop {T : Type} (p : A) : 
    pure (@embed A (ILPreFrm ord B) _ p).
  Proof.
    eapply pure_axiom. 
    unfold parameter_pure; repeat split; intros; intros t; simpl.
    + apply prB; apply prE.
    + apply prB; [apply prE | apply H].
    + apply prB; apply prE.
    + apply prB; apply prE.
    + apply lforallR; intro t'; apply lforallR; intro Ht.
      apply lforallL with t'; apply lforallL with Ht.
      apply prB; apply prE.
    + apply lforallR; intro t'; apply lforallR; intro Ht.
      apply lforallL with t'; apply lforallL with Ht.
      apply prB; [apply prE | apply H].
  Qed.

  Instance PureEmbedPre {T : Type} (p : (ILPreFrm ord A)) : 
    pure (@embed (ILPreFrm ord A) (ILPreFrm ord B) _ p).
  Proof.
    eapply pure_axiom. 
    unfold parameter_pure; repeat split; intros; intros t; simpl.
    + apply prB; apply prE.
    + apply prB; [apply prE | apply H].
    + apply prB; apply prE.
    + apply prB; apply prE.
    + apply lforallR; intro t'; apply lforallR; intro Ht.
      apply lforallL with t'; apply lforallL with Ht.
      apply prB; apply prE.
    + apply lforallR; intro t'; apply lforallR; intro Ht.
      apply lforallL with t'; apply lforallL with Ht.
      apply prB; [apply prE | apply H].
  Qed.

End PureBILogicPre.
