Add Rec LoadPath "/Users/jebe/git/Charge/Charge!/bin".
Add Rec LoadPath "/Users/jebe/git/mirror-core/src/" as MirrorCore.

Require Import ILogic ILInsts BILogic ILEmbed ILQuantTac.
Require Import Setoid Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Section Pure.

  Context {A : Type} {ILOPs : ILogicOps A} {BILOps : BILOperators A}.

  Class PureOp := {
    pure : A -> Prop
  }.

  Definition parameter_pure (pure : A -> Prop) (P : A) : Prop :=
    (forall Q, P //\\ Q |-- P ** Q) /\
    (forall  Q, pure Q -> P ** Q |-- P //\\ Q) /\
    (forall Q R, (P //\\ Q) ** R -|- P //\\ (Q ** R)) /\
    (forall Q, P -* Q |-- P -->> Q) /\
    (forall Q, pure Q -> P -->> Q |-- P -* Q).

  Class Pure {HP : PureOp} := {
    pure_axiom : forall p, pure p <-> parameter_pure pure p
  }.

  Existing Class pure.

  Context (IL : ILogic A) (BIL : BILogic A) (po : PureOp) (p : @Pure po).

  Lemma pureandsc P Q : pure P -> P //\\ Q |-- P ** Q.
  Proof.
    intros. eapply pure_axiom in H. destruct H. intuition.
  Qed.

  Lemma purescand  P Q : pure P -> pure Q -> P ** Q |-- P //\\ Q.
  Proof.
    intros. eapply pure_axiom in H. destruct H. intuition.
  Qed.

  Lemma pureandscD P Q R : pure P -> (P //\\ Q) ** R -|- P //\\ (Q ** R).
  Proof.
    intros. eapply pure_axiom in H; destruct H; intuition.
  Qed.

  Lemma puresiimpl P Q : pure P -> P -* Q |-- P -->> Q.
  Proof.
    intros. eapply pure_axiom in H; destruct H; intuition.
  Qed.

  Lemma pureimplsi P Q : pure P -> pure Q -> P -->> Q |-- P -* Q.
  Proof.
    intros. eapply pure_axiom in H; destruct H; intuition.
  Qed.

  Global Instance Proper_pure_lequiv : Proper (lequiv ==> iff)%signature pure.
  Proof.
    red. red. intros.
    do 2 rewrite pure_axiom.
    unfold parameter_pure.
    setoid_rewrite H. reflexivity.
  Qed.

  Instance pure_ltrue : pure ltrue.
  Proof.
    eapply pure_axiom.
    repeat constructor.
    { intros. rewrite <- (empSPL (ltrue //\\ Q)).
      etransitivity. 2: eapply bilsep.
      rewrite sepSPC. erewrite (sepSPC _ Q). eapply bilsep.
      eapply landL2. reflexivity. eapply ltrueR. }
    { intros.
      rewrite sepSPC.
      rewrite <- (landtrueR Q) at 1.
      rewrite pureandscD by auto.
      eapply landR. eapply ltrueR. eapply landL1. reflexivity. }
    { eapply landR. eapply ltrueR.
      eapply bilsep. eapply landL2. reflexivity. }
    { eapply landL2. eapply bilsep. eapply landR. eapply ltrueR. reflexivity. }
    { intros. eapply limplAdj. eapply landL1.
      rewrite septrue. eapply wandSPL; auto. }
    { intros. eapply wandSepSPAdj.
      rewrite limplTrue.
      rewrite <- (landtrueR Q) at 1.
      rewrite pureandscD; auto. apply landL1. reflexivity. }
  Qed.

  Instance pure_land x y : pure x -> pure y ->  pure (x //\\ y).
  Proof.
    intros.
    eapply pure_axiom.
    constructor.
    { intros. rewrite landA.
      rewrite pureandscD; auto.
      apply landR. apply landL1. reflexivity.
      apply landL2. apply pureandsc; auto. }
    constructor.
    { intros.
      rewrite pureandscD by auto.
      rewrite landA. apply landR. apply landL1. reflexivity.
      apply landL2. apply purescand; auto. }
    constructor.
    { intros.
      rewrite landA. rewrite pureandscD by auto.
      rewrite landA. rewrite pureandscD by auto.
      reflexivity. }
    constructor.
    { intros.
      eapply limplAdj. rewrite landC.
      rewrite landA.
      rewrite pureandsc by auto.
      rewrite pureandsc by auto.
      rewrite <- sepSPA.
      rewrite (@purescand x y) by auto.
      rewrite sepSPC. apply wandSPL; reflexivity. }
    { intros.
      rewrite landC at 1.
      rewrite curry.
      rewrite pureandsc by auto.
      rewrite wand_curry.
      eapply wandSPAdj.
      rewrite <- pureimplsi by auto.
      apply limplAdj.
      rewrite landC.
      rewrite <- pureandscD by auto.
      eapply sepSPAdj.
      rewrite landC.
      eapply limplL. reflexivity.
      apply landL1.
      eapply pureimplsi; auto. }
  Qed.

  Instance pure_sc x y (Hx : pure x) (Hy : pure y) : pure (x ** y).
  Proof.
    eapply pure_axiom; repeat split; intros.
    + rewrite sepSPA. 
      do 2 (etransitivity; [|rewrite <- pureandsc; eauto]).
      rewrite purescand by auto. apply landA.
    + etransitivity; [|rewrite <- pureandsc; eauto].
      rewrite landA. rewrite <- purescand by auto using pure_land.
      rewrite <- purescand by auto.
      apply sepSPA.
    + etransitivity; [rewrite (purescand Hx Hy); reflexivity|].
      etransitivity; [|rewrite <- pureandsc by auto; reflexivity].
      rewrite <- pureandscD by eauto using pure_land. reflexivity.
    + etransitivity; [|rewrite <- (@pureandsc x y) by auto; reflexivity].
      rewrite purescand by auto.
      rewrite pureandscD by auto using pure_land; reflexivity.
    + etransitivity; [|rewrite purescand by auto; reflexivity].
      etransitivity; [rewrite <- pureandsc by auto; reflexivity|].
      rewrite puresiimpl by auto using pure_land; reflexivity.
    + etransitivity; [|rewrite purescand by auto; reflexivity].
      etransitivity; [rewrite <- pureandsc by auto; reflexivity|].
      rewrite pureimplsi by auto using pure_land; reflexivity.
  Qed.

(*

  Instance pure_limpl x y (Hx : pure x) (Hy : pure y) : pure (x -->> y).

  Instance pure_lor x y : pure x -> pure y ->  pure (x \\// y).
*)


End Pure.

Implicit Arguments Pure [[A] [ILOPs] [BILOps]].

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


(*
Section PureBILogicFun.
  Context {A : Type} `{ILA: ILogic A}.
  Context {B : Type} `{BILB: BILogic B} {ILB : ILogic B}.
  Context {HEmbOp : EmbedOp A B} {HEmb : Embed A B}.

  Local Existing Instance ILFun_Ops.
  Local Existing Instance BILFun_Ops.
  Transparent ILFun_Ops.
  Transparent BILFun_Ops.

  Instance PureFunOp {T : Type} {H : @PureOp B} : @PureOp (T -> B) := {
    pure := fun f => forall x, pure (f x)
  }.
  
  Instance PureFunDrop {T : Type} {HOp : @PureOp B} {H : @Pure B _ _ _} : 
  	@Pure (T -> B) _ _ (@PureFunOp T HOp).
  Proof.
    split; intros.
    + intros s; simpl; apply pureandsc; apply H0.
    + intros s; simpl; apply purescand; [apply H0 | apply H1].
    + split; intros s; simpl; apply pureandscD; apply H0.
    + intros s; simpl; apply puresiimpl; apply H0.
    + intros s; simpl; apply pureimplsi; [apply H0 | apply H1].
  Qed.

  Local Existing Instance EmbedILFunDropOp.
  Local Existing Instance EmbedILFunDrop.
Set Printing All.
Check embed.
  Lemma pure_fun_drop {T : Type} (P : B) {HOp : @PureOp B} 
        (f : T -> A) (H : @pure (T -> B) (@PureFunOp T HOp) (@embed f)) : True.
  Proof.
    unfold pure; simpl. apply H.
  Qed.

  
  Local Existing Instance EmbedILFunOp.

  Instance PureFunOp {T : Type} (P : T -> A) {H : @PureOp B} : @PureOp (T -> B) := {
    pure := fun f => forall x, pure (f x)
  }.

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
*)