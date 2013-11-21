Add Rec LoadPath "/Users/jebe/git/Charge/Charge!/bin".
Add Rec LoadPath "/Users/jebe/git/mirror-core/src/" as MirrorCore.

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

  (** TODO : move to bil **)
  

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

(*
  Instance pure_limpl x y : pure x -> pure y ->  pure (x -->> y).
  Proof.
    intros. eapply pure_axiom.
    constructor.
    { 
*)
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

End Pure.

(*
Section EmbedPropPure.

  Context {A : Type} `{HIL: ILogic A} {HPropOp: EmbedOp Prop A} {HProp: Embed Prop A}.
  Context {BILOPA : BILOperators A} {BILA : BILogic A}.

  Instance EmbedPropPureOp : PureOp := {
     pure := fun P => exists p, P -|- embed p
  }.

  Instance EmbedPropPure : @Pure A _ _ EmbedPropPureOp.
  Proof.
    split; intros.
    + destruct H as [p H].
      rewrite H.
      etransitivity; [rewrite embedPropExists|rewrite <- (embedPropExistsL p empSP)];
      [reflexivity|].
      lexistsL Hp. rewrite sepSPC, <- bilexistsscL.
      lexistsR Hp. rewrite empSPR. apply landL2. reflexivity.
    + destruct H as [p H], H0 as [q H0].
      rewrite H, H0; apply landR.
      * rewrite <- embedPropExists', sepSPC, bilexistsscR.
        lexistsL Hp; lexistsR Hp; apply ltrueR.
      * do 2 rewrite <- embedPropExists'. rewrite bilexistsscR.
        lexistsL Hp; lexistsR Hp; apply ltrueR.
    + destruct H as [p H]; rewrite H, <- embedPropExists'; split.
      * apply landR.
        - apply wandSepSPAdj. apply landL1.
          lexistsL Hp. apply wandSepSPAdj.
          lexistsR Hp. apply ltrueR.
        - apply bilsep. apply landL2. reflexivity.
      * rewrite landexistsDL; lexistsL Hp.
        apply landL2. apply bilsep. apply landR; [|reflexivity].
        lexistsR Hp. apply ltrueR.
    + destruct H as [p H].
      rewrite H.
      rewrite <- embedPropExists', siexistsE.
      apply limplAdj. rewrite landC, landexistsDL.
      lexistsL Hp. apply landL2. lforallL Hp.
      transitivity ((ltrue -* Q) ** empSP); [apply empSPR|].
      apply wandSPL; [apply ltrueR | reflexivity].
    + destruct H as [p H]; rewrite H.
      apply wandSepSPAdj. rewrite <- embedPropExists', bilexistsscR.
      lexistsL Hp. apply wandSepSPAdj.
      rewrite limplexistsE. lforallL Hp.
      transitivity ((ltrue -->> Q) //\\ ltrue); [apply landR; [reflexivity | apply ltrueR]|].
      apply limplL; [apply ltrueR|apply landL1].
      destruct H0 as [q H0]; rewrite H0.
      rewrite <- embedPropExists'.
      lexistsL Hq. apply wandSepSPAdj. lexistsR Hq. apply ltrueR.
  Qed.

  Lemma pureEmbedProp (p : Prop) : pure (embed p).
  Proof.
    unfold pure; simpl.
    exists p; reflexivity.
  Qed.
  
End EmbedPropPure.
*)

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