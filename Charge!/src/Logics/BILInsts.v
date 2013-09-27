Require Import Setoid Morphisms RelationClasses Program.Basics. 
Require Import ILogic BILogic ILQuantTac ILInsts.
Require Import Equiv SepAlg.

Set Implicit Arguments.
Unset Strict Implicit.

Section BISepAlg.
  Context {A} `{sa : SepAlg A}.
  Context {B} `{IL: ILogic B}.
  Context {HPre : PreOrder (@equiv A _)}.

  Open Scope sa_scope.

  Program Instance SABIOps: BILOperators (ILPreFrm equiv B) := {
    empSP := mkILPreFrm (fun x => Exists a : (sa_unit x), ltrue) _;
    sepSP P Q :=  mkILPreFrm (fun x => Exists x1, Exists x2, Exists H : sa_mul x1 x2 x,
                                                P x1 //\\ Q x2) _;
    wandSP P Q := mkILPreFrm (fun x => Forall x1, Forall x2, Forall H : sa_mul x x1 x2,  
                                                 P x1 -->> Q x2) _
  }.
  Next Obligation.
  	lexistsL H1. eapply lexistsR. rewrite <- H. assumption. apply ltrueR.
  Qed.
  Next Obligation.
  	lexistsL a b Hab.
  	lexistsR a b. eapply lexistsR. eapply sa_mul_monR; eassumption. reflexivity.
  Qed.
  Next Obligation.
	lforallR a b Hab.
	lforallL a b. apply lforallL. eapply sa_mul_mon; [symmetry|]; eassumption.
	reflexivity.
  Qed.

  Local Existing Instance ILPre_Ops.
  Local Existing Instance ILPre_ILogic.
  Local Transparent ILPre_Ops.

  Definition SABILogic : BILogic (ILPreFrm equiv B).
  Proof.
    split.
    + apply _.
    + intros P Q x; simpl.
      lexistsL x1 x2 H'; apply sa_mulC in H'.
      lexistsR x2 x1 H'; apply landC.
    + intros P Q R x; simpl.
      lexistsL x1 x2 Hx x3. lexistsL x4 Hx1.
      destruct (sa_mulA Hx1 Hx) as [x5 [Hx2 Hx5]].
      lexistsR x3 x5 Hx5 x4. lexistsR x2 Hx2.
      apply landA.
    + intros P Q R; split; intros H x; simpl.
      - lforallR x1 x2 Hx1.
        apply limplAdj.
        specialize (H x2); simpl in H.
        rewrite <- H.
        lexistsR x x1 Hx1. reflexivity.
      - lexistsL x1 x2 Hx.
        specialize (H x1); simpl in H.
        setoid_rewrite H.
        lforallL x2 x Hx.
        apply landAdj. reflexivity.
    + intros P Q R H x; simpl.
      lexistsL x1 x2 Hx.
      lexistsR x1 x2 Hx.      
      rewrite H. reflexivity.
    + intros P; split; intros x; simpl.
      - lexistsL x1 x2 Hx H2.
        apply landL1.
        apply sa_unit_eq in Hx. rewrite <- Hx. reflexivity. assumption.
      - destruct (sa_unit_ex x) as [u [H1 H2]].
        lexistsR x u H2 H1. 
        apply landR; [reflexivity| apply ltrueR].
  Qed.

End BISepAlg.

Global Opaque SABIOps.

Section BILPre.
  Context T (ord: relation T) {HPre: PreOrder ord}.
  Context {A : Type} `{HBI: BILogic A}.
  Context {HIL : ILogic A}.

  Program Definition BILPre_Ops : BILOperators (ILPreFrm ord A) := {|
    empSP      := mkILPreFrm (fun t => empSP) _;
    sepSP  P Q := mkILPreFrm (fun t => P t ** Q t) _;
    wandSP P Q := mkILPreFrm (fun t => Forall t', Forall H : ord t t', P t' -* Q t') _
  |}.
  Next Obligation.
    intros; rewrite H; reflexivity.
  Qed.
  Next Obligation.
    intros.
    lforallR x Hx. rewrite <- H in Hx.
    lforallL x Hx; reflexivity.
  Qed.

  Local Existing Instance ILPre_Ops.
  Local Existing Instance ILPre_ILogic.
  Local Existing Instance BILPre_Ops.

  Local Transparent ILPre_Ops.

  Definition BILPreLogic : BILogic (ILPreFrm ord A).
  Proof.
    split.
    + apply _.
    + intros P Q x; simpl; apply sepSPC.
    + intros P Q R x; simpl; apply sepSPA.
    + intros P Q R; split; intros H t; simpl.
      * lforallR t' H1.
        transitivity (P t'); [apply ILPreFrm_closed; assumption|].
        apply wandSepSPAdj; apply H. 
      *  apply wandSepSPAdj; specialize (H t); unfold wandSP in H; simpl in H.
         rewrite H. lforallL t; apply lforallL; reflexivity.
    + intros P Q R H x; simpl; apply bilsep; apply H. 
    + intros P; split; intros x; simpl; apply empSPR.
  Qed.
End BILPre.

Global Opaque BILPre_Ops.

Section BILogic_Fun.
  Context (T: Type).
  Context {A : Type} `{BIL: BILogic A}.
  Context {HIL : ILogic A}.

  Local Transparent ILFun_Ops.

  Program Definition BILFun_Ops : BILOperators (T -> A) := {|
    empSP         := fun t => empSP;
    sepSP     P Q := fun t => P t ** Q t;
    wandSP    P Q := fun t => P t -* Q t
  |}.
  
  Local Existing Instance ILFun_Ops.
  Local Existing Instance ILFun_ILogic.
  Local Existing Instance BILFun_Ops.

  Program Definition BILFunLogic : BILogic (T -> A). 
  Proof.
    split.
    + apply _.
    + intros P Q x; simpl; apply sepSPC1.
    + intros P Q R x; simpl; apply sepSPA.
    + intros P Q R; split; intros H x; simpl;
      apply wandSepSPAdj; apply H.
    + intros P Q R H x; simpl; apply bilsep; apply H.
    + intros P; split; intros x; simpl; apply empSPR.
  Qed.

End BILogic_Fun.

Global Opaque BILFun_Ops.