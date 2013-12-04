Require Import Setoid Morphisms RelationClasses Program.Basics. 
Require Import ILogic BILogic ILQuantTac ILInsts Pure.
Require Import Rel SepAlg.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Section BISepAlg.
  Context {A} `{sa : SepAlg A}.
  Context {B} `{IL: ILogic B}.
  Context {HPre : PreOrder (@rel A _)}.

  Open Scope sa_scope.

  Program Instance SABIOps: BILOperators (ILPreFrm rel B) := {
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

  Instance SABILogic : BILogic (ILPreFrm rel B). 
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

  Instance pureop_bi_sepalg : PureOp := { 
    pure := fun (P : ILPreFrm rel B) => forall h h', P h |-- P h'
  }.

  Instance pure_bi_sepalg : Pure pureop_bi_sepalg.
  Proof.
    constructor.
    { unfold pure; simpl; constructor.
      { unfold sepSP; simpl; intros.
        destruct (sa_unit_ex t).
        apply lexistsR with x.
        apply lexistsR with t.
        destruct H0.
        apply sa_mulC in H1.
        eapply lexistsR; eauto.
        rewrite H. reflexivity. }
      constructor.
      { unfold sepSP; simpl; intros.
        repeat (eapply lexistsL; intros).
        rewrite H. rewrite H0. reflexivity. }
      constructor.
      { split; intros; unfold sepSP; simpl; intros.
        { repeat (eapply lexistsL; intros).
          apply landR. do 2 apply landL1. auto.
          eapply lexistsR.
          eapply lexistsR.
          eapply lexistsR. eassumption.
          eapply landR. apply landL1. apply landL2. reflexivity.
          apply landL2. reflexivity. }
        { rewrite landC.
          rewrite landexistsDL.
          repeat (eapply lexistsL; intros).
          rewrite landexistsDL.
          repeat (eapply lexistsL; intros).
          rewrite landexistsDL.
          repeat (eapply lexistsL; intros).
          do 3 eapply lexistsR.
          eassumption.
          rewrite H.
          rewrite landC. rewrite landA. reflexivity. } }
      constructor.
      { unfold wandSP; simpl; intros.
        repeat (eapply lforallR; intros).
        destruct (sa_unit_ex x).
        destruct H0.
        eapply lforallL with x1.
        apply lforallL with x.
        eapply lforallL.
        rewrite x0. auto.
        apply limplAdj. apply limplL. apply H. apply landL1. reflexivity. }
      { unfold wandSP; simpl; intros.
        repeat (eapply lforallR; intros).
        eapply lforallL. eapply lforallL. reflexivity.
        apply limplAdj. apply limplL; auto. apply landL1. auto. } }
    { red. red. unfold pure; simpl.
      intros. setoid_rewrite H.
      reflexivity. }
  Qed.

End BISepAlg.

Global Opaque SABIOps.

Section BILPre.
  Context T (ord: relation T) {HPre: PreOrder ord}.
  Context {A : Type} `{HBI: BILogic A}.
  Context {HIL : ILogic A}.

  Program Instance BILPre_Ops : BILOperators (ILPreFrm ord A) := {|
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

  Local Transparent ILPre_Ops.

  Instance BILPreLogic : BILogic (ILPreFrm ord A).
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

  Context {POA : @PureOp A} {PA : Pure POA}.

  Instance PureBILPreOp : @PureOp (ILPreFrm ord A) := {
    pure := fun a => forall t, pure (a t)
  }.

  Instance PureBILPre : Pure (PureBILPreOp).
  Proof.
    constructor.
    { repeat split; intros; intro t; simpl.
      * apply pureandsc with (po := POA); auto.
      * apply purescand with (po := POA); auto.
      * apply pureandscD with (po := POA); auto.
      * apply pureandscD with (po := POA); auto.
      * apply lforallR; intro t'; apply lforallR; intro Ht.
        apply lforallL with t'; apply lforallL with Ht.
        apply puresiimpl with (po := POA); auto.
      * apply lforallR; intro t'; apply lforallR; intro Ht.
        apply lforallL with t'; apply lforallL with Ht.
        apply pureimplsi with (po := POA); auto. }
    { do 2 red. unfold pure; simpl. intros.
      split.
      { intros. eapply pure_proper. 2: eapply H0. symmetry.
        instantiate (1 := t).
        red in H. red. unfold lentails in H. simpl in H.
        intuition. }
      { intros. eapply pure_proper. 2: eapply H0. symmetry.
        instantiate (1 := t).
        red in H. red. unfold lentails in H. simpl in H.
        intuition. } }
  Qed.

  Instance pureBILPre (a : ILPreFrm ord A) (H : forall t, pure (a t)) : pure a.
  Proof.
    simpl; apply H.
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

  Context {POA : @PureOp A} {PA : Pure POA}.

  Instance PureBILFunOp : @PureOp (T -> A) := {
    pure := fun a => forall t, pure (a t)
  }.

  Instance PureBILFun : Pure (PureBILFunOp).
  Proof.
    constructor.
    { intros. repeat split; intros; intro t; simpl.
      * apply pureandsc with (po := POA); auto.
      * apply purescand with (po := POA); auto.
      * apply pureandscD with (po := POA); auto.
      * apply pureandscD with (po := POA); auto.
      * apply puresiimpl with (po := POA); auto.
      * apply pureimplsi with (po := POA); auto. }
    { do 2 red; simpl; intros.
      red in H. simpl in H.
      split.
      { intros. eapply pure_proper.
        2: eapply H0. split. intuition. intuition. }
      { intros. eapply pure_proper.
        2: eapply H0. split. intuition. intuition. } }
  Qed.

  Instance pureBILFun (a : T -> A) (H : forall t, pure (a t)) : pure a.
  Proof.
    simpl; apply H.
  Qed.

End BILogic_Fun.

Global Opaque BILFun_Ops.