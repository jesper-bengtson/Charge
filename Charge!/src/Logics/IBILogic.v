Require Import RelationClasses Setoid Morphisms.
Require Import ILogic ILInsts BILInsts ILQuantTac BILogic SepAlg.
Require Import Pure.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Section IBILogicSect.
  Context {A : Type} {ILOps : ILogicOps A} {BIOps: BILOperators A}.
  Context {BIL : BILogic A}.
 
  Polymorphic Class IBILogic := {
    ibil_bil :> BILogic A;
    emp_trueE : |-- empSP
  }.

End IBILogicSect.

Implicit Arguments IBILogic [[ILOps] [BIOps]].

Section IBILogicProperties.

  Context {A : Type} `{HIBI: IBILogic A}.

  Lemma sep_forget (p q : A) : p ** q |-- p.
  Proof.
    rewrite <- empSPR, sepSPA.
    rewrite ltrueR with (C := q ** empSP).
    rewrite emp_trueE, empSPR.
    reflexivity.
  Qed.
  
  Lemma ibilsepand (p q : A) : p ** q |-- p //\\ q.
  Proof.
  	apply landR; [|rewrite sepSPC]; apply sep_forget; reflexivity.
  Qed.

End IBILogicProperties.

Section IBISepAlg.
  Context {A} `{sa : SepAlg A}.
  Context {B} `{IL: ILogic B}.
  
  Program Instance SAIBIOps: BILOperators (ILPreFrm subheap B) := {
    empSP := mkILPreFrm (fun x => ltrue) _;
    sepSP P Q := mkILPreFrm (fun x => Exists x1, Exists x2, Exists H : sa_mul x1 x2 x,
                                                P x1 //\\ Q x2) _;
    wandSP P Q := mkILPreFrm (fun x => Forall x1, Forall x2, Forall H : sa_mul x x1 x2, 
                                                 P x1 -->> Q x2) _
  }.
  Next Obligation.
    lexistsL x1 x2 H1.
    unfold subheap in H.
    destruct H as [t'' H].
    destruct (sa_mulA H1 H) as [ac [H2 H3]].
    lexistsR x1 ac. apply lexistsR. assumption. apply landR.
    + apply landL1; reflexivity.
    + apply landL2; apply ILPreFrm_closed; simpl.
      exists t''; assumption.
  Qed.
  Next Obligation.
    lforallR x1 x2 H1.
    destruct H as [t'' H].
    destruct (sa_mulA H H1) as [ac [H2 H3]].
    lforallL ac x2. apply lforallL; [assumption|].
    apply limplAdj. apply limplL.
    apply ILPreFrm_closed. exists t''. eapply sa_mulC. assumption.
    apply landL1. reflexivity.
  Qed.

  Local Existing Instance ILPre_Ops.
  Local Existing Instance ILPre_ILogic.
  Local Transparent ILPre_Ops.
  
  Definition SAIBILogic_aux : BILogic (ILPreFrm subheap B).
  Proof.
    split.
    + apply _.
    + intros P Q x; simpl.
      lexistsL x1 x2 H1. lexistsR x2 x1.
      apply lexistsR; [apply sa_mulC; assumption|intuition].
    + intros P Q R x; simpl.
      lexistsL x1 x2 Hx x3. lexistsL x4 Hx1.
      lexistsR x3.
      destruct (sa_mulA Hx1 Hx) as [x5 [Hx2 Hx5]].
      lexistsR x5 Hx5 x4. lexistsR x2 Hx2. rewrite landA. reflexivity. 
    + intros P Q R; split; intros H x; simpl.
      - lforallR x1 x2 Hx1.
        apply limplAdj.
        specialize (H x2); simpl in H.
        rewrite <- H.
        lexistsR x x1 Hx1. reflexivity.
      - lexistsL x1 x2 Hx.
        specialize (H x1); simpl in H.
        setoid_rewrite H.
        lforallL x2 x Hx. apply landAdj; reflexivity.
    + intros P Q R H x; simpl.
      lexistsL x1 x2 Hx.
      lexistsR x1 x2 Hx; specialize (H x1); setoid_rewrite H.
      reflexivity.
    + intros P; split; intros x; simpl.
      - lexistsL x1 x2 H1. apply landL1.
        apply ILPreFrm_closed; simpl.
        exists x2. assumption.
      - destruct (sa_unit_ex x) as [u [H1 H2]]. lexistsR x u.
        lexistsR H2. apply landR; [reflexivity | apply ltrueR].
  Qed.

  Local Existing Instance SAIBILogic_aux.

  Definition SAIBILogic : IBILogic (ILPreFrm subheap B).
  Proof.
    split.
    + apply _.
    + simpl; intros _. apply ltrueR.
  Qed.


  Instance pureop_pure_ibi_sepalg : PureOp := { 
    pure := fun (P : ILPreFrm subheap B) => forall h h', P h |-- P h'
  }.

  Instance pure_ibi_sepalg : Pure pureop_pure_ibi_sepalg.
  Proof.
    constructor.
    { intros.
      unfold pure in H; simpl in H; repeat split; intros; 
      unfold pure in *; simpl in *; intros h; simpl.
      * destruct (sa_unit_ex h) as [u [H1 H2]].
        apply lexistsR with u. apply lexistsR with h.
        eapply lexistsR. apply sa_mulC; apply H2.
        apply landR; [apply landL1; apply H| apply landL2; reflexivity].
      * apply lexistsL; intros x1.
        apply lexistsL; intros x2.
        apply lexistsL; intros Hx.
        apply landR; [apply landL1; apply H | apply landL2; apply H0].
      * apply lexistsL; intros x1; apply lexistsL; intro x2; apply lexistsL; intros Hx.
        rewrite landA. apply landR; [apply landL1; apply H|].
        apply lexistsR with x1; apply lexistsR with x2; apply lexistsR with Hx.
        apply landL2. reflexivity.
      * rewrite landC. apply landAdj.
        apply lexistsL; intros x1; apply lexistsL; intro x2; apply lexistsL; intros Hx.
        apply limplAdj. 
        apply lexistsR with x1. apply lexistsR with x2. apply lexistsR with Hx.
        rewrite landC, landA.
        apply landR; [apply landL1; apply H | apply landL2; reflexivity].
      * apply lforallR; intro x1; apply lforallR; intro Hx.
        destruct Hx as [x2 Hx].
        apply lforallL with x2; apply lforallL with x1. apply lforallL.
        - assumption.
        - apply limplAdj. apply limplL; [apply H | apply landL1; reflexivity].
      * apply lforallR; intro x1; apply lforallR; intro x2; apply lforallR; intro Hx.
        apply lforallL with h. apply lforallL; [reflexivity|].
        apply limplAdj. apply limplL; [apply H| apply landL1; apply H0]. }
    { unfold pure; simpl. do 2 red; intros.
      red in H. simpl in H.
      split; intro. intros.
      destruct H.
      rewrite H1. rewrite H0. rewrite H. reflexivity.
      intros. destruct H.
      rewrite H. rewrite H0. rewrite H1. reflexivity. }
  Qed.

End IBISepAlg.

Section IBILPre.
  Context T (ord: relation T) {ord_Pre: PreOrder ord}.
  Context {A : Type} `{HBI: IBILogic A}.
  Context {BIL : BILogic A} {IL : ILogic A}.

  Local Existing Instance ILPre_Ops.
  Local Existing Instance ILPre_ILogic.
  Local Existing Instance BILPre_Ops.

  Local Transparent ILPre_Ops.

  Definition IBILPreLogic : IBILogic (ILPreFrm ord A).
  Proof.
    split.
    apply BILPreLogic.
    intro x; simpl; apply emp_trueE.
  Qed.

End IBILPre.

Section IBILogic_Fun.
  Context (T: Type).
  Context {A : Type} `{BIL: IBILogic A}.

  Local Existing Instance ILFun_Ops.
  Local Existing Instance ILFun_ILogic.
  Local Existing Instance BILFun_Ops.

  Local Transparent ILFun_Ops.

  Definition IBILFunLogic : IBILogic (T -> A).
  Proof.
    split.
    apply BILFunLogic. apply BIL.
    apply _. intro x; simpl; apply emp_trueE.
  Qed.

End IBILogic_Fun.
