Require Import Setoid Morphisms RelationClasses Program.Basics. 
Require Import ILogic BILogic ILInsts Pure.
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
  	apply lexistsL; intro H1. eapply lexistsR. rewrite <- H. assumption. apply ltrueR.
  Qed.
  Next Obligation.
  	apply lexistsL; intro a; apply lexistsL; intro b; apply lexistsL; intro Hab.
  	apply lexistsR with a; apply lexistsR with b. 
        eapply lexistsR. eapply sa_mul_monR; eassumption. reflexivity.
  Qed.
  Next Obligation.
	apply lforallR; intro a; apply lforallR; intro b; apply lforallR; intro Hab.
	apply lforallL with a; apply lforallL with b. apply lforallL. eapply sa_mul_mon; [symmetry|]; eassumption.
	reflexivity.
  Qed.

  Local Existing Instance ILPre_Ops.
  Local Existing Instance ILPre_ILogic.
  Local Transparent ILPre_Ops.

  Instance SABILogic : BILogic (ILPreFrm rel B). 
    split.
    + apply _.
    + intros P Q x; simpl.
      apply lexistsL; intro x1; apply lexistsL; intro x2; apply lexistsL; intro H'; apply sa_mulC in H'.
      apply lexistsR with x2; apply lexistsR with x1; apply lexistsR with H'; apply landC.
    + intros P Q R x; simpl.
      apply lexistsL; intro x1; apply lexistsL; intro x2; apply lexistsL; intro Hx. 
      repeat setoid_rewrite landexistsDL.
      apply lexistsL; intro x3; apply lexistsL; intro x4; apply lexistsL; intro Hx1. 
      destruct (sa_mulA Hx1 Hx) as [x5 [Hx2 Hx5]].
      apply lexistsR with x3; apply lexistsR with x5; apply lexistsR with Hx5.
      rewrite landA. apply landR. apply landL1. reflexivity.
      apply lexistsR with x4; apply lexistsR with x2; apply lexistsR with Hx2.
      apply landL2. reflexivity.      
    + intros P Q R; split; intros H x; simpl.
      - apply lforallR; intro x1; apply lforallR; intro x2; apply lforallR; intro Hx1.
        apply limplAdj.
        specialize (H x2); simpl in H.
        rewrite <- H.
        apply lexistsR with x; apply lexistsR with x1; apply lexistsR with Hx1. reflexivity.
      - apply lexistsL; intro x1; apply lexistsL; intro x2; apply lexistsL; intro Hx.
        specialize (H x1); simpl in H.
        setoid_rewrite H.
        repeat setoid_rewrite landforallDL.
        apply lforallL with x2; apply lforallL with x; apply lforallL with Hx.
        apply landAdj. reflexivity.
    + intros P Q R H x; simpl.
      apply lexistsL; intro x1; apply lexistsL; intro x2; apply lexistsL; intro Hx.
      apply lexistsR with x1; apply lexistsR with x2; apply lexistsR with Hx.      
      rewrite H. reflexivity.
    + intros P; split; intros x; simpl.
      - apply lexistsL; intro x1; apply lexistsL; intro x2; apply lexistsL; intro Hx. 
        rewrite landC, landexistsDL. apply lexistsL; intro H2.
        apply landL2.
        apply sa_unit_eq in Hx. rewrite <- Hx. reflexivity. assumption.
      - destruct (sa_unit_ex x) as [u [H1 H2]].
        apply lexistsR with x; apply lexistsR with u; apply lexistsR with H2. 
        apply landR; [reflexivity|].
        apply lexistsR with H1; apply ltrueR. 
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

Require Import ILEmbed.

(* not sure about this *)
Definition setrel {A} (rel: relation A) : relation (A -> Prop) :=
  fun P Q => forall a, Q a -> exists a', P a' /\ rel a' a.
(*
Module BIViews.
Section BIViews.
  Context {A} `{sr : SepAlg A}.
  Context {B} `{IL: ILogic B}.
  Context {EO: EmbedOp Prop B} {Emb: Embed Prop B}.
  Context (rel: relation A) {HPre : PreOrder rel}.
  Context {HPre_equiv: PreOrder (Equivalence.equiv)}. (* redundant but practical *)
  (* This property is weaker than Proper (rel ++> impl) (sr_mul a b) *)
  Context (Hmul_K: forall x1 x2 x x', sa_mul x1 x2 x -> rel x x' ->
                                      exists x1' x2', rel x1 x1' /\ rel x2 x2'
                                                      /\ sa_mul x1' x2' x').
  Context (Hunit_proper: Proper (rel ++> impl) sa_unit).
  Context (Hrel_proper: Proper (Equivalence.equiv ==> Equivalence.equiv ==> iff) rel).

  (* beware: cyclic *)
  Instance: subrelation impl lentails.
  Proof. reflexivity. Qed.

  Local Existing Instance ILPre_Ops.
  Local Existing Instance ILPre_ILogic.
  Local Existing Instance EmbedILPreDropOp.
  Local Existing Instance EmbedILPreDrop.

  Program Instance SRBIOps: BILOperators (ILPreFrm rel B) := {
    empSP := mkILPreFrm (fun x => embed (sa_unit x)) _;
    sepSP P Q := mkILPreFrm (fun x =>
        Exists x1, Exists x2,
        sa_mul x1 x2 x /\\ P x1 //\\ Q x2) _;
    wandSP P Q := mkILPreFrm (fun x2 =>
        Forall x2', Forall x1, Forall x,
        rel x2 x2' ->> sa_mul x1 x2' x ->> P x1 -->> Q x) _
  }.
  Next Obligation.
    intros. setoid_rewrite H. reflexivity.
  Qed.
  Next Obligation.
    lexistsL x1 x2. apply lpropandL; intro Hmulx.
    destruct (Hmul_K Hmulx H) as [x1' [x2' [Hrelx1 [Hrelx2 Hmulx']]]].
    lexistsR x1' x2'. apply lpropandR; [assumption|].
    rewrite Hrelx1, Hrelx2. reflexivity.
  Qed.
  Next Obligation.
    intros. setoid_rewrite H. reflexivity.
  Qed.

  Local Transparent ILPre_Ops.

  Instance SRBILogic : BILogic (ILPreFrm rel B).
  Proof.
    split.
    + apply _.
    + intros P Q x; simpl.
      lexistsL x1 x2. apply lpropandL; intros Hmul. apply sa_mulC in Hmul.
      lexistsR x2 x1. apply lpropandR; [assumption|]. apply landC.
    + intros P Q R x; simpl.
      lexistsL xPQ' xR. apply lpropandL; intro HmulPQ_R.
      lexistsL xP xQ. unfold lembedand. rewrite landA. apply lpropandL; intro HmulPQ.
      destruct (sa_mulA HmulPQ HmulPQ_R) as [xQR [HmulQR HmulP_QR]].
      lexistsR xP xQR. apply lpropandR; [assumption|].
      rewrite landA. apply landR; [apply landL1; reflexivity|]. 
      lexistsR xQ xR. apply lpropandR; [assumption|]. 
      apply landL2. reflexivity.
    + intros P Q R. split; intros H.
      * simpl. intros xP. lforallR xP' xQ xR'. 
      	apply lpropimplR; intro Hrel_xP.
      	apply lpropimplR; intro Hmul_xR'.
        apply limplAdj. rewrite <-H. simpl.
        lexistsR xP' xQ. apply lpropandR; [now apply sa_mulC|].
        now rewrite Hrel_xP.
      * simpl. intros xR. lexistsL xP xQ. apply lpropandL; intro Hmul_xR.
        apply landAdj. rewrite ->H. simpl. lforallL xP xQ xR.
        apply lpropimplL; [reflexivity|]. apply lpropimplL; [now apply sa_mulC|].
        reflexivity.
    + intros. simpl. setoid_rewrite H. reflexivity.
    + intros P; split; intros x; simpl.
      - lexistsL x1 x2. apply lpropandL; intro Hx12.
        rewrite landC. apply landAdj.
        apply embedPropL; intros Hex2. apply limplValid.
        cancel1. rewrite (sa_unit_eq Hex2 Hx12). reflexivity.
      - destruct (sa_unit_ex x) as [ex [Hunit Hmul]].
        lexistsR x ex. apply lpropandR; [assumption|].
        apply landR; [reflexivity|].
        etransitivity; [apply ltrueR|]. apply embedPropR. assumption.
  Qed.

  Program Definition SRBIAtom (a: A) : ILPreFrm rel B :=
    mkILPreFrm (fun a' => embed (rel a a')) _.
  Next Obligation.
    intros. rewrite H. reflexivity.
  Qed.

  Global Instance SRBIAtom_Proper: Proper (rel --> lentails) SRBIAtom.
  Proof.
    intros a a' Ha t. simpl. rewrite <-Ha. reflexivity.
  Qed.

  Lemma SRBIAtom_mul a b
    (Hmul_proper: Proper (rel ++> rel ++> setrel rel) sa_mul):
    SRBIAtom a ** SRBIAtom b -|- Exists c, sa_mul a b c /\\ SRBIAtom c.
  Proof.
    split.
    - simpl. intros x.
      lexistsL a' b'. apply lpropandL; intros Hmulab'.
      apply landAdj. apply embedPropL; intros Hrela.
      apply limplValid. apply embedPropL; intros Hrelb.
      destruct (Hmul_proper _ _ Hrela _ _ Hrelb _ Hmulab')
        as [ab [Hmulab Hrelab]].
      lexistsR ab. apply landR; apply embedPropR; assumption.
    - lexistsL c. apply landAdj.
      apply embedPropL; intros Hmulc. apply limplValid. (* tactic fails *)
      simpl. intros x. apply embedPropL; intros Hrelc.
      destruct (Hmul_K Hmulc Hrelc) as [x1' [x2' [Hrelx1 [Hrelx2 Hmulx']]]].
      lexistsR x1' x2'. apply lpropandR; [assumption|].
      apply landR; apply embedPropR; assumption.
   Qed.

  Lemma SRBIAtom_emp: Exists e, sa_unit e /\\ SRBIAtom e -|- empSP.
  Proof.
    split; intros x; simpl.
    - lexistsL e'.
      apply landAdj. apply embedPropL; intros He'. apply limplValid.
      apply embedPropL; intros Hrele'. apply embedPropR.
      rewrite <-Hrele'. assumption.
    - apply embedPropL; intros Hx.
      lexistsR x. apply landR; apply embedPropR; [assumption|reflexivity].
  Qed.

End BIViews.
End BIViews.

Module BISepRel.
Section BISepRel.
  Context {A} `{sr : SepAlg A}.
  Context {B} `{IL: ILogic B}.
  Context {EO: EmbedOp Prop B} {Emb: Embed Prop B}.
  Context (rel: relation A) {HPre : PreOrder rel}.
  Context {HPre_equiv: PreOrder Equivalence.equiv}. (* redundant but practical *)
  Context (Hmul_proper: Proper (rel ++> rel ++> setrel rel) sa_mul).
  Context (Hrel_proper: Proper (Equivalence.equiv ==> Equivalence.equiv ==> iff) rel).
  (* Pym requires the relation to be a partial order wrt. equiv.
     Pym has the assertions closed under reverse rel *)

  (* beware: cyclic *)
  Instance: subrelation impl lentails.
  Proof. reflexivity. Qed.

  Local Existing Instance ILPre_ILogic.
  Local Existing Instance EmbedILPreDropOp.
  Local Existing Instance EmbedILPreDrop.

  Program Instance SRBIOps: BILOperators (ILPreFrm rel B) := {
    empSP := mkILPreFrm (fun x => embed (exists e, sa_unit e /\ rel e x)) _;
    sepSP P Q := mkILPreFrm (fun x =>
        Exists x1, Exists x2, Exists x12,
        sa_mul x1 x2 x12 /\\ rel x12 x /\\ P x1 //\\ Q x2) _;
    wandSP P Q := mkILPreFrm (fun x2 =>
        Forall x1, Forall x, sa_mul x1 x2 x ->> P x1 -->> Q x) _
  }.
  Next Obligation.
    intros. setoid_rewrite H. reflexivity.
  Qed.
  Next Obligation.
    intros. setoid_rewrite H. reflexivity.
  Qed.
  Local Existing Instance ILPre_Ops.
  Next Obligation.
    cancel1; intros x1. lforallR x'.
    apply lpropimplR; intro Hmul_x'.
    destruct (Hmul_proper (reflexivity x1) H Hmul_x')
      as [x [Hmul_x Hrel_x]].
    lforallL x. apply lpropimplL; [assumption|]. now rewrite Hrel_x.
  Qed.

  Local Transparent ILPre_Ops.

  Instance SRBILogic : BILogic (ILPreFrm rel B).
  Proof.
    split.
    + apply _.
    + intros P Q x; simpl.
      lexistsL x1 x2 x12. 
      apply lpropandL; intros Hmul.
      apply lpropandL; intros Hrel. apply sa_mulC in Hmul.
      lexistsR x2 x1 x12. do 2 (apply lpropandR; [assumption|]). apply landC.
    + intros P Q R x; simpl.
      lexistsL xPQ' xR xPQ_R. 
      apply lpropandL; intros HmulPQ_R.
      apply lpropandL; intros HrelPQ_R.
      lexistsL xP xQ xPQ. unfold lembedand. rewrite landA.
      apply lpropandL; intros HmulPQ. rewrite landA.
      apply lpropandL; intros HrelPQ.
      destruct (Hmul_proper HrelPQ (reflexivity xR) HmulPQ_R)
        as [xPQ_R' [HmulPQ_R' HrelPQ_R']].
      destruct (sa_mulA HmulPQ HmulPQ_R') as [xQR [HmulQR HmulP_QR]].
      lexistsR xP xQR xPQ_R'. apply lpropandR; [assumption|].
      apply lpropandR; [etransitivity; eassumption|].
      lexistsR xQ xR xQR. 
      rewrite landA. apply landR; [apply landL1; reflexivity | apply landL2].
      apply lpropandR; [assumption|]; apply lpropandR; reflexivity.
    + intros P Q R. split; intros H.
      * simpl. intros xP. lforallR xQ xR. apply lpropimplR; intros Hmul_xR. apply limplAdj.
        specialize (H xR). rewrite <-H. simpl. lexistsR xP xQ xR.
        apply lpropandR; [now apply sa_mulC|]. apply lpropandR; reflexivity.
      * simpl. intros xR'. lexistsL xP xQ xR. 
        apply lpropandL; intros Hmul_xR.
        apply lpropandL; intros Hrel_xR.
        apply landAdj. rewrite ->H. simpl. lforallL xQ xR.
        apply lpropimplL; [now apply sa_mulC|]. now rewrite Hrel_xR.
    + intros. simpl. setoid_rewrite H. reflexivity.
    + intros P; split; intros x; simpl.
      - lexistsL x1 x2 x12. 
        apply lpropandL; intros Hx12.
        apply lpropandL; intros Hrelx12.
        rewrite landC. apply landAdj.
        apply embedPropL; intros [ex2 [Hex2 Hrelex2]].
        apply limplValid. rewrite <-Hrelx12.
        destruct (Hmul_proper (reflexivity x1) Hrelex2 Hx12)
          as [x' [Hmulx' Hrelx']].
        rewrite (sa_unit_eq Hex2 Hmulx') in Hrelx'. rewrite <-Hrelx'.
        reflexivity.
      - destruct (sa_unit_ex x) as [ex [Hunit Hmul]].
        lexistsR x ex x. apply lpropandR; [assumption|].
        apply lpropandR; [reflexivity|]. apply landR; [reflexivity|].
        etransitivity; [apply ltrueR|].
        apply embedPropR. exists ex. split; [assumption|reflexivity].
  Qed.

  Program Definition SRBIAtom (a: A) : ILPreFrm rel B :=
    mkILPreFrm (fun a' => embed (rel a a')) _.
  Next Obligation.
    intros. rewrite H. reflexivity.
  Qed.

  Global Instance SRBIAtom_Proper: Proper (rel --> lentails) SRBIAtom.
  Proof.
    intros a a' Ha t. simpl. rewrite <-Ha. reflexivity.
  Qed.

  Lemma SRBIAtom_mul a b:
    SRBIAtom a ** SRBIAtom b -|- Exists c, sa_mul a b c /\\ SRBIAtom c.
  Proof.
    split.
    - simpl. intros x.
      lexistsL a' b' ab'. 
      apply lpropandL; intros Hmulab'.
      apply lpropandL; intros Hrelab'.
      apply landAdj. apply embedPropL; intros Hrela.
      apply limplValid. apply embedPropL; intros Hrelb.
      destruct (Hmul_proper Hrela Hrelb Hmulab') as [ab [Hmulab Hrelab]].
      lexistsR ab. apply landR.
      + apply embedPropR. assumption.
      + apply embedPropR. etransitivity; eassumption.
    - lexistsL c. apply landAdj.
      apply embedPropL; intros Hmulc. apply limplValid. (* tactic fails *)
      simpl. intros x. apply embedPropL; intros Hrelc.
      lexistsR a b c. apply lpropandR; [assumption|]. apply lpropandR; [assumption|].
      apply landR; apply embedPropR; reflexivity.
   Qed.

  Lemma SRBIAtom_emp: Exists e, sa_unit e /\\ SRBIAtom e -|- empSP.
  Proof.
    split; intros x; simpl.
    - lexistsL e'.
      apply landAdj. apply embedPropL; intros He'. apply limplValid.
      apply embedPropL; intros Hrele'. apply embedPropR.
      exists e'. split; assumption.
    - apply embedPropL; intros [e' [He' Hrele']].
      lexistsR e'. apply landR; apply embedPropR; assumption.
  Qed.

End BISepRel.
End BISepRel.

*)
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
    apply lforallR; intro x; apply lforallR; intro Hx. rewrite <- H in Hx.
    apply lforallL with x; apply lforallL with Hx; reflexivity.
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
      * apply lforallR; intro t'; apply lforallR; intro H1.
        transitivity (P t'); [apply ILPreFrm_closed; assumption|].
        apply wandSepSPAdj; apply H. 
      *  apply wandSepSPAdj; specialize (H t); unfold wandSP in H; simpl in H.
         rewrite H. apply lforallL with t; apply lforallL; reflexivity.
    + intros P Q R H x; simpl; apply bilsep; apply H. 
    + intros P; split; intros x; simpl; apply empSPR.
  Qed.

  Context {POA : @PureOp A} {PA : Pure POA}.

  Instance PureBILPreOp : @PureOp (ILPreFrm ord A) := {
    pure := fun a => forall t, pure (a t)
  }.

  Instance PureBILPre : Pure (PureBILPreOp).
  Proof.
    admit.

(*    constructor.
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
        intuition. } }*)
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
    admit.
(*
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
*)
  Qed.

  Instance pureBILFun (a : T -> A) (H : forall t, pure (a t)) : pure a.
  Proof.
    simpl; apply H.
  Qed.

End BILogic_Fun.

Global Opaque BILFun_Ops.