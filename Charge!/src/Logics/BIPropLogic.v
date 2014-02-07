Require Import Setoid Morphisms RelationClasses Program.Basics. 
Require Import IPropLogic.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Section BILogic.
  Context {A : Type}.
  Context {HILOp: IPropLogicOps A}.

  Class BILOperators (A : Type) := {
    empSP  : A;
    sepSP  : A -> A -> A;
    wandSP : A -> A -> A
  }.

  Class BILogic {BILOp: BILOperators A} := {
    bilil :> IPropLogic A;
    sepSPC1 P Q : sepSP P Q |-- sepSP Q P;
    sepSPA1 P Q R : sepSP (sepSP P Q) R |-- sepSP P (sepSP Q R);
    wandSepSPAdj P Q R : sepSP P Q |-- R <-> P |-- wandSP Q R;
    bilsep P Q R : P |-- Q -> sepSP P R |-- sepSP Q R;
    empSPR P : sepSP P empSP -|- P
  }.

End BILogic.

Implicit Arguments BILogic [[BILOp] [HILOp]].

Notation "a '**' b"  := (sepSP a b)
  (at level 75, right associativity).
Notation "a '-*' b"  := (wandSP a b)
  (at level 77, right associativity).

Section CorePropInferenceRules.

  Context {A} `{HBIL: BILogic A}.

  Lemma wandSPAdj P Q C (HSep: C ** P |-- Q) : C |-- P -* Q.
  Proof.
    apply wandSepSPAdj; assumption.
  Qed.

  Lemma wandSPAdj' P Q C (HSep: P ** C |-- Q) : C |-- P -* Q.
  Proof.
    apply wandSepSPAdj. etransitivity; [apply sepSPC1|]. assumption.
  Qed.

  Lemma sepSPAdj P Q C (HWand: C |-- P -* Q) : C ** P |-- Q.
  Proof.
    apply wandSepSPAdj; assumption.
  Qed.

  Lemma sepSPAdj' P Q C (HWand: C |-- P -* Q) : P ** C |-- Q.
  Proof.
    etransitivity; [apply sepSPC1|]. apply wandSepSPAdj. assumption.
  Qed.

  Lemma sepSPC (P Q : A) : P ** Q -|- Q ** P.
  Proof.
    split; apply sepSPC1.
  Qed.

  Lemma sepSPA2 (P Q R : A) : P ** (Q ** R) |-- (P ** Q) ** R.
  Proof.
    rewrite sepSPC.
    etransitivity; [apply sepSPA1|].
    rewrite sepSPC.
    etransitivity; [apply sepSPA1|].
    rewrite sepSPC.
    reflexivity.
  Qed.

  Lemma sepSPA (P Q R : A) : (P ** Q) ** R -|- P ** (Q ** R).
  Proof.
    split; [apply sepSPA1 | apply sepSPA2].
  Qed.
    
  Lemma wandSPI (P Q R : A) (HQ : P ** Q |-- R) : (P |-- Q -* R).
  Proof.
    apply wandSPAdj; assumption.
  Qed.

  Lemma wandSPE (P Q R T : A) (HQR: Q |-- T -* R) (HP : P |-- Q ** T) : P |-- R.
  Proof.
    apply sepSPAdj in HQR.
    rewrite <- HQR, HP. reflexivity.
  Qed.

  Lemma empSPL P : empSP ** P -|- P.
  Proof.
    rewrite sepSPC; apply empSPR.
  Qed.

  Lemma bilandscDL (P Q R : A) : (P //\\ Q) ** R |-- (P ** R) //\\ (Q ** R).
  Proof.
  	apply landR.
  	+ apply wandSepSPAdj; apply landL1; apply wandSepSPAdj; reflexivity. 
  	+ apply wandSepSPAdj; apply landL2; apply wandSepSPAdj; reflexivity. 
  Qed.
  
  Lemma bilorscDL (P Q R : A) : (P \\// Q) ** R -|- (P ** R) \\// (Q ** R).
  Proof.
  	split.
  	+ apply wandSepSPAdj; apply lorL; apply wandSepSPAdj;
  	  [apply lorR1 | apply lorR2]; reflexivity.
  	+ apply lorL; apply bilsep; [apply lorR1 | apply lorR2]; reflexivity.
  Qed.
  
End CorePropInferenceRules.



Section BILogicMorphisms.
  Context {A : Type} `{BIL: BILogic A}.

  Global Instance sepSP_lentails_m:
    Proper (lentails ++> lentails ++> lentails) sepSP.
  Proof.
    intros P P' HP Q Q' HQ.
    etransitivity; [eapply bilsep; exact HP|].
    rewrite -> sepSPC.
    etransitivity; [eapply bilsep; exact HQ|].
    rewrite -> sepSPC. reflexivity.
  Qed.  

  Global Instance sepSP_lequiv_m:
    Proper (lequiv ==> lequiv ==> lequiv) sepSP.
  Proof.
    intros P P' HP Q Q' HQ.
    split; apply sepSP_lentails_m; (apply HP || apply HQ).
  Qed.  

  Global Instance wandSP_lentails_m:
    Proper (lentails --> lentails ++> lentails) wandSP.
  Proof.
    intros P P' HP Q Q' HQ. red in HP.
    apply wandSPAdj. rewrite <- HQ, -> HP.
    apply sepSPAdj. reflexivity.
  Qed.

  Global Instance wandSP_lequiv_m:
    Proper (lequiv ==> lequiv ==> lequiv) wandSP.
  Proof.
    intros P P' HP Q Q' HQ.
    split; apply wandSP_lentails_m; (apply HP || apply HQ).
  Qed.  

End BILogicMorphisms.

Section DerivedPropInferenceRules.
  Context {A} `{BILogic A}.

  Lemma scME (P Q R S : A) (HPR: P |-- R) (HQS: Q |-- S) :
    P ** Q |-- R ** S.
  Proof.
    rewrite HPR, HQS; reflexivity.
  Qed.

  Lemma wandSPL P Q CL CR (HP: CL |-- P) (HR: Q |-- CR) :
    (P -* Q) ** CL |-- CR.
  Proof.
    rewrite <-HR, <-HP. apply sepSPAdj. reflexivity.
  Qed.
    
  Lemma septrue : forall p, p |-- p ** ltrue.
  Proof.
    intros. rewrite <- empSPR at 1.
    rewrite sepSPC. rewrite (sepSPC p).
    apply bilsep. apply ltrueR.
  Qed.

  Lemma wand_curry : forall a b c, (a ** b) -* c -|- a -* (b -* c).
  Proof.
    intros; split.
    { eapply wandSPAdj.
      eapply wandSPAdj.
      rewrite sepSPA.
      eapply sepSPAdj.
      reflexivity. }
    { eapply wandSPAdj.
      rewrite <- sepSPA.
      eapply sepSPAdj.
      eapply sepSPAdj. reflexivity. }
  Qed.

End DerivedPropInferenceRules.