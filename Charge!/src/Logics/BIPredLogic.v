Require Import Setoid Morphisms RelationClasses Program.Basics. 
Require Import IPredLogic BIPropLogic IPredLogic IPropLogic.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Section DerivedPropInferenceRules.

Section CorePredInferenceRules.
  Context {A : Type} `{HBIL : BILogic A} {HAOps : IPredLogicOps A} {HA : IPredLogic A}.
  
  Lemma bilexistsscL {T} (P : A) (Q : T -> A) :
    Exists x : T, P ** Q x |-- P ** Exists x : T, Q x.
  Proof.
  	apply lexistsL; intro x.
    rewrite sepSPC. etransitivity; [|rewrite <- sepSPC; reflexivity].
    apply bilsep. eapply lexistsR; reflexivity.
  Qed.

  Lemma bilexistsscR {T} (P : A) (Q : T -> A) :
    P ** (Exists x : T, Q x) |-- Exists x : T, P ** Q x.
  Proof.
    rewrite sepSPC; rewrite wandSepSPAdj.
    apply lexistsL; intro x; erewrite <- wandSPAdj. reflexivity.
    eapply lexistsR; rewrite sepSPC; reflexivity.
  Qed.

  Lemma bilexistssc {T} (P : A) (Q : T -> A) :
    Exists x : T, P ** Q x -|- P ** Exists x : T, Q x.
  Proof.
    split; [apply bilexistsscL | apply bilexistsscR].
  Qed.

  Lemma bilforallscR {T} (P : A) (Q : T -> A) :
    P ** (Forall x : T, Q x) |-- Forall x : T, P ** Q x.
  Proof.
    apply lforallR; intro x.
    rewrite sepSPC; etransitivity; [|rewrite <- sepSPC; reflexivity].
    apply bilsep. apply lforallL with x. reflexivity.
  Qed.

End CorePredInferenceRules.

Section DerivedPredInferenceRules.
  Context {A : Type} `{HBIL : BILogic A} {HAOps : IPredLogicOps A} {HA : IPredLogic A}.

  Lemma sepSP_falseR P : P ** lfalse -|- lfalse.
  Proof.
    rewrite lfalse_is_exists, <- bilexistssc.
    split; apply lexistsL; intro x; destruct x.
  Qed.
  
  Lemma sepSP_falseL P : lfalse ** P -|- lfalse.
  Proof.
    rewrite -> sepSPC; apply sepSP_falseR.
  Qed.

  Lemma siexistsE {T : Type} (P : T -> A) (Q : A) :
    (Exists x, P x) -* Q -|- Forall x, (P x -* Q).
  Proof.
    split.
	+ apply lforallR; intro x. apply wandSepSPAdj; eapply wandSPL; [|reflexivity].
	  apply lexistsR with x. reflexivity.
	+ apply wandSepSPAdj. rewrite bilexistsscR. apply lexistsL; intro x.
	  rewrite sepSPC, bilforallscR. apply lforallL with x. rewrite sepSPC. 
	  apply wandSPL; reflexivity.
  Qed.

End DerivedPredInferenceRules.