Require Import Setoid Morphisms RelationClasses Program.Basics Omega.
Require Import ILogic ILInsts ILQuantTac.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Section LaterSect.
  Context {A : Type}.
  Context `{ILOps: ILogicOps A}.
          
Class ILLOperators (A : Type) := {
  illater : A -> A
}.

Class ILLater {ILLOps: ILLOperators A} := {
  illogic :> ILogic A;                                           
  spec_lob P : illater P |-- P -> |-- P;
  spec_later_weaken P : P |-- illater P;
  spec_later_impl P Q : illater (P -->> Q) -|- (illater P) -->> (illater Q);
  spec_later_forall {T} (F : T -> A) : illater (Forall x:T, F x) -|- Forall x:T, illater (F x);
  spec_later_exists {T} (F : T -> A) : Exists x : T, illater (F x) |-- illater (Exists x : T, F x);
  spec_later_exists_inhabited {T} (F : T -> A) : inhabited T -> illater (Exists x : T, F x) |-- Exists x : T, illater (F x)
}.
End LaterSect.

Check @illater.
Implicit Arguments ILLater [[ILLOps] [ILOps]].
Notation "'|>' a"  := (illater a) (at level 71).

Section ILogicLaterCoreRules.
  Context {A} `{IL: ILLater A}.

  Global Instance spec_later_entails:
    Proper (lentails ==> lentails) illater.
  Proof.
    intros P P' HP.
    rewrite <- limplValid, <- spec_later_impl, <- spec_later_weaken, limplValid.
    assumption.
  Qed.

  Global Instance spec_later_equiv:
    Proper (lequiv ==> lequiv) illater.
  Proof.
    intros P P' HP. split; cancel1; rewrite HP; reflexivity.
  Qed.

  Lemma spec_later_and P P': |>(P //\\ P') -|- |>P //\\ |>P'.
  Proof.
    do 2 rewrite land_is_forall; rewrite spec_later_forall;
    split; lforallR x; lforallL x; 
    destruct x; reflexivity.
  Qed.

  Lemma spec_later_or P P': |>(P \\// P') -|- |>P \\// |>P'.
  Proof.
    do 2 rewrite lor_is_exists; split;
    [rewrite spec_later_exists_inhabited; [|firstorder]| rewrite <- spec_later_exists];
    lexistsL x; lexistsR x; destruct x; reflexivity.
  Qed.    

  Lemma spec_later_true : |>ltrue -|- ltrue.
  Proof.
    split; [intuition|].
    rewrite ltrue_is_forall, spec_later_forall.
    lforallR x; destruct x.
  Qed.

End ILogicLaterCoreRules.

Hint Rewrite
  @spec_later_and
  @spec_later_impl
  @spec_later_true
  @spec_later_forall
  : push_later.

Section ILogic_nat.
  Context {A : Type}.
  Context `{IL: ILogic A}.

  Program Definition ILLaterPreOps : ILLOperators (ILPreFrm ge A)  := 
    {|
      illater P := mkILPreFrm (fun x => Forall y : nat, Forall H : y < x, P y) _
    |}.
  Next Obligation.
    intros.
    lforallR x Hx; lforallL x. 
    apply lforallL; [omega | reflexivity].
  Qed.

Local Transparent ILPre_Ops.
Local Existing Instance ILLaterPreOps.
Local Existing Instance ILPre_Ops.
Local Existing Instance ILPre_ILogic.

  Instance ILLaterPre : ILLater (ILPreFrm ge A).
  Proof.
    split.
    + apply _.
    + intros P H x; induction x. 
      - rewrite <- H; simpl; lforallR y;
        lforallR Hy; omega.
      - rewrite <- H; simpl; lforallR y Hy.
        assert (x >= y) by omega.
        rewrite <- ILPreFrm_closed; eassumption.
    + intros P x; simpl; lforallR y Hyx.
      apply ILPreFrm_closed; simpl. omega.
    + intros P Q; split; intros x; simpl.
      - lforallR y Hxy.
        apply limplAdj.
        lforallR z Hzy.
        lforallL z z.
        lforallL_aux. do 2 (apply lforallL; [omega |]).
	    lforallL z. lforallL_aux. apply lforallL; [omega|].
        apply landAdj. reflexivity.
      - lforallR y Hyx z Hyz.
        lforallL (z + 1).
        apply lforallL. omega.
        apply limplAdj.
        apply limplL.
        lforallR a Ha.
        apply ILPreFrm_closed. omega.
        lforallL z.
        lforallL. apply lforallL. omega.
        apply landL1. reflexivity.
    + intros T F; split; simpl; intros x.
      - lforallR a y Hyx.
        lforallL y Hyx a.
        reflexivity.
      - lforallR y Hyx a.
        lforallL a y Hyx.
        reflexivity.
    + intros T F x; simpl.
      lexistsL a; lforallR y H.
      lforallL y H; lexistsR a.
      reflexivity.
    + intros T F Hin x; simpl.      
      inversion Hin as [a]; destruct x.
      - lexistsR a; lforallR y H; omega.
      - lforallL x. apply lforallL; [omega|].
        lexistsL b; lexistsR b.
        lforallR y H.
        apply ILPreFrm_closed; omega.
  Qed.

End ILogic_nat.

Global Opaque ILLaterPreOps.
