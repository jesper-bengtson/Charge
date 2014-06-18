Require Import Setoid Morphisms RelationClasses Program.Basics Omega.
Require Import ILogic ILInsts ILEmbed.

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
    split; apply lforallR; intro x; apply lforallL with x; 
    destruct x; reflexivity.
  Qed.

  Lemma spec_later_or P P': |>(P \\// P') -|- |>P \\// |>P'.
  Proof.
    do 2 rewrite lor_is_exists; split;
    [rewrite spec_later_exists_inhabited; [|firstorder]| rewrite <- spec_later_exists];
    apply lexistsL; intro x; apply lexistsR with x; destruct x; reflexivity.
  Qed.    

  Lemma spec_later_true : |>ltrue -|- ltrue.
  Proof.
    split; [intuition|].
    rewrite ltrue_is_forall, spec_later_forall.
    apply lforallR; intro x; destruct x.
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

  Program Definition ILLaterNatOps : ILLOperators (ILPreFrm ge A)  := 
    {|
      illater P := mkILPreFrm (fun x => Forall y : nat, Forall H : y < x, P y) _
    |}.
  Next Obligation.
    intros.
    apply lforallR; intro x; apply lforallR; intro Hx; apply lforallL with x. 
    apply lforallL; [omega | reflexivity].
  Qed.

Local Transparent ILPre_Ops.
Local Existing Instance ILLaterNatOps.
Local Existing Instance ILPre_Ops.
Local Existing Instance ILPre_ILogic.

  Instance ILLaterNat : ILLater (ILPreFrm ge A).
  Proof.
    admit.
(*
    split.
    + apply _.
    + intros P H x; induction x. 
      - rewrite <- H; simpl; lforallR x.
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
*)
  Qed.

End ILogic_nat.

Section IBILPre.
  Context T (ord: relation T) {ord_Pre: PreOrder ord}.
  Context {A : Type} `{HBI: ILLater A}.
  Context {IL : ILogic A}.
  
  Local Existing Instance ILPre_Ops.
  Local Existing Instance ILPre_ILogic.

  Local Transparent ILPre_Ops.

  Program Instance ILLaterPreOps : ILLOperators (ILPreFrm ord A) := {|
    illater P := mkILPreFrm (fun t => |>(P t)) _
  |}.
  Next Obligation.
    rewrite H. reflexivity.
  Qed.
  
  Program Definition ILLaterPre : ILLater (ILPreFrm ord A).
  Proof.
    split.
    + apply _.
    + intros P HP x. apply spec_lob. apply HP.
    + intros P x. apply spec_later_weaken.
    + intros P Q; split; intros x; simpl; 
        setoid_rewrite <- spec_later_impl;
        do 2 setoid_rewrite spec_later_forall; reflexivity.
    + intros B F; split; intros x; simpl; apply spec_later_forall.
    + intros B F x; simpl; apply spec_later_exists.
    + intros B F I x; simpl; apply spec_later_exists_inhabited; apply I.
  Qed.

End IBILPre.

Section IBILogic_Fun.
  Context (T: Type).
  Context {A : Type} `{ILL: ILLater A}.

  Local Existing Instance ILFun_Ops.
  Local Existing Instance ILFun_ILogic.

  Local Transparent ILFun_Ops.

  Program Instance ILLaterFunOps : ILLOperators (T -> A) := {|
    illater P := fun t => |>(P t)
  |}.
  
  Program Definition ILLaterFun : ILLater (T -> A).
  Proof.
    split.
    + apply _.
    + intros P HP x. apply spec_lob. apply HP.
    + intros P x. apply spec_later_weaken.
    + intros P Q; split; intros x; simpl;
      apply spec_later_impl.
    + intros B F; split; intros x; simpl; apply spec_later_forall.
    + intros B F x; simpl; apply spec_later_exists.
    + intros B F I x; simpl; apply spec_later_exists_inhabited; apply I.
  Qed.

End IBILogic_Fun.

Global Opaque ILLaterPreOps.
Global Opaque ILLaterNatOps.
Global Opaque ILLaterFunOps.
