(*---------------------------------------------------------------------------
    This file axiomatises the inference rules of an intuitionistic logic and
    offers some parametric instances to make it straightforward to create a new
    logic that satisfies those axioms. The purpose is to factor out what the
    assertion logic and specification logic of a separation logic framework
    have in common.
  ---------------------------------------------------------------------------*)
Require Import Setoid Morphisms RelationClasses Program.Basics Omega. 

Set Implicit Arguments. 
Unset Strict Implicit.
Set Maximal Implicit Insertion.

(* The natural numbers in descending order. *)
Global Instance ge_Pre: PreOrder ge.
Proof. repeat constructor. hnf. eauto with arith. Qed.


Class Inhabited A := { cinhabited : inhabited A}.

Instance inhabitedNat: Inhabited nat. Proof. split; split; apply 0. Qed.
Instance inhabitedBool: Inhabited bool. Proof. split; split; apply true. Qed.

Generalizable Variables Frm.

(* Logical connectives *)
Class IPropLogicOps Frm := {
  lentails: relation Frm;
  ltrue: Frm;
  lfalse: Frm;
  limpl: Frm -> Frm -> Frm;
  land: Frm -> Frm -> Frm;
  lor: Frm -> Frm -> Frm
}.

(* These notations have to sit strictly between level 80 (precendence of /\)
   and level 70 (precedence of =). *)
Infix "|--"  := lentails (at level 79, no associativity).
Infix "//\\"   := land (at level 75, right associativity).
Infix "\\//"   := lor (at level 76, right associativity).
Infix "-->>"   := limpl (at level 77, right associativity).

Section IPropLogicEquiv.
  Context `{IL: IPropLogicOps Frm}.
  
  Definition lequiv P Q := P |-- Q /\ Q |-- P.
End IPropLogicEquiv.

Infix "-|-"  := lequiv (at level 85, no associativity).

(* Axioms of an intuitionistic logic, presented in a sequent calculus style
   with singleton contexts on the left of the turnstile. This form is
   particularly suited for the undisciplined context manipulation that tends to
   happen in separation logic.

   Every connective has a number of L-rules and a number of R-rules describing
   what can be done to prove a goal that has the connective as the head symbol
   of the left, respectively right, side of a turnstile. The notable exception
   to this pattern is implication, which is required to be the right adjoint of
   conjunction. This makes singleton contexts work. *)
Class IPropLogic Frm {ILOps: IPropLogicOps Frm} := {
  lentailsPre:> PreOrder lentails;
  ltrueR: forall C, C |-- ltrue;
  lfalseL: forall C, lfalse |-- C;
  landL1: forall P Q C, P |-- C  ->  P //\\ Q |-- C;
  landL2: forall P Q C, Q |-- C  ->  P //\\ Q |-- C;
  lorR1:  forall P Q C, C |-- P  ->  C |-- P \\// Q;
  lorR2:  forall P Q C, C |-- Q  ->  C |-- P \\// Q;
  landR:  forall P Q C, C |-- P  ->  C |-- Q  ->  C |-- P //\\ Q;
  lorL:   forall P Q C, P |-- C  ->  Q |-- C  ->  P \\// Q |-- C;
  landAdj: forall P Q C, C |-- (P -->> Q) -> C //\\ P |-- Q;
  limplAdj: forall P Q C, C //\\ P |-- Q -> C |-- (P -->> Q)
}.
Implicit Arguments IPropLogic [[ILOps]].

Notation "|--  P" := (ltrue |-- P) (at level 85, no associativity).
Hint Extern 0 (?x |-- ?x) => reflexivity.
Hint Extern 0 (_ |-- ltrue) => apply ltrueR.
Hint Extern 0 (lfalse |-- _) => apply lfalseL.
Hint Extern 0 (?P |-- ?Q) => (is_evar P; reflexivity) || (is_evar Q; reflexivity).

Section IPropLogicEquiv2.
  Context `{IL: IPropLogic Frm}.

  Global Instance lequivEquivalence : Equivalence lequiv.
  Proof.
    unfold lequiv. constructor; red.
    + split; reflexivity.
    + intuition.
    + intros P Q R [HPQ HQP] [HQR HRQ]; 
      split; etransitivity; eassumption.
  Qed.

End IPropLogicEquiv2.


(* Most of the connectives in IPropLogicOps are redundant. They can be derived from
   lexists, lforall and limpl, and the choice of limpl is unique up to lequiv
   since it is an adjoint. *)

Section IPropLogicMorphisms.
  Context `{IL: IPropLogic Frm}.
  
  Global Instance lequiv_lentails : subrelation lequiv lentails.
  Proof. firstorder. Qed.
  Global Instance lequiv_inverse_lentails: subrelation lequiv (inverse lentails).
  Proof. firstorder. Qed.

  Global Instance : Proper (lequiv ==> lequiv ==> iff) lequiv.
  Proof.
    intros P P' HP Q Q' HQ; split; intros H.
    + rewrite <- HP; rewrite <- HQ; assumption.
    + rewrite HP; rewrite HQ; assumption.
  Qed.

  Global Instance lequiv_lentails_m : Proper (lequiv ==> lequiv ==> iff) lentails.
  Proof.
    cbv; intuition; (etransitivity; [etransitivity|]); eassumption.
  Qed.

  Global Instance lentails_lentails_m: Proper (lentails --> lentails ++> impl) lentails.
  Proof.
    intuition.
  Qed.

  Global Instance land_lentails_m:
    Proper (lentails ++> lentails ++> lentails) land.
  Proof.
    intros P P' HP Q Q' HQ.
    apply landR; [apply landL1 | apply landL2]; assumption.
  Qed.

  Global Instance land_lequiv_m:
    Proper (lequiv ==> lequiv ==> lequiv) land.
  Proof.
    intros P P' HP Q Q' HQ.
    split; apply land_lentails_m; (apply HP || apply HQ).
  Qed.

  Global Instance lor_lentails_m:
    Proper (lentails ++> lentails ++> lentails) lor.
  Proof.
    intros P P' HP Q Q' HQ.
    apply lorL; [apply lorR1 | apply lorR2]; assumption.
  Qed.

  Global Instance lor_lequiv_m:
    Proper (lequiv ==> lequiv ==> lequiv) lor.
  Proof.
    intros P P' HP Q Q' HQ.
    split; apply lor_lentails_m; (apply HP || apply HQ).
  Qed.

  Global Instance limpl_lentails_m:
    Proper (lentails --> lentails ++> lentails) limpl.
  Proof.
    intros P P' HP Q Q' HQ; red in HP.
    apply limplAdj; rewrite <- HQ, HP; apply landAdj; reflexivity.
  Qed.

  Global Instance limpl_lequiv_m:
    Proper (lequiv ==> lequiv ==> lequiv) limpl.
  Proof.
    intros P P' HP Q Q' HQ.
    split; apply limpl_lentails_m; (apply HP || apply HQ).
  Qed.
    
End IPropLogicMorphisms.

Hint Extern 0 (?x -|- ?x) => reflexivity.
Hint Extern 0 (?P -|- ?Q) => (is_evar P; reflexivity) || (is_evar Q; reflexivity).

(* TODO: also add lforwardR. *)
Lemma lforwardL {Frm} `{IL: IPropLogic Frm} {Q R}:
    Q |-- R -> forall P G,
    P |-- Q ->
    (P |-- R -> G) ->
    G.
Proof. intros HQR ** HPQ HG. apply HG. etransitivity; eassumption. Qed.

Tactic Notation "lforwardL" hyp(H) := 
  eapply (lforwardL H); clear H; [|intros H].

Section IPropLogicFacts.
  Context `{IL: IPropLogic Frm}.
  
  (* Experiments with proof search. *)
  Ltac landR :=
    repeat match goal with
    | |- _ |-- _ //\\ _ => apply landR
    end.
  
  Ltac landL :=
    repeat match goal with
    | |- ?L1 //\\ ?L2 |-- ?R =>
        match L1 with
        | context [R] => apply landL1
        | _ =>
          match L2 with
          | context [R] => apply landL2
          end
        end
    end.

  Lemma landC P Q: P //\\ Q -|- Q //\\ P.
  Proof. split; landR; landL; reflexivity. Qed.

  Lemma landA P Q R: (P //\\ Q) //\\ R -|- P //\\ (Q //\\ R).
  Proof. split; landR; landL; reflexivity. Qed.
  
  Lemma lorC P Q : P \\// Q -|- Q \\// P.
  Proof.
    split; apply lorL; [apply lorR2 | apply lorR1 | apply lorR2 | apply lorR1]; reflexivity.
  Qed.
  
  Lemma lorA P Q R : (P \\// Q) \\// R -|- P \\// (Q \\// R).
  Proof.
  	split; apply lorL; try apply lorL; [
  	   apply lorR1 | 
       apply lorR2; apply lorR1 | 
       apply lorR2; apply lorR2 | 
       apply lorR1; apply lorR1 |
       apply lorR1; apply lorR2 |
       apply lorR2 
     ]; reflexivity.
   Qed.
  
  (* Special case of limplAdj/landAdj when there is just ltrue on the lhs *)
  Lemma limplValid P Q:
    |-- P -->> Q <->
    P |-- Q.
  Proof.
    split; intro H.
    - etransitivity; [eapply landR; [apply ltrueR|reflexivity]|].
      apply landAdj; assumption.
    - apply limplAdj. apply landL2; assumption.
  Qed.
  
  (* Left-rule for limpl. This breaks the discipline of the IPropLogic presentation
     since the implication is not strictly the top symbol of the left-hand side,
     but it remains a convenient rule. *)
  Lemma limplL P Q CL CR (HP: CL |-- P) (HR: Q //\\ CL |-- CR) :
    (P -->> Q) //\\ CL |-- CR.
  Proof.
    rewrite <-HR, <-HP. apply landR; [apply landAdj |apply landL2]; reflexivity.
  Qed.

  Lemma limplAdj2 P Q R : P -->> Q -->> R -|- P //\\ Q -->> R.
  Proof.
  	split.
  	+ apply limplAdj. do 2 (apply limplL; [landL; reflexivity|]).
  	  landL. reflexivity. 
    + do 2 apply limplAdj; rewrite landA.  	   
      apply limplL; [reflexivity | landL; reflexivity].
  Qed.
 
  Lemma limplTrue P : ltrue -->> P -|- P.
  Proof.
    split.
    + transitivity ((ltrue -->> P) //\\ ltrue).
      apply landR; [reflexivity | apply ltrueR].
      apply limplL; [apply ltrueR| apply landL1; reflexivity].
    + apply limplAdj; apply landL1; reflexivity.
  Qed.
  
 
  Lemma landtrueL : forall a, ltrue //\\ a -|- a.
  Proof.
    intros. split. eapply landL2. reflexivity. apply landR; eauto.
  Qed.

  Lemma landtrueR : forall a, a //\\ ltrue -|- a.
  Proof.
    intros. split. eapply landL1. reflexivity. apply landR; eauto.
  Qed.

  Lemma curry : forall a b c, (a //\\ b) -->> c -|- a -->> (b -->> c).
  Proof.
    clear - IL.
    intros.
    split.
    { eapply limplAdj.
      eapply limplAdj.
      rewrite landA.
      eapply landAdj.
      reflexivity. }
    { eapply limplAdj.
      rewrite <- landA.
      eapply landAdj.
      eapply landAdj. reflexivity. }
  Qed.

End IPropLogicFacts.

(* Prop is an intuitionistic logic *)
Global Instance IPropLogicOps_Prop : IPropLogicOps Prop := {|
  lentails P Q := P -> Q;
  ltrue        := True;
  lfalse       := False;
  limpl    P Q := P -> Q;
  land     P Q := P /\ Q;
  lor      P Q := P \/ Q
|}.

Global Instance IPropLogic_Prop : IPropLogic Prop.
Proof.
  split; cbv; firstorder.
Qed.

(* Make the setoid system realize that these are the same things (in the
   direction that seems useful. *)
Instance: subrelation lentails Basics.impl.
Proof. reflexivity. Qed.
Instance: subrelation lequiv iff.
Proof. reflexivity. Qed.