(*---------------------------------------------------------------------------
    This file axiomatises the inference rules of an intuitionistic logic and
    offers some parametric instances to make it straightforward to create a new
    logic that satisfies those axioms. The purpose is to factor out what the
    assertion logic and specification logic of a separation logic framework
    have in common.
  ---------------------------------------------------------------------------*)
Require Import Setoid Morphisms RelationClasses IPropLogic.

Set Implicit Arguments. 
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Section IPredLogic.
  Context {A : Type}.
  Context {HILOp: IPropLogicOps A}.

  Class IPredLogicOps (A : Type) := {
    lforall: forall {T}, (T -> A) -> A;
    lexists: forall {T}, (T -> A) -> A
  }.

  Class IPredLogic A {IPropOps : IPropLogicOps A} {IPredOps: IPredLogicOps A} := {
	ipl_logic :> IPropLogic A;
	lforallL: forall T x (P: T -> A) C, P x |-- C -> lforall P |-- C;
	lforallR: forall T (P: T -> A) C, (forall x, C |-- P x) -> C |-- lforall P;
	lexistsL: forall T (P: T -> A) C, (forall x, P x |-- C) -> lexists P |-- C;
	lexistsR: forall T x (P: T -> A) C, C |-- P x -> C |-- lexists P
  }.
End IPredLogic.

Implicit Arguments IPredLogic [[IPropOps] [IPredOps]].
Implicit Arguments lforallL [[IPropOps] [IPredOps] [A] [IPredLogic] [T] [P] [C]].
Implicit Arguments lexistsR [[IPropOps] [IPredOps] [A] [IPredLogic] [T] [P] [C]].

Notation "'Forall' x : T , p" := 
  (lforall (fun x : T => p)) (at level 78, x ident, right associativity).
Notation "'Forall' x , p" := 
  (lforall (fun x => p)) (at level 78, x ident, right associativity, only parsing).
Notation "'Exists' x : T , p" := 
  (lexists (fun x : T => p)) (at level 78, x ident, right associativity).
Notation "'Exists' x , p" := 
  (lexists (fun x => p)) (at level 78, x ident, right associativity, only parsing).

Section IPredLogicEquivOps.
  Context {A : Type} `{IL: IPredLogic A}.
  
  Lemma land_is_forall P Q :
    P //\\ Q -|- Forall b : bool, if b then P else Q.
  Proof.
    split.
    - apply lforallR; intro x; destruct x.
      + apply landL1; reflexivity.
      + apply landL2; reflexivity.
    - apply landR.
      + apply lforallL with true; reflexivity.
      + apply lforallL with false; reflexivity.
  Qed.

  Lemma lor_is_exists P Q:
    P \\// Q -|- Exists b : bool, if b then P else Q.
  Proof.
    split.
    - apply lorL.
      + apply lexistsR with true; reflexivity.
      + apply lexistsR with false; reflexivity.
    - apply lexistsL; intro x; destruct x.
      + apply lorR1; reflexivity.
      + apply lorR2; reflexivity.
  Qed.

  Lemma ltrue_is_forall:
    ltrue -|- Forall x: Empty_set, Empty_set_rect _ x.
  Proof. 
    split; [apply lforallR|]; intuition.
  Qed.

  Lemma lfalse_is_exists:
    lfalse -|- Exists x: Empty_set, Empty_set_rect _ x.
  Proof. split; [|apply lexistsL]; intuition. Qed.
  
End IPredLogicEquivOps.

Section IPredLogicMorphisms.
  Context {A : Type} `{IL: IPredLogic A}.

  Global Instance lforall_lentails_m T:
    Proper (pointwise_relation T lentails ++> lentails) lforall.
  Proof.
    intros P P' HP. apply lforallR; intro x;  apply lforallL with x.
    rewrite HP; reflexivity.
  Qed.

  Global Instance lforall_lequiv_m T:
    Proper (pointwise_relation T lequiv ++> lequiv) lforall.
  Proof.
    intros P P' HP; split; apply lforall_lentails_m; intro x; apply HP.
  Qed.

  Global Instance lexists_lentails_m T:
    Proper (pointwise_relation T lentails ++> lentails) lexists.
  Proof.
    intros P P' HP. apply lexistsL; intro x; apply lexistsR with x.
    rewrite HP; reflexivity.
  Qed.

  Global Instance lexists_lequiv_m T:
    Proper (pointwise_relation T lequiv ++> lequiv) lexists.
  Proof.
    intros P P' HP; split; apply lexists_lentails_m; intro x; apply HP.
  Qed.

End IPredLogicMorphisms.

Section IPredLogicFacts.
  Context {A : Type} `{IL: IPredLogic A}.
  
  Lemma landexistsDL {T} (f : T -> A) (P : A) :
    (Exists a, f a) //\\ P |-- Exists a, (f a //\\ P).
  Proof.
    apply landAdj; apply lexistsL; intro a; 
    apply limplAdj; apply lexistsR with a; reflexivity.
  Qed.


  Lemma landexistsDR {T} (f : T -> A) (P : A) :
     Exists a, (f a //\\ P) |-- (Exists a, f a) //\\ P.
  Proof.
    apply lexistsL; intro a; apply landR.
    - apply landL1; apply lexistsR with a; reflexivity.
    - apply landL2; reflexivity.
  Qed.

  Lemma landexistsD {T} (f : T -> A) (P : A) :
    (Exists a, f a) //\\ P -|- Exists a, (f a //\\ P).
  Proof.
    split; [apply landexistsDL | apply landexistsDR].
  Qed.
  
  Lemma lorexistsDL {T} (f : T -> A) (P : A) {H : Inhabited T} :
    (Exists a, f a) \\// P |-- Exists a, (f a \\// P).
  Proof.
  	apply lorL.  
	+ apply lexistsL; intro x; apply lexistsR with x; apply lorR1; reflexivity. 
	+ destruct H as [[x]]; apply lexistsR with x; apply lorR2; reflexivity.
  Qed.

  Lemma lorexistsDR {T} (f : T -> A) (P : A) :
     Exists a, (f a \\// P) |-- (Exists a, f a) \\// P.
  Proof.
  	apply lexistsL; intro x; apply lorL.
  	+ apply lorR1; apply lexistsR with x; reflexivity.
  	+ apply lorR2; reflexivity.
  Qed.

  Lemma lorexistsD {T} (f : T -> A) (P : A) {H : Inhabited T} :
    (Exists a, f a) \\// P -|- Exists a, (f a \\// P).
  Proof.
    split; [apply lorexistsDL; apply H| apply lorexistsDR].
  Qed.

  Lemma landforallDL {T} (f : T -> A) (P : A) :
    (Forall a, f a) //\\ P |-- Forall a, (f a //\\ P).
  Proof.
    apply lforallR; intro a; apply landR.
    + apply landL1; apply lforallL with a; reflexivity.
    + apply landL2; reflexivity.
  Qed.

  Lemma landforallDR {T} {H: Inhabited T} (f : T -> A) (P : A) :
    Forall a, (f a //\\ P) |-- (Forall a, f a) //\\ P.
  Proof.
    apply landR.
    + apply lforallR; intro a; apply lforallL with a; apply landL1; reflexivity.
    + destruct H as [[a]]. apply lforallL with a; apply landL2; reflexivity.
  Qed.
  
  Lemma landforallD {T} (f : T -> A) (P : A) {H : Inhabited T} :
    (Forall a, f a) //\\ P -|- Forall a, (f a //\\ P).
  Proof.
  	split; [apply landforallDL | apply landforallDR].
  Qed.


  Lemma lorforallDL {T} (f : T -> A) (P : A) :
    (Forall a, f a) \\// P |-- Forall a, (f a \\// P).
  Proof.
  	apply lforallR; intro a; apply lorL.
  	+ apply lforallL with a; apply lorR1; reflexivity.
  	+ apply lorR2; reflexivity.
  Qed.
  
  Lemma limplexistsE {T : Type} (P : T -> A) (Q : A) :
    (Exists x, P x) -->> Q -|- Forall x, (P x -->> Q).
  Proof.
    split.
	+ apply lforallR; intro x. apply limplAdj; apply limplL. 
	  * apply lexistsR with x; reflexivity.
	  * apply landL1; reflexivity.
	+ apply limplAdj. rewrite landC, landexistsDL.
	  apply lexistsL; intro x. rewrite landC, landforallDL.
	  apply lforallL with x. apply limplL.
	  * reflexivity.
	  * apply landL1. reflexivity.
  Qed.
  
  Lemma limplforallER {T : Type} (P : T -> A) (Q : A) :
    Exists x, (P x -->> Q) |-- (Forall x, P x) -->> Q.
  Proof.
  	apply lexistsL; intro x. apply limplAdj. apply limplL.
  	+ apply lforallL with x. reflexivity.
  	+ apply landL1. reflexivity.
  Qed.
  
  (* The following two lemmas have an explicit forall to help unification *)
  
  Lemma lforallR2 {T : Type} (P : A) (Q : T -> A) (H : P |-- lforall Q) :
  	forall x, P |-- Q x.
  Proof.
    intro x; rewrite H. apply lforallL with x; reflexivity.
  Qed.

  Lemma lexistsL2 {T : Type} (P : T -> A) (Q : A) (H : lexists P |-- Q) :
  	forall x, P x |-- Q.
  Proof.
    intro x; rewrite <- H. apply lexistsR with x; reflexivity.
  Qed.

End IPredLogicFacts.

(* Prop is an intuitionistic logic *)
Global Instance IPredLogicOps_Prop : IPredLogicOps Prop := {|
  lforall  T F := forall x:T, F x;
  lexists  T F := exists x:T, F x
|}.

Global Instance IPredLogic_Prop : IPredLogic Prop.
Proof.
  split; cbv; firstorder.
Qed.
