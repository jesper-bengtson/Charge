Require Import ILogic BILogic ILEmbed ILQuantTac.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Section Pure.

  Context {A : Type} {ILOPs : ILogicOps A} {BILOps : BILOperators A}.

(* This version of Pure will not work for classical separation logics as that 
   requires a negative occurrence of a recursive call for the rule that states that
   P ** Q |-- P //\\ Q (both P and Q must be pure). This is most likely solvable,
   and is true even for non-pure predicates in intuitionistic separation logic,
   but I want to do it in a nice way. *)

  Class Pure (P : A) := {
    pureandscL  : (forall Q, P //\\ Q |-- P ** Q);
    pureandscR  : (forall Q, Q //\\ P |-- Q ** P);
	pureandscD  : (forall Q R, (Q //\\ P) ** R -|- (Q ** R) //\\ P);
    puresiimpl  : (forall Q, P -* Q |-- P -->> Q)
  }.
  
End Pure.

Section EmbedPropPure.

  Context {A : Type} `{HIL: ILogic A} {HPropOp: EmbedOp Prop A} {HProp: Embed Prop A}.
  Context {BILOPA : BILOperators A} {BILA : BILogic A}. 

  Instance EmbedPropPure (P : Prop) : Pure (embed P).
  Proof.
  	split; intros.
  	+ etransitivity; [rewrite embedPropExists |rewrite <- (embedPropExistsL P empSP)];
  		[reflexivity|].
  	  lexistsL Hp. rewrite sepSPC, <- bilexistsscL.
  	  lexistsR Hp. rewrite empSPR. apply landL2. reflexivity.
  	+ etransitivity; [rewrite embedPropExists |rewrite <- (embedPropExistsL P empSP)];
  		[reflexivity|].
  	  lexistsL Hp. rewrite <- bilexistsscL.
  	  lexistsR Hp. rewrite empSPR. apply landL1. reflexivity.
    + split.
      * apply landR.
        - apply bilsep. apply landL1. reflexivity.
        - rewrite <- embedPropExists', landC, landexistsDL, sepSPC, bilexistsscR.
          lexistsL Hp; lexistsR Hp; apply ltrueR.
      * rewrite <- embedPropExists'.
      	lexistsL Hp. apply landL1. apply bilsep. apply landR; 
      	  [reflexivity | lexistsR Hp; apply ltrueR].
	+ apply limplAdj. rewrite <- embedPropExists'.
	  lexistsL Hp. apply landL1.
	  rewrite siexistsE. lforallL Hp.
	  transitivity ((ltrue -* Q) ** empSP); [apply empSPR|].
	  apply wandSPL. apply ltrueR. reflexivity.
  Qed.
  
End EmbedPropPure.

