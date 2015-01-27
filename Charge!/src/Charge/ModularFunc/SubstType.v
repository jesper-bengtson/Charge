Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.PreFun.

Require Import MirrorCore.TypesI.

Require Import Charge.Open.Subst.
Require Import Charge.Open.Stack.
Require Import Charge.ModularFunc.BaseType.

Require Import Coq.Strings.String.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Class SubstType (typ : Type) := {
  tyVal : typ;
  tySubst : typ
}.

Section SubstTypeD.
	Context {typ : Type} {HT : SubstType typ} {HR : RType typ}.
	Context {VN : ValNull (typD tyVal)}.
	Context {BT : BaseType typ}.

	Class SubstTypeD := {
	  stSubst : typD tySubst = @subst (typD tyString) (typD tyVal)
	}.
	
End SubstTypeD.
