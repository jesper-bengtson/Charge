Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.PreFun.

Require Import MirrorCore.TypesI.

Require Import Coq.Strings.String.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Class ListType (typ : Type) := {
  tyList : typ -> typ
}.

Section ListTypeD.
	Context {typ : Type} {HT : ListType typ} {HR : RType typ}.
	
	Class ListTypeD := {
	  btList : forall t, typD (tyList t) = list (typD t)
	}.
	
End ListTypeD.
