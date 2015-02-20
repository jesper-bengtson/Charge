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

Section ListTypeD'.
  Context `{LTD : ListTypeD}.
 
  Definition listD (t : typ) (p : typD (tyList t)) : list (typD t) :=
    eq_rect _ id p _ (btList t).
    
  Definition listD_inv (t : typ) (p : list (typD t)) : typD (tyList t) :=
    eq_rect _ id p _ (eq_sym (btList t)).
    
End ListTypeD'.  