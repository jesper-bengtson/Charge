Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.PreFun.

Require Import MirrorCore.TypesI.

Require Import Charge.ModularFunc.Denotation.

Require Import Coq.Strings.String.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.


Class BaseType (typ : Type) := {
  tyNat  : typ;
  tyBool : typ;
  tyString : typ;
  tyPair : typ -> typ -> typ
}.

Section BaseTypeD.
	Context {typ : Type} {HT : BaseType typ} {HR : RType typ}.
	
	Class BaseTypeD := {
	  btNat : typD tyNat = nat;
	  btBool : typD tyBool = bool;
	  btString : typD tyString = string;
	  btPair : forall t1 t2, typD (tyPair t1 t2) = (typD t1 * typD t2)%type
	}.
	
End BaseTypeD.

Section BaseTypeD'.
  Context `{BTD : BaseTypeD}.
 
  Definition natD (n : typD tyNat) : nat :=
    eq_rect _ id n _ btNat.

  Definition boolD (b : typD tyBool) : bool :=
    eq_rect _ id b _ btBool.

  Definition stringD (s : typD tyString) : string :=
    eq_rect _ id s _ btString.

  Definition pairD (t1 t2 : typ) (p : typD (tyPair t1 t2)) : (typD t1 * typD t2)%type :=
    eq_rect _ id p _ (btPair t1 t2).
    
End BaseTypeD'.  