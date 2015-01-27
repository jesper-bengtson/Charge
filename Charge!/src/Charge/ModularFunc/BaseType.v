Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.PreFun.

Require Import MirrorCore.TypesI.
Require Import Charge.Logics.ILogic.

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

