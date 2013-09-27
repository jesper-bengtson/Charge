Require Import Maps MapInterface MapFacts.
	 
Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Class ValNull := {
  val    : Type;
  null   :  val
}.

Definition stack {key : Type} {H : OrderedType key} {V : ValNull} := Map [key, val]. 