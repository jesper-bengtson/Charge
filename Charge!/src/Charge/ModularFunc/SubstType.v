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
  tyVal : typ
}.
