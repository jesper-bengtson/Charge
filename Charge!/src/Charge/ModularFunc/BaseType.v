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
  tyProd : typ -> typ -> typ
}.

Section BaseTypeD.
	Context {typ : Type} {HT : BaseType typ} {HR : RType typ}.
	
	Class BaseTypeD := {
	  btNat : typD tyNat = nat;
	  btBool : typD tyBool = bool;
	  btString : typD tyString = string;
	  btProd : forall t1 t2, typD (tyProd t1 t2) = (typD t1 * typD t2)%type
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

  Definition prodD (t1 t2 : typ) (p : typD (tyProd t1 t2)) : (typD t1 * typD t2)%type :=
    eq_rect _ id p _ (btProd t1 t2).
    
  Definition natR (n : nat) : typD tyNat :=
    eq_rect _ id n _ (eq_sym btNat).

  Definition boolR (b : bool) : typD tyBool :=
    eq_rect _ id b _ (eq_sym btBool).

  Definition stringR (s : string) : typD tyString :=
    eq_rect _ id s _ (eq_sym btString).

  Definition prodR (t1 t2 : typ) (p : (typD t1 * typD t2)%type) : typD (tyProd t1 t2) :=
    eq_rect _ id p _ (eq_sym (btProd t1 t2)).
    
    
  Lemma natDR n : natD (natR n) = n.
  Proof.
    unfold natD, natR, eq_rect_r, eq_rect, eq_sym, id.
    destruct btNat; reflexivity.
  Qed.

  Lemma natRD n : natR (natD n) = n.
  Proof.
    unfold natD, natR, eq_rect_r, eq_rect, eq_sym, id.
    destruct btNat; reflexivity.
  Qed.

  Lemma boolDR b : boolD (boolR b) = b.
  Proof.
    unfold boolD, boolR, eq_rect_r, eq_rect, eq_sym, id.
    destruct btBool; reflexivity.
  Qed.

  Lemma boolRD b : boolR (boolD b) = b.
  Proof.
    unfold boolD, boolR, eq_rect_r, eq_rect, eq_sym, id.
    destruct btBool; reflexivity.
  Qed.
  
  Lemma stringDR s : stringD (stringR s) = s.
  Proof.
    unfold stringD, stringR, eq_rect_r, eq_rect, eq_sym, id.
    destruct btString; reflexivity.
  Qed.

  Lemma stringRD s : stringR (stringD s) = s.
  Proof.
    unfold stringD, stringR, eq_rect_r, eq_rect, eq_sym, id.
    destruct btString; reflexivity.
  Qed.

  Lemma prodDR t u p : prodD t u (prodR t u p) = p.
  Proof.
    unfold prodD, prodR, eq_rect_r, eq_rect, eq_sym, id.
    destruct (btProd t u); reflexivity.
  Qed.

  Lemma prodRD t u p : prodR t u (prodD t u p) = p.
  Proof.
    unfold prodD, prodR, eq_rect_r, eq_rect, eq_sym, id.
    destruct (btProd t u); reflexivity.
  Qed.

End BaseTypeD'.  