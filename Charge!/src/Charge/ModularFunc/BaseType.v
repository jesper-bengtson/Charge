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
	  btProd : forall t1 t2, typD (tyProd t1 t2) = (typD t1 * typD t2)%type;

      tyProd_inj : forall t u t' u', Rty (tyProd t u) (tyProd t' u') -> Rty t t' /\ Rty u u'
	}.
	
End BaseTypeD.

Implicit Arguments BaseTypeD [[typ] [HR]].

Ltac prod_inj :=
  match goal with
    | typ : Type |- _ =>
      match goal with
        | BT : BaseType typ, RType_typ : RType typ |- _ =>
          match goal with
            | _ : BaseTypeD BT, H : tyProd _ _ = tyProd _ _ |- _ => apply tyProd_inj in H; unfold Rty in H; destruct H; subst
          end
      end
  end.

Section BaseTypeD'.
  Context {typ : Type} {BT : BaseType typ} {RType_typ : RType typ} {BTD : BaseTypeD BT}.
 
  Definition natD (n : typD tyNat) : nat :=
    trmD n btNat.
 
  Definition boolD (b : typD tyBool) : bool :=
    trmD b btBool.

  Definition stringD (s : typD tyString) : string :=
    trmD s btString.
    
  Definition pairE {A B : Type} {t u : typ} (e1 : typD t = A) (e2 : typD u = B) : typD (tyProd t u) = (A * B)%type :=
    eq_ind (typD t) (fun X : Type => typD (tyProd t u) = (X * B)%type)
      (eq_ind (typD u) (fun Y : Type => typD (tyProd t u) = (typD t * Y)%type)
         (btProd t u) B e2) A e1.
    
    
  Definition natR (n : nat) : typD tyNat :=
    trmR n btNat.

  Definition boolR (b : bool) : typD tyBool :=
    trmR b btBool.

  Definition stringR (s : string) : typD tyString :=
    trmR s btString.

  Definition prodD t u (p : typD (tyProd t u)) : typD t * typD u :=
    trmD p (btProd t u).
	  
  Definition prodR t u (p : typD t * typD u) : typD (tyProd t u) :=
    trmR p (btProd t u).

End BaseTypeD'.  