Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.PreFun.
Require Import ExtLib.Data.String.
  
Require Import MirrorCore.TypesI.

Require Import Charge.ModularFunc.Denotation.

Require Import Coq.Strings.String.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Polymorphic Definition BTType := Type.

Class BaseType (typ : BTType) := {
  tyNat  : typ;
  tyBool : typ;
  tyString : typ;
  tyProd : typ -> typ -> typ
}.
Print RType.
Section BaseTypeD.
	Context {typ : BTType} {HT : BaseType typ} {HR : RType typ}.
	
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
  Context {typ : BTType} {BT : BaseType typ} {RType_typ : RType typ} {BTD : BaseTypeD BT}.
 
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
    trmD p (pairE (t := t) (u := u) eq_refl eq_refl).
	  
  Definition prodR t u (p : typD t * typD u) : typD (tyProd t u) :=
    trmR p (pairE (t := t) (u := u) eq_refl eq_refl).

  Lemma prodDR (t u : typ) A B C D (x : A) (y : B) (e1 : typD t = A) (e2 : typD u = B) (e3 : typD t = C) (e4 : typD u = D) :
    trmD (trmR (x, y) (pairE e1 e2)) (pairE e3 e4) = 
    (trmD (trmR x e1) e3, trmD (trmR y e2) e4).
  Proof.
    unfold trmD, trmR, pairE, eq_ind, eq_rect_r, eq_rect, eq_sym, id.
    clear.
    revert e1 e2 e3 e4.
    generalize (btProd t u).
    generalize dependent (tyProd t u).
    generalize dependent (typD t).
    generalize dependent (typD u).
    do 3 intros.
    generalize dependent (typD t0).
    intros; repeat subst. reflexivity.
  Qed.

End BaseTypeD'.  

Section BaseTypeRelDec.
  Context {typ : BTType} {BT : BaseType typ} {RType_typ : RType typ} {BTD : BaseTypeD BT}.
  
  Global Instance RelDec_tyString : RelDec (@eq (typD tyString)) := {
    rel_dec a b := stringD a ?[ eq ] stringD b
  }.

  Lemma rel_dec_tyString_correct (a b : typD tyString) :
    a ?[ eq ] b = true <-> a = b.
  Proof.
    split; intros.
    + unfold rel_dec in H; simpl in H.
      rewrite rel_dec_correct in H.
      apply trmD_inj in H. apply H.
    + subst; unfold rel_dec; simpl; apply rel_dec_eq_true; [apply _| reflexivity].
  Qed.

  Global Instance RelDec_Correct_tyString : RelDec_Correct RelDec_tyString := {
    rel_dec_correct := rel_dec_tyString_correct
  }.

End BaseTypeRelDec.
