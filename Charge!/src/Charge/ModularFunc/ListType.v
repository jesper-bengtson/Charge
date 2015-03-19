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
  Context {typ : Type} {LT : ListType typ} {RType_typ : RType typ}.
	
  Class ListTypeD := {
    btList : forall t, typD (tyList t) = list (typD t);
    
    tyList_inj : forall t u, Rty (tyList t) (tyList u) -> Rty t u
  }.

End ListTypeD.

Implicit Arguments ListTypeD [[typ] [RType_typ]].

Section ListTypeD'.
  Context {typ : Type} {LT : ListType typ} {RType_typ : RType typ} {LTD : ListTypeD LT}.
(*
  Definition typD1 (t : typ) (f : typ -> typ) (g : Type -> Type) (p : typD (f t)) (e : typD (f t) = g (typD t)) : g (typD t)  :=
    eq_rect _ id p _ e.
 
 Require Import Charge.ModularFunc.BaseType.
 
  Definition typD2 (t u : typ) (f : typ -> typ -> typ) (g : Type -> Type -> Type) (p : typD (f t u)) (e : typD (f t u) = g (typD t) (typD u)) : g (typD t) (typD u) :=
    eq_rect _ id p _ e.
 
  Implicit Arguments typD1 [[t] [f] [g]].
  Implicit Arguments typD2 [[t] [u] [f] [g]].
 
  Definition listD (t : typ) (p : typD (tyList t)) : list (typD t) := typD1 p (btList t).
  Context {BT : BaseType typ} {BTD : BaseTypeD}.
  Definition pairD (t u : typ) (p : typD (tyProd t u)) : (typD t * typD u)%type := typD2 p (btProd t u).
  
  Program Definition test (a : typD (tyList (tyProd tyNat tyString))) : list (nat * string) := typD1 a _.
  Proof.
    apply typD1.
 *)
  Definition listD (t : typ) (p : typD (tyList t)) : list (typD t) := 
    eq_rect _ id p _ (btList t).
    
  Definition listR (t : typ) (p : list (typD t)) : typD (tyList t) :=
    eq_rect _ id p _ (eq_sym (btList t)).
    
    
  Lemma listDR (t : typ) (lst : list (typD t)) : listD t (listR t lst) = lst.
  Proof.
    unfold listD, listR, eq_rect, eq_sym, id.
    destruct (btList t). reflexivity.
  Qed.

  Lemma listRD (t : typ) (lst : typD (tyList t)) : listR t (listD t lst) = lst.
  Proof.
    unfold listD, listR, eq_rect, eq_sym, id.
    destruct (btList t). reflexivity.
  Qed.
  Require Import Charge.ModularFunc.BaseType.
  Check stringD.
Context {BT : BaseType typ} {BTD : BaseTypeD BT}.

  Definition listE {A : Type} {t : typ} (e : typD t = A) : typD (tyList t) = list A :=
    eq_ind (typD t) (fun B : Type => typD (tyList t) = list B) (btList t) A e.

  Definition pairE {A B : Type} {t u : typ} (e1 : typD t = A) (e2 : typD u = B) : typD (tyProd t u) = (A * B)%type :=
    eq_ind (typD t) (fun X : Type => typD (tyProd t u) = (X * B)%type)
      (eq_ind (typD u) (fun Y : Type => typD (tyProd t u) = (typD t * Y)%type)
         (btProd t u) B e2) A e1.

  Definition trmD {A B : Type} (p : A) (e : A = B) : B :=
    eq_rect _ id p _ e.
    
  Definition trmR {A B : Type} (p : B) (e : A = B) : A :=
    eq_rect_r id p e.
    
    
  Implicit Arguments trmD [[A] [B]].
  Implicit Arguments trmR [[A] [B]].

  Definition blurbel (lst : typD (tyList (tyProd tyNat tyString))) : list (nat * string) :=
    trmD lst (listE (pairE btNat btString)).
    
  Definition trm

  Definition listI {A : Type} {t : typ} (f : typD t -> A) (p : typD (tyList t)) : list A.
  Proof.
    pose proof (btList t).
    rewrite H in p.
    pose proof (cong (A := A)).
    eq_rect _ id p _ (cong f (btList t)).
    (eq_rect _ (fun t => f t) p _ (btList t)).
  Print eq_rect.  
  Definition pairI {A B : Type} {t u : typ} (f : typD t -> A) (g : typD u -> B) (p : typD (tyProd t u)) : A * B :=
    let x := eq_rect _ id p _ (btProd t u) in (f (fst x), g (snd x)).
  Definition blarbel (lst : typD (tyList (tyProd tyNat tyString))) : list (nat * String.string) :=
    listI (pairI natD stringD) lst.

End ListTypeD'.  

Implicit Arguments listD [[typ] [LT] [RType_typ] [LTD] [t]].
Implicit Arguments listR [[typ] [LT] [RType_typ] [LTD] [t]].

Ltac list_inj :=
  match goal with
    | typ : Type |- _ =>
      match goal with
        | LT : ListType typ, RType_typ : RType typ |- _ =>
          match goal with
            | _ : ListTypeD LT, H : tyList _ = tyList _ |- _ => apply tyList_inj in H; unfold Rty in H; subst
          end
      end
  end.
     
(*
This would be the ideal tactic, unfortunately it seems like LTac can not handle type class inference in a proper way
but everything has to be made explicit.

Ltac list_inj :=
  match goal with
    | H : tyList _ = tyList _ |- _ => apply tyList_inj in H; unfold Rty in H; subst
  end.
*)