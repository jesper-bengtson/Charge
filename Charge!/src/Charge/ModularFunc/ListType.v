Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.PreFun.

Require Import MirrorCore.TypesI.

Require Import Coq.Strings.String.

Require Import Charge.ModularFunc.Denotation.

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

  Definition listE {A : Type} {t : typ} (e : typD t = A) : typD (tyList t) = list A :=
    eq_ind (typD t) (fun B : Type => typD (tyList t) = list B) (btList t) A e.

  Definition listD {A : Type} (t : typ) (lst : typD (tyList t)) : list (typD t) :=
    trmD lst (listE eq_refl).

  Definition listR {A : Type} (t : typ) (lst : typD (tyList t)) : list (typD t) :=
    trmR lst (eq_sym (listE eq_refl)).

End ListTypeD'.  

Implicit Arguments listE [[typ] [LT] [RType_typ] [LTD] [t]].

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