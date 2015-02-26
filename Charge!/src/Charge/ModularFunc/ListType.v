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
 
  Definition listD (t : typ) (p : typD (tyList t)) : list (typD t) :=
    eq_rect _ id p _ (btList t).
    
  Definition listD_sym (t : typ) (p : list (typD t)) : typD (tyList t) :=
    eq_rect _ id p _ (eq_sym (btList t)).
    
    
  Lemma listD_inv (t : typ) (lst : list (typD t)) : listD t (listD_sym t lst) = lst.
  Proof.
    unfold listD, listD_sym, eq_rect, eq_sym, id.
    destruct (btList t). reflexivity.
  Qed.

  Lemma listD_sym_inv (t : typ) (lst : typD (tyList t)) : listD_sym t (listD t lst) = lst.
  Proof.
    unfold listD, listD_sym, eq_rect, eq_sym, id.
    destruct (btList t). reflexivity.
  Qed.

End ListTypeD'.  

Implicit Arguments listD [[typ] [LT] [RType_typ] [LTD] [t]].
Implicit Arguments listD_sym [[typ] [LT] [RType_typ] [LTD] [t]].

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