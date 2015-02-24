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
  Context {typ : Type} {HT : ListType typ} {HR : RType typ}.
	
  Class ListTypeD := {
    btList : forall t, typD (tyList t) = list (typD t);
    
    tyList_inj : forall t u, Rty (tyList t) (tyList u) -> Rty t u
  }.

End ListTypeD.

Section ListTypeD'.
  Context `{LTD : ListTypeD}.
 
  Definition listD (t : typ) (p : typD (tyList t)) : list (typD t) :=
    eq_rect _ id p _ (btList t).
    
  Definition listD_sym (t : typ) (p : list (typD t)) : typD (tyList t) :=
    eq_rect _ id p _ (eq_sym (btList t)).
    
    
  Lemma listD_inv (t : typ) (lst : list (typD t)) : listD t (listD_sym t lst) = lst.
  Proof.
    unfold listD, listD_sym, eq_rect, eq_sym, id.
    destruct (btList t). reflexivity.
  Qed.
End ListTypeD'.  

Implicit Arguments listD [[typ] [HT] [HR] [LTD] [t]].
Implicit Arguments listD_sym [[typ] [HT] [HR] [LTD] [t]].

Ltac list_inj :=
  match goal with
    | H : tyList _ = tyList _ |- _ => apply tyList_inj in H; unfold Rty in H; subst
  end.
