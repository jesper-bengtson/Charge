Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Map.FMapPositive.
Require Import MirrorCore.CTypes.CoreTypes.
Require Import MirrorCore.RTac.PApply.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprSubst.
Require Import MirrorCore.SymI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require Import MirrorCore.PLemma.

Section PApplyTac.
  Context {typ' : nat -> Set} {func : Set}.
  Let typ := ctyp typ'.
  Context {RType_typ : RType typ}.
  Context {Typ2_typ : Typ2 RType_typ RFun}.
  Context {Typ0_typ : Typ0 RType_typ Prop}.
  Context {RSym_func : @RSym _ RType_typ func}.

  Context (unify_func : PolyInst.sym_unifier (typ := typ) (sym := func)).

  Definition PAPPLY (plem : PolyLemma typ (expr typ func) (expr typ func)) :
    Core.rtac typ (expr typ func) :=
    PAPPLY
      (fun subst SS SU =>
         @exprUnify subst typ func RType_typ RSym_func Typ2_typ
                    SS SU 10) unify_func plem.

End PApplyTac.

Arguments PAPPLY {_ _ _ _ _ _} _ _ _ _ _.