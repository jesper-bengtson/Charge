Require Import ExtLib.Core.RelDec.

Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprSubst.
Require Import MirrorCore.SymI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.Lambda.ExprUnify_simul.

Section AutoTac.
  Context {typ func : Type}.
  Context {RType_typ : RType typ}.
  Context {Typ0_typ : Typ0 RType_typ Prop}.
  Context {Typ2_typ : Typ2 RType_typ RFun}.
  Context {RSym_func : @RSym _ RType_typ func}.
  Context {E : @Expr _ RType_typ (expr typ func)}.
  Context {EU : ExprUVar (expr typ func)}.

  Definition APPLY :=
    @APPLY typ (expr typ func) RType_typ Typ0_typ E EU
           (fun subst SS SU tus tvs n l r t s =>
              @exprUnify subst typ func RType_typ RSym_func Typ2_typ
                         SS SU 10 tus tvs n l r t s).

End AutoTac.

Implicit Arguments APPLY [[RType_typ] [Typ2_typ] [Typ0_typ] [RSym_func] [E] [EU]].
