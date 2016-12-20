Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprSubst.

Section MinifyTac.
  Context {typ func : Set}.
  Context {RType_typ : RType typ}.
  Context {EU : ExprUVar (expr typ func)}.
  Context {E : @Expr _ RType_typ (expr typ func)}.

  Definition MINIFY :=
    @MINIFY typ (expr typ func) RType_typ E EU.

End MinifyTac.

Implicit Arguments MINIFY [[RType_typ] [E] [EU]].
