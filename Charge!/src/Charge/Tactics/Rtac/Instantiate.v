Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprSubst.

Section InstantiateTac.
	Context {typ func : Type}.
	Context {RType_typ : RType typ}.
	Context {E : @Expr _ RType_typ (expr typ func)}.

	Definition INSTANTIATE := 
		@INSTANTIATE typ (expr typ func) RType_typ E.

End InstantiateTac.

Implicit Arguments INSTANTIATE [[RType_typ] [E]].