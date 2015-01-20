Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprSubst.

Section InstantiateTac.
	Context {typ func : Type}.
	Context {EU : ExprUVar (expr typ func)}.

	Definition INSTANTIATE := 
		@INSTANTIATE typ (expr typ func) EU.

End InstantiateTac.

Implicit Arguments INSTANTIATE [[EU]].