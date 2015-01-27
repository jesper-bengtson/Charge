Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprSubst.

Section InstantiateTac.
	Context {typ func : Type}.
	Context {EU : ExprUVar (expr typ func)}.

	Definition MINIFY := 
		@MINIFY typ (expr typ func) EU.

End InstantiateTac.

Implicit Arguments MINIFY [[EU]].