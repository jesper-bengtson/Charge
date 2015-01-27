Require Import ExtLib.Core.RelDec.

Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprSubst.
Require Import MirrorCore.SymI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.Lambda.ExprUnify_simul.

Section EAutoTac.
	Context {typ func : Type}.
	Context {RType_typ : RType typ}.
	Context {Typ2_typ : Typ2 RType_typ Fun}.
	Context {Typ0_typ : Typ0 RType_typ Prop}.
	Context {RSym_func : @RSym _ RType_typ func}.
	Context {EU : ExprUVar (expr typ func)}.
	Context {MA : MentionsAny (expr typ func)}.

	Definition EAPPLY := @EAPPLY typ (expr typ func) RType_typ Typ0_typ EU MA
                      (@vars_to_uvars _ _)
                      (fun subst SS SU tus tvs n l r t s =>
                         @exprUnify subst typ func RType_typ RSym_func Typ2_typ 
                                    SS SU 10 tus tvs n l r t s).

End EAutoTac.

Implicit Arguments EAPPLY [[RType_typ] [Typ2_typ] [Typ0_typ] [RSym_func] [EU] [MA]].