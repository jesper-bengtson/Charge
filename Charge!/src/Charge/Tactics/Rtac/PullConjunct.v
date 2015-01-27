Require Import ExtLib.Core.RelDec.

Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.Subst.FMapSubst.
Require Import MirrorCore.Lambda.ExprSubst.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require MirrorCore.syms.SymEnv.
Require MirrorCore.syms.SymSum.

Require Import Charge.ModularFunc.BaseFunc.
Require Import Charge.ModularFunc.ILogicFunc.
Require Import Charge.SetoidRewrite.Base.
Require Import Charge.SetoidRewrite.ILSetoidRewrite.
Require Import Charge.Tactics.PullConjunct.ILPullConjunct.
Require Import Charge.Logics.ILogic.

Set Implicit Arguments.
Set Strict Implicit.

Section PullConjunct.
  Context (typ func : Type).
  Context {HIL : ILogicFunc typ func} {HB : BaseFunc typ func}.
  Context {RelDec_func : RelDec (@eq (expr typ func))}.
  Context {target : expr typ func -> bool}.
  Context {RType_typ : RType typ}.
  Context {Typ2_typ : Typ2 RType_typ Fun}.
  Context {Typ0_typ : Typ0 RType_typ Prop}.
  Context {RSym_func : RSym func}.
  Context {ilogic : forall t : typ, option (ILogicOps (typD t))}.
Check setoid_rewrite.
  Definition pull_conjunct vars := 
	setoid_rewrite vars _ fEntails rw_fail (il_rewrite_respects typ func ilogic) (il_pull_conjunct target).

  Definition PULLCONJUNCTL : rtac typ (expr typ func) :=
    fun tus tvs lus lvs c s e =>
      match e with
        | App (App f L) R =>
          match ilogicS f with
	        | Some (ilf_entails l) =>
	        	match pull_conjunct (getVars c) l L with
	        	  | Some (e', _) => More s (GGoal (mkEntails l e' R))
	        	  | _ => More s (GGoal e)
	        	end
	        | _ => More s (GGoal e)
	      end
        | _ => More s (GGoal e)
      end.

End PullConjunct.

Implicit Arguments PULLCONJUNCTL [[HIL] [HB] [RelDec_func] [RType_typ] [Typ2_typ] [Typ0_typ] [RSym_func]].