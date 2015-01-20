Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.Red.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.TypesI.

Require Import ExtLib.Core.RelDec.

Require Import Charge.SetoidRewrite.Base.
Require Import Charge.SetoidRewrite.AutoSetoidRewrite.
Require Import Charge.ModularFunc.ILogicFunc.
Require Import Charge.ModularFunc.EmbedFunc.

Require Import Charge.Logics.ILogic.

Section EILPullQuant.
  Context {typ func : Type} {HIL : ILogicFunc typ func} {HB : EmbedFunc typ func}.
  Context {RType_typ : RType typ}.
  Context {RelDec_func : RelDec (@eq (expr typ func))}.

  Let Rbase := expr typ func.

  Variable rg_eq : typ -> expr typ func.

  Definition rw_under_exists (t : typ) (l : typ) (rw : rewriter _) :=
    rw_under (RGinj (rg_eq t))
             (fun e rvars rg => rg_fmap (mkExists t l) (rw e rvars rg)).

  Definition eil_match_plus (rw : rewriter _) (e : expr typ func) (rvars : list (RG (expr typ func))) (rg : RG Rbase) : m (expr typ func) :=
    match e with
      | App a (App b (Abs _ P)) =>
        match embedS (typ := typ) (func := expr typ func) a, ilogicS b with 
      	  | Some (eilf_embed u v), Some (ilf_exists t l) =>
	    rg_plus
	      (rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGflip (RGinj (fEntails v))))
	               (fun _ => rw_under_exists t v rw (mkEmbed u v P) rvars rg))
	      (rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGinj (fEntails v)))
	               (fun _ => rw_under_exists t v rw (mkEmbed u v P) rvars rg))
	  | _, _ => rg_fail
	end
      | _ => rg_fail
    end.

End EILPullQuant.

Implicit Arguments eil_match_plus [[typ] [func] [HIL] [HB] [RelDec_func]].
