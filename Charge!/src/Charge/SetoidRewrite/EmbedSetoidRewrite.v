Require Import MirrorCore.Lambda.ExprCore.

Require Import ExtLib.Core.RelDec.

Require Import Charge.SetoidRewrite.AutoSetoidRewrite.
Require Import Charge.SetoidRewrite.Base.
Require Import Charge.ModularFunc.BaseFunc.
Require Import Charge.ModularFunc.ILogicFunc.
Require Import Charge.ModularFunc.EmbedFunc.

Section EmbedSetoidRewrite.
  Context {typ func : Type} {RType_typ : RType typ}.
  Context {HIL : ILogicFunc typ func} {HB : BaseFunc typ func}.
  Context {HE : EmbedFunc typ func}.
  Context {RelDec_func : RelDec (@eq (expr typ func))}.

  Let Rbase := expr typ func.

  Definition embed_respects (e : Rbase) (_ : list (RG Rbase))
	     (rg : RG Rbase) : m (expr typ func) :=
    match embedS (typ := typ) (func := expr typ func) e with
      | Some (eilf_embed t u) => 
	rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg
	   	 	 (RGrespects (RGinj (fEntails t))
	   	 		     (RGinj (fEntails u))))
	   	(fun _ => rg_ret (fEmbed t u))
      | _ => rg_fail
    end.

End EmbedSetoidRewrite.