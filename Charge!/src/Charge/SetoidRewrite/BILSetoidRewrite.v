Require Import MirrorCore.Lambda.ExprCore.

Require Import ExtLib.Core.RelDec.

Require Import Charge.SetoidRewrite.AutoSetoidRewrite.
Require Import Charge.SetoidRewrite.Base.
Require Import Charge.ModularFunc.ILogicFunc.
Require Import Charge.ModularFunc.BILogicFunc.

Section BILSetoidRewrite.
  Context {typ func : Type} {HIL : ILogicFunc typ func} {HBIL : BILogicFunc typ func}.
  Context {RelDec_func : RelDec (@eq (expr typ func))}.

  Let Rbase := expr typ func.

  Definition bil_respects (e : Rbase) (_ : list (RG Rbase))
	   (rg : RG Rbase) : m (expr typ func) :=
	   match bilogicS (typ := typ) (func := expr typ func) e with
		 | Some (bilf_star l) => 
		 	 rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg 
			         (RGrespects (RGinj (fEntails l)) 
			         (RGrespects (RGinj (fEntails l)) 
			         (RGinj (fEntails l)))))
				 (fun _ => rg_ret (fStar l))
		 | Some (bilf_wand l) => 
			 rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg 
			                  (RGrespects (RGflip (RGinj (fEntails l))) 
			                  (RGrespects (RGinj (fEntails l)) 
			                  (RGinj (fEntails l)))))
				 (fun _ => rg_ret (fWand l))
		 | Some (bilf_emp l) => rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGinj (fEntails l)))
			 	(fun _ => rg_ret (fEmp l))
		 | _ => rg_fail
	 end.

End BILSetoidRewrite.