Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.Red.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.TypesI.

Require Import ExtLib.Core.RelDec.

Require Import Charge.SetoidRewrite.Base.
Require Import Charge.SetoidRewrite.AutoSetoidRewrite.
Require Import Charge.ModularFunc.ILogicFunc.
Require Import Charge.ModularFunc.BILogicFunc.
Require Import Charge.Logics.BILogic.
Require Import Charge.Logics.ILogic.

Section BILPullQuant.
  Context {typ func : Type} {HIL : ILogicFunc typ func} {HBIL : BILogicFunc typ func}.
  Context {RType_typ : RType typ}.
  Context {RelDec_func : RelDec (@eq (expr typ func))}.

  Let Rbase := expr typ func.

  Variable rg_eq : typ -> expr typ func.

  Definition rw_under_exists (t : typ) (l : typ) (rw : rewriter _) :=
    rw_under (RGinj (rg_eq t))
             (fun e rvars rg => rg_fmap (mkExists t l) (rw e rvars rg)).

  Definition bil_match_plus_l (rw : rewriter _)
             (e : expr typ func) (rvars : list (RG (expr typ func))) (rg : RG Rbase) : m (expr typ func) :=
  match e with
    | App (App a (App b (Abs _ P))) Q =>
      let Q' := lift 0 1 Q in
      match bilogicS (typ := typ) (func := expr typ func) a, ilogicS b with 
      	| Some (bilf_star _), Some (ilf_exists t l) =>
	      rg_plus
	      (rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGflip (RGinj (fEntails l))))
	        (fun _ => rw_under_exists t l rw (mkStar l P Q') rvars rg))
	      (rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGinj (fEntails l)))
	        (fun _ => rw_under_exists t l rw (mkStar l P Q') rvars rg))
	    | _, _ => rg_fail
	  end
	| _ => rg_fail
  end.
  
Definition bil_match_plus_r (rw : rewriter _) (e : expr typ func)
           (rvars : list (RG (expr typ func))) (rg : RG Rbase) : m (expr typ func) :=
  match e with
   | App (App a P) (App b (Abs _ Q)) =>
   	 let P' := lift 0 1 P in
     match bilogicS a, ilogicS b with
       | Some (bilf_star _), Some (ilf_exists t l) =>
	      rg_plus
	        (rg_bind
	          (unifyRG (@rel_dec (expr typ func) _ _ ) rg (RGinj (fEntails l)))
	            (fun _ => rw_under_exists t l rw (mkStar l P' Q) rvars rg))
  	        (rg_bind
	          (unifyRG (@rel_dec (expr typ func) _ _) rg (RGflip (RGinj (fEntails l))))
	            (fun _ => rw_under_exists t l rw (mkStar l P' Q) rvars rg))
	   | _, _ => rg_fail
	 end
   | _ => rg_fail
 end.

Definition bil_match_plus := sr_combineK bil_match_plus_l bil_match_plus_r.

End BILPullQuant.