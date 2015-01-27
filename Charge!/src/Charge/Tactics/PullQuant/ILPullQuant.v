Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.Red.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.TypesI.

Require Import ExtLib.Core.RelDec.

Require Import Charge.SetoidRewrite.Base.
Require Import Charge.SetoidRewrite.AutoSetoidRewrite.
Require Import Charge.ModularFunc.ILogicFunc.
Require Import Charge.Logics.ILogic.

Section ILPullQuant.
  Context {typ func : Type} {HIL : ILogicFunc typ func}.
  Context {RType_typ : RType typ}.
  Context {RelDec_func : RelDec (@eq (expr typ func))}.

  Let Rbase := expr typ func.

  Variable inhabited : typ -> bool.  
  Variable inhabited_sound : forall t, inhabited t = true -> Inhabited (typD t).

  Variable rg_eq : typ -> expr typ func.

  Definition rw_under_exists (t : typ) (l : typ) (rw : rewriter _) :=
    rw_under (RGinj (rg_eq t))
             (fun e rvars rg => rg_fmap (mkExists t l) (rw e rvars rg)).

  Definition il_match_plus_l (rw : @rw_type typ func) (e : expr typ func)
             (rvars : list (RG (expr typ func))) (rg : RG Rbase) : m (expr typ func) :=
  match e with
    | App (App a (App b (Abs _ P))) Q =>
      let Q' := lift 0 1 Q in
      match ilogicS (typ := typ) (func := expr typ func) a, ilogicS b with 
      	| Some (ilf_and _), Some (ilf_exists t l) =>
	  rg_plus
	    (rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGflip (RGinj (fEntails l))))
	             (fun _ => rw_under_exists t l rw (mkAnd l P Q') rvars rg))
	    (rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGinj (fEntails l)))
	             (fun _ => rw_under_exists t l rw (mkAnd l P Q') rvars rg))

(*(fun _ => rg_ret (mkExists t l (mkAnd l P Q)))) *)
      	| Some (ilf_or _), Some (ilf_exists t l) =>
      	  let rewrite_rl :=
	      rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGflip (RGinj (fEntails l))))
		      (fun _ => rw_under_exists t l rw (mkOr l P Q') rvars rg)
(* (fun _ => rg_ret (mkExists t l (mkOr l P Q))) *)in
	  if inhabited t then
	    rg_plus 
	      rewrite_rl 
	      (rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGinj (fEntails l)))
		       (fun _ => rw_under_exists t l rw (mkOr l P Q') rvars rg))
(* (fun _ => rg_ret (mkExists t l (mkOr l P Q)))) *)
	  else
	    rewrite_rl
	| _, _ => rg_fail
      end
    | _ => rg_fail
  end.

Definition il_match_plus_r (rw : @rw_type typ func)
           (e : expr typ func) (rvars : list (RG (expr typ func))) (rg : RG Rbase) : m (expr typ func) :=
  match e with
   | App (App a P) (App b (Abs _ Q)) =>
   	 let P' := lift 0 1 P in
     match ilogicS a, ilogicS b with
       | Some (ilf_and _), Some (ilf_exists t l) =>
	      rg_plus
	        (rg_bind
	          (unifyRG (@rel_dec (expr typ func) _ _ ) rg (RGinj (fEntails l)))
	            (fun _ => rw_under_exists t l rw (mkAnd l P' Q) rvars rg))
  	        (rg_bind
	          (unifyRG (@rel_dec (expr typ func) _ _) rg (RGflip (RGinj (fEntails l))))
	            (fun _ => rw_under_exists t l rw (mkAnd l P' Q) rvars rg))
       | Some (ilf_or _), Some (ilf_exists t l) =>
         let rewrite_rl := 
		   rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGflip (RGinj (fEntails l))))
		     (fun _ => rw_under_exists t l rw (mkOr l P' Q) rvars rg) in
		   if inhabited t then
		     rg_plus
		       rewrite_rl
		       (rg_bind (unifyRG (@rel_dec (expr typ func) _ _ ) rg (RGinj (fEntails l)))
		         (fun _ => rw_under_exists t l rw (mkOr t P' Q) rvars rg))
		   else
		     rewrite_rl
	   | _, _ => rg_fail
	 end
   | _ => rg_fail
 end.

Definition il_match_plus := sr_combineK il_match_plus_l il_match_plus_r.

End ILPullQuant.

Implicit Arguments il_match_plus [[typ] [func] [HIL] [RelDec_func]].
