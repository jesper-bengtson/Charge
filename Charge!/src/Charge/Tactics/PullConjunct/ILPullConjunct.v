Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.Red.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.TypesI.

Require Import ExtLib.Core.RelDec.

Require Import Charge.SetoidRewrite.Base.
Require Import Charge.SetoidRewrite.AutoSetoidRewrite.
Require Import Charge.ModularFunc.ILogicFunc.

Require Import Charge.Logics.ILogic.

Section ILPullConjunct.
  Context {typ func : Type} {HIL : ILogicFunc typ func}.
  Context {RType_typ : RType typ}.
   Context {RelDec_func : RelDec (@eq (expr typ func))}.

  Let Rbase := expr typ func.

  Variable target : expr typ func -> bool.  
Print rewriter.
Check @rewriter.

  Definition rw_under_and (l : typ) (P : expr typ func) (rw : rewriter _) : rewriter _ :=
    fun e rvars rg => rg_fmap (typ := typ) (func := func) (mkAnd l P) (rw e rvars rg).

Definition il_pull_conjunct_l (rw : @rw_type typ func) (e : expr typ func) (rvars : list (RG (expr typ func))) (rg : RG Rbase) : m (expr typ func) :=
  match e with
    | App (App a P) (App (App b Q) R) =>
      match ilogicS (typ := typ) (func := expr typ func) a, ilogicS b with
      	| Some (ilf_and l), Some (ilf_and _) =>
      		match target Q with
      			| true => rg_plus
                   (rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGflip (RGinj (fEntails l))))
                      (fun _ => rw_under_and l Q rw (mkAnd l P R) rvars rg))
				   (rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGinj (fEntails l)))
				      (fun _ => rw_under_and l Q rw (mkAnd l P R) rvars rg))      			
      		    | _ => rg_fail
      		end
      	| _, _ => rg_fail
      end
    | _ => rg_fail
  end.

Definition il_pull_conjunct_r (rw : @rw_type typ func) (e : expr typ func) (rvars : list (RG (expr typ func))) (rg : RG Rbase) : m (expr typ func) :=
  match e with
    | App (App a (App (App b P) Q)) R =>
      match ilogicS (typ := typ) (func := expr typ func) a, ilogicS b with
      	| Some (ilf_and l), Some (ilf_and _) =>
      		match target P with
      			| true => rg_plus
	               (rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGflip (RGinj (fEntails l))))
	                 (fun _ => rw_under_and l P rw (mkAnd l Q R) rvars rg))
				   (rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGinj (fEntails l)))
	                 (fun _ => rw_under_and l P rw (mkAnd l Q R) rvars rg))
      		    | _ => rg_fail
      		end
      	| _, _ => rg_fail
      end
    | _ => rg_fail
  end.

Variable gs : logic_ops.

Definition il_pull_conjunct_sym (rw : @rw_type typ func) (e : expr typ func) (rvars : list (RG (expr typ func))) (rg : RG Rbase) : m (expr typ func) :=
  match e with
    | App (App a P) Q =>
      match ilogicS (typ := typ) (func := expr typ func) a with
      	| Some (ilf_and l) =>
      		match target Q with
      		  | true => rg_plus
		                  (rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGflip (RGinj (fEntails l))))
		                     (fun _ => rw_under_and l Q rw P rvars rg))
				 		  (rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGinj (fEntails l)))
		                     (fun _ => rw_under_and l Q rw P rvars rg))
      		  | _ => rg_fail
      		end
        | _ => rg_fail
      end
    | _ => rg_fail
  end.  

Definition il_pull_conjunct := sr_combineK il_pull_conjunct_sym (sr_combineK il_pull_conjunct_l il_pull_conjunct_r).

End ILPullConjunct.

Implicit Arguments il_pull_conjunct [[typ] [func] [HIL] [RelDec_func]].
