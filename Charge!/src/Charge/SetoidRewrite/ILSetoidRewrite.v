Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.SymI.

Require Import ExtLib.Core.RelDec.

Require Import Charge.SetoidRewrite.AutoSetoidRewrite.
Require Import Charge.SetoidRewrite.Base.
Require Import Charge.ModularFunc.BaseFunc.
Require Import Charge.ModularFunc.ILogicFunc.

Require Import Charge.Logics.ILogic.

Section ILSetoidRewrite.
	Context {typ func : Type} {RType_typ : RType typ}.
	Context {HIL : ILogicFunc typ func} {HB : BaseFunc typ func}.
	Context {RelDec_func : RelDec (@eq (expr typ func))}.
	Context {ilogic : forall t : typ, option (ILogicOps (typD t))}.
	Context {HT2 : Typ2 RType_typ Fun}.
	Context {HT0 : Typ0 _ Prop}.
	Context {RSym_func : RSym func}.

    Let tyProp : typ := @typ0 _ _ _ _.
	
	Let Rbase := expr typ func.

  Definition il_respects (e : Rbase) (_ : list (RG Rbase))
	   (rg : RG Rbase) : m (expr typ func) :=
	   match ilogicS (typ := typ) (func := expr typ func) e with
		 | Some (ilf_and l) => 
		 	 rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg 
			         (RGrespects (RGinj (fEntails l)) 
			         (RGrespects (RGinj (fEntails l)) 
			         (RGinj (fEntails l)))))
				 (fun _ => rg_ret (fAnd l))
		 | Some (ilf_or l) => 
			 rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg 
			         (RGrespects (RGinj (fEntails l)) 
			         (RGrespects (RGinj (fEntails l))
			         (RGinj (fEntails l)))))
				 (fun _ => rg_ret (fOr l))
		 | Some (ilf_entails l) => 
			 rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg 
			                  (RGrespects (RGflip (RGinj (fEntails l))) 
			                  (RGrespects (RGinj (fEntails l)) 
			                  (RGinj (fEntails tyProp)))))
				 (fun _ => rg_ret (fEntails l))
		 | Some (ilf_impl l) => 
			 rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg 
			                  (RGrespects (RGflip (RGinj (fEntails l))) 
			                  (RGrespects (RGinj (fEntails l)) 
			                  (RGinj (fEntails l)))))
				 (fun _ => rg_ret (fImpl l))
		 | Some (ilf_exists t l) => 
			 rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg 
			                  (RGrespects (RGrespects (RGinj (fEq t))
				 	 	                              (RGinj (fEntails l)))
						                  (RGinj (fEntails l))))
						                 
				 (fun _ => rg_ret (fExists t l))
(*		 | Some (ilf_true l) => rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGinj (fEntails l)))
			 	(fun _ => rg_ret (fTrue l))
		 | Some (ilf_false l) => rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGinj (fEntails l)))
			 	(fun _ => rg_ret (fFalse l))*)
		 | _ => rg_fail
	 end.

  Definition il_respects_reflexive (e : Rbase) (_ : list (RG Rbase))
	   (rg : RG Rbase) : m (expr typ func) :=
  	match typeof_expr nil nil e with
      | Some t => match ilogic t with
  				    | Some _ => 
  				      rg_plus 
  				        (rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGinj (fEntails t)))
					      (fun _ => rg_ret e))
  				        (rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGflip (RGinj (fEntails t))))
					      (fun _ => rg_ret e))
  				    | None => rg_fail
  				  end
  	  | None => rg_fail
  	end.
(*
	   rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGinj (fEntails l)))
	   	 (fun _ => rg_ret e).

  Definition il_respects_reflexive := fold_right (fun t acc => sr_combine (il_respects_reflexive_aux t) acc) 
  	(fun _ _ _ => rg_fail).
*)
Definition eq_respects :=
  fun (e : expr typ func) (_ : list (AutoSetoidRewrite.RG Rbase))
      (rg : AutoSetoidRewrite.RG Rbase) =>
    match baseS e with
      | Some (pEq t) =>
        rg_bind
          (AutoSetoidRewrite.unifyRG
             (RelDec.rel_dec (equ:=@eq (expr typ func))) rg
             (AutoSetoidRewrite.RGrespects
                (AutoSetoidRewrite.RGinj e)
                (AutoSetoidRewrite.RGrespects
                   (AutoSetoidRewrite.RGinj e)
                   (AutoSetoidRewrite.RGinj (fEntails tyProp)))))
          (fun _ : AutoSetoidRewrite.RG (expr typ func) => rg_ret e)
      | _ => rg_fail
    end.

Definition refl :=
  let Rbase := expr typ func in
  fun (e : expr typ func) (_ : list (AutoSetoidRewrite.RG Rbase))
      (rg : AutoSetoidRewrite.RG Rbase) =>
    match typeof_expr nil nil e with
      | Some t =>
        rg_bind
          (AutoSetoidRewrite.unifyRG (RelDec.rel_dec (equ:=@eq (expr typ func))) rg
                                     (AutoSetoidRewrite.RGinj (fEq t)))
          (fun _ : AutoSetoidRewrite.RG (expr typ func) => rg_ret e)
      | None => rg_fail
    end.

Definition il_rewrite_respects :=    
    sr_combine il_respects
               (sr_combine il_respects_reflexive (sr_combine eq_respects refl)).
                                                    
End ILSetoidRewrite.

Implicit Arguments il_rewrite_respects [[HIL] [HB] [RelDec_func] [RType_typ] [HT2] [HT0] [RSym_func]].
