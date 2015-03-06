Require Import Charge.ModularFunc.OpenFunc.
Require Import Charge.ModularFunc.BaseType.
Require Import Charge.ModularFunc.SubstType.

Require Import Charge.Tactics.Base.MirrorCoreTacs.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.ExprI.

Local Notation "'tyStack'" := (typ2 tyString tyVal).

Ltac of_apply_subst_type :=
  match goal with
    | H1 : open_funcS ?e = Some (of_apply_subst ?t) |- _ =>
      match goal with
        | _ : ExprDsimul.ExprDenote.funcAs e (typ2 (typ2 tyStack t) (typ2 tySubst (typ2 tyStack t))) = Some _ |- _ => fail 1
        | _ : ExprDsimul.ExprDenote.exprD' _ _ (typ2 (typ2 tyStack t) (typ2 tySubst (typ2 tyStack t))) e = Some _ |- _ => fail 1
        | H2 : ExprDsimul.ExprDenote.funcAs e _ = Some _ |- _ =>
  	  	  let H := fresh "H" in
	        pose proof (of_apply_subst_func_type_eq _ _ H1 H2) as H; try (r_inj H); repeat clear_eq; subst
	    | H2 : ExprDsimul.ExprDenote.exprD' _ _ _ e = Some _ |- _ =>
	      let H := fresh "H" in
	        pose proof (of_apply_subst_type_eq _ _ H1 H2) as H; try (r_inj H); repeat clear_eq; subst
	  end
  end.

Ltac of_apply_subst_expr :=
  match goal with
    | H1 : open_funcS ?e = Some (of_apply_subst ?t) |- _ => 
      match goal with
        | _ : ExprDsimul.ExprDenote.exprD' _ _ (typ2 (typ2 tyStack t) (typ2 tySubst (typ2 tyStack t))) _ =
          Some (fun _ _ => applySubstD _ t) |- _ => fail 1
        | _ : ExprDsimul.ExprDenote.funcAs _ (typ2 (typ2 tyStack t) (typ2 tySubst (typ2 tyStack t))) =
   		  Some (applySubstD _ t) |- _ => fail 1
		| H2 : ExprDsimul.ExprDenote.funcAs e (typ2 (typ2 tyStack t) (typ2 tySubst (typ2 tyStack t))) = Some _ |- _ =>
	 	  let H := fresh "H" in pose proof(of_apply_subst_func_eq _ H1 H2); subst
		| H2 : ExprDsimul.ExprDenote.exprD' _ _ (typ2 (typ2 tyStack t) (typ2 tySubst (typ2 tyStack t))) e = Some _ |- _ =>
	  	  let H := fresh "H" in pose proof(of_apply_subst_eq _ H1 H2); subst
	 end
(*    | H : ExprDsimul.ExprDenote.exprD' _ _ (tyList ?t) (mkNoDup ?t _ _) = Some _ |- _ =>
	  pose proof (mkNoDupD _ _ _ H); clear H; (repeat destruct_match_oneres)*)
  end.

Ltac bf_forward_step :=
  match goal with 
    | H : Some _ = open_funcS _ |- _ =>  symmetry in H
    | _ => 
       first [
        of_apply_subst_type |
        of_apply_subst_expr
      ]
  end.
    
Ltac bf_rewrite_in_match :=
  match goal with 
  (*  | |- context [typeof_sym (fConst ?t ?c)] =>
        rewrite (BaseFunc_typeOk _ (bf_fConstOk _ _)); simpl     *)
    | |- context [ExprDsimul.ExprDenote.exprD' _ _ (typ2 (typ2 tyStack t) (typ2 tySubst (typ2 tyStack t))) (mkApplySubst ?t)] =>
      rewrite mkApplySubst_sound      
  end.