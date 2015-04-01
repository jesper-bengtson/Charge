Require Import Charge.ModularFunc.OpenFunc.
Require Import Charge.ModularFunc.BaseType.
Require Import Charge.ModularFunc.ListType.
Require Import Charge.ModularFunc.SubstType.

Require Import Charge.Tactics.Base.MirrorCoreTacs.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.ExprI.

Local Notation "'tyStack'" := (typ2 tyString tyVal).
Local Notation "'tySubst'" := (typ2 tyString (typ2 tyStack tyVal)).
Local Notation "'tyExpr'" := (typ2 tyStack tyVal).
Local Notation "'tySubstList'" := (tyList (tyProd tyString (typ2 tyStack tyVal))).

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
          Some (fun _ _ => applySubstD t) |- _ => fail 1
        | _ : ExprDsimul.ExprDenote.funcAs _ (typ2 (typ2 tyStack t) (typ2 tySubst (typ2 tyStack t))) =
   		  Some (applySubstD t) |- _ => fail 1
		| H2 : ExprDsimul.ExprDenote.funcAs e (typ2 (typ2 tyStack t) (typ2 tySubst (typ2 tyStack t))) = Some _ |- _ =>
	 	  let H := fresh "H" in pose proof(of_apply_subst_func_eq _ H1 H2); subst
		| H2 : ExprDsimul.ExprDenote.exprD' _ _ (typ2 (typ2 tyStack t) (typ2 tySubst (typ2 tyStack t))) e = Some _ |- _ =>
	  	  let H := fresh "H" in pose proof(of_apply_subst_eq _ H1 H2); subst
	 end
(*    | H : ExprDsimul.ExprDenote.exprD' _ _ (tyList ?t) (mkNoDup ?t _ _) = Some _ |- _ =>
	  pose proof (mkNoDupD _ _ _ H); clear H; (repeat destruct_match_oneres)*)
  end.

Ltac of_const_type :=
  match goal with
    | H1 : open_funcS ?e = Some (of_const ?t) |- _ =>
      match goal with
        | _ : ExprDsimul.ExprDenote.funcAs e (typ2 t (typ2 tyStack t)) = Some _ |- _ => fail 1
        | _ : ExprDsimul.ExprDenote.exprD' _ _ (typ2 t (typ2 tyStack t)) e = Some _ |- _ => fail 1
        | H2 : ExprDsimul.ExprDenote.funcAs e _ = Some _ |- _ =>
  	  	  let H := fresh "H" in
	        pose proof (of_const_func_type_eq _ _ H1 H2) as H; try (r_inj H); repeat clear_eq; subst
	    | H2 : ExprDsimul.ExprDenote.exprD' _ _ _ e = Some _ |- _ =>
	      let H := fresh "H" in
	        pose proof (of_const_type_eq _ _ H1 H2) as H; try (r_inj H); repeat clear_eq; subst
	  end
  end.

Ltac of_const_expr :=
  match goal with
    | H1 : open_funcS ?e = Some (of_const ?t) |- _ => 
      match goal with
        | _ : ExprDsimul.ExprDenote.exprD' _ _ (typ2 t (typ2 tyStack t)) _ =
          Some (fun _ _ => constD t) |- _ => fail 1
        | _ : ExprDsimul.ExprDenote.funcAs _ (typ2 t (typ2 tyStack t)) =
   		  Some (constD t) |- _ => fail 1
		| H2 : ExprDsimul.ExprDenote.funcAs e (typ2 t (typ2 tyStack t)) = Some _ |- _ =>
	 	  let H := fresh "H" in pose proof(of_const_func_eq _ H1 H2); subst
		| H2 : ExprDsimul.ExprDenote.exprD' _ _ (typ2 t (typ2 tyStack t)) e = Some _ |- _ =>
	  	  let H := fresh "H" in pose proof(of_const_eq _ H1 H2); subst
	 end
  end.
  
Ltac of_ap_type :=
  match goal with
    | H1 : open_funcS ?e = Some (of_ap ?t ?u) |- _ =>
      match goal with
        | _ : ExprDsimul.ExprDenote.funcAs e
   			  (typ2 (typ2 tyStack (typ2 t u))
                (typ2 (typ2 tyStack t) (typ2 tyStack u))) = Some _ |- _ => fail 1
        | _ : ExprDsimul.ExprDenote.exprD' _ _  
              (typ2 (typ2 tyStack (typ2 t u))
                (typ2 (typ2 tyStack t) (typ2 tyStack u))) e = Some _ |- _ => fail 1
        | H2 : ExprDsimul.ExprDenote.funcAs e _ = Some _ |- _ =>
  	  	  let H := fresh "H" in
	        pose proof (of_ap_func_type_eq _ _ H1 H2) as H; r_inj H; repeat clear_eq; subst
	    | H2 : ExprDsimul.ExprDenote.exprD' _ _ _ e = Some _ |- _ =>
	      let H := fresh "H" in
	        pose proof (of_ap_type_eq _ _ H1 H2) as H; r_inj H; repeat clear_eq; subst
	  end
  end.

Ltac of_ap_expr :=
  match goal with
    | H1 : open_funcS ?e = Some (of_ap ?t ?u) |- _ =>
      match goal with
        | _ : ExprDsimul.ExprDenote.exprD' _ _ 
              (typ2 (typ2 tyStack (typ2 t u))
                (typ2 (typ2 tyStack t) (typ2 tyStack u))) e =
          Some (fun _ _ => apD t u) |- _ => fail 1
        | _ : ExprDsimul.ExprDenote.funcAs e 
  			  (typ2 (typ2 tyStack (typ2 t u))
                (typ2 (typ2 tyStack t) (typ2 tyStack u))) =
   		  Some (apD t u) |- _ => fail 1
		| H2 : ExprDsimul.ExprDenote.funcAs e 
			   (typ2 (typ2 tyStack (typ2 t u))
                (typ2 (typ2 tyStack t) (typ2 tyStack u))) = Some _ |- _ =>
	 	  let H := fresh "H" in pose proof(of_ap_func_eq _ H1 H2); subst
		| H2 : ExprDsimul.ExprDenote.exprD' _ _ 
			   (typ2 (typ2 tyStack (typ2 t u))
                (typ2 (typ2 tyStack t) (typ2 tyStack u))) e = Some _ |- _ =>
	  	  let H := fresh "H" in pose proof(of_ap_eq _ H1 H2); subst
	 end
  end.

Ltac of_trunc_subst_type :=
  match goal with
    | H1 : open_funcS ?e = Some of_trunc_subst |- _ =>
      match goal with
        | _ : ExprDsimul.ExprDenote.funcAs e
   			  (typ2 (tyList (tyProd tyString tyExpr)) (typ2 tyString tyExpr)) = Some _ |- _ => fail 1
        | _ : ExprDsimul.ExprDenote.exprD' _ _  
              (typ2 (tyList (tyProd tyString tyExpr)) (typ2 tyString tyExpr)) e = Some _ |- _ => fail 1
        | H2 : ExprDsimul.ExprDenote.funcAs e _ = Some _ |- _ =>
  	  	  let H := fresh "H" in
	        pose proof (of_trunc_subst_func_type_eq _ _ H1 H2) as H; r_inj H; repeat clear_eq; subst
        | H2 : ExprDsimul.ExprDenote.exprD' _ _ _ _ e = Some _ |- _ =>
  	  	  let H := fresh "H" in
	        pose proof (of_trunc_subst_type_eq _ _ H1 H2) as H; r_inj H; repeat clear_eq; subst
	  end
  end.

Ltac of_trunc_subst_expr :=
  match goal with
    | H1 : open_funcS ?e = Some of_trunc_subst |- _ =>
      match goal with
        | _ : ExprDsimul.ExprDenote.exprD' _ _ 
              (typ2 (tyList (tyProd tyString tyExpr)) (typ2 tyString tyExpr)) e =
          Some (fun _ _ => truncSubstD) |- _ => fail 1
        | _ : ExprDsimul.ExprDenote.funcAs e 
  			  (typ2 (tyList (tyProd tyString tyExpr)) (typ2 tyString tyExpr)) =
   		  Some truncSubstD |- _ => fail 1
		| H2 : ExprDsimul.ExprDenote.funcAs e 
			   (typ2 (tyList (tyProd tyString tyExpr)) (typ2 tyString tyExpr)) = Some _ |- _ =>
	 	  let H := fresh "H" in pose proof(of_trunc_subst_func_eq _ H1 H2); subst
		| H2 : ExprDsimul.ExprDenote.exprD' _ _ 
			   (typ2 tyString (typ2 tyStack tyVal)) e = Some _ |- _ =>
	  	  let H := fresh "H" in pose proof(of_trunc_subst_eq _ H1 H2); subst
	 end
  end.

Ltac of_single_subst_type :=
  match goal with
    | H1 : open_funcS ?e = Some of_single_subst |- _ =>
      match goal with
        | _ : ExprDsimul.ExprDenote.funcAs e
   			  (typ2 (typ2 tyStack tyVal) (typ2 tyString tySubst)) = Some _ |- _ => fail 1
        | _ : ExprDsimul.ExprDenote.exprD' _ _  
              (typ2 (typ2 tyStack tyVal) (typ2 tyString tySubst)) e = Some _ |- _ => fail 1
        | H2 : ExprDsimul.ExprDenote.funcAs e _ = Some _ |- _ =>
  	  	  let H := fresh "H" in
	        pose proof (of_single_subst_func_type_eq _ _ H1 H2) as H; r_inj H; repeat clear_eq; subst
        | H2 : ExprDsimul.ExprDenote.exprD' _ _ _ _ e = Some _ |- _ =>
  	  	  let H := fresh "H" in
	        pose proof (of_single_subst_type_eq _ _ H1 H2) as H; r_inj H; repeat clear_eq; subst
	  end
  end.

Ltac of_single_subst_expr :=
  match goal with
    | H1 : open_funcS ?e = Some of_single_subst |- _ =>
      match goal with
        | _ : ExprDsimul.ExprDenote.exprD' _ _ 
              (typ2 (typ2 tyStack tyVal) (typ2 tyString tySubst)) e =
          Some (fun _ _ => singleSubstD) |- _ => fail 1
        | _ : ExprDsimul.ExprDenote.funcAs e 
  			  (typ2 (typ2 tyStack tyVal) (typ2 tyString tySubst)) =
   		  Some singleSubstD |- _ => fail 1
		| H2 : ExprDsimul.ExprDenote.funcAs e 
			   (typ2 (typ2 tyStack tyVal) (typ2 tyString tySubst)) = Some _ |- _ =>
	 	  let H := fresh "H" in pose proof(of_single_subst_func_eq _ H1 H2); subst
		| H2 : ExprDsimul.ExprDenote.exprD' _ _ 
			   (typ2 (typ2 tyStack tyVal) (typ2 tyString tySubst)) e = Some _ |- _ =>
	  	  let H := fresh "H" in pose proof(of_single_subst_eq _ H1 H2); subst
	 end
  end.

Ltac of_stack_get_type :=
  match goal with
    | H1 : open_funcS ?e = Some of_stack_get |- _ =>
      match goal with
        | _ : ExprDsimul.ExprDenote.funcAs e
   			  (typ2 tyString (typ2 (typ2 tyString tyVal) tyVal)) = Some _ |- _ => fail 1
        | _ : ExprDsimul.ExprDenote.exprD' _ _  
              (typ2 tyString (typ2 (typ2 tyString tyVal) tyVal)) e = Some _ |- _ => fail 1
        | H2 : ExprDsimul.ExprDenote.funcAs e _ = Some _ |- _ =>
  	  	  let H := fresh "H" in
	        pose proof (of_stack_get_func_type_eq _ _ H1 H2) as H; r_inj H; repeat clear_eq; subst
        | H2 : ExprDsimul.ExprDenote.exprD' _ _ _ _ e = Some _ |- _ =>
  	  	  let H := fresh "H" in
	        pose proof (of_stack_get_type_eq _ _ H1 H2) as H; r_inj H; repeat clear_eq; subst
	  end
  end.

Ltac of_stack_get_expr :=
  match goal with
    | H1 : open_funcS ?e = Some of_stack_get |- _ =>
      match goal with
        | _ : ExprDsimul.ExprDenote.exprD' _ _ 
              (typ2 tyString (typ2 (typ2 tyString tyVal) tyVal)) e =
          Some (fun _ _ => stack_getD) |- _ => fail 1
        | _ : ExprDsimul.ExprDenote.funcAs e 
  			  (typ2 tyString (typ2 (typ2 tyString tyVal) tyVal)) =
   		  Some stack_getD |- _ => fail 1
		| H2 : ExprDsimul.ExprDenote.funcAs e 
			   (typ2 tyString (typ2 (typ2 tyString tyVal) tyVal)) = Some _ |- _ =>
	 	  let H := fresh "H" in pose proof(of_stack_get_func_eq _ H1 H2); subst
		| H2 : ExprDsimul.ExprDenote.exprD' _ _ 
			   (typ2 tyString (typ2 (typ2 tyString tyVal) tyVal)) e = Some _ |- _ =>
	  	  let H := fresh "H" in pose proof(of_stack_get_eq _ H1 H2); subst
	 end
  end.

Ltac of_unfold := 
  first [
    progress (unfold applySubstD) |
    progress (unfold constD) |
    progress (unfold apD) | 
    progress (unfold truncSubstD) | 
    progress (unfold singleSubstD) |
    progress (unfold parSubstD) |
    progress (unfold stack_getD) |
    progress (unfold substD) |
    progress (unfold substR) |
    progress (unfold substListD)
  ].
  
  Ltac of_forward_step :=
  match goal with 
    | H : Some _ = open_funcS _ |- _ =>  symmetry in H
    | _ => 
       first [
        of_apply_subst_type |
        of_const_type |
        of_ap_type |
        of_trunc_subst_type |
        of_single_subst_type |
        of_stack_get_type |
        of_apply_subst_expr |
        of_const_expr |
        of_ap_expr |
        of_trunc_subst_expr |
        of_single_subst_expr |
        of_stack_get_expr
      ]
  end.
    
Ltac bf_rewrite_in_match :=
  match goal with 
  (*  | |- context [typeof_sym (fConst ?t ?c)] =>
        rewrite (BaseFunc_typeOk _ (bf_fConstOk _ _)); simpl     *)
    | |- context [ExprDsimul.ExprDenote.exprD' _ _ (typ2 (typ2 tyStack ?t) (typ2 tySubst (typ2 tyStack ?t))) (mkApplySubst ?t)] =>
      rewrite mkApplySubst_sound      
  end.