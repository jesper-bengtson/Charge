Require Import Charge.ModularFunc.Denotation.
Require Import Charge.ModularFunc.BILogicFunc.

Require Import Charge.Tactics.Base.MirrorCoreTacs.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.ExprI.

Ltac bilf_emp_type :=
  match goal with
    | H1 : bilogicS ?e = Some (bilf_emp ?t) |- _ =>
      match goal with
        | _ : ExprDsimul.ExprDenote.funcAs e t = Some _ |- _ => fail 1
        | _ : ExprDsimul.ExprDenote.exprD' _ _ t e = Some _ |- _ => fail 1
        | H2 : ExprDsimul.ExprDenote.funcAs e _ = Some _ |- _ =>
  	  	  let H := fresh "H" in
	        pose proof (bilf_emp_func_type_eq _ _ H1 H2) as H; repeat clear_eq; subst
	    | H2 : ExprDsimul.ExprDenote.exprD' _ _ _ e = Some _ |- _ =>
	      let H := fresh "H" in
	        pose proof (bilf_emp_type_eq _ _ H1 H2) as H; repeat clear_eq; subst
	  end
  end.

Ltac bilf_emp_expr :=
  match goal with
    | H1 : bilogicS ?e = Some (bilf_emp ?t), gs : bilogic_ops |- _ =>
      match goal with
        |  H2 : gs ?t = Some _ |- _ =>
	      match goal with
	        | _ : ExprDsimul.ExprDenote.exprD' _ _ t _ =
	          Some (fun _ _ => BILogic.empSP) |- _ => fail 1
	        | _ : ExprDsimul.ExprDenote.funcAs _ t =
	   		  Some BILogic.empSP |- _ => fail 1
			| H3 : ExprDsimul.ExprDenote.funcAs e t = Some _ |- _ =>
		 	  let H := fresh "H" in pose proof(bilf_emp_func_eq _ H2 H1 H3); subst
			| H3 : ExprDsimul.ExprDenote.exprD' _ _ t e = Some _ |- _ =>
		  	  let H := fresh "H" in pose proof(bilf_emp_eq _ H2 H1 H3); subst
		 end
	  end
  end.

Ltac bilf_star_type :=
  match goal with
    | H1 : bilogicS ?e = Some (bilf_star ?t) |- _ =>
      match goal with
        | _ : ExprDsimul.ExprDenote.funcAs e (typ2 t (typ2 t t)) = Some _ |- _ => fail 1
        | _ : ExprDsimul.ExprDenote.exprD' _ _ (typ2 t (typ2 t t)) e = Some _ |- _ => fail 1
        | H2 : ExprDsimul.ExprDenote.funcAs e _ = Some _ |- _ =>
  	  	  let H := fresh "H" in
	        pose proof (bilf_star_func_type_eq _ _ H1 H2) as H; r_inj H; repeat clear_eq; subst
	    | H2 : ExprDsimul.ExprDenote.exprD' _ _ _ e = Some _ |- _ =>
	      let H := fresh "H" in
	        pose proof (bilf_star_type_eq _ _ H1 H2) as H; r_inj H; repeat clear_eq; subst
	  end
  end.

Ltac bilf_star_expr :=
  match goal with
    | H1 : bilogicS ?e = Some (bilf_star ?t), gs : bilogic_ops |- _ =>
      match goal with 
        | H2 : gs t = Some _ |- _ => 
	      match goal with
	        | _ : ExprDsimul.ExprDenote.exprD' _ _ (typ2 t (typ2 t t)) _ =
	          Some (fun _ _ => starD t _) |- _ => fail 1
	        | _ : ExprDsimul.ExprDenote.funcAs _ (typ2 t (typ2 t t)) =
	   		  Some (starD t _) |- _ => fail 1
			| H3 : ExprDsimul.ExprDenote.funcAs e (typ2 t (typ2 t t)) = Some _ |- _ =>
		 	  let H := fresh "H" in pose proof(bilf_star_func_eq _ H2 H1 H3); subst
			| H3 : ExprDsimul.ExprDenote.exprD' _ _ (typ2 t (typ2 t t)) e = Some _ |- _ =>
		  	  let H := fresh "H" in pose proof(bilf_star_eq _ H2 H1 H3); subst
		  end
      end
  end.

Ltac bilf_wand_type :=
  match goal with
    | H1 : bilogicS ?e = Some (bilf_wand ?t) |- _ =>
      match goal with
        | _ : ExprDsimul.ExprDenote.funcAs e (typ2 t (typ2 t t)) = Some _ |- _ => fail 1
        | _ : ExprDsimul.ExprDenote.exprD' _ _ (typ2 t (typ2 t t)) e = Some _ |- _ => fail 1
        | H2 : ExprDsimul.ExprDenote.funcAs e _ = Some _ |- _ =>
  	  	  let H := fresh "H" in
	        pose proof (bilf_wand_func_type_eq _ _ H1 H2) as H; r_inj H; repeat clear_eq; subst
	    | H2 : ExprDsimul.ExprDenote.exprD' _ _ _ e = Some _ |- _ =>
	      let H := fresh "H" in
	        pose proof (bilf_wand_type_eq _ _ H1 H2) as H; r_inj H; repeat clear_eq; subst
	  end
  end.

Ltac bilf_wand_expr :=
  match goal with
    | H1 : bilogicS ?e = Some (bilf_wand ?t), gs : bilogic_ops |- _ =>
      match goal with 
        | H2 : gs t = Some _ |- _ => 
	      match goal with
	        | _ : ExprDsimul.ExprDenote.exprD' _ _ (typ2 t (typ2 t t)) _ =
	          Some (fun _ _ => wandD t _) |- _ => fail 1
	        | _ : ExprDsimul.ExprDenote.funcAs _ (typ2 t (typ2 t t)) =
	   		  Some (wandD t _) |- _ => fail 1
			| H3 : ExprDsimul.ExprDenote.funcAs e (typ2 t (typ2 t t)) = Some _ |- _ =>
		 	  let H := fresh "H" in pose proof(bilf_wand_func_eq _ H2 H1 H3); subst
			| H3 : ExprDsimul.ExprDenote.exprD' _ _ (typ2 t (typ2 t t)) e = Some _ |- _ =>
		  	  let H := fresh "H" in pose proof(bilf_wand_eq _ H2 H1 H3); subst
		  end
      end
  end.

(*
Ltac bil_pointwise_bilogicD :=  
  match goal with
    | bilp : bil_pointwise, gs : bilogic_ops |- _ =>
      match goal with
        | H1 : bilp (typ2 ?t ?u) = true |- _ =>
          match goal with
            | _ : gs (typ2 t u) = Some _ |- _ => fail 1
            | H2 : bil_pointwiseOk gs bilp |- _ => destruct (bil_pointwise_bilogic H2 _ _ H1)
          end
      end
  end.

Ltac bil_pointwise_bilogic_rangeD :=  
  match goal with
    | bilp : bil_pointwise, gs : bilogic_ops |- _ =>
      match goal with
        | H1 : bilp (typ2 ?t ?u) = true |- _ =>
          match goal with
            | _ : gs u = Some _ |- _ => fail 1
            | H2 : bil_pointwiseOk gs bilp |- _ => destruct (bil_pointwise_bilogic_range H2 _ _ H1)
          end
      end
  end.
*)
Ltac bilf_unfold := 
  first [
    progress (unfold empD) |
    progress (unfold starD) |
    progress (unfold wandD)
  ].
(*
Ltac pointwise_empD_rewrite :=
  match goal with
    | gs : bilogic_ops, bilp : bil_pointwise |- context [trmD BILogic.empSP _ _] =>
      match goal with
        | H1 : bil_pointwiseOk gs bilp, H2 : bilp (typ2 ?t ?u) = true,
          H3 : gs (typ2 ?t ?u) = Some _, H4 : gs ?u = Some _ |- _ =>
     	  let H := fresh "H" in 
     	    pose proof (bil_pointwise_empD H1 _ _ H2 H3 H4) as H;
     	    unfold tyArrD, tyArrD' in H; simpl in H; simpl; rewriteD H; clear H
      end
  end.

Ltac pointwise_empR_rewrite :=
  match goal with
    | gs : bilogic_ops, bilp : bil_pointwise |- context [trmR (fun x : _ => BILogic.empSP) _] =>
      match goal with
        | H1 : bil_pointwiseOk gs bilp, H2 : bilp (typ2 ?t ?u) = true,
          H3 : gs (typ2 ?t ?u) = Some _, H4 : gs ?u = Some _ |- _ =>
     	  let H := fresh "H" in 
     	    pose proof (bil_pointwise_empR H1 _ _ H2 H3 H4) as H;
     	    unfold tyArrR, tyArrR' in H; simpl in H; simpl; rewriteD H; clear H
      end
  end.

Ltac bilf_rewrite := 
  first [
    pointwise_empD_rewrite |
    pointwise_empR_rewrite
  ].
*)
Ltac bilf_forward_step :=
  match goal with 
    | H : Some _ = bilogicS _ |- _ =>  symmetry in H
    | _ => 
       first [
  (*      bil_pointwise_bilogicD |
        bil_pointwise_bilogic_rangeD |
   *)     bilf_emp_type |
        bilf_star_type |
        bilf_wand_type |
        bilf_emp_expr |
        bilf_star_expr |
        bilf_wand_expr
        
      ]
  end.