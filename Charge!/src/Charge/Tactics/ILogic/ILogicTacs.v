Require Import Charge.ModularFunc.ILogicFunc.

Require Import Charge.Tactics.Base.MirrorCoreTacs.
Require Import Charge.ModularFunc.Denotation.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.ExprI.

Ltac ilf_true_type :=
  match goal with
    | H1 : ilogicS ?e = Some (ilf_true ?t) |- _ =>
      match goal with
        | _ : ExprDsimul.ExprDenote.funcAs e t = Some _ |- _ => fail 1
        | _ : ExprDsimul.ExprDenote.exprD' _ _ t e = Some _ |- _ => fail 1
        | H2 : ExprDsimul.ExprDenote.funcAs e _ = Some _ |- _ =>
  	  	  let H := fresh "H" in
	        pose proof (ilf_true_func_type_eq _ _ H1 H2) as H; repeat clear_eq; subst
	    | H2 : ExprDsimul.ExprDenote.exprD' _ _ _ e = Some _ |- _ =>
	      let H := fresh "H" in
	        pose proof (ilf_true_type_eq _ _ H1 H2) as H; repeat clear_eq; subst
	  end
  end.

Ltac ilf_true_expr :=
  match goal with
    | H1 : ilogicS ?e = Some (ilf_true ?t), gs : logic_ops |- _ =>
      match goal with
        | H2 : gs ?t = Some _ |- _ =>
	      match goal with
	        | _ : ExprDsimul.ExprDenote.exprD' _ _ t _ =
	          Some (fun _ _ => trueD _ H2) |- _ => fail 1
	        | _ : ExprDsimul.ExprDenote.funcAs _ t =
	   		  Some (trueD _ H2) |- _ => fail 1
			| H3 : ExprDsimul.ExprDenote.funcAs e t = Some _ |- _ =>
		 	  let H := fresh "H" in pose proof(ilf_true_func_eq _ H2 H1 H3); subst
			| H3 : ExprDsimul.ExprDenote.exprD' _ _ t e = Some _ |- _ =>
		  	  let H := fresh "H" in pose proof(ilf_true_eq _ H2 H1 H3); subst
		 end
	  end
  end.

Ltac ilf_false_type :=
  match goal with
    | H1 : ilogicS ?e = Some (ilf_false ?t) |- _ =>
      match goal with
        | _ : ExprDsimul.ExprDenote.funcAs e t = Some _ |- _ => fail 1
        | _ : ExprDsimul.ExprDenote.exprD' _ _ t e = Some _ |- _ => fail 1
        | H2 : ExprDsimul.ExprDenote.funcAs e _ = Some _ |- _ =>
  	  	  let H := fresh "H" in
	        pose proof (ilf_false_func_type_eq _ _ H1 H2) as H; repeat clear_eq; subst
	    | H2 : ExprDsimul.ExprDenote.exprD' _ _ _ e = Some _ |- _ =>
	      let H := fresh "H" in
	        pose proof (ilf_false_type_eq _ _ H1 H2) as H; repeat clear_eq; subst
	  end
  end.

Ltac ilf_false_expr :=
  match goal with
    | H1 : ilogicS ?e = Some (ilf_false ?t), gs : logic_ops  |- _ =>
      match goal with
        | H2 : gs ?t = Some _ |- _ =>
	      match goal with
	        | _ : ExprDsimul.ExprDenote.exprD' _ _ t _ =
	          Some (fun _ _ => falseD _ H2) |- _ => fail 1
	        | _ : ExprDsimul.ExprDenote.funcAs _ t =
	   		  Some (falseD _ H2) |- _ => fail 1
			| H3 : ExprDsimul.ExprDenote.funcAs e t = Some _ |- _ =>
		 	  let H := fresh "H" in pose proof(ilf_false_func_eq _ H2 H1 H3); subst
			| H3 : ExprDsimul.ExprDenote.exprD' _ _ t e = Some _ |- _ =>
		  	  let H := fresh "H" in pose proof(ilf_false_eq _ H2 H1 H3); subst
		 end
      end
  end.

Ltac ilf_and_type :=
  match goal with
    | H1 : ilogicS ?e = Some (ilf_and ?t) |- _ =>
      match goal with
        | _ : ExprDsimul.ExprDenote.funcAs e (typ2 t (typ2 t t)) = Some _ |- _ => fail 1
        | _ : ExprDsimul.ExprDenote.exprD' _ _ (typ2 t (typ2 t t)) e = Some _ |- _ => fail 1
        | H2 : ExprDsimul.ExprDenote.funcAs e _ = Some _ |- _ =>
  	  	  let H := fresh "H" in
	        pose proof (ilf_and_func_type_eq _ _ H1 H2) as H; r_inj H; repeat clear_eq; subst
	    | H2 : ExprDsimul.ExprDenote.exprD' _ _ _ e = Some _ |- _ =>
	      let H := fresh "H" in
	        pose proof (ilf_and_type_eq _ _ H1 H2) as H; r_inj H; repeat clear_eq; subst
	  end
  end.

Ltac ilf_and_expr :=
  match goal with
    | H1 : ilogicS ?e = Some (ilf_and ?t), gs : logic_ops |- _ =>
      match goal with
        |  H2 : gs ?t = Some _ |- _ =>
	      match goal with
	        | _ : ExprDsimul.ExprDenote.exprD' _ _ (typ2 t (typ2 t t)) _ =
	          Some (fun _ _ => andD _ H2) |- _ => fail 1
	        | _ : ExprDsimul.ExprDenote.funcAs _ (typ2 t (typ2 t t)) =
	   		  Some (andD _ H2) |- _ => fail 1
			| H3 : ExprDsimul.ExprDenote.funcAs e (typ2 t (typ2 t t)) = Some _ |- _ =>
		 	  let H := fresh "H" in pose proof(ilf_and_func_eq _ H2 H1 H3); subst
			| H3 : ExprDsimul.ExprDenote.exprD' _ _ (typ2 t (typ2 t t)) e = Some _ |- _ =>
		  	  let H := fresh "H" in pose proof(ilf_and_eq _ H2 H1 H3); subst
		 end
      end
  end.

Ltac ilf_or_type :=
  match goal with
    | H1 : ilogicS ?e = Some (ilf_or ?t) |- _ =>
      match goal with
        | _ : ExprDsimul.ExprDenote.funcAs e (typ2 t (typ2 t t)) = Some _ |- _ => fail 1
        | _ : ExprDsimul.ExprDenote.exprD' _ _ (typ2 t (typ2 t t)) e = Some _ |- _ => fail 1
        | H2 : ExprDsimul.ExprDenote.funcAs e _ = Some _ |- _ =>
  	  	  let H := fresh "H" in
	        pose proof (ilf_or_func_type_eq _ _ H1 H2) as H; r_inj H; repeat clear_eq; subst
	    | H2 : ExprDsimul.ExprDenote.exprD' _ _ _ e = Some _ |- _ =>
	      let H := fresh "H" in
	        pose proof (ilf_or_type_eq _ _ H1 H2) as H; r_inj H; repeat clear_eq; subst
	  end
  end.

Ltac ilf_or_expr :=
  match goal with
    | H1 : ilogicS ?e = Some (ilf_or ?t), gs : logic_ops |- _ =>
      match goal with
        |  H2 : gs ?t = Some _ |- _ =>
	      match goal with
	        | _ : ExprDsimul.ExprDenote.exprD' _ _ (typ2 t (typ2 t t)) _ =
	          Some (fun _ _ => orD _ H2) |- _ => fail 1
	        | _ : ExprDsimul.ExprDenote.funcAs _ (typ2 t (typ2 t t)) =
	   		  Some (orD _ H2) |- _ => fail 1
			| H3 : ExprDsimul.ExprDenote.funcAs e (typ2 t (typ2 t t)) = Some _ |- _ =>
		 	  let H := fresh "H" in pose proof(ilf_or_func_eq _ H2 H1 H3); subst
			| H3 : ExprDsimul.ExprDenote.exprD' _ _ (typ2 t (typ2 t t)) e = Some _ |- _ =>
		  	  let H := fresh "H" in pose proof(ilf_or_eq _ H2 H1 H3); subst
		 end
      end
  end.

Ltac ilf_impl_type :=
  match goal with
    | H1 : ilogicS ?e = Some (ilf_impl ?t) |- _ =>
      match goal with
        | _ : ExprDsimul.ExprDenote.funcAs e (typ2 t (typ2 t t)) = Some _ |- _ => fail 1
        | _ : ExprDsimul.ExprDenote.exprD' _ _ (typ2 t (typ2 t t)) e = Some _ |- _ => fail 1
        | H2 : ExprDsimul.ExprDenote.funcAs e _ = Some _ |- _ =>
  	  	  let H := fresh "H" in
	        pose proof (ilf_impl_func_type_eq _ _ H1 H2) as H; r_inj H; repeat clear_eq; subst
	    | H2 : ExprDsimul.ExprDenote.exprD' _ _ _ e = Some _ |- _ =>
	      let H := fresh "H" in
	        pose proof (ilf_impl_type_eq _ _ H1 H2) as H; r_inj H; repeat clear_eq; subst
	  end
  end.

Ltac ilf_impl_expr :=
  match goal with
    | H1 : ilogicS ?e = Some (ilf_impl ?t), gs : logic_ops |- _ =>
      match goal with
        | H2 : gs ?t = Some _ |- _ =>
	      match goal with
	        | _ : ExprDsimul.ExprDenote.exprD' _ _ (typ2 t (typ2 t t)) _ =
	          Some (fun _ _ => implD _ H2) |- _ => fail 1
	        | _ : ExprDsimul.ExprDenote.funcAs _ (typ2 t (typ2 t t)) =
	   		  Some (implD _ H2) |- _ => fail 1
			| H3 : ExprDsimul.ExprDenote.funcAs e (typ2 t (typ2 t t)) = Some _ |- _ =>
		 	  let H := fresh "H" in pose proof(ilf_impl_func_eq _ H2 H1 H3); subst
			| H3 : ExprDsimul.ExprDenote.exprD' _ _ (typ2 t (typ2 t t)) e = Some _ |- _ =>
		  	  let H := fresh "H" in pose proof(ilf_impl_eq _ H2 H1 H3); subst
		 end
      end
  end.

Ltac il_pointwise_ilogicD :=  
  match goal with
    | ilp : il_pointwise, gs : logic_ops |- _ =>
      match goal with
        | H1 : ilp (typ2 ?t ?u) = true |- _ =>
          match goal with
            | _ : gs (typ2 t u) = Some _ |- _ => fail 1
            | H2 : il_pointwiseOk gs ilp |- _ => destruct (il_pointwise_ilogic H2 _ _ H1)
          end
      end
  end.

Ltac il_pointwise_ilogic_rangeD :=  
  match goal with
    | ilp : il_pointwise, gs : logic_ops |- _ =>
      match goal with
        | H1 : ilp (typ2 ?t ?u) = true |- _ =>
          match goal with
            | _ : gs u = Some _ |- _ => fail 1
            | H2 : il_pointwiseOk gs ilp |- _ => destruct (il_pointwise_ilogic_range H2 _ _ H1)
          end
      end
  end.

Ltac lf_unfold := 
  first [
    progress (unfold trueD) |
    progress (unfold falseD) |
    progress (unfold andD) | 
    progress (unfold orD) | 
    progress (unfold implD)
  ].

Ltac pointwise_trueD_rewrite :=
  match goal with
    | gs : logic_ops, ilp : il_pointwise |- context [trmD ILogic.ltrue _ _] =>
      match goal with
        | H1 : il_pointwiseOk gs ilp, H2 : ilp (typ2 ?t ?u) = true,
          H3 : gs (typ2 ?t ?u) = Some _, H4 : gs ?u = Some _ |- _ =>
     	  let H := fresh "H" in 
     	    pose proof (il_pointwise_trueD H1 _ _ H2 H3 H4) as H;
     	    unfold tyArrD, tyArrD' in H; simpl in H; simpl; rewriteD H; clear H
      end
  end.

Ltac pointwise_trueR_rewrite :=
  match goal with
    | gs : logic_ops, ilp : il_pointwise |- context [trmR (fun x : _ => ILogic.ltrue) _] =>
      match goal with
        | H1 : il_pointwiseOk gs ilp, H2 : ilp (typ2 ?t ?u) = true,
          H3 : gs (typ2 ?t ?u) = Some _, H4 : gs ?u = Some _ |- _ =>
     	  let H := fresh "H" in 
     	    pose proof (il_pointwise_trueR H1 _ _ H2 H3 H4) as H;
     	    unfold tyArrR, tyArrR' in H; simpl in H; simpl; rewriteD H; clear H
      end
  end.

Ltac pointwise_falseD_rewrite :=
  match goal with
    | gs : logic_ops, ilp : il_pointwise |- context [trmD ILogic.lfalse _ _] =>
      match goal with
        | H1 : il_pointwiseOk gs ilp, H2 : ilp (typ2 ?t ?u) = true,
          H3 : gs (typ2 ?t ?u) = Some _, H4 : gs ?u = Some _ |- _ =>
     	  let H := fresh "H" in 
     	    pose proof (il_pointwise_falseD H1 _ _ H2 H3 H4) as H;
     	    unfold tyArrD, tyArrD' in H; simpl in H; simpl; rewriteD H; clear H
      end
  end.

Ltac pointwise_falseR_rewrite :=
  match goal with
    | gs : logic_ops, ilp : il_pointwise |- context [trmR (fun x : _ => ILogic.lfalse) _] =>
      match goal with
        | H1 : il_pointwiseOk gs ilp, H2 : ilp (typ2 ?t ?u) = true,
          H3 : gs (typ2 ?t ?u) = Some _, H4 : gs ?u = Some _ |- _ =>
     	  let H := fresh "H" in 
     	    pose proof (il_pointwise_falseR H1 _ _ H2 H3 H4) as H;
     	    unfold tyArrR, tyArrR' in H; simpl in H; simpl; rewriteD H; clear H
      end
  end.

Ltac lf_rewrite := 
  first [
    pointwise_trueD_rewrite |
    pointwise_trueR_rewrite | 
    pointwise_falseD_rewrite |
    pointwise_falseR_rewrite
  ].

Ltac ilf_forward_step :=
  match goal with 
    | H : Some _ = ilogicS _ |- _ =>  symmetry in H
    | _ => 
       first [
        il_pointwise_ilogicD |
        il_pointwise_ilogic_rangeD |
        ilf_true_type |
        ilf_false_type |
        ilf_and_type |
        ilf_or_type |
        ilf_impl_type |
        ilf_true_expr |
        ilf_false_expr |
        ilf_and_expr |
        ilf_or_expr |
        ilf_impl_expr
        
      ]
  end.
