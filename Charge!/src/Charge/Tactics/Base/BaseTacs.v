Require Import Charge.ModularFunc.BaseFunc.
Require Import Charge.ModularFunc.BaseType.

Require Import Charge.Tactics.Base.MirrorCoreTacs.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.ExprI.


Ltac bf_const_type :=
  match goal with
    | H1 : baseS ?e = Some (pConst ?t ?c) |- _ =>
      match goal with
        | _ : ExprDsimul.ExprDenote.funcAs e t = Some _ |- _ => fail 1
        | _ : ExprDsimul.ExprDenote.exprD' _ _ t e = Some _ |- _ => fail 1
        | H2 : ExprDsimul.ExprDenote.funcAs e _ = Some _ |- _ =>
  	  	  let H := fresh "H" in
	        pose proof (bf_const_func_type_eq _ _ H1 H2) as H; repeat clear_eq; subst
	    | H2 : ExprDsimul.ExprDenote.exprD' _ _ _ e = Some _ |- _ =>
	      let H := fresh "H" in
	        pose proof (bf_const_type_eq _ _ H1 H2) as H; repeat clear_eq; subst
	  end
  end.
	  
Ltac bf_const_expr :=
  match goal with
    | H1 : baseS ?e = Some (pConst ?t ?c) |- _ =>
      match goal with
        | _ : ExprDsimul.ExprDenote.exprD' _ _ t e =
          Some (fun _ _ => c) |- _ => fail 1
        | _ : ExprDsimul.ExprDenote.funcAs e t =
   		  Some c |- _ => fail 1
		| H2 : ExprDsimul.ExprDenote.funcAs e t = Some _ |- _ =>
	 	  let H := fresh "H" in pose proof(bf_const_func_eq _ H1 H2); subst
		| H2 : ExprDsimul.ExprDenote.exprD' _ _ t e = Some _ |- _ =>
	  	  let H := fresh "H" in pose proof(bf_const_eq _ H1 H2); subst
	 end
   end.

Ltac bf_forward_step :=
  match goal with 
    | H : Some _ = baseS _ |- _ =>  symmetry in H
    | _ => 
       first [
        bf_const_type |
        bf_const_expr
      ]
  end.
    
Ltac bf_rewrite_in_match :=
  match goal with 
    | |- context [typeof_sym (fConst ?t ?c)] =>
        rewrite (BaseFunc_typeOk _ (bf_fConstOk _ _)); simpl     
    | |- context [ExprDsimul.ExprDenote.exprD' _ _ ?t (mkConst ?t _)] =>
      rewrite mkConst_sound      
  end.
