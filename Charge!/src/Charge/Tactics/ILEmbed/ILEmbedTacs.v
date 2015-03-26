Require Import Charge.ModularFunc.EmbedFunc.

Require Import Charge.Tactics.Base.MirrorCoreTacs.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.ExprI.

Ltac eilf_embed_type :=
  match goal with
    | H1 : embedS ?e = Some (eilf_embed ?t ?u) |- _ =>
      match goal with
        | _ : ExprDsimul.ExprDenote.funcAs e (typ2 t u) = Some _ |- _ => fail 1
        | _ : ExprDsimul.ExprDenote.exprD' _ _ (typ2 t u) e = Some _ |- _ => fail 1
        | H2 : ExprDsimul.ExprDenote.funcAs e _ = Some _ |- _ =>
  	  	  let H := fresh "H" in
	        pose proof (eilf_embed_func_type_eq _ _ H1 H2) as H; r_inj H; repeat clear_eq; subst
	    | H2 : ExprDsimul.ExprDenote.exprD' _ _ _ e = Some _ |- _ =>
	      let H := fresh "H" in
	        pose proof (eilf_embed_type_eq _ _ H1 H2) as H; r_inj H; repeat clear_eq; subst
	  end
  end.

Ltac eilf_embed_expr :=
  match goal with
    | H1 : embedS ?e = Some (eilf_embed ?t ?u), gs : embed_ops |- _ =>
      match goal with 
        | H2 : gs t u = Some _ |- _ => 
	      match goal with
	        | _ : ExprDsimul.ExprDenote.exprD' _ _ (typ2 t u) _ =
	          Some (fun _ _ => embedD t u _) |- _ => fail 1
	        | _ : ExprDsimul.ExprDenote.funcAs _ (typ2 t u) =
	   		  Some (embedD t u _) |- _ => fail 1
			| H3 : ExprDsimul.ExprDenote.funcAs e (typ2 t u) = Some _ |- _ =>
		 	  let H := fresh "H" in pose proof(eilf_embed_func_eq _ H2 H1 H3); subst
			| H3 : ExprDsimul.ExprDenote.exprD' _ _ (typ2 t u) e = Some _ |- _ =>
		  	  let H := fresh "H" in pose proof(eilf_embed_eq _ H2 H1 H3); subst
		  end
      end
  end.
  
Ltac eilf_forward_step :=
  match goal with 
    | H : Some _ = embedS _ |- _ =>  symmetry in H
    | _ => 
       first [
        eilf_embed_type |
        eilf_embed_expr
      ]
  end.
