Require Import Charge.ModularFunc.BaseFunc.
Require Import Charge.ModularFunc.BaseType.

Require Import Charge.Tactics.Base.MirrorCoreTacs.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.ExprI.

(*
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

Ltac bf_eq_type :=
  match goal with
    | H1 : baseS ?e = Some (pEq ?t) |- _ =>
      match goal with
        | _ : ExprDsimul.ExprDenote.funcAs e (typ2 t (typ2 t typ0)) = Some _ |- _ => fail 1
        | _ : ExprDsimul.ExprDenote.exprD' _ _ (typ2 t (typ2 t typ0)) e = Some _ |- _ => fail 1
        | H2 : ExprDsimul.ExprDenote.funcAs e _ = Some _ |- _ =>
  	  	  let H := fresh "H" in
	        pose proof (bf_eq_func_type_eq _ _ H1 H2) as H; repeat clear_eq; subst
	    | H2 : ExprDsimul.ExprDenote.exprD' _ _ _ e = Some _ |- _ =>
	      let H := fresh "H" in
	        pose proof (bf_eq_type_eq _ _ H1 H2) as H; repeat clear_eq; subst
	  end
  end.
	  
Ltac bf_eq_expr :=
  match goal with
    | H1 : baseS ?e = Some (pEq ?t) |- _ =>
      match goal with
        | _ : ExprDsimul.ExprDenote.exprD' _ _ (typ2 t (typ2 t typ0)) e =
          Some (fun _ _ => eqD t) |- _ => fail 1
        | _ : ExprDsimul.ExprDenote.funcAs e (typ2 t (typ2 t typ0)) =
   		  Some (eqD t) |- _ => fail 1
		| H2 : ExprDsimul.ExprDenote.funcAs e (typ2 t (typ2 t typ0)) = Some _ |- _ =>
	 	  let H := fresh "H" in pose proof(bf_eq_func_eq _ H1 H2); subst
		| H2 : ExprDsimul.ExprDenote.exprD' _ _ (typ2 t (typ2 t typ0)) e = Some _ |- _ =>
	  	  let H := fresh "H" in pose proof(bf_eq_eq _ H1 H2); subst
	 end
   end.

Ltac bf_pair_type :=
  match goal with
    | H1 : baseS ?e = Some (pPair ?t ?u) |- _ =>
      match goal with
        | _ : ExprDsimul.ExprDenote.funcAs e (typ2 t (typ2 u (tyProd t u))) = Some _ |- _ => fail 1
        | _ : ExprDsimul.ExprDenote.exprD' _ _ (typ2 t (typ2 u (tyProd t u))) e = Some _ |- _ => fail 1
        | H2 : ExprDsimul.ExprDenote.funcAs e _ = Some _ |- _ =>
  	  	  let H := fresh "H" in
	        pose proof (bf_pair_func_type_eq _ _ H1 H2) as H; try (r_inj H); try prod_inj; repeat clear_eq; subst
	    | H2 : ExprDsimul.ExprDenote.exprD' _ _ _ e = Some _ |- _ =>
	      let H := fresh "H" in
	        pose proof (bf_pair_type_eq _ _ H1 H2) as H; try (r_inj H); try prod_inj; repeat clear_eq; subst
	  end
  end.
	  
Ltac bf_pair_expr :=
  match goal with
    | H1 : baseS ?e = Some (pPair ?t ?u) |- _ =>
      match goal with
        | _ : ExprDsimul.ExprDenote.exprD' _ _ (typ2 t (typ2 u (tyProd t u))) e =
          Some (fun _ _ => pairD t u) |- _ => fail 1
        | _ : ExprDsimul.ExprDenote.funcAs e (typ2 t (typ2 u (tyProd t u))) =
   		  Some (pairD t u) |- _ => fail 1
		| H2 : ExprDsimul.ExprDenote.funcAs e (typ2 t (typ2 u (tyProd t u))) = Some _ |- _ =>
	 	  let H := fresh "H" in pose proof(bf_pair_func_eq _ H1 H2); subst
		| H2 : ExprDsimul.ExprDenote.exprD' _ _ (typ2 t (typ2 u (tyProd t u))) e = Some _ |- _ =>
	  	  let H := fresh "H" in pose proof(bf_pair_eq _ H1 H2); subst
	 end
   end.

Ltac bf_forward_step :=
  match goal with 
    | H : Some _ = baseS _ |- _ =>  symmetry in H
    | _ => 
       first [
        bf_const_type |
        bf_eq_type |
        bf_pair_type |
        bf_const_expr |
        bf_eq_expr |
        bf_pair_expr
      ]
  end.

Ltac bf_unfold := 
  first [
    progress (unfold stringD) |
    progress (unfold stringR) |
    progress (unfold boolD) | 
    progress (unfold boolR) | 
    progress (unfold natD) |
    progress (unfold natR) |
    progress (unfold pairD)
  ].

Ltac bf_rewrite_in_match :=
  match goal with 
    | |- context [typeof_sym (fConst ?t ?c)] =>
        rewrite (BaseFunc_typeOk _ (bf_fConstOk _ _)); simpl     
    | |- context [ExprDsimul.ExprDenote.exprD' _ _ ?t (mkConst ?t _)] =>
      rewrite mkConst_sound      
    | |- context [ExprDsimul.ExprDenote.exprD' _ _ _ (mkString _)] =>
      unfold mkString; rewrite mkConst_sound      
    | |- context [ExprDsimul.ExprDenote.exprD' _ _ _ (mkNat _)] =>
      unfold mkNat; rewrite mkConst_sound      
    | |- context [ExprDsimul.ExprDenote.exprD' _ _ _ (mkBool _)] =>
      unfold mkBool; rewrite mkConst_sound      
    | |- context [typeof_sym (fEq ?t)] =>
        rewrite (BaseFunc_typeOk _ (bf_fEqOk _)); simpl     
    | |- context [ExprDsimul.ExprDenote.exprD' _ _ ?t (mkEq ?t _ _)] =>
      rewrite mkEq_sound      
    | |- context [typeof_sym (fPair ?t ?u)] =>
        rewrite (BaseFunc_typeOk _ (bf_fPairOk _ _)); simpl     
    | |- context [ExprDsimul.ExprDenote.exprD' _ _ ?t (mkPair ?t ?u _ _)] =>
      rewrite mkPair_sound      
  end.
*)