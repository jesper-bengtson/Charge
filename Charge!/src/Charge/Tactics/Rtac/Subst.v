Require Import String.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprVariables.
Require Import MirrorCore.Lambda.AppN.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.Lambda.RedAll.

Require Import Charge.ModularFunc.Denotation.
Require Import Charge.ModularFunc.BaseFunc.
Require Import Charge.ModularFunc.OpenFunc.
Require Import Charge.ModularFunc.ILogicFunc.
Require Import Charge.ModularFunc.BILogicFunc.
Require Import Charge.ModularFunc.LaterFunc.
Require Import Charge.ModularFunc.EmbedFunc.
Require Import Charge.ModularFunc.ListFunc.
Require Import Charge.ModularFunc.SubstType.
Require Import Charge.ModularFunc.BaseType.
Require Import Charge.ModularFunc.ListType.
Require Import Charge.Open.Stack.

Set Implicit Arguments.
Set Strict Implicit.

Section ApplySubst.
	Context {typ func : Type} {RType_typ : RType typ} {ST : SubstType typ} {BT : BaseType typ} {LT : ListType typ}
	        {HOF : OpenFunc typ func} {HLF : ListFunc typ func} {HBF : BaseFunc typ func}
	        {BTD : BaseTypeD} {LTD : ListTypeD LT}.
	Context {RelDec_typ : RelDec (@eq typ)}.
	Context {RelDec_string : RelDec (@eq (typD tyString))}.

    Variable Typ2_tyArr : Typ2 _ Fun.
    Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.

	Definition applySingleSubst (p : expr typ func) (x y : String.string) e :=
		if x ?[ eq ] y then e else p.
		    	
    Fixpoint applyParSubst (p : expr typ func) (x : String.string) vs es :=
    	match es with
    		| App (App f e) es =>
    			match vs, listS f with
    				| v :: vs, Some (pCons t) =>
    					if t ?[ eq ] tyArr tyString tyVal then
    						if x ?[ eq ] v then
    							e
    						else
    							applyParSubst p x vs es
    					else
    						p
    				| _, _ => p
    			end
    		| _ => p
    	end.
    						
    Fixpoint applyTruncSubst (p : expr typ func) (x : String.string) vs es :=
    	match es with
    		| App (App f e) es =>
    			match vs, listS f with
    				| v :: vs, Some (pCons t) =>
    					if t ?[ eq ] tyArr tyString tyVal then
    						if x ?[ eq ] v then
    							e
    						else
    							applyTruncSubst p x vs es
    					else
    						mkNull
    				| _, _ => mkNull
    			end
    		| _ => p
    	end.				

	Definition applySubst (t : typ) (f e : expr typ func) (x : String.string) :=
		match f with
		  | App (App g e') y =>
		  	match open_funcS g, baseS y with
		  	  | Some of_single_subst, Some (pConst t' v) => 
		  	    match type_cast t' tyString with
		  	      | Some pf => applySingleSubst e x (stringD (eq_rect _ typD v _ pf)) e'
		  	      | None => mkApplySubst t e f
		  	    end
		  	  | Some of_trunc_subst, Some (pConst t' v) => 
		  	    match type_cast t' (tyList tyString) with
		  	      | Some pf => applyTruncSubst e x 
		  	        (eq_rect _ list (listD (eq_rect _ typD v _ pf)) _ btString) e'
		  	      | None => mkApplySubst t e f
		  	    end
		  (*	  | Some of_trunc_subst, Some (pString v) => applyTruncSubst e x v e'*)
		  	  | _, _ => mkApplySubst t e f
		  	end
		  | _ => mkApplySubst t e f
(*		  | mkApplySubst [t, p, mkSubstList [mkVarList [vs], es]] => applyParSubst p x vs es
		  | mkApplyTruncSubst [t, p, mkSubstList [mkVarList [vs], es]] => applyTruncSubst x vs es*)
		end.

End ApplySubst.

Section PushSubst.
  Context {typ func : Type} {ST : SubstType typ} {BT : BaseType typ} {RType_typ : RType typ}.
  Context {BTD : BaseTypeD} {LT : ListType typ} {LTD : ListTypeD LT}.
  Context {OF : OpenFunc typ func} {ILF : ILogicFunc typ func} {BILF : BILogicFunc typ func} {HBF : BaseFunc typ func}.
  Context {EF : EmbedFunc typ func} {LF : ListFunc typ func}.
  Context {RelDec_string : RelDec (@eq (typD tyString))}.
  Context {RelDec_type : RelDec (@eq typ)}.
  Context {ilp : il_pointwise (typ := typ)}.
  Context {bilp : bil_pointwise (typ := typ)}.
  Variable Typ2_tyArr : Typ2 _ Fun.
  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.

  Variable f : expr typ func.

  Fixpoint pushSubst (e : expr typ func) (t : typ) : expr typ func :=
    match e with
    	| App (App g p) q =>
    		match ilogicS g with
    			| Some (ilf_and l) => if ilp l then mkAnd l (pushSubst p t) (pushSubst q t) else mkApplySubst t e f
    			| Some (ilf_or l) => if ilp l then mkOr l (pushSubst p t) (pushSubst q t) else mkApplySubst t e f
    			| Some (ilf_impl l) => if ilp l then mkImpl l (pushSubst p t) (pushSubst q t) else mkApplySubst t e f
    			| Some _ => mkApplySubst t e f
    			| None => match open_funcS g with
		    			 | Some (of_ap t1 t2) => mkAp t1 t2 (pushSubst p (tyArr t1 t2))
		    			             									 (pushSubst q t1)
		    			 | Some _ => mkApplySubst t e f
		    			 | _ => match bilogicS g with
		    			          | Some (bilf_star l) => if bilp l then mkStar l (pushSubst p t) (pushSubst q t) else mkApplySubst t e f
		    			          | Some (bilf_wand l) => if bilp l then mkWand l (pushSubst p t) (pushSubst q t) else mkApplySubst t e f
		    			 	      | _ => mkApplySubst t e f
		    			 	    end
		    		   end
    		end
    	| App g p =>
    		match open_funcS g, baseS p with
    			| Some of_stack_get, Some (pConst t' x) =>
    			  match type_cast t' tyString with
    			    | Some pf => applySubst Typ2_tyArr t f e (stringD (eq_rect _ typD x _ pf))
    			    | None => mkApplySubst t e f
    			  end
    			| Some (of_const t), _ => OpenFunc.mkConst t p
    			| Some _, _ => mkApplySubst t e f
    			| None, _ => match embedS g with
    					    | Some (eilf_embed u v) => mkEmbed u v (pushSubst p u)
    					    | _ => mkApplySubst t e f
    					  end
    		end
    	| _ => match ilogicS e with
    		     | Some (ilf_true l) => if ilp l then mkTrue l else mkApplySubst t e f
    		     | Some (ilf_false l) => if ilp l then mkFalse l else mkApplySubst t e f
    		     | Some _ => mkApplySubst t e f
    		     | None => match bilogicS e with
    		     		  | Some (bilf_emp l) => if bilp l then mkEmp l else mkApplySubst t e f
    		     		  | _ => mkApplySubst t e f
    		     		end
    		   end
    end.
    
End PushSubst.
(*
Implicit Arguments typeof_funcAs [[typ] [func] [RType_typ] [RSym_func] [f] [t] [e]].
*)

Require Import Charge.ModularFunc.SemiEqDecTyp.

Section SubstTac.
  Context {typ func subst : Type} {ST : SubstType typ} {BT : BaseType typ} {RType_typ : RType typ}.
  Context {OF : OpenFunc typ func} {ILF : ILogicFunc typ func} {BILF : BILogicFunc typ func} {BF : BaseFunc typ func}.
  Context {LT : ListType typ} {LF : ListFunc typ func}.
  Context {EF : EmbedFunc typ func}.
  Context {RelDec_string : RelDec (@eq (typD tyString))}.
  Context {RelDec_typ : RelDec (@eq typ)}.
  Context {RelDec_typOk : RelDec_Correct RelDec_typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {RSym_func : RSym func}.
  Context {RSym_funcOk : RSymOk RSym_func}.
  Variable Typ2_tyArr : Typ2 _ Fun.
  Variable Typ0_Prop : Typ0 _ Prop.
  Context {Typ2_tyArrOk : Typ2Ok Typ2_tyArr}.
  Context {HV : ValNull (typD tyVal)}.
  Context {HSTD : SubstTypeD}.
  Context {HBTD : BaseTypeD} {HLTD : ListTypeD LT}.
  Context {OFOK : OpenFuncOk typ func}.
  Context {gs : @logic_ops _ RType_typ}.
  Context {bs : @bilogic_ops _ RType_typ}.
  Context {ILFOK : ILogicFuncOk typ func gs}.
  Context {BILFOK : BILogicFuncOk typ func bs}.
  Context {Heqd : SemiEqDecTyp typ}.
  Context {BFOK : BaseFuncOk (RelDec_eq := RelDec_typ) (Heqd := Heqd) typ func}.
  Context {EqDec_typ : EqDec typ eq}.
  Context {ilp : il_pointwise (typ := typ)}.
  Context {ilpOk : il_pointwiseOk _ gs ilp}.
  Context {bilp : bil_pointwise (typ := typ)}.
  Context {bilpOk : bil_pointwiseOk _ bs bilp}.
  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.

  Let Expr_expr := Expr_expr (typ := typ) (func := func).
  Let ExprOk_expr := ExprOk_expr (typ := typ) (func := func).
  Let ExprUVar_expr := ExprUVar_expr (typ := typ) (func := func).
  
  Local Existing Instance Expr_expr.
  Local Existing Instance ExprOk_expr.
  Local Existing Instance ExprUVar_expr.

  Definition substTac (_ : list (option (expr typ func))) (e : expr typ func) (args : list (expr typ func))
  : expr typ func :=
    match open_funcS (RType_typ := RType_typ) (HST := ST) e with
	  | Some (of_apply_subst t) =>
	    match args with
	      | e :: f :: nil =>
	        pushSubst (ilp := ilp) (bilp := bilp) Typ2_tyArr f e t
	      | _ => apps e args
	    end
	  | _ => apps e args
	end.
Require Import Charge.Open.Subst.	
Require Import MirrorCore.Lambda.ExprTac.
Require Import FunctionalExtensionality.	
  
      Lemma Rcast_eq_refl (t : typ) (F : Type -> Type) (a b : F (typD t)) (H : Rcast F eq_refl a = b) : a = b.
      Proof.
        apply H.
      Qed.

  Lemma Rcast_option_inj (t u : typ) r (a : typD t) (b : typD u)
    (H : Rcast option r (Some a) = Some b) :
    b = Rcast id r a.
  Proof.
    clear -H.
    unfold Rcast, Relim, Rsym, eq_sym in *.
    destruct r; inv_all; subst. reflexivity.
  Qed.

  Lemma Rcast_id t f : 
    Rcast id (Rrefl t) f = f.
  Proof.
    reflexivity.
  Qed.

  Ltac clear_eq := 
    match goal with 
      | H : ?x = ?x |- _ => clear H
    end.
    
  Ltac r_inj H :=
      first [
        let H1 := fresh "H" in let H2 := fresh "H" in
          apply typ2_inj in H as [H1 H2]; [unfold Rty in H1, H2; r_inj H1; r_inj H2 | apply _] |
        repeat subst].
    
Ltac forward_step :=
  match goal with 
    | H : Some _ = baseS _ |- _ =>  symmetry in H
    | H : Some _ = embedS _ |- _ =>  symmetry in H
    | H : Some _ = open_funcS _ |- _ =>  symmetry in H
    | H : Some _ = bilogicS _ |- _ =>  symmetry in H
    | H : Some _ = ilogicS _ |- _ =>  symmetry in H
    | H : typ2 _ _ = typ2 _ _ |- _ => r_inj H; clear_eq
    | H : Rty (typ2 _ _) (typ2 _ _) |- _ => r_inj H; clear_eq
    | H : Rcast option _ (Some _) = Some _ |- _ => apply Rcast_option_inj in H; subst
  (*  | H1 : baseS ?f = Some (pString ?typ ?s), H2 : funcAs ?f ?t = Some _ |- _ =>
      assert (t = tyString) by (apply (bf_string_type_eq _ _ H1 H2)); subst;
      let H := fresh "H" in
      assert (funcAs f tyString = funcAs (pString typ s) tyString) as H by
        (apply bf_funcAsOk; assumption); 
      rewrite H in H2; clear H;
      unfold funcAs in H2; simpl in H2; rewrite type_cast_refl in H2;
        [| apply _]
    *)  
    | H1 : open_funcS ?f = Some (of_apply_subst ?t), H2 : funcAs ?f ?u = Some _ |- _ =>
      let v := constr:(typ2 (typ2 (typ2 tyString tyVal) t) (typ2 tySubst (typ2 (typ2 tyString tyVal) t))) in
      let Heq := fresh "Heq" in assert (u = v) as Heq by (apply (of_apply_subst_type_eq _ _ H1 H2)); r_inj Heq;
      let H := fresh "H" in pose proof (of_funcAsOk _ H1) as H;
      rewrite H in H2; clear H;
      unfold funcAs in H2; simpl in H2; rewrite type_cast_refl in H2;
        [| apply _]
      
    | H1 : open_funcS ?f = Some (of_const ?t), H2 : funcAs ?f ?u = Some _ |- _ =>
      let v := constr:(typ2 t (typ2 (typ2 tyString tyVal) t)) in
      let Heq := fresh "Heq" in assert (u = v) as Heq by (apply (of_const_type_eq _ _ H1 H2)); r_inj Heq;
      let H := fresh "H" in
      pose proof (of_funcAsOk _ H1) as H;
      rewrite H in H2; clear H;
      unfold funcAs in H2; simpl in H2; rewrite type_cast_refl in H2 ;
        [| apply _]
        
    | H1 : open_funcS ?f = Some (of_ap ?t ?u), H2 : funcAs ?f ?v = Some _ |- _ =>
      let w := constr:(typ2 (typ2 (typ2 tyString tyVal) (typ2 t u)) (typ2 (typ2 (typ2 tyString tyVal) t) (typ2 (typ2 tyString tyVal) u))) in
      let Heq := fresh "Heq" in assert (v = w) as Heq by (apply (of_ap_type_eq _ _ H1 H2)); r_inj Heq;
      let H := fresh "H" in
      pose proof (of_funcAsOk _ H1) as H;
      rewrite H in H2; clear H;
      unfold funcAs in H2; simpl in H2; rewrite type_cast_refl in H2 ;
        [| apply _]
        
    | H1 : open_funcS ?f = Some (of_single_subst), H2 : funcAs ?f ?t = Some _ |- _ =>
      let u := constr:(typ2 (typ2 (typ2 tyString tyVal) tyVal) (typ2 tyString tySubst)) in
      let Heq := fresh "Heq" in assert (t = u) as Heq
       by (apply (of_single_subst_type_eq _ _ H1 H2)); r_inj Heq;
      let H := fresh "H" in
      pose proof (of_funcAsOk _ H1) as H;
      rewrite H in H2; clear H;
      unfold funcAs in H2; simpl in H2; rewrite type_cast_refl in H2 ;
        [| apply _]
        
    | H1 : open_funcS ?f = Some of_stack_get, H2 : funcAs ?f ?u = Some _ |- _ =>
      let v := constr:(typ2 tyString (typ2 (typ2 tyString tyVal) tyVal)) in
      let Heq := fresh "Heq" in assert (u = v) as Heq
       by (apply (of_stack_get_type_eq _ _ H1 H2)); r_inj Heq;
      let H := fresh "H" in
      pose proof (of_funcAsOk _ H1) as H;
      rewrite H in H2; clear H;
      unfold funcAs in H2; simpl in H2; rewrite type_cast_refl in H2;
        [| apply _]

    | H1 : bilogicS ?f = Some (bilf_emp ?t), H2 : funcAs ?f ?u = Some _ |- _ =>
      let Heq := fresh "Heq" in assert (t = u) 
       by (apply (bilf_emp_type_eq _ _ H1 H2));
      let H := fresh "H" in
      pose proof (bilf_funcAsOk _ H1) as H;
      rewrite H in H2; clear H ;
      unfold funcAs in H2; simpl in H2; forward; inv_all; subst

    | H1 : bilogicS ?f = Some (bilf_star ?t), H2 : funcAs ?f ?u = Some _ |- _ =>
      let Heq := fresh "Heq" in assert (u = typ2 t (typ2 t t)) 
       by (apply (bilf_star_type_eq _ _ H1 H2));
      let H := fresh "H" in
      pose proof (bilf_funcAsOk _ H1) as H;
      rewrite H in H2; clear H ;
      unfold funcAs in H2; simpl in H2; forward; inv_all; subst

    | H1 : bilogicS ?f = Some (bilf_wand ?t), H2 : funcAs ?f ?u = Some _ |- _ =>
      let Heq := fresh "Heq" in assert (u = typ2 t (typ2 t t)) 
       by (apply (bilf_wand_type_eq _ _ H1 H2));
      let H := fresh "H" in
      pose proof (bilf_funcAsOk _ H1) as H;
      rewrite H in H2; clear H ;
      unfold funcAs in H2; simpl in H2; forward; inv_all; subst

    | H1 : ilogicS ?f = Some (ilf_true ?t), H2 : funcAs ?f ?u = Some _ |- _ =>
      let Heq := fresh "Heq" in assert (t = u) as Heq 
       by (apply (ilf_true_type_eq _ _ H1 H2));
      let H := fresh "H" in
      pose proof (ilf_funcAsOk _ H1) as H;
      rewrite H in H2; clear H ;
      unfold funcAs in H2; simpl in H2; forward; inv_all; subst

    | H1 : ilogicS ?f = Some (ilf_false ?t), H2 : funcAs ?f ?u = Some _ |- _ =>
      let Heq := fresh "Heq" in assert (t = u) as Heq 
       by (apply (ilf_false_type_eq _ _ H1 H2));
      let H := fresh "H" in
      pose proof (ilf_funcAsOk _ H1) as H;
      rewrite H in H2; clear H ;
      unfold funcAs in H2; simpl in H2; forward; inv_all; subst

    | H1 : ilogicS ?f = Some (ilf_and ?t), H2 : funcAs ?f ?u = Some _ |- _ =>
      let Heq := fresh "Heq" in assert (u = tyArr t (tyArr t t)) as Heq 
       by (apply (ilf_and_type_eq _ _ H1 H2));
      let H := fresh "H" in
      pose proof (ilf_funcAsOk _ H1) as H;
      rewrite H in H2; clear H ;
      unfold funcAs in H2; simpl in H2; forward; inv_all; subst

    | H1 : ilogicS ?f = Some (ilf_or ?t), H2 : funcAs ?f ?u = Some _ |- _ =>
      let Heq := fresh "Heq" in assert (u = tyArr t (tyArr t t)) as Heq 
       by (apply (ilf_or_type_eq _ _ H1 H2));
      let H := fresh "H" in
      pose proof (ilf_funcAsOk _ H1) as H;
      rewrite H in H2; clear H ;
      unfold funcAs in H2; simpl in H2; forward; inv_all; subst

    | H1 : ilogicS ?f = Some (ilf_impl ?t), H2 : funcAs ?f ?u = Some _ |- _ =>
      let Heq := fresh "Heq" in assert (u = tyArr t (tyArr t t)) as Heq 
       by (apply (ilf_impl_type_eq _ _ H1 H2));
      let H := fresh "H" in
      pose proof (ilf_funcAsOk _ H1) as H;
      rewrite H in H2; clear H ;
      unfold funcAs in H2; simpl in H2; forward; inv_all; subst
  end.

Require Import Charge.Tactics.Lists.ListTacs.
Require Import Charge.Tactics.Base.DenotationTacs.
Require Import Charge.Tactics.Base.MirrorCoreTacs.

Lemma substTac_ok : partial_reducer_ok (substTac nil).
  Proof.
    unfold partial_reducer_ok. intros.
    eexists; split; [|reflexivity].
    unfold substTac.
    do 5 (destruct_exprs; try assumption).
    simpl in H.
    reduce.
    of_apply_subst_type.
    of_apply_subst_expr.
    Print RSym.
    unfold applySubstD, fun_to_typ3.
    do 2 rewrite exprT_App_wrap.
    do 6 (destruct_exprs; try assumption).
    destruct_exprs; (try (reduce; apply zipExprOk; [reduce | eassumption])).
    destruct_exprs. destruct e1; try congruence.
    destruct_exprs; (try (reduce; apply zipExprOk; reduce)).
    destruct_exprs; try assumption.
    destruct_exprs; try assumption.
    unfold substTac; simpl.
    destruct e; try (exists val; tauto).
    remember (open_funcS f). destruct o; try (exists val; tauto).
    destruct o; try (exists val; tauto).
    destruct es; try (exists val; tauto).
    destruct es; try (exists val; tauto).
    destruct es; try (exists val; tauto).
    simpl in H.
    autorewrite with exprD_rw in H; simpl in H; forward; inv_all; subst.
    autorewrite with exprD_rw in H0; simpl in H0; forward; inv_all; subst.
    autorewrite with exprD_rw in H2; simpl in H2; forward; inv_all; subst.
    
    repeat forward_step.
    repeat rewrite Rcast_id.
    clear Heqo.
	generalize dependent t0.
    induction e using expr_strong_ind; intros;
    try (solve [simpl; eexists; split; [eapply mkApplySubst_sound; eassumption|reflexivity]]). {
      (* True, False, and Emp *)
      autorewrite with exprD_rw in H3; simpl in H3; forward; inv_all; subst.
	  simpl; remember (ilogicS i) as o; destruct o; [destruct i0|];
	  try (solve [simpl; eexists; split; [eapply mkApplySubst_sound; try eassumption; autorewrite with exprD_rw; simpl; forward; inv_all; subst; reflexivity|reflexivity]]);
	  [| | (remember (bilogicS i) as o; destruct o; [destruct b|])]; 
	  try (solve [simpl; eexists; split; [eapply mkApplySubst_sound; try eassumption; autorewrite with exprD_rw; simpl; forward; inv_all; subst; reflexivity|reflexivity]]).
	  { (* True *)
	    remember (ilp logic).
	    destruct b; [|simpl; eexists; split; [eapply mkApplySubst_sound; try eassumption; autorewrite with exprD_rw; simpl; forward; inv_all; subst; reflexivity | reflexivity]].
	    repeat forward_step.
	    unfold applySubstD, fun_to_typ3; repeat rewrite exprT_App_wrap.
	    eexists; split; [eapply mkTrue_sound; eassumption|]; intros.
	    unfold trueD.
	    unfold fun_to_typ, typ_to_fun, eq_rect_r, eq_rect, eq_sym.
	    unfold il_pointwiseOk in ilpOk.
	    specialize (ilpOk (typ2 (typ2 tyString tyVal) t0)).
	    rewrite typ2_match_zeta in ilpOk.
	    rewrite H2 in ilpOk.
	    rewrite <- Heqb in ilpOk.

	    revert ilpOk.
	    generalize (typ2_cast (typ2 tyString tyVal) t0).
	    generalize (typ2_cast tyString tyVal).
	    generalize dependent (typ2 tyString tyVal).
	    intro.
	    generalize dependent (typ2 t t0). intro.
	    generalize dependent (typD t).
	    intros; subst.
	    clear -ilpOk RTypeOk_typ RType_typ.
	    revert ilpOk. revert e1.
		uip_all.
		rewrite Rcast_id.
		revert ilpOk.
	    generalize dependent (typD t1). 
	    intros; subst. unfold eq_sym in ilpOk.
	    destruct (gs t0); [|destruct ilpOk].

	    destruct ilpOk as [H [_ [_ [_ [_ [_ _]]]]]]; clear ilpOk.
	    unfold apply_subst. 
	    apply functional_extensionality; intros. 
	    do 2 rewrite H. reflexivity.
	    apply _.
	  } { (* False *) 
	    remember (ilp logic).
	    destruct b; [|simpl; eexists; split; [eapply mkApplySubst_sound; try eassumption; autorewrite with exprD_rw; simpl; forward; inv_all; subst; reflexivity | reflexivity]].
	    repeat forward_step.
	    unfold applySubstD, fun_to_typ3; repeat rewrite exprT_App_wrap.
	    eexists; split; [eapply mkFalse_sound; eassumption|]; intros.
	    unfold falseD.
	    unfold fun_to_typ, typ_to_fun, eq_rect_r, eq_rect, eq_sym.
	    unfold il_pointwiseOk in ilpOk.
	    specialize (ilpOk (typ2 (typ2 tyString tyVal) t0)).
	    rewrite typ2_match_zeta in ilpOk.
	    rewrite H2 in ilpOk.
	    rewrite <- Heqb in ilpOk.

	    revert ilpOk.
	    generalize (typ2_cast (typ2 tyString tyVal) t0).
	    generalize (typ2_cast tyString tyVal).
	    generalize dependent (typ2 tyString tyVal).
	    intro.
	    generalize dependent (typ2 t t0). intro.
	    generalize dependent (typD t).
	    intros; subst.
	    clear -ilpOk RTypeOk_typ RType_typ.
	    revert ilpOk. revert e1.
		uip_all.
		rewrite Rcast_id.
		revert ilpOk.
	    generalize dependent (typD t1). 
	    intros; subst. unfold eq_sym in ilpOk.
	    destruct (gs t0); [|destruct ilpOk].

	    destruct ilpOk as [_ [H [_ [_ [_ [_ _]]]]]]; clear ilpOk.
	    unfold apply_subst. 
	    apply functional_extensionality; intros. 
	    do 2 rewrite H. reflexivity.
	    apply _.
	  } { (* Emp *)	    
	    remember (bilp logic).
	    destruct b; [|simpl; eexists; split; [eapply mkApplySubst_sound; try eassumption; autorewrite with exprD_rw; simpl; forward; inv_all; subst; reflexivity | reflexivity]].
	    repeat forward_step.
	    unfold applySubstD, fun_to_typ3; repeat rewrite exprT_App_wrap.
	    eexists; split; [eapply mkEmp_sound; eassumption|]; intros.
	    unfold empD.
	    unfold fun_to_typ, typ_to_fun, eq_rect_r, eq_rect, eq_sym.
	    specialize (bilpOk (typ2 (typ2 tyString tyVal) t0)).
	    rewrite typ2_match_zeta in bilpOk.
	    rewrite H2 in bilpOk.
	    rewrite <- Heqb in bilpOk.

	    revert bilpOk.
	    generalize (typ2_cast (typ2 tyString tyVal) t0).
	    generalize (typ2_cast tyString tyVal).
	    generalize dependent (typ2 tyString tyVal).
	    intro.
	    generalize dependent (typ2 t t0). intro.
	    generalize dependent (typD t).
	    intros; subst.
	    clear -bilpOk RTypeOk_typ RType_typ.
	    revert bilpOk. revert e1.
		uip_all.
		rewrite Rcast_id.
		revert bilpOk.
	    generalize dependent (typD t1). 
	    intros; subst. unfold eq_sym in bilpOk.
	    destruct (bs t0); [|destruct bilpOk].

	    destruct bilpOk as [H [_ _]]; clear bilpOk.
	    unfold apply_subst. 
	    apply functional_extensionality; intros. 
	    do 2 rewrite H. reflexivity.
	    apply _.
	 }
   } {
     autorewrite with exprD_rw in H3; simpl in H3; forward; inv_all; subst; simpl.
     destruct e1; autorewrite with exprD_rw in H4; simpl in H4; forward; inv_all; subst;
     try (solve [simpl; eexists; split; [eapply mkApplySubst_sound; try eassumption; repeat (autorewrite with exprD_rw; simpl; forward; inv_all; subst); reflexivity|reflexivity]]).
     remember (open_funcS f0); destruct o; [destruct o|];
     try (solve [simpl; eexists; split; [eapply mkApplySubst_sound; try eassumption; repeat (autorewrite with exprD_rw; simpl; forward; inv_all; subst); reflexivity|reflexivity]]).
     { (* const *)
       repeat forward_step.
       rewrite Rcast_id.
       eexists; split; [eapply mkConst_sound; eassumption|]; intros.
       unfold applySubstD, constD, fun_to_typ3; repeat rewrite exprT_App_wrap.
       admit.
     } { (* applySubst *)
		destruct e3; autorewrite with exprD_rw in H5; simpl in H5; forward; inv_all; subst;
        autorewrite with exprD_rw in H3; simpl in H3; forward; inv_all; subst;
        try (solve [simpl; eexists; split; [eapply mkApplySubst_sound; try eassumption; 
          repeat (autorewrite with exprD_rw; simpl; forward; inv_all; subst); try (rewrite H11 in H9; inv_all; subst; forward; inv_all; subst); reflexivity|reflexivity]]).
        remember (baseS f1); destruct o; [destruct b|];
          try (solve [eexists; split; [eapply mkApplySubst_sound; try eassumption|reflexivity];
              repeat (autorewrite with exprD_rw; simpl; forward; inv_all; subst); reflexivity]).
		destruct e0; simpl;
        try (solve [simpl; eexists; split; [eapply mkApplySubst_sound; try eassumption; repeat (autorewrite with exprD_rw; simpl; forward; inv_all; subst); reflexivity|reflexivity]]).
		destruct e0_1; simpl;
        try (solve [simpl; eexists; split; [eapply mkApplySubst_sound; try eassumption; repeat (autorewrite with exprD_rw; simpl; forward; inv_all; subst); reflexivity|reflexivity]]).
		destruct e0_1_1; simpl;
        try (solve [simpl; eexists; split; [eapply mkApplySubst_sound; try eassumption; repeat (autorewrite with exprD_rw; simpl; forward; inv_all; subst); reflexivity|reflexivity]]).
		remember (open_funcS f2). destruct o;
        try (solve [simpl; eexists; split; [eapply mkApplySubst_sound; try eassumption; repeat (autorewrite with exprD_rw; simpl; forward; inv_all; subst); reflexivity|reflexivity]]).
		destruct o; simpl;
        try (solve [simpl; eexists; split; [eapply mkApplySubst_sound; try eassumption; repeat (autorewrite with exprD_rw; simpl; forward; inv_all; subst); reflexivity|reflexivity]]).
		destruct e0_2; simpl;
        try (solve [simpl; eexists; split; [eapply mkApplySubst_sound; try eassumption; repeat (autorewrite with exprD_rw; simpl; forward; inv_all; subst); reflexivity|reflexivity]]).
		remember (baseS f3); destruct o; [destruct b|];
        try (solve [simpl; eexists; split; [eapply mkApplySubst_sound; try eassumption; repeat (autorewrite with exprD_rw; simpl; forward; inv_all; subst); reflexivity|reflexivity]]).
		unfold applySingleSubst.
		clear H0.

		autorewrite with exprD_rw in H1; simpl in H1; forward; inv_all; subst.
		autorewrite with exprD_rw in H6; simpl in H6; forward; inv_all; subst.
		autorewrite with exprD_rw in H1; simpl in H1; forward; inv_all; subst.
		autorewrite with exprD_rw in H7; simpl in H7; forward; inv_all; subst.
		
		consider (s ?[ eq ] s0). {
		  intros; subst; repeat forward_step.
		  repeat rewrite Rcast_id.
		  unfold applySubstD, stack_getD, singleSubstD, fun_to_typ3, fun_to_typ2.
		  repeat rewrite exprT_App_wrap.
		  eexists; split; [eassumption|].
		  intros. 
		  admit.
		} {
		  intros.
		  repeat (autorewrite with exprD_rw; simpl; forward; inv_all; subst).
		  eexists; split; [reflexivity|].
		  intros; repeat forward_step.
		  unfold applySubstD, stack_getD, singleSubstD, fun_to_typ3, fun_to_typ2.
		  repeat rewrite exprT_App_wrap.
		  repeat rewrite Rcast_id.
		  repeat rewrite exprT_App_wrap.
		  admit.
	   }
	 } { (* embed *)
 	   remember (embedS f0); destruct o; [destruct e|]; [|
         simpl; eexists; split; [eapply mkApplySubst_sound; try eassumption; repeat (autorewrite with exprD_rw; simpl; forward; inv_all; subst); reflexivity|reflexivity]
	   ].
  	   admit. (* Need to check if one logic is embedded in the other *)
  	 } {
       destruct e1_1; simpl; autorewrite with exprD_rw in H6; simpl in H6; forward; inv_all; subst;
       try (solve [simpl; eexists; split; [eapply mkApplySubst_sound; try eassumption; repeat (autorewrite with exprD_rw; simpl; forward; inv_all; subst); reflexivity|reflexivity]]).
	   remember (ilogicS f0); destruct o; [destruct i|];
       try (solve [simpl; eexists; split; [eapply mkApplySubst_sound; try eassumption; repeat (autorewrite with exprD_rw; simpl; forward; inv_all; subst); reflexivity|reflexivity]]).
	   {
	    assert (TransitiveClosure.leftTrans (expr_acc (func := func)) e1_2 (App (App (Inj f0) e1_2) e3))
	      by (eapply TransitiveClosure.LTStep; [apply acc_App_r | constructor; eapply acc_App_l]).
	    assert (TransitiveClosure.leftTrans (expr_acc (func := func)) e3 (App (App (Inj f0) e1_2) e3))
	      by (constructor; apply acc_App_r).
	    repeat forward_step.

	    destruct (H0 _ H8 _ H4 _ H7) as [? [? ?]].
	    destruct (H0 _ H9 _ H3 _ H5) as [? [? ?]].
	    clear H0.
		eexists; split; [eapply mkAnd_sound; eassumption|]; intros.
		specialize (H12 _ _ X); specialize (H14 _ _ X).

		unfold applySubstD, andD, fun_to_typ2, fun_to_typ3; repeat rewrite exprT_App_wrap. 
		rewrite <- H12, <- H14.
		unfold applySubstD, fun_to_typ3; repeat rewrite exprT_App_wrap.
		admit.
      } {
	    assert (TransitiveClosure.leftTrans (expr_acc (func := func)) e1_2 (App (App (Inj f0) e1_2) e3))
	      by (eapply TransitiveClosure.LTStep; [apply acc_App_r | constructor; eapply acc_App_l]).
	    assert (TransitiveClosure.leftTrans (expr_acc (func := func)) e3 (App (App (Inj f0) e1_2) e3))
	      by (constructor; apply acc_App_r).
	    repeat forward_step.

	    destruct (H0 _ H8 _ H4 _ H7) as [? [? ?]].
	    destruct (H0 _ H9 _ H3 _ H5) as [? [? ?]].
	    clear H0.
		eexists; split; [eapply mkOr_sound; eassumption|]; intros.
		specialize (H12 _ _ X); specialize (H14 _ _ X).

		unfold applySubstD, orD, fun_to_typ2, fun_to_typ3; repeat rewrite exprT_App_wrap. 
		rewrite <- H12, <- H14.
		unfold applySubstD, fun_to_typ3; repeat rewrite exprT_App_wrap.
		admit.
      } {
	    assert (TransitiveClosure.leftTrans (expr_acc (func := func)) e1_2 (App (App (Inj f0) e1_2) e3))
	      by (eapply TransitiveClosure.LTStep; [apply acc_App_r | constructor; eapply acc_App_l]).
	    assert (TransitiveClosure.leftTrans (expr_acc (func := func)) e3 (App (App (Inj f0) e1_2) e3))
	      by (constructor; apply acc_App_r).
	    repeat forward_step.

	    destruct (H0 _ H8 _ H4 _ H7) as [? [? ?]].
	    destruct (H0 _ H9 _ H3 _ H5) as [? [? ?]].
	    clear H0.
		eexists; split; [eapply mkImpl_sound; eassumption|]; intros.
		specialize (H12 _ _ X); specialize (H14 _ _ X).

		unfold applySubstD, implD, fun_to_typ2, fun_to_typ3; repeat rewrite exprT_App_wrap. 
		rewrite <- H12, <- H14.
		unfold applySubstD, fun_to_typ3; repeat rewrite exprT_App_wrap.
		admit.
     } {
       remember (open_funcS f0); destruct o; [destruct o;
         try (solve [simpl; eexists; split; [eapply mkApplySubst_sound; try eassumption; repeat (autorewrite with exprD_rw; simpl; forward; inv_all; subst); reflexivity|reflexivity]])
       |].
       {
	     assert (TransitiveClosure.leftTrans (expr_acc (func := func)) e1_2 (App (App (Inj f0) e1_2) e3))
	       by (eapply TransitiveClosure.LTStep; [apply acc_App_r | constructor; eapply acc_App_l]).
	     assert (TransitiveClosure.leftTrans (expr_acc (func := func)) e3 (App (App (Inj f0) e1_2) e3))
	       by (constructor; apply acc_App_r).
	     repeat forward_step.
	     
	    destruct (H0 _ H8 _ H4 _ H7) as [? [? ?]].
	    destruct (H0 _ H9 _ H3 _ H5) as [? [? ?]].
	    clear H0.
		eexists; split; [eapply mkAp_sound; eassumption|]; intros.
		specialize (H10 _ _ X); specialize (H14 _ _ X).
	    rewrite Rcast_id.
		unfold applySubstD, apD, fun_to_typ2, fun_to_typ3; repeat rewrite exprT_App_wrap. 
		rewrite <- H10, <- H14.
		unfold applySubstD, fun_to_typ3; repeat rewrite exprT_App_wrap.
		admit.
      } {
        remember (bilogicS f0); destruct o; [destruct b|];
          try (solve [simpl; eexists; split; [eapply mkApplySubst_sound; try eassumption; repeat (autorewrite with exprD_rw; simpl; forward; inv_all; subst); reflexivity|reflexivity]]).
	    { (* Star *) 
	      assert (TransitiveClosure.leftTrans (expr_acc (func := func)) e1_2 (App (App (Inj f0) e1_2) e3))
	        by (eapply TransitiveClosure.LTStep; [apply acc_App_r | constructor; eapply acc_App_l]).
	      assert (TransitiveClosure.leftTrans (expr_acc (func := func)) e3 (App (App (Inj f0) e1_2) e3))
	        by (constructor; apply acc_App_r).
	      repeat forward_step.
	     
	      destruct (H0 _ H8 _ H4 _ H7) as [? [? ?]].
	      destruct (H0 _ H9 _ H3 _ H5) as [? [? ?]].
	      clear H0.
		  eexists; split; [eapply mkStar_sound; eassumption|]; intros.
		  specialize (H12 _ _ X); specialize (H14 _ _ X).

		  unfold applySubstD, starD, fun_to_typ2, fun_to_typ3; repeat rewrite exprT_App_wrap. 
	      rewrite <- H12, <- H14.
		  unfold applySubstD, fun_to_typ3; repeat rewrite exprT_App_wrap.
		  admit.
	    } { (* Wand *) 
	      assert (TransitiveClosure.leftTrans (expr_acc (func := func)) e1_2 (App (App (Inj f0) e1_2) e3))
	        by (eapply TransitiveClosure.LTStep; [apply acc_App_r | constructor; eapply acc_App_l]).
	      assert (TransitiveClosure.leftTrans (expr_acc (func := func)) e3 (App (App (Inj f0) e1_2) e3))
	        by (constructor; apply acc_App_r).
	      repeat forward_step.
	     
	      destruct (H0 _ H8 _ H4 _ H7) as [? [? ?]].
	      destruct (H0 _ H9 _ H3 _ H5) as [? [? ?]].
	      clear H0.
		  eexists; split; [eapply mkWand_sound; eassumption|]; intros.
		  specialize (H12 _ _ X); specialize (H14 _ _ X).

		  unfold applySubstD, wandD, fun_to_typ2, fun_to_typ3; repeat rewrite exprT_App_wrap. 
	      rewrite <- H12, <- H14.
		  unfold applySubstD, fun_to_typ3; repeat rewrite exprT_App_wrap.
		  admit.
		}
      }
    }
  }
}
*)
Time Qed.
	      
	    
  Definition SUBST := SIMPLIFY (typ := typ) (fun _ _ _ _ => beta_all substTac).

  
End SubstTac.
Print SUBST.
Implicit Arguments SUBST [[ST] [BT] [RType_typ] [OF] [ILF] [BILF] [LT] [LF] [EF] [BF] [Typ2_tyArr] [ilp] [bilp] [RelDec_typ] [HBTD] [HLTD]].
