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

Local Notation "'tyStack'" := (typ2 tyString tyVal).
Local Notation "'tySubst'" := (typ2 tyString (typ2 tyStack tyVal)).
Local Notation "'tyExpr'" := (typ2 tyStack tyVal).
Local Notation "'tySubstList'" := (tyList (tyProd tyString (typ2 tyStack tyVal))).

Section ApplySubst.
	Context {typ func : Type} {RType_typ : RType typ} {ST : SubstType typ} {BT : BaseType typ} {LT : ListType typ}
	        {HOF : OpenFunc typ func} {HLF : ListFunc typ func} {HBF : BaseFunc typ func}
	        {BTD : BaseTypeD BT} {LTD : ListTypeD LT}.
	Context {RelDec_typ : RelDec (@eq typ)}.

    Context {Typ2_tyArr : Typ2 RType_typ Fun}.
    Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.

	Definition applySingleSubst (x y : String.string) e :=
		if x ?[ eq ] y then e else App fStackGet (mkString (stringR x)).
		    	
	Fixpoint applyTruncSubst (t : typ) (x : String.string) (lst : expr typ func) : expr typ func :=
	  match listS lst with
	    | Some (pNil u) => mkConst tyVal mkNull
	    | _ => 
	      match lst with
	        | App (App f (App (App g y) e)) ys =>
	          match listS f, baseS g, baseS y with
	            | Some (pCons _), Some (pPair _ _), Some (pConst u y) =>
	              match type_cast u tyString with
	                | Some pf => 
	                  if x ?[ eq ] stringD (eq_rect_r typD y (eq_sym pf)) then
	                    e
	                  else
	                    applyTruncSubst t x ys
	                | None => mkApplySubst t (App fStackGet (mkString (stringR x))) (mkTruncSubst lst)
	              end
	            | _, _, _ => mkApplySubst t (App fStackGet (mkString (stringR x))) (mkTruncSubst lst)
	          end
	        | _ => mkApplySubst t (App fStackGet (mkString (stringR x))) (mkTruncSubst lst)
	      end
	  end.
	  
	Fixpoint applyParSubst (t : typ) (x : String.string) (lst : expr typ func) : expr typ func :=
	  match listS lst with
	    | Some (pNil u) => App (Inj fStackGet) (BaseFunc.mkConst tyString (stringR x))
	    | _ => 
	      match lst with
	        | App (App f (App (App g y) e)) ys =>
	          match listS f, baseS g, baseS y with
	            | Some (pCons _), Some (pPair _ _), Some (pConst u y) =>
	              match type_cast u tyString with
	                | Some pf => 
	                  if x ?[ eq ] stringD (eq_rect_r typD y (eq_sym pf)) then
	                    e
	                  else
	                    applyParSubst t x ys
	                | None => mkApplySubst t (App fStackGet (mkString (stringR x))) (mkSubst lst)
	              end
	            | _, _, _ => mkApplySubst t (App fStackGet (mkString (stringR x))) (mkSubst lst)
	          end
	        | _ => mkApplySubst t (App fStackGet (mkString (stringR x))) (mkSubst lst)
	      end
	  end.
	  
	Definition applySubst (t : typ) (f : expr typ func) (x : String.string) :=
		match f with
		  | App (App g e) y =>
		  	match open_funcS g, baseS y with
		  	  | Some of_single_subst, Some (pConst t' v) => 
		  	    match type_cast t' tyString with
		  	      | Some pf => applySingleSubst x (stringD (eq_rect_r typD v (eq_sym pf))) e
		  	      | None => mkApplySubst t (App fStackGet (mkString (stringR x))) f
		  	    end
		  	  | _, _ => mkApplySubst t (App fStackGet (mkString (stringR x))) f
		    end
		  | App g lst =>
		    match open_funcS g with	  
		  	  | Some of_trunc_subst => applyTruncSubst t x lst
		  	  | _ => mkApplySubst t (App fStackGet (mkString (stringR x))) f
		    end
		  | _ => mkApplySubst t (App fStackGet (mkString (stringR x))) f
	end.

End ApplySubst.

Section PushSubst.
  Context {typ func : Type} {ST : SubstType typ} {BT : BaseType typ} {RType_typ : RType typ}.
  Context {BTD : BaseTypeD BT} {LT : ListType typ} {LTD : ListTypeD LT}.
  Context {OF : OpenFunc typ func} {ILF : ILogicFunc typ func} {BILF : BILogicFunc typ func} {HBF : BaseFunc typ func}.
  Context {EF : EmbedFunc typ func} {LF : ListFunc typ func}.
  Context {RelDec_type : RelDec (@eq typ)}.
  Context {ilp : il_pointwise (typ := typ)}.
  Context {bilp : bil_pointwise (typ := typ)}.
  Context {eilp : eil_pointwise (typ := typ)}.
  Context {Typ2_tyArr : Typ2 _ Fun}.
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
    			    | Some pf => applySubst t f (stringD (eq_rect _ typD x _ pf))
    			    | None => mkApplySubst t e f
    			  end
    			| Some (of_const t), _ => OpenFunc.mkConst t p
    			| Some _, _ => mkApplySubst t e f
    			| None, _ => match embedS g with
    					    | Some (eilf_embed u v) => 
    					      typ2_simple_match u 
    					        (fun d r =>
    					          match type_cast d (tyArr tyString tyVal) with
    					            | Some _ => if eilp u v then mkEmbed u v (pushSubst p r) else mkApplySubst t e f
    					            | _ => mkApplySubst t e f
    					          end) (mkApplySubst t e f)
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
  Context {RelDec_typ : RelDec (@eq typ)}.
  Context {RelDec_typOk : RelDec_Correct RelDec_typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {RSym_func : RSym func}.
  Context {RSym_funcOk : RSymOk RSym_func}.
  Context {Typ2_tyArr : Typ2 _ Fun}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Typ2_tyArrOk : Typ2Ok Typ2_tyArr}.
  Context {HV : ValNull (typD tyVal)}.
  Context {HBTD : BaseTypeD BT} {HLTD : ListTypeD LT}.
  Context {OFOK : OpenFuncOk typ func}.
  Context {LFOK : ListFuncOk typ func}.
  Context {gs : @logic_ops _ RType_typ}.
  Context {bs : @bilogic_ops _ RType_typ}.
  Context {es : @embed_ops _ RType_typ}.
  Context {ILFOK : ILogicFuncOk typ func gs}.
  Context {BILFOK : BILogicFuncOk typ func bs}.
  Context {EILFOK : EmbedFuncOk typ func es}.
  Context {Heqd : SemiEqDecTyp typ}.
  Context {BFOK : BaseFuncOk (RelDec_eq := RelDec_typ) (Heqd := Heqd) typ func}.
  Context {EqDec_typ : EqDec typ eq}.
  Context {ilp : il_pointwise (typ := typ)}.
  Context {ilpOk : il_pointwiseOk gs ilp}.
  Context {bilp : bil_pointwise (typ := typ)}.
  Context {bilpOk : bil_pointwiseOk bs bilp}.
  Context {eilp : eil_pointwise (typ := typ)}.
  Context {eilpOk : eil_pointwiseOk es eilp}.
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
	        pushSubst (ilp := ilp) (bilp := bilp) (eilp := eilp) f e t
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
    (*
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
*)
Require Import Charge.Tactics.Lists.ListTacs.
Require Import Charge.Tactics.Base.DenotationTacs.
Require Import Charge.Tactics.Base.MirrorCoreTacs.
Require Import MirrorCore.Lambda.Expr.

Print Typ2.
Print Typ2Ok.

     Require Import Charge.Tactics.Base.BaseTacs.

  Lemma applyTruncSubst_sound tus tvs x s sD 
    (Hs : ExprDsimul.ExprDenote.exprD' tus tvs tySubstList s = Some sD) :
    ExprDsimul.ExprDenote.exprD' tus tvs tyExpr (applyTruncSubst tyVal (stringD x) s) =
      Some (exprT_App (exprT_App (fun _ _ => applySubstD tyVal)
             (exprT_App (fun _ _ => stack_getD) (fun _ _ => x))) (exprT_App (fun _ _ => truncSubstD) sD)).
  Proof.
     generalize dependent sD; induction s; simpl; intros;
     try (solve [apply mkApplySubst_sound; [apply mkTruncSubst_sound; assumption|
       repeat reduce; repeat bf_rewrite_in_match; reduce; rewrite funcAs_fStackGet_eq;
       reduce; reflexivity]]).
     + repeat destruct_exprs;
     
       try (solve [
	      apply mkApplySubst_sound; [apply mkTruncSubst_sound; assumption|
	      red_exprD_goal; unfold stringR, stringD; rewrite trmRD; rewrite bf_typeof_const; red_exprD_goal; rewrite funcAs_fStackGet_eq;
	      unfold mkString; rewrite BaseFunc.mkConst_sound; reflexivity]]).
       reduce. 
       erewrite mkConst_sound; [|apply mkNull_sound].
       reduce.
       reflexivity.
     + repeat destruct_exprs;
       try (solve [
	     apply mkApplySubst_sound; [apply mkTruncSubst_sound; assumption|
	     red_exprD_goal; unfold stringR, stringD; rewrite trmRD; rewrite bf_typeof_const; red_exprD_goal; rewrite funcAs_fStackGet_eq;
	     unfold mkString; rewrite BaseFunc.mkConst_sound; reflexivity]]).
	   * reduce.
	     unfold prodR.
	     rewrite Heqo13.
	     rewriteD trmDR_cons.
	     rewriteD trmR_eq_refl.
	     rewriteD prodDR.
	     repeat rewriteD @trmR_eq_refl.
	     repeat rewriteD @trmD_eq_refl.
	     unfold apply_subst, stack_subst; simpl.
	     assert (x ?[ eq ] t3 = true) by apply Heqb.
  		 rewrite H.
  		 rewriteD trmD_App.
  		 reduce. reflexivity.
       * reduce. unfold stringD in IHs2. erewrite IHs2; [|eassumption].
         reduce.
  		 unfold apply_subst, stack_subst.
	     unfold prodR.
	     rewriteD trmDR_cons.
	     rewriteD trmR_eq_refl.
	     rewriteD prodDR.
	     repeat rewriteD @trmR_eq_refl.
	     repeat rewriteD @trmD_eq_refl.
	     simpl.
  		 assert (x ?[ eq ] t3 = false) by (apply Heqb).
 		 rewrite H.
 		 rewriteD @trmRD.
 		 reflexivity.
  Qed.

  Lemma applySingleSubst_sound tus tvs x y e eD 
    (Hs : ExprDsimul.ExprDenote.exprD' tus tvs tyExpr e = Some eD) :
    ExprDsimul.ExprDenote.exprD' tus tvs tyExpr (applySingleSubst (stringD x) (stringD y) e) =
      Some (exprT_App (exprT_App (fun _ _ => applySubstD tyVal)
             (exprT_App (fun _ _ => stack_getD) (fun _ _ => x))) 
               (exprT_App (exprT_App (fun _ _ => singleSubstD) eD) (fun _ _ => y))).
  Proof.
    reduce.
    unfold apply_subst, stack_subst, applySingleSubst.
    destruct_exprs.
    + assert (x ?[ eq ] y = true) by (apply Heqb).
      unfold subst1. rewrite H0.
      reduce.
      assumption.
    + assert (x ?[ eq ] y = false) by (apply Heqb).
      unfold subst1; rewrite H0.
      reduce.
	  repeat bf_rewrite_in_match.
	  reduce.
	  rewrite funcAs_fStackGet_eq.
	  reduce.
	  reflexivity.
  Qed.


  Lemma applySubst_sound tus tvs s x sD
    (Hs : ExprDsimul.ExprDenote.exprD' tus tvs tySubst s = Some sD) :
    ExprDsimul.ExprDenote.exprD' tus tvs tyExpr (applySubst tyVal s (stringD x)) =
    Some (exprT_App (exprT_App (fun us vs => applySubstD tyVal) (exprT_App (fun us vs => stack_getD) (fun us vs => x))) sD).
  Proof.
    unfold applySubst.
    repeat destruct_exprs; try (solve [
	    apply mkApplySubst_sound; [assumption|
	    red_exprD_goal; unfold stringR, stringD; rewrite trmRD; rewrite bf_typeof_const; red_exprD_goal; rewrite funcAs_fStackGet_eq;
	    unfold mkString; rewrite BaseFunc.mkConst_sound; reflexivity]]).
    reduce.
    pose proof applyTruncSubst_sound. unfold stringD in H. erewrite H; [|eassumption].
    reduce. reflexivity.
    reduce.
    unfold eq_rect_r, eq_rect. simpl.
    pose proof applySingleSubst_sound.
    unfold stringD in H. erewrite H; [|eassumption].
    reduce. reflexivity.
  Qed.
  
Lemma pushSubst_sound tus tvs (t : typ) (e s : expr typ func)
  (eD : exprT tus tvs (typD (tyArr tyStack t))) (sD : exprT tus tvs (typD tySubst))
  (He : ExprDsimul.ExprDenote.exprD' tus tvs (tyArr tyStack t) e = Some eD)
  (Hs : ExprDsimul.ExprDenote.exprD' tus tvs tySubst s = Some sD) :
  ExprDsimul.ExprDenote.exprD' tus tvs (tyArr tyStack t) (pushSubst (ilp := ilp) (bilp := bilp) (eilp := eilp) s e t) = Some (exprT_App (exprT_App (fun _ _ => applySubstD t) eD) sD).
Proof.
  generalize dependent eD. generalize dependent t.
  induction e using expr_strong_ind; intros; 
    try (simpl; eapply mkApplySubst_sound; eassumption). {
    simpl. do 2 destruct_exprs; try (simpl; eapply mkApplySubst_sound; eassumption).
    + destruct_exprs; [|simpl; eapply mkApplySubst_sound; eassumption].
      unfold tyArr in *.
      reduce.
      unfold apply_subst.
      reduce.
      apply mkTrue_sound; apply H.
    + destruct_exprs; [|simpl; eapply mkApplySubst_sound; eassumption].
      unfold tyArr in *.
      reduce.
      unfold apply_subst.
      reduce.
      apply mkFalse_sound; apply H.
    + do 2 (destruct_exprs; try (solve [simpl; eapply mkApplySubst_sound; eassumption])). 
      unfold tyArr in *. 
      reduce.
      unfold apply_subst.
      reduce.
      apply mkEmp_sound; assumption.
  } {
    simpl.
    destruct_exprs; try (solve [simpl; eapply mkApplySubst_sound; eassumption]).
    + repeat destruct_exprs; try (solve [simpl; eapply mkApplySubst_sound; eassumption]).
      * unfold tyArr in *.
        reduce.
        unfold apply_subst.
        erewrite mkConst_sound; [|eassumption].
        reduce. reflexivity.
      * unfold tyArr in *.
        reduce.
        pose proof applySubst_sound.
        unfold stringD in H1.
        erewrite H1; [|eassumption].
        reduce. reflexivity.
      * unfold tyArr in *.
        apply typ2_simple_match_cases; [simpl; eapply mkApplySubst_sound; eassumption|]; intros.
        destruct_exprs; [|simpl; eapply mkApplySubst_sound; eassumption].
        reduce.
        destruct (eil_pointwise_embed eilpOk _ _ _ _ Heqb).
        destruct (eil_pointwise_embed_range eilpOk _ _ _ _ Heqb).
        erewrite mkEmbed_sound; [|
          eassumption |
          eapply H; [repeat constructor | eassumption]
        ].
        reduce.
        unfold embedD, tyArrR, tyArrR'.
        reduce.
        pose proof (eilf_pointwise_embed_eq eilpOk _ _ _ Heqb H1 H2). unfold tyArrD, tyArrD' in H3; rewriteD H3.
        unfold apply_subst.
        pose proof (eilf_pointwise_embed_eq2 eilpOk _ _ _ Heqb H1 H2); unfold tyArrR, tyArrR' in H4; rewriteD H4.
        reflexivity.
      * apply typ2_simple_match_cases; [simpl; eapply mkApplySubst_sound; eassumption|]; intros.
        destruct_exprs; simpl; eapply mkApplySubst_sound; eassumption.
    + repeat destruct_exprs; try (solve [simpl; eapply mkApplySubst_sound; eassumption]).
      * unfold tyArr in *.
        reduce.
		erewrite mkAnd_sound; [ | 
		  eassumption |
		  eapply H; [eapply TransitiveClosure.LTStep; [eapply acc_App_r | constructor; apply acc_App_l] | 
		             eassumption] |
		  eapply H; [repeat constructor | eassumption]
		].
		reduce.
        pose proof (il_pointwise_andD ilpOk _ _ Heqb H0 H1); unfold tyArrD, tyArrD' in H3; rewriteD H3.
        unfold apply_subst. 
        pose proof (il_pointwise_andR ilpOk _ _ Heqb H0 H1); unfold tyArrR, tyArrR' in H4; rewriteD H4.
        reflexivity.
      * unfold tyArr in *.
        reduce.
		erewrite mkOr_sound; [ | 
		  eassumption |
		  eapply H; [eapply TransitiveClosure.LTStep; [eapply acc_App_r | constructor; apply acc_App_l] | 
		             eassumption] |
		  eapply H; [repeat constructor | eassumption]
		].
		reduce.
        pose proof (il_pointwise_orD ilpOk _ _ Heqb H0 H1); unfold tyArrD, tyArrD' in H3; rewriteD H3.
        unfold apply_subst. 
        pose proof (il_pointwise_orR ilpOk _ _ Heqb H0 H1); unfold tyArrR, tyArrR' in H4; rewriteD H4.
        reflexivity.
      * unfold tyArr in *.
        reduce.
		erewrite mkImpl_sound; [ | 
		  eassumption |
		  eapply H; [eapply TransitiveClosure.LTStep; [eapply acc_App_r | constructor; apply acc_App_l] | 
		             eassumption] |
		  eapply H; [repeat constructor | eassumption]
		].
		reduce.
        pose proof (il_pointwise_implD ilpOk _ _ Heqb H0 H1); unfold tyArrD, tyArrD' in H3; rewriteD H3.
        unfold apply_subst. 
        pose proof (il_pointwise_implR ilpOk _ _ Heqb H0 H1); unfold tyArrR, tyArrR' in H4; rewriteD H4.
        reflexivity.
      * unfold tyArr in *.
        reduce.
		erewrite mkAp_sound; [|
		  eapply H; [eapply TransitiveClosure.LTStep; [eapply acc_App_r | constructor; apply acc_App_l] |
		             eassumption] |
		  eapply H; [repeat constructor | eassumption]
		].
		reduce.
		reflexivity.
      * unfold tyArr in *.
        reduce.
		erewrite mkStar_sound; [ | 
		  eassumption |
		  eapply H; [eapply TransitiveClosure.LTStep; [eapply acc_App_r | constructor; apply acc_App_l] | 
		             eassumption] |
		  eapply H; [repeat constructor | eassumption]
		].
		reduce.
        pose proof (bil_pointwise_starD bilpOk _ _ Heqb H0 H1); unfold tyArrD, tyArrD' in H3; rewriteD H3.
        unfold apply_subst. 
        pose proof (bil_pointwise_starR bilpOk _ _ Heqb H0 H1); unfold tyArrR, tyArrR' in H4; rewriteD H4.
        reflexivity.
      * unfold tyArr in *.
        reduce.
		erewrite mkWand_sound; [ | 
		  eassumption |
		  eapply H; [eapply TransitiveClosure.LTStep; [eapply acc_App_r | constructor; apply acc_App_l] | 
		             eassumption] |
		  eapply H; [repeat constructor | eassumption]
		].
		reduce.
        pose proof (bil_pointwise_wandD bilpOk _ _ Heqb H0 H1); unfold tyArrD, tyArrD' in H3; rewriteD H3.
        unfold apply_subst. 
        pose proof (bil_pointwise_wandR bilpOk _ _ Heqb H0 H1); unfold tyArrR, tyArrR' in H4; rewriteD H4.
        reflexivity.
     }
   Qed.

  Definition SUBST := SIMPLIFY (typ := typ) (fun _ _ _ _ => beta_all substTac).

  
End SubstTac.
Print SUBST.
Implicit Arguments SUBST [[ST] [BT] [RType_typ] [OF] [ILF] [BILF] [LF] [EF] [BF] [Typ2_tyArr] [ilp] [bilp] [eilp] [HBTD]].
