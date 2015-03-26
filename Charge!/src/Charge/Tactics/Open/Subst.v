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
	Context {RelDec_string : RelDec (@eq (typD tyString))}.

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
  Context {RelDec_string : RelDec (@eq (typD tyString))}.
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
  Context {RelDec_string : RelDec (@eq (typD tyString))}.
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
        unfold apply_subst.

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

  Lemma applyTruncSubst_sound tus tvs x s sD 
    (Hs : ExprDsimul.ExprDenote.exprD' tus tvs tySubstList s = Some sD) :
    ExprDsimul.ExprDenote.exprD' tus tvs tyExpr (applyTruncSubst tyVal (stringD x) s) =
      Some (exprT_App (exprT_App (fun _ _ => applySubstD tyVal)
             (exprT_App (fun _ _ => stack_getD) (fun _ _ => x))) (exprT_App (fun _ _ => truncSubstD) sD)).
  Proof.
     induction s; simpl;
     try (solve [
	    apply mkApplySubst_sound; [apply mkTruncSubst_sound; assumption|
	    red_exprD_goal; unfold stringR, stringD; rewrite trmRD; rewrite bf_typeof_const; red_exprD_goal; rewrite funcAs_fStackGet_eq;
	    unfold mkString; rewrite BaseFunc.mkConst_sound; reflexivity]]).
     repeat destruct_exprs;
     try (solve [
	    apply mkApplySubst_sound; [apply mkTruncSubst_sound; assumption|
	    red_exprD_goal; unfold stringR, stringD; rewrite trmRD; rewrite bf_typeof_const; red_exprD_goal; rewrite funcAs_fStackGet_eq;
	    unfold mkString; rewrite BaseFunc.mkConst_sound; reflexivity]]).
    reduce. unfold substD, substR.
    reduce.
    erewrite mkConst_sound; [|apply mkNull_sound].
    reduce.
    unfold nilD, listR. unfold apply_subst, substListD.
    rewriteD trmDR2. reflexivity.
     repeat destruct_exprs;
     try (solve [
	    apply mkApplySubst_sound; [apply mkTruncSubst_sound; assumption|
	    red_exprD_goal; unfold stringR, stringD; rewrite trmRD; rewrite bf_typeof_const; red_exprD_goal; rewrite funcAs_fStackGet_eq;
	    unfold mkString; rewrite BaseFunc.mkConst_sound; reflexivity]]).
    reduce. unfold substD, consD, pairD, prodR, listR, substR, substListD.
    reduce.
    Check (listE (pairE eq_refl (funE (funE eq_refl eq_refl) eq_refl))).
    rewrite Heqo13.
    f_equal.
    do 2 (apply functional_extensionality; intros).
    Check trmDR2.
    Check ((trmD
              (trmR
                 (trmR (t3, e3 x0 x1) (btProd tyString tyExpr)
                  :: trmD (e0 x0 x1) (listE eq_refl)) (listE eq_refl))
              (listE (pairE eq_refl (funE (funE eq_refl eq_refl) eq_refl))))).  

                 Check ((trmR (t3, e3 x0 x1) (btProd tyString tyExpr)
                  :: (trmD (e0 x0 x1) (listE eq_refl)))).
                  Check @listE.
                  Check eq_trans.
  Lemma trmDR_cons (t : typ) A B (x : A) (xs : list A) (e1 : typD t = A) (e2 : typD t = B) :
    (trmD (trmR (x :: xs) (listE e1)) (listE e2)) =
      trmD (trmR x e1) e2 :: trmD (trmR xs (listE e1)) (listE e2). 
  Proof.
	unfold trmD, trmR, listE, eq_ind, eq_rect_r, eq_rect, eq_sym, id.
	clear.
	revert e1 e2.
	generalize (btList t).
	generalize dependent (typD (tyList t)).
	generalize dependent (typD t); intros; repeat subst. reflexivity.
  Qed.
  
  Lemma trmR_eq_refl A t (x : A) (e : typD t = A) :
    trmR (trmR x e) eq_refl = trmR x e.
  Proof.
    unfold trmR, eq_rect_r, eq_rect, eq_sym.
    clear.
    revert e.
    generalize dependent (typD t); intros; subst. reflexivity.
  Qed.
  
  rewrite trmDR_cons.
  
  rewrite trmR_eq_refl.

  Lemma prodDR (t u : typ) A B C D (x : A) (y : B) (e1 : typD t = A) (e2 : typD u = B) (e3 : typD t = C) (e4 : typD u = D) :
    trmD (trmR (x, y) (pairE e1 e2)) (pairE e3 e4) = 
    (trmD (trmR x e1) e3, trmD (trmR y e2) e4).
  Proof.
    unfold trmD, trmR, pairE, eq_ind, eq_rect_r, eq_rect, eq_sym, id.
    clear.
    revert e1 e2 e3 e4.
    generalize (btProd t u).
    generalize dependent (tyProd t u).
    generalize dependent (typD t).
    generalize dependent (typD u).
    do 3 intros.
    generalize dependent (typD t0).
    intros; repeat subst. reflexivity.
  Qed.
  
  replace (pairE (t := tyString) (u := tyExpr) eq_refl eq_refl) with (btProd tyString tyExpr). 
  
  rewriteD prodDR.
  
  
  
  
  rewriteD trmDR2.
  Opaque pairE.
  unfold eq_sym, eq_trans, funE. simpl.
  simpl.
  
  rewriteD trmD_cons.
    unfold listE, pairE.
    rewriteD trmDR2.
    erewrite mkApplySubst_sound.
    Focus 2.
    apply mkTruncSubst_sound.
    reduce.
    reflexivity.
    induction s; simpl;
    try (solve [apply mkApplySubst_sound; [apply mkTruncSubst_sound; assumption |
                red_exprD_hyp; red_exprD_goal; rewrite bf_typeof_const; red_exprD_goal; rewrite funcAs_fStackGet_eq; 
                unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]]).
    Focus 2.
    + repeat (destruct_exprs;
      try (solve [apply mkApplySubst_sound; [apply mkTruncSubst_sound; assumption |
                red_exprD_hyp; red_exprD_goal; rewrite bf_typeof_const; red_exprD_goal; rewrite funcAs_fStackGet_eq; 
                unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]])).
      reduce.

repeat rewrite exprT_App_wrap_sym.
repeat rewrite exprT_App_wrap_tyArrD.
repeat unfold applySubstD, truncSubstD, substR, substD, stack_getD, tyArrR3, tyArrD2, tyArrD2', tyArrR2, tyArrR3', tyArrR2', tyArrR, tyArrR', tyArrD, tyArrD'.
repeat rewrite trmDR.
Check @trmDR.
repeat rewriteD @trmDR.
unfold substListD, nilD.
unfold listR.
Check @listE.
Check @trmR.
Check (trmD (trmR nil (listE eq_refl))
              (listE (pairE eq_refl (funE (funE eq_refl eq_refl) eq_refl)))).



rewrite trmDR2.

erewrite mkConst_sound; [|eapply mkNull_sound].
rewrite exprT_App_wrap_tyArrD.
unfold tyArrD, tyArrD', constD, tyArrR, tyArrR'.
rewrite trmDR. reflexivity.


Focus 2. intros; subst.
reflexivity.
pose proof (@trmDR2 tyList list (@listE typ _ _ _)).
rewriteD H.
rewriteD trmDR2.

pose proof (@trmDR2 tyList list (tyProd tyString (tyArr tyStack tyExpr)) (String.string * (@Open.expr (typD tyString) (typD tyVal))) (@listE typ _ _ _) nil (pairE eq_refl (funE (funE eq_refl eq_refl) eq_refl))).
unfold listE.
simpl.
rewriteD @trmDR2.
  generalize dependent (typD (f t)).
  generalize dependent (typD t).
  intros; subst.
  generalize (f t).
  generalize dependent (typD (f t)).
rewriteD @trmDR.
simpl.

erewrite mkConst_sound; [|eapply mkNull_sound].
f_equal. rewrite exprT_App_wrap_tyArrD.
do 2 (apply functional_extensionality; intros).
simpl.

rewriteD @trmDR.
Print ap.
rewrite mkConst_sound.
assert (tyExpr = tyVal) by admit.
rewrite H.
Check mkNull_sound.
rewrite mkNull_sound.
rewrite trmDR.
unfold 
unfold substD.
repeat rewriteD fun_to_typ_inv.
Lemma substDR s : substD (substR s) = s.
Proof.
  admit.
Qed.

rewrite substDR.

Lemma substListD_nil : substListD (nilD (tyProd tyString tyExpr)) = nil.
Proof.
  admit.
Qed.

rewrite substListD_nil. simpl.
unfold apply_subst.
admit.

    + repeat (destruct_exprs;
      try (solve [apply mkApplySubst_sound; [apply mkTruncSubst_sound; assumption |
                red_exprD_hyp; red_exprD_goal; rewrite bf_typeof_const; red_exprD_goal; rewrite funcAs_fStackGet_eq; 
                unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]])).
      idtac.
      reduce.
      repeat rewrite exprT_App_wrap_sym.
      unfold applySubstD, stack_getD, truncSubstD, pairD, fun_to_typ3, fun_to_typ2.
      repeat rewriteD fun_to_typ_inv.
      rewriteD substDR.
      clear IHs1 IHs2.
      Check consD.
  Lemma listR_cons x xs t :
    listR (x :: xs) = (fun_to_typ2 (consD t)) x (listD xs).
      Print substListD.
     (try red_exprD_hyp).
      Require Import  Charge.Tactics.Base.BaseTacs.
	 forward_step.
	 forward_step.
	 forward_step.
	 bf_forward_step.
	 bf_forward_step.
	 forward_step.
	 forward_step.
	 forward_step.
     repeat bf_forward_step.
     repeat lf_forward_step.
repeat forward_step.
reduce.
 
      bf_forward_step.
      bf_forward_step.
      bf_forward_step.
      bf_forward_step.
      lf_forward_step.
      lf_forward_step.
      repeat forward_step.
      reduce.
      bf_forward_step.
      lf_forward_step.
      prod_inj.
      repeat exprD_saturate_types.
      repeat (first [rewrite_in_match | bf_rewrite_in_match]).
      (try red_exprD_goal).
      repeat (first [
        progress (unfold foldD, fun_to_typ3) |
        progress (unfold consD, fun_to_typ2) |
        progress (repeat rewrite (exprT_App_wrap) in *)]).
        forward_step.
        forward_step.

  match goal with
    | typ : Type |- _ =>
      match goal with
        | BT : BaseType typ, RType_typ : RType typ |- _ => 
          match goal with
            | _ : BaseTypeD, H : tyProd _ _ = tyProd _ _ |- _ => apply tyProd_inj in H; unfold Rty in H; destruct H; subst
          end
      end
  end.
reduce.
        
        
        prod_inj.
        bf_forward_step.
        repeat forward_step.
  (try red_exprD_hyp); repeat forward_step; (repeat exprD_saturate_types); (repeat (first [rewrite_in_match | bf_rewrite_in_match])); (try red_exprD_goal); repeat (first [
        progress (unfold foldD, fun_to_typ3) |
        progress (unfold consD, fun_to_typ2) |
        progress (repeat rewrite (exprT_App_wrap) in *)]).

      bf_rewrite_in_match.
      reduce.
      bf_forward_step.
      bf_forward_step.
      bf_forward_step.
      bf_forward_step.
      bf_forward_step.
      bf_forward_step.
      bf_forward_step.
      r_inj H8.
      bf_forward_step.
      bf_forward_step.
      bf_forward_step.
	  reduce.
assert (exists LFOK : ListFuncOk typ func, True) by admit.
destruct H as [LFOK _].

  repeat rewrite exprT_App_wrap_sym.
  reduce.
Check pPair.
Ltac bf_pair_type :=
  match goal with
    | H1 : baseS ?e = Some (pPair ?t ?u) |- _ =>
      match goal with
        | _ : ExprDsimul.ExprDenote.funcAs e
   			  (typ2 t (typ2 u (tyProd t u))) = Some _ |- _ => fail 1
        | _ : ExprDsimul.ExprDenote.exprD' _ _  
              (typ2 t (typ2 u (tyProd t u))) e = Some _ |- _ => fail 1
        | H2 : ExprDsimul.ExprDenote.funcAs e _ = Some _ |- _ =>
  	  	  let H := fresh "H" in
	        pose proof (bf_pair_type_eq _ _ H1 H2) as H; r_inj H; repeat clear_eq; subst
	  end
  end.

  clear IHs1. clear IHs2.
bf_pair_type.
bf_pair_type.  
  bf_const_expr.
  
  lf_cons_expr.


pose proof (lf_cons_func_type_eq _ _ Heqo Heqo8).

  match goal with
    | H1 : listS ?e = Some (pCons ?t) |- _ =>
      match goal with
        | _ : ExprDsimul.ExprDenote.funcAs e (typ2 t (typ2 (tyList t) (tyList t))) = Some _ |- _ => fail 1
        | _ : ExprDsimul.ExprDenote.exprD' _ _ (typ2 t (typ2 (tyList t) (tyList t))) e = Some _ |- _ => fail 1
        | H2 : ExprDsimul.ExprDenote.funcAs e _ = Some _ |- _ =>
  	  	  let H := fresh "H" in
	        pose proof (lf_cons_func_type_eq _ _ H1 H2) as H; try (r_inj H); try list_inj; repeat clear_eq; subst
	    | H2 : ExprDsimul.ExprDenote.exprD' _ _ _ e = Some _ |- _ =>
	      let H := fresh "H" in
	        pose proof (lf_cons_type_eq _ _ H1 H2) as H; try (r_inj H); try list_inj; repeat clear_eq; subst
	  end
  end.


  repeat rewrite exprT_App_wrap_sym.
  lf_cons_type.
unfold substListD.
Print substListD.
lf_nil_type.
pose proof (@lf_nil_func_type_eq typ func RType_typ LF RSym_func RelDec_typ BT HBTD LT HLTD Typ2_tyArr Typ0_Prop LFOK RTypeOk_typ _ _ _ _ Heqo Heqo0).
  match goal with
    | _ : listS ?e = Some (pNil ?t), _ : ExprDsimul.ExprDenote.funcAs ?e (tyList ?t) = Some _ |- _ => fail 1
    | _ : listS ?e = Some (pNil ?t), _ : ExprDsimul.ExprDenote.exprD' ?tus ?tvs (tyList ?t) ?e = Some _ |- _ => fail 1
 	| H1 : listS ?e = Some (pNil _), H2 : ExprDsimul.ExprDenote.funcAs ?e _ = Some _ |- _ => 
	  let H := fresh "H" in idtac end.
	  
	  
	     pose proof (lf_nil_func_type_eq _ _ H1 H2) as H end list_inj; repeat clear_eq; subst
	| H1 : listS ?e = Some (pNil _), H2 : ExprDsimul.ExprDenote.exprD' _ _ _ ?e = Some _ |- _ =>
	  let H := fresh "H" in
	     pose proof (lf_nil_type_eq _ _ H1 H2) as H; list_inj; repeat clear_eq; subst
  end.


      lf_nil_type.
  Qed.
  
  apply applyTruncSubst_sound.
assumption.
repeat rewrite exprT_App_wrap_sym.
unfold applySubstD, stack_getD, truncSubstD, fun_to_typ2, fun_to_typ3.
repeat rewriteD fun_to_typ_inv. 
rewrite substDR.
Check exprT_App_wrap_sym.
repeat rewriteD exrpT_App_wrap_sym.
simpl.
pose proof (bf_pair_type_eq _ _ Heqo0 Heqo10). 
r_inj H.
Print substlist.
progress reduce.

of_trunc_subst_expr.



  of_single_subst_func_type_eq.
  Lemma applySingleSubst_sound tus tvs x y e sD :
    ExprDsimul.ExprDenote.exprD' tus tvs tyExpr (applySingleSubst (stringD x) (stringD y) e) =
      Some (exprT_App (exprT_App (fun us vs => applySubstD tyVal) (exprT_App (fun us vs => stack_getD) (fun us vs => x))) sD).
  Proof.
    admit.
    
    
     solve [
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
solve [
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
solve [
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
solve [
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
solve [
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
solve [
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
solve [
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
solve [
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
solve [
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
solve [
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
solve [
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
solve [
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
solve [
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
solve [
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
solve [
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
      solve [apply mkApplySubst_sound; [assumption|
             red_exprD_hyp; red_exprD_goal; rewrite bf_typeof_const; red_exprD_goal; rewrite funcAs_fStackGet_eq; 
             unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
      solve [apply mkApplySubst_sound; [assumption|
             red_exprD_hyp; red_exprD_goal; rewrite bf_typeof_const; red_exprD_goal; rewrite funcAs_fStackGet_eq; 
             unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
      solve [apply mkApplySubst_sound; [assumption|
             red_exprD_hyp; red_exprD_goal; rewrite bf_typeof_const; red_exprD_goal; rewrite funcAs_fStackGet_eq; 
             unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
      solve [apply mkApplySubst_sound; [assumption|
             red_exprD_hyp; red_exprD_goal; rewrite bf_typeof_const; red_exprD_goal; rewrite funcAs_fStackGet_eq; 
             unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
      solve [apply mkApplySubst_sound; [assumption|
             red_exprD_hyp; red_exprD_goal; rewrite bf_typeof_const; red_exprD_goal; rewrite funcAs_fStackGet_eq; 
             unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
      solve [apply mkApplySubst_sound; [assumption|
             red_exprD_hyp; red_exprD_goal; rewrite bf_typeof_const; red_exprD_goal; rewrite funcAs_fStackGet_eq; 
             unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
      solve [apply mkApplySubst_sound; [assumption|
             red_exprD_hyp; red_exprD_goal; rewrite bf_typeof_const; red_exprD_goal; rewrite funcAs_fStackGet_eq; 
             unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
      solve [apply mkApplySubst_sound; [assumption|
             red_exprD_hyp; red_exprD_goal; rewrite bf_typeof_const; red_exprD_goal; rewrite funcAs_fStackGet_eq; 
             unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
      solve [apply mkApplySubst_sound; [assumption|
             red_exprD_hyp; red_exprD_goal; rewrite bf_typeof_const; red_exprD_goal; rewrite funcAs_fStackGet_eq; 
             unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
      solve [apply mkApplySubst_sound; [assumption|
             red_exprD_hyp; red_exprD_goal; rewrite bf_typeof_const; red_exprD_goal; rewrite funcAs_fStackGet_eq; 
             unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
      solve [apply mkApplySubst_sound; [assumption|
             red_exprD_hyp; red_exprD_goal; rewrite bf_typeof_const; red_exprD_goal; rewrite funcAs_fStackGet_eq; 
             unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
      solve [apply mkApplySubst_sound; [assumption|
             red_exprD_hyp; red_exprD_goal; rewrite bf_typeof_const; red_exprD_goal; rewrite funcAs_fStackGet_eq; 
             unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
      solve [apply mkApplySubst_sound; [assumption|
             red_exprD_hyp; red_exprD_goal; rewrite bf_typeof_const; red_exprD_goal; rewrite funcAs_fStackGet_eq; 
             unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].

      Require Import Charge.Tactics.Open.OpenTacs.
  pose proof (of_const_func_type_eq _ _ Heqo Heqo7).
      of_const_type.
      of_const_type.
      of_forward_step.
      of_forward_step.
      of_forward_step.
      of_const_type.
      unfold tyArr in *.
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
  subst.
  pose proof (of_const_func_type_eq _ _ Heqo Heqo7).
  unfold Rty in H4.
  r_inj H4.

       repeat of_forward_step.
solve [
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
solve [
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
solve [
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
solve [
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
solve [
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
solve [
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
solve [
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
solve [
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
solve [
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
apply mkApplySubst_sound. assumption.
reduce.
rewrite bf_typeof_const. reduce. rewrite funcAs_fStackGet_eq. unfold mkString. rewrite BaseFunc.mkConst_sound.uuuuu
 solve [reduce;
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
try solve [reduce;
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
try solve [reduce;
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
try solve [reduce;
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
try solve [reduce;
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
try solve [reduce;
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
try solve [reduce;
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
try solve [reduce;
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
try solve [reduce;
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
try solve [reduce;
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
try solve [reduce;
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
try solve [reduce;
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
try solve [reduce;
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
try solve [reduce;
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
try solve [reduce;
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
try solve [reduce;
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
try solve [reduce;
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
try solve [reduce;
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
try solve [reduce;
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
    apply mkApplySubst_sound; 
      [assumption |
      reduce; rewrite bf_typeof_const; reduce; rewrite funcAs_fStackGet_eq; unfold mkString; rewrite BaseFunc.mkConst_sound; rewrite stringRD; reflexivity]].
    reduce.
    Check bf_const_type_eq.
    rewrite bf_typeof_const.
    reduce.
    rewrite funcAs_fStackGet_eq.
    unfold mkString. rewrite BaseFunc.mkConst_sound.
    rewrite stringRD. reflexivity.
  Lemma fStackGet_func_eq : funcAs fStackGet tySubst = Some stack_getD.
  Proof.
    admit.
  Qed.
  
  rewrite fStackGet_func_eq.
  unfold mkString.
  
  rewrite BaseFunc.mkConst_sound.
  rewrite stringRD. reflexivity.
  apply mkString_sound.
    Check
        reduce.
    destruct s; simpl; [admit | admit | | admit | admit].
    do 2 destruct_exprs.
    apply mkApplySubst_sound; try assumption.
    reduce. rewrite stringRD. simpl.
    assert (typeof_sym (BaseFunc.fConst tyString x) = Some tyString) by admit.
    rewrite H0.
    reduce.
    assert (funcAs fStackGet tySubst = Some stack_getD) by admit.
    rewrite H1. 
    unfold mkString.
    rewrite BaseFunc.mkConst_sound.
    reflexivity.
    apply mkApplySubst_sound.
  Qed.
    apply mkApplySubst_sound.
  Qed.
  apply applySubst_sound. assumption.
    destruct s; simpl.
    
    erewrite mkApplySubst_sound; try eassumption.
    Focus 2.
    reduce.
    rewrite stringRD.
    assert (typeof_sym (BaseFunc.fConst tyString x) = Some tyString) by admit.
    rewrite H0. reduce.
    assert (funcAs fStackGet tySubst = Some stack_getD) by admit.
    rewrite H1.
    unfold mkString.
    rewrite BaseFunc.mkConst_sound. 
    reflexivity.
    repeat rewrite exprT_App_wrap_sym.
    unfold applySubstD, stack_getD, fun_to_typ2, fun_to_typ3.
    repeat rewrite fun_to_typ_inv.
    rewriteD fun_to_typ_inv. reflexivity.
    unfold fStackGet.
    apply mkApplySubst_sound.
  Qed.
    
    apply applySubst_sound.
    assumption.
        simpl.
        repeat rewriteD exprT_App_wrap.
        rewriteD exprT_App_wrap_sym.
Check @apply_subst.

  Lemma applySubst_sound
    ExprDsimul.ExprDenote.exprD' tus tvs tyExpr (applySubst Typ2_tyArr tyVal f (stringD x)) =
      fun us vs => fun_to_typ (fun c => apply_subst (fun x => typ_to_fun (typ_to_fun fD x) (fun_to_typ
        
        rewriteD_sym exprT_App_wrap_sym.
        unfold apply_subst.
        rewriteD exprT_App_wrap_sym.
        rewriteD fun_to_typ_inv.
        repeat rewrite exrpT_App_wrap.
      
      * unfold tyArr in *.
        apply typ2_simple_match_cases; [eapply mkApplySubst_sound; eassumption|]; intros.
        destruct_exprs; [|eapply mkApplySubst_sound; eassumption]; intros.
        reduce.
        eilf_embed_type.
        destruct (eil_pointwise_embed eilpOk _ _ _ _ Heqb).
        destruct (eil_pointwise_embed_range eilpOk _ _ _ _ Heqb).
        eilf_embed_expr.
        erewrite mkEmbed_sound; [|
          eassumption |
          eapply H; [repeat constructor | eassumption]
        ].
        unfold applySubstD, embedD, fun_to_typ3.
        repeat rewrite exprT_App_wrap_sym.
        repeat rewriteD fun_to_typ_inv.
        rewriteD (eilf_pointwise_embed_eq eilpOk _ _ _ Heqb H1 H2).
   	    unfold apply_subst.
        rewriteD (eilf_pointwise_embed_eq2 eilpOk _ _ _ Heqb H1 H2).
        reflexivity.
      * apply typ2_simple_match_cases; [eapply mkApplySubst_sound; eassumption|]; intros.
        destruct_exprs; eapply mkApplySubst_sound; eassumption.
    + do 3 (destruct_exprs; try (solve [simpl; eapply mkApplySubst_sound; eassumption])).
      * reduce.
        ilf_and_type.
        destruct (il_pointwise_ilogic ilpOk _ _ Heqb). 
        ilf_and_expr.
		erewrite mkAnd_sound; [ | 
		  eassumption |
		  eapply H; [| eassumption] |
		  eapply H; [repeat constructor | eassumption]
		].
		unfold andD, applySubstD, substD, fun_to_typ3, fun_to_typ2.
	    repeat rewrite exprT_App_wrap.
        destruct (il_pointwise_ilogic_range ilpOk _ _ Heqb).
        rewriteD (il_pointwise_and_eq ilpOk _ _ Heqb H1 H2).
        unfold apply_subst.
        rewriteD (il_pointwise_and_eq2 ilpOk _ _ Heqb H1 H2).
        reflexivity.

		eapply TransitiveClosure.LTStep.
		eapply acc_App_r.
		constructor.
		apply acc_App_l.
      * reduce.
        ilf_or_type.
        destruct (il_pointwise_ilogic ilpOk _ _ Heqb). 
        ilf_or_expr.
		erewrite mkOr_sound; [ |
		  eassumption |
		  eapply H; [| eassumption] |
		  eapply H; [repeat constructor | eassumption]
		].
		unfold orD, applySubstD, substD, fun_to_typ3, fun_to_typ2.
	    repeat rewrite exprT_App_wrap.
        destruct (il_pointwise_ilogic_range ilpOk _ _ Heqb).
        rewriteD (il_pointwise_or_eq ilpOk _ _ Heqb H1 H2).
        unfold apply_subst.
        rewriteD (il_pointwise_or_eq2 ilpOk _ _ Heqb H1 H2).
        reflexivity.

		eapply TransitiveClosure.LTStep.
		eapply acc_App_r.
		constructor.
		apply acc_App_l.
      * reduce.
        ilf_impl_type.
        destruct (il_pointwise_ilogic ilpOk _ _ Heqb). 
        ilf_impl_expr.
		erewrite mkImpl_sound; [ |
		  eassumption |
		  eapply H; [| eassumption] |
		  eapply H; [repeat constructor | eassumption]
		].
		unfold implD, applySubstD, substD, fun_to_typ3, fun_to_typ2.
	    repeat rewrite exprT_App_wrap.
        destruct (il_pointwise_ilogic_range ilpOk _ _ Heqb).
        rewriteD (il_pointwise_impl_eq ilpOk _ _ Heqb H1 H2).
        unfold apply_subst.
        rewriteD (il_pointwise_impl_eq2 ilpOk _ _ Heqb H1 H2).
        reflexivity.

		eapply TransitiveClosure.LTStep.
		eapply acc_App_r.
		constructor.
		apply acc_App_l.
      * reduce.
        of_ap_type.
        unfold tyArr in *.
		of_ap_expr.
		erewrite mkAp_sound; [|
		  eapply H; [|eassumption] |
		  eapply H; [repeat constructor | eassumption]
		].
		unfold apD, applySubstD, substD, fun_to_typ3, fun_to_typ2, typ_to_fun2.
		repeat rewrite exprT_App_wrap.
		repeat rewriteD fun_to_typ_inv.
		reflexivity.
		eapply TransitiveClosure.LTStep.
		eapply acc_App_r.
		constructor.
		apply acc_App_l.

      * do 2 (destruct_exprs; try (solve [simpl; eapply mkApplySubst_sound; eassumption])).
        - reduce.
          bilf_star_type.
          unfold tyArr in *.
          destruct (bil_pointwise_bilogic bilpOk _ _ Heqb). 
          bilf_star_expr.
	      erewrite mkStar_sound; [ |
		    eassumption |
		    eapply H; [| eassumption] |
		    eapply H; [repeat constructor | eassumption]
		  ].
		  unfold starD, applySubstD, substD, fun_to_typ3, fun_to_typ2.
	      repeat rewrite exprT_App_wrap.
          destruct (bil_pointwise_bilogic_range bilpOk _ _ Heqb).
          rewriteD (bil_pointwise_star_eq bilpOk _ _ Heqb H1 H2).
          unfold apply_subst.
          rewriteD (bil_pointwise_star_eq2 bilpOk _ _ Heqb H1 H2).
          reflexivity.

		  eapply TransitiveClosure.LTStep.
		  eapply acc_App_r.
		  constructor.
		  apply acc_App_l.
        - reduce.
          bilf_wand_type.
          unfold tyArr in *.
          destruct (bil_pointwise_bilogic bilpOk _ _ Heqb). 
          bilf_wand_expr. (* Can be run twice *)
	      erewrite mkWand_sound; [ |
		    eassumption |
		    eapply H; [| eassumption] |
		    eapply H; [repeat constructor | eassumption]
		  ].
		  unfold wandD, applySubstD, substD, fun_to_typ3, fun_to_typ2.
	      repeat rewrite exprT_App_wrap.
          destruct (bil_pointwise_bilogic_range bilpOk _ _ Heqb).
          rewriteD (bil_pointwise_wand_eq bilpOk _ _ Heqb H1 H2).
          unfold apply_subst.
          rewriteD (bil_pointwise_wand_eq2 bilpOk _ _ Heqb H1 H2).
          reflexivity.

		  eapply TransitiveClosure.LTStep.
		  eapply acc_App_r.
		  constructor.
		  apply acc_App_l.
    }
Qed. 

Lemma substTac_sound : partial_reducer_ok (substTac nil).
  Proof.
    unfold partial_reducer_ok. intros.
    eexists; split; [|reflexivity].
    unfold substTac.
    do 5 (destruct_exprs; try assumption).
    simpl in H.
    reduce.   
    eapply pushSubst_sound; try eassumption.
Qed.
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
