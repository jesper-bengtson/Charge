Require Import String.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprVariables.
Require Import MirrorCore.Lambda.AppN.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.Lambda.RedAll.

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
	Context {typ func : Type} {RType_typ : RType typ} {ST : SubstType typ} {BT : BaseType typ}
	        {HOF : OpenFunc typ func} {HLF : ListFunc typ func} {HBF : BaseFunc typ func}.
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
    							applyParSubst p x vs es
    					else
    						fNull
    				| _, _ => fNull
    			end
    		| _ => fNull
    	end.				
Check @open_funcS.
Print baseS.
	Definition applySubst (t : typ) (f e : expr typ func) (x : String.string) :=
		match f with
		  | App (App g e') y =>
		  	match open_funcS g, baseS y with
		  	  | Some (of_singleSubst), Some (pString v) => applySingleSubst e x v e'
		  	  | _, _ => mkApplySubst t e f
		  	end
		  | _ => mkApplySubst t e f
(*		  | mkApplySubst [t, p, mkSubstList [mkVarList [vs], es]] => applyParSubst p x vs es
		  | mkApplyTruncSubst [t, p, mkSubstList [mkVarList [vs], es]] => applyTruncSubst x vs es*)
		end.

End ApplySubst.

Section PushSubst.
  Context {typ func : Type} {ST : SubstType typ} {BT : BaseType typ} {RType_typ : RType typ}.
  Context {OF : OpenFunc typ func} {ILF : ILogicFunc typ func} {BILF : BILogicFunc typ func} {HBF : BaseFunc typ func}.
  Context {EF : EmbedFunc typ func}.
  Context {RelDec_string : RelDec (@eq (typD tyString))}.
  Context {RelDec_type : RelDec (@eq typ)}.
  
  Variable Typ2_tyArr : Typ2 _ Fun.
  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.

  Variable f : expr typ func.


  Fixpoint pushSubst (e : expr typ func) (t : typ) : expr typ func :=
    match e with
    	| App (App g p) q =>
    		match ilogicS g with
    			| Some (ilf_and l) => mkAnd l (pushSubst p l) (pushSubst q l)
    			| Some (ilf_or l) => mkOr l (pushSubst p l) (pushSubst q l)
    			| Some (ilf_impl l) => mkImpl l (pushSubst p l) (pushSubst q l)
    			| _ => match open_funcS g with
		    			 | Some (of_ap t1 t2) => mkAp t1 t2 (pushSubst p (tyArr t1 t2))
		    			             									 (pushSubst q t2)
		    			 | _ => match bilogicS g with
		    			          | Some (bilf_star l) => mkStar l (pushSubst p l) (pushSubst q l)
		    			          | Some (bilf_wand l) => mkWand l (pushSubst p l) (pushSubst q l)
		    			 	      | _ => mkApplySubst t e f
		    			 	    end
		    		   end
    		end
    	| App g p =>
    		match open_funcS g, baseS p with
    			| Some of_stack_get, Some (pString x) => applySubst t f e x
    			| Some (of_const _), _ => e
    			| _, _ => match embedS g with
    					    | Some (eilf_embed u v) => mkEmbed u v (pushSubst p u)
    					    | _ => mkApplySubst t e f
    					  end
    		end
    	| _ => match ilogicS e with
    		     | Some (ilf_true l) => mkTrue l
    		     | Some (ilf_false l) => mkFalse l
    		     | _ => match bilogicS e with
    		     		  | Some (bilf_emp l) => mkEmp l
    		     		  | _ => mkApplySubst t e f
    		     		end
    		   end
    end.
    
End PushSubst.
(*
Implicit Arguments typeof_funcAs [[typ] [func] [RType_typ] [RSym_func] [f] [t] [e]].
*)

Section SubstTac.
  Context {typ func subst : Type} {ST : SubstType typ} {BT : BaseType typ} {RType_typ : RType typ}.
  Context {OF : OpenFunc typ func} {ILF : ILogicFunc typ func} {BILF : BILogicFunc typ func} {BF : BaseFunc typ func}.
  Context {LT : ListType typ}.
  Context {EF : EmbedFunc typ func}.
  Context {RelDec_string : RelDec (@eq (typD tyString))}.
  Context {RelDec_typ : RelDec (@eq typ)}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {RSym_func : RSym func}.
  Context {RSym_funcOk : RSymOk RSym_func}.
  Variable Typ2_tyArr : Typ2 _ Fun.
  Variable Typ0_Prop : Typ0 _ Prop.
  Context {Typ2_tyArrOk : Typ2Ok Typ2_tyArr}.
  Context {HV : ValNull (typD tyVal)}.
  Context {HSTD : SubstTypeD}.
  Context {HBTD : BaseTypeD} {HLTD : ListTypeD}.
  Context {OFOK : OpenFuncOk typ func}.
  Context {gs : @logic_ops _ RType_typ}.
  Context {bs : @bilogic_ops _ RType_typ}.
  Context {ILFOK : ILogicFuncOk typ func gs}.
  Context {BILFOK : BILogicFuncOk typ func bs}.
  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.

  Let Expr_expr := Expr_expr (typ := typ) (func := func).
  Let ExprOk_expr := ExprOk_expr (typ := typ) (func := func).
  Let ExprUVar_expr := ExprUVar_expr (typ := typ) (func := func).
  
  Local Existing Instance Expr_expr.
  Local Existing Instance ExprOk_expr.
  Local Existing Instance ExprUVar_expr.

  Definition substTac (_ : list (option (expr typ func))) (e : expr typ func) (args : list (expr typ func))
  : expr typ func :=
    match open_funcS e with
	  | Some (of_apply_subst t) =>
	    match args with
	      | e :: f :: nil =>
	        pushSubst Typ2_tyArr f e t
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

    Lemma exprT_App_wrap tus tvs (t u : typ) (f : HList.hlist typD tus -> HList.hlist typD tvs -> typD t -> typD u) (a : exprT tus tvs (typD t)) :
      exprT_App (fun us vs => fun1_wrap _ (f us vs)) a = fun us vs => (f us vs) (a us vs).
    Proof.
      unfold fun1_wrap, exprT_App, eq_rect_r, eq_sym, eq_rect.
      forward.
    Qed.

  Lemma substTac_ok : partial_reducer_ok (substTac nil).
  Proof.
    admit.
  Qed.
    (*
    unfold partial_reducer_ok; intros.
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
    
    symmetry in Heqo.
    pose proof (typeof_funcAs _ _ H2).
    pose proof (OpenFunc_typeOk _ Heqo).
    rewrite H4 in H5. simpl in H5.
    inversion H5; subst.
    apply typ2_inj in H7 as [H7 H8]; [|apply _].
    apply typ2_inj in H8 as [H8 H9]; [|apply _].
    unfold Rty in *.
    subst; inv_all; subst.
    clear H6 H12 H11 H5 H8 H10 H9 H4.
    induction e using expr_strong_ind;
    try (solve [simpl; eexists; split; [eapply mkApplySubst_sound; eassumption|reflexivity]]).
    + (* True, False, and Emp *)
      autorewrite with exprD_rw in H3; simpl in H3; forward; inv_all; subst.
	  simpl; remember (ilogicS i) as o; destruct o; [destruct i0|];
	  try (remember (bilogicS i) as o; destruct o; [destruct b|]);
	  try (solve [simpl; eexists; split; [eapply mkApplySubst_sound; try eassumption; autorewrite with exprD_rw; simpl; forward; inv_all; subst; reflexivity|reflexivity]]).
	  autorewrite with exprD_rw in H0; simpl in *.

      pose proof (of_funcAsOk).
      specialize (H4 _ _ Heqo).
      rewrite H4 in H2.
      unfold funcAs in H2. simpl in H2. rewrite type_cast_refl in H2. unfold Rrefl in H2.
      apply Rcast_eq_refl in H2. inversion H2; subst; clear H2.
      unfold fun3_wrap.
      unfold fun2_wrap.
      rewrite exprT_App_wrap.
      rewrite exprT_App_wrap.
      symmetry in Heqo1.
      eexists. split.
      eapply mkEmp_sound; [eapply Heqo1|eapply H3].
      intros.
      pose proof (bilf_funcAsOk i Heqo1). simpl in H4.
      rewrite H2 in H3.
      unfold funcAs in H3; simpl in H3; forward.
      unfold Rty in r.
      subst.
      apply Rcast_eq_refl in H6. inv_all; subst.
      Check fun1D.
      unfold fun1_wrap, fun1D, eq_rect_r, eq_rect, eq_sym.
      remember (typ2_cast (typ2 tyString tyVal) t0).
      inversion e; subst.
      remember (typ2_cast (typ2 tyString tyVal) t0).
      generalize dependent e.
      rewrite H7.
      rewrite H7 in e.
      do 2 rewrite typ2_cast in H7.
      unfold Fun in H7.
      remember (typ2_cast (typ2 tyString tyVal) t0).
      rewrite (UIP_refl H7).
      assert (forall (x:Type) (p:x = x), p = eq_refl x) by admit.
      remember (typ2_cast (typ2 tyString tyVal) t0).
      unfold Fun in e.
      subst.
      remember (typ2_cast (typ2 tyString tyVal) t0).
      unfold id.
      remember (typ2_cast tyString tyVal).
      assert(forall (x y:Type) (p1 p2:x = y), p1 = p2) by admit.
      pose proof e1 as e3.
      specialize (H7 _ _ e1 e3).
      assert (typD (typ2 tyString tyVal) = Fun (typD tyString) (typD tyVal)) by (apply typ2_cast).
      generalize dependent e3.
      rewrite H8.
      subst.
      Check typ2_cast.
      rewrite (@typ2_cast typ RType_typ Fun _ tyString tyVal).
      generalize dependent (fun y : typD (typ2 tyString tyVal) =>
    apply_subst
      (fun x : stack (typD tyString) (typD tyVal) =>
       match e in (_ = y0) return (id y0) with
       | eq_refl => BILogic.empSP
       end
         match
           match
             typ2_cast tyString tyVal in (_ = y0)
             return (y0 = typD (typ2 tyString tyVal))
           with
           | eq_refl => eq_refl
           end in (_ = y0) return (id y0)
         with
         | eq_refl => x
         end)
      match stSubst in (_ = y0) return (id y0) with
      | eq_refl => e2 us vs
      end).
      
      
      assert (typD (typ2 (typ2 tyString tyVal) t0) = Fun (typD (typ2 tyString tyVal)) (typD t0)) by (apply typ2_cast).
      progress eapply eq_ind_r with (typD (typ2 (typ2 tyString tyVal) t0)); [|symmetry; eapply H7].
      subst.
      assert (typD (typ2 tyString tyVal) = Fun (typD tyString) (typD tyVal)) by (apply typ2_cast).
      subst.
      apply typ2_cast.
      SearchAbout typD typ2.
      generalize dependent e.
      Check typ2_cast.
      
      rewrite (@typ2_cast typ RType_typ Fun _ tyString tyVal).
 specialize (H6 _ Heqe).
      SearchAbout typ2_cast.
      Check typ2_cast.
      generalize dependent (e2 us vs). intros.
      generalize dependent (BILogic.empSP). intros.
      generalize dependent (typ2_cast tyString tyVal). intros.
      generalize dependent (typ2_cast (typ2 tyString tyVal)).
      intros.
      destruct stSubst.
      destruct e.
      destruct e.
      destruct (typ2_cast tyString tyVal).
      
      destruct (typ2_cast (typ2 tyString tyVal) t0).
      Lemma blurb f : (fun x => (fun1D Typ2_tyArr f) (fun1_wrap Typ2_tyArr x)) = fun1D _ f.
      
      unfold fun1_wrap.
      unfold eq_rect_r, eq_rect, eq_sym. simpl. forward.
      specialize (H5 (typ2 (typ2 tyString tyVal) t0)).
      rewrite H5 in H3. simpl. inv_all; subst. simpl in H3.
      Check bilf_funcAsOk.
      simpl in H3.
      unfold funcAs in H3. simpl in H3. forward. inv_all; subst.
     destruct r; subst. 
     
     
      Lemma Rcast_option (t u : typ) (r : Rty t u) (a : typD t) (b : typD u) (H : Rcast option r (Some a) = Some b) :
        Rcast (fun T => T) r a = b.
      Proof.
        unfold Rcast, Relim, Rsym in *.
        destruct r; unfold eq_sym in *.
        inversion H; subst; reflexivity.
      Qed.
      
      apply Rcast_eq_refl in H7.
      inversion H7; subst; clear H7.
      
      
      
      apply Rcast_option in H7.
      unfold Rcast, Relim, Rsym, eq_sym in H7.
      destruct r. subst.
      simpl in *.
      SearchAbout Rcast.
      Check Rcast.
      Print Rcast.
      unfold Rcast, Relim, Rsym, eq_sym in H7.
      forward.
      unfold Rty in r.
      SearchAbout type_cast.
      unfold type_cast in H6. simpl in H6.
      rewrite r in H7.
      pose proof (bilf_fStarOk logic0) as HfuncOk.
      rewrite H4 in *.
      specialize
      Lemma test tus tvs (t u : typ) (f : exprT tus tvs (typD (typ2 t u))) g us vs : exists x, exprT_App f g us vs = x.
      Proof.
        unfold exprT_App.
        simpl.
        unfold eq_sym.
        generalize dependent ( fun (f0 : exprT tus tvs (typD t -> typD u))
        (x0 : exprT tus tvs (typD t)) (us0 : HList.hlist typD tus)
        (vs0 : HList.hlist typD tvs) => f0 us0 vs0 (x0 us0 vs0)). intros.
        SearchAbout typ2_cast.
        unfold typ2_cast. simpl.
        destruct (typ2_cast t u).
      unfold exprT_App.
      simpl.
      SearchAbout exprT_App.
      unfold exprT_App, eq_sym.
      destruct (typ2_cast (typ2 (typ2 tyString tyVal) t0)
         (typ2 tySubst (typ2 (typ2 tyString tyVal) t0))).
      destruct (typ2_cast tySubst (typ2 (typ2 tyString tyVal) t0)).
      unfold exprT_App.
      simpl.
      reflexivity.
      unfold exprT_App. intros. simpl.
      rewrite mkEmp_sound with (f := i).
      setoid_rewrite mkEmp_sound.
      eexists. split. erewrite mkEmp_sound.
      erewrite mkEmp_sound.
      Focus 3. eapply H3.
      eexists. split.
      eexists; split; [reflexivity|].
      eexists.
      split.
      eapply mkEmp_sound; try eassumption.
      rewrite mkEmp_sound.
      Check mkEmp_sound.
      eapply mkEmp_sound.
      rewrite mkEmp_sound.
      setoid_rewrite mkEmp_sound.
      SearchAbout exprT_App.
      unfold exprT_App. simpl.
      eexists. split.
      autorewrite with exprD_rw. simpl.
      Print funcAs.
      Print RType.
      Print RSym.
      Print funcAs.
      unfold funcAs.
      assert (typeof_sym (fEmp logic0) = Some logic0).  admit.
      rewrite H4.
      Print symD.
      unfold symD. simpl.
            Require Import Charge.Logics.BILogic.
      SearchAbout typ2 typD.
      Print Typ2_tyArr.
      unfold exprT, OpenT. simpl.
      rewrite (@typ2_cast typ RType_typ Fun Typ2_tyArr (typ2 tyString tyVal) t0).
      unfold typ2. simpl. unfold exprT. simpl. unfold OpenT. simpl. unfold Ty
      exists (fun _ _ => empSP).
      
      
      try (solve [simpl; eexists; split; [eapply mkApplySubst_sound; eassumption|reflexivity]]).
      Focus 2.
      simpl; eexists; split; [|reflexivity].
      Check @ilf_true_type_eq.
      symmetry in Heqo0.
      pose proof (ilf_true_type_eq (gs := gs) _ _ Heqo0 H3).
      rewrite H4 in *; clear H4.
      erewrite (mkTrue_sound (gs := gs)); [|eassumption|eassumption].
      rewrite (ilf_funcAsOk _ Heqo0) in H3.
      unfold funcAs in H3; simpl in H3. forward; inv_all; subst.
      unfold Rcast, Relim, Rsym, eq_sym in H5. simpl in H5.
      rewrite type_cast_refl in H4.
      unfold Rrefl in H4; inv_all; subst.
      inv_all; subst.
      rewrite (of_funcAsOk _ Heqo) in H2.
      pose proof (of_fApplySubstOk t0).
      pose proof (OpenFunc_typeOk _ H4).
      simpl in H5.
      unfold funcAs in H2; simpl in H2.
      rewrite type_cast_refl in H2.
      inv_all; subst.
      
      (* Gregory: This should be true, but I don't quite know where to go from here. *)
      
      unfold exprT_App, fun3_wrap, fun2_wrap, fun1_wrap, fun1D, id, eq_rect_r, eq_rect. uip_all'.
      
      (* This gives me a bunch of equivalence proofs, and a lot of typing problems *)
      
      unfold Fun in *.
      unfold exprT_App. simpl.
      rewrite funcAs_Some with (pf := H5) in H2.
      Check funcAs_Some.
      Check OpenFunc_typeOk.
      unfold funcAs in H2; simpl in H2; forward; inv_all; subst.
      rewrite type_cast_refl in H2; inv_all; subst.
      unfold Rcast, Rrefl in H4; simpl in H4; inv_all; subst.
      unfold Rcast, Rrefl, Relim, Rsym, eq_sym, fun3_wrap, fun2_wrap, fun1_wrap, eq_rect, eq_rect_r, eq_rect, eq_sym, fun1D, eq_rect.
      simpl.
      unfold exprT_App, eq_sym.
      forward.
      simpl.
      inv_all; subst.
      clear H2 H4.
      uip_all.
      unfold Fun in e3.
      subst.
      uip_all.
      unfold id.
      generalize dependent (typD (typ2 tyString tyVal)).
      destruct e1.
      uip_all'.
      destruct stSubst.
      destruct ( typ2_cast (typ2 tyString tyVal) t0).
      forward.
      SearchAbout typ2_cast.
      unfold typ2_cast in H2.
      rewrite type_cast_refl in H2.
      inversion H2; subst. f_equal.
      unfold exprT_App, fun3_wrap, eq_sym. simpl.
      apply functional_extensionality. intros.
      apply functional_extensionality. intros.
      Check of_funcAsOk.
      rewrite mkTrue_sound.
      assert (exprD' tus tvs
      try (solve [simpl; eexists; split; [apply mkApplySubst_sound | reflexivity]; assumption]).
    simpl.
    assumption.
    assumption.
    + simpl. eexists; split; [|reflexivity].
      apply mkApplySubst_sound; assumption.
    + simpl; eexists; split; [|reflexivity].
      apply mkApplySubst_sound; assumption.
    + 
      autorewrite with exprD_rw in H3; simpl in H3; forward; inv_all; subst.
      unfold Rty in r. subst.
      unfold mkApplySubst. simpl.
      autorewrite with exprD_rw; simpl; forward; inv_all; subst.
      autorewrite with exprD_rw; simpl; forward; inv_all; subst.
      pose (nth_error_get_hlist_nth_Some _ H3).
      destruct e as [? ?].
      rewrite x.
      autorewrite with exprD_rw; simpl; forward; inv_all; subst.
      rewrite type_cast_refl.
      unfold Rcast_val, Rrefl, Rcast, Relim, Rsym, eq_sym; simpl.
      assert (open_funcS (fApplySubst t0) = Some (of_apply_subst t0)) by admit.
      assert (typeof_sym (of_apply_subst t0) = Some (typ2 (typ2 (typ2 tyString tyVal) t0)
                   (typ2 tySubst (typ2 (typ2 tyString tyVal) t0)))) by admit.
      pose proof (funcAsOk _ H3); rewrite H7.
      pose proof (funcAs_Some _ H6).
      rewrite H8. simpl.
      f_equal. f_equal. f_equal.
      Require Import FunctionalExtensionality.
      apply functional_extensionality. intros.
      apply functional_extensionality. intros.
      clear -H6.
      revert H6.
      generalize (symD (of_apply_subst t0)).
      intros.
      admit.
      apply _.
    + eexists; split; [|reflexivity].
      
      simpl.
      Check symD.
      Print typD.
      Print RType.
      Check exprT_App.
      Print exprT.
 
Check @exprT_App.

    generalize dependent (
       (typ2 (typ2 (typ2 tyString tyVal) t)
          (typ2 tySubst (typ2 (typ2 tyString tyVal) t)))).
    generalize dependent (typD t0).
    destruct z.
    generalize dependent (typeof_sym (of_apply_subst t)).
    rewrite H2.
    destruct H2.
    f_e
    rewrite H.
      progress autorewrite with exprD_rw; simpl; forward; inv_all; subst.
      autorewrite with exprD_rw; simpl; forward; inv_all; subst.
      
      pose (nth_error_get_hlist_nth_Some _ H3).
      destruct e as [? ?].
      rewrite x.
      autorewrite with exprD_rw; simpl; forward; inv_all; subst.
      rewrite type_cast_refl.
      unfold Rcast_val, Rrefl, Rcast, Relim, Rsym, eq_sym; simpl.
      assert (open_funcS (fApplySubst t0) = Some (of_apply_subst t0)) by admit.
      assert (typeof_sym (of_apply_subst t0) = Some (typ2 (typ2 (typ2 tyString tyVal) t0)
                   (typ2 tySubst (typ2 (typ2 tyString tyVal) t0)))) by admit.
      pose proof (funcAsOk _ H3); rewrite H7.
      pose proof (funcAs_Some _ H6).
      rewrite H8. simpl.
      f_equal. f_equal. f_equal.
      Require Import FunctionalExtensionality.
      apply functional_extensionality. intros.
      apply functional_extensionality. intros.
      clear -H6.
      revert H6.
      generalize (symD (of_apply_subst t0)).
      intros.
      admit.
      apply _.    
      generalize  (typ2 (typ2 (typ2 tyString tyVal) t0)
            (typ2 tySubst (typ2 (typ2 tyString tyVal) t0))).
      generalize dependent (Some (typ2 (typ2 (typ2 tyString tyVal) t0)
          (typ2 tySubst (typ2 (typ2 tyString tyVal) t0)))); intros; subst; reflexivity.
      generalize (symD (of_apply_subst t0)).
      intros. 
      generalize dependent H6.
      generalize dependent (Some (typ2 (typ2 (typ2 tyString tyVal) t0)
          (typ2 tySubst (typ2 (typ2 tyString tyVal) t0)))); intros; subst; reflexivity.
      generalize dependent H6.
      uip_all.
      subst.
      destruct H6.
      generalize dependent H6. uip_all'.
      assert (symD (fApplySubst t0) = symD (of_apply_subst t0)).
      assert (typo
        Print symAs_Some.
      
      pose proof (funcAsOk _ H3). rewrite H6.
      SearchAbout exprD' symD.
      SearchAbout symD.

      
      Check symD.
      SearchAbout funcAs symD.
      Check funcAs.
      
      Print exprT_App.
      assert (funcAs (fApplySubst t0)
        (typ2 (typ2 (typ2 tyString tyVal) t0)
           (typ2 tySubst (typ2 (typ2 tyString tyVal) t0))) = symD (of_apply_subst t0)).
      destruct o.
      admit.
      unfold funcAs in Heqo0.
      simpl in Heqo0.
      admit.
      assert False.
      rewrite H3 in Heqo0.
      forward.
      rewrite H3.
      rewrite type_cast_refl.
      assert (open_funcS (fApplySubst t0) = Some (of_apply_subst t0)).
      admit.
      pose (funcAsOk _ H3). 
      Check typeof_funcAs.
      
      rewrite e; clear e.
      pose proof (OpenFunc_typeOk _ H3).
      simpl.
      unfold fApplySubst. simpl.
      unfold funcAs.
      simpl.
      Transparent symD.
      simpl.
      SearchAbout nth_error nth_error_get_hlist_nth.
      unfold nth_error.
      progress autorewrite with exprD_rw; simpl; forward; inv_all; subst.
      simpl in H3.
    Check expr_strong_ind.
    Check (fun (_ : HList.hlist typD tus) (_ : HList.hlist typD tvs) =>
         symD (of_apply_subst t0)).
    Check (fun (_ : HList.hlist typD tus) (_ : HList.hlist typD tvs) =>
         @apply_subst).
    Transparent symD.
    simpl.
    unfold fun3_wrap, fun2_wrap, eq_rect_r, eq_rect, eq_sym. simpl.
    rewrite (@typ2_cast typ _ Fun _).
    rewrite typ2_cast.
    SearchAbout exprT_App.
    unfold eq_rect_r, eq_rect, eq_sym.
    SearchAbout typ2_cast.
    Check @typ2_cast.
    remember (typ2_cast (typ2 (typ2 tyString tyVal) t0)
               (typ2 tySubst (typ2 (typ2 tyString tyVal) t0))).
    destruct e1.
    unfold typ2_cast.
    Transparent symD. 
    simpl.
    refine (exists val' : exprT tus tvs (typD (typ2 (typ2 tyString tyVal) t0)),
  ExprDsimul.ExprDenote.exprD' tus tvs (typ2 (typ2 tyString tyVal) t0)
    (pushSubst Typ2_tyArr e0 e t0) = Some val' /\
  (forall (us : HList.hlist typD tus) (vs : HList.hlist typD tvs),
   P us vs ->
   exprT_App
     (exprT_App
        _ e4) e2 us vs = val' us vs)).
    simpl.
    erewrite typ2_cast.
    generalize dependent t3.
    Transparent symD.
    rewrite typ2_cast.
    Print symD.
    simpl in H2.
    Example test t0 : exists x, x = typD (typ2 (typ2 (typ2 tyString tyVal) t0)
          (typ2 tySubst (typ2 (typ2 tyString tyVal) t0))).
    Proof.
      repeat rewrite typ2_cast.
      unfold Fun.
      repeat rewrite btString.
      rewrite stVal.
      vm_compute.
      destruct RType_typ. simpl.
      destruct Typ2_tyArr.
      simpl.
      destruct BT. simpl. destruct ST. simpl.
      SearchAbout typ2.
      repeat rewrite typ2_cast.
      unfold Fun. simpl.
      destruct BT.
      rewrite btString.
    unfold funcAs in H2; simpl in H2.
    rewrite type_cast_refl in H2.
    unfold Rcast, Relim, Rrefl in H2. simpl in H2.
    unfold eq_rect_r, eq_rect, Fun, eq_sym, eq_rect_r, typ2_cast in H2; simpl in H2.
    destruct Typ2_tyArr; simpl in H2.
    SearchAbout typ2_cast.
    Print Typ2Ok.
    Print typ2_match.
    rewrite typ2_match_Proper in H2.
    progress unfold typ2_cast in H2.
    Print Rcast.
    inv_all; subst.
    unfold exprT_App, eq_sym, typ2_cast, exprT, OpenT, typ2_cast; simpl.
    
    rewrite type_cast_refl in H2.
    SearchAbout Typ2.
    unfold Rcast, Rrefl, eq_rect_r, eq_sym, eq_rect, typ2_cast in H2; simpl in H2.
    
    unfold Rcast, Rrefl, eq_rect_r, eq_sym, typ2_cast, Fun, eq_rect in H2; simpl in H2.
    destruct Typ2_tyArr. simpl in H2.
    unfold typD in H2. simpl in H2.
    destruct RType_typ; simpl in *.
    forward.
    inv_all; subst.
    unfold exprT_App, eq_sym. simpl.
    uip_all'.
    uip_all'.
    destruct e3.
    uip_all'.
    revert H2. uip_all.
    unfold eq_rect in H2.
    inv_all; subst.
    vm_compute in H2.
    subst.
    rewrite H8 in *.
    inversion H7.
    rewrite H7 in H2.
    simpl in H4.
    unfold typ2 in H2. simpl in H2.
    destruct Typ2_tyArr.
    simpl.
    unfold typ2 in H2.
    unfold funcAs in H2. simpl in H2.
    forward.
    generalize dependent t3.
    subst.
    unfold Rty in r.
    rewrite <- r.
    unfold Rcast, Relim, Rsym, eq_sym, eq_rect_r, eq_rect, eq_sym, typ2_cast, Fun, typD in H2; simpl in H2.
    destruct RType_typ; simpl in *.
    
     destruct r.
    simpl in H4.
    unfold type_cast in H2. simpl in H2.
    destruct RType_typ.
    destruct r.
    rewrite OpenFunc_typeOk in .
    pose proof (
       
    assert (typeof_sym f = typeof_open_func _ (of_apply_subst t0)) by admit.
    Check symD.
    Check exprD.
    Print RSymOk.
    Print exprD'.
    Print Expr.
    Print exprT.
    Print OpenT.
    assert (funcAs f (typeof_open_func _ (of_apply_subst t0)) = 
       Some (fun _ _ => @apply_subst (typD tyString) (typD tyVal) (typD t0))).
    assert (funcAs ).
    simpl in H4.
    pose proof (typeof_funcAs H2) as H5.
    rewrite H5 in H4; clear H5; inv_all; subst.


    eexists; split; [|intros; reflexivity].

    induction e using expr_strong_ind.
    + simpl.
    SearchAbout exprT_App.
    
    unfold exprT_App. simpl.
    unfold exprT, OpenT. simpl.
    split.
    Focus 2.
    intros. reflexivity.
    exists e2.
    + simpl in H0.
      unfold exprT_App. simpl.
      unfold exprT. simpl. unfold OpenT. simpl.
      SearchAbout typ2_cast.
    generalize dependent t3.
    generalize dependent t2.
    generalize dependent t1.
    generalize dependent t.
    generalize dependent tus.
    generalize dependent tvs.
    generalize dependent e.
    generalize dependent e0.
    subst.
    rewrite H4.
    remember (typeof_sym f).
    rewrite H4 in H2.
    simpl in H4. 
    Check @UIP_refl.
    revert H2 Heqo.
    uip_all.
    generalize dependent t3.
    generalize dependent t2. generalize dependent t1. generalize dependent t.
    generalize dependent tus. generalize dependent tvs. generalize dependent e.
    generalize dependent e0.
    symmetry in H4. setoid_rewrite <- H4.
     generalize dependent func.
    setoid_rewrite H4.
     rewrite H4.
    red in H4.
    rewrite (@UIP_refl (option typ) _ _ H4) in H2.
    U
    Check UIP_rewrite.
    UIP_rewrite
    rewrite H4 in H2.
    simpl. unfold typ2. simpl. unfold typ2. simpl.
    destruct f. simpl in Heqo.
    unfold funcAs in H2. simpl in H2.
    unfold exprT_App, OpenT; simpl. uip_all.
    rewrite (UIP_refl e1).
	simpl in H. red_exprD.
	Locate idred.
Check idred.
*)
Print full_reducer.
  Definition SUBST := SIMPLIFY (typ := typ) (fun _ _ _ _ => beta_all substTac).
(*
  Lemma substTac_ok : full_reducer_ok substTac.
  Proof.
    unfold full_reducer_ok; intros.
    SearchAbout exprT.
    Print OpenT.
    unfold exprT, OpenT in *.
Check hlist_build.
SearchAbout apps.
Print apps_sem'.
Print apply_sem'.
Check apps_sound.
    Print var_termsP.
    unfold applys. simpl.
  Lemma substTac_sound   
    (He : exprD' tus tvs (fold_right (typ2 (F := Fun)) t targs) e = Some de) :
    exists de', exprD' tus' tvs' t (substTac var_terms e es) = Some de'
    SearchAbout 
    unfold OpenT.
  Qed.
Check @SIMPLIFY_sound.
  Lemma SUBST_sound : @rtac_sound typ (expr typ func) RType_typ _ Expr_expr _ SUBST.
  Proof.
    unfold SUBST.
    apply SIMPLIFY_sound.
    intros; simpl; forward.
    unfold propD, exprD'_typ0 in H3. forward; inv_all; subst.
    destruct (beta_all_sound substTac_ok _ _ e1 H3) as [v [H4 H5]].
    unfold propD, exprD'_typ0; simpl.
    forward; inv_all; subst.
    SearchAbout typ0_cast.
    uip_all.
    Check Pure_pctxD.
    eapply Pure_pctxD; eauto.
    intros us0 vs0; autorewrite with eq_rw. intro; rewrite H5. tauto.
    assumption.
  Qed.
*)
  
End SubstTac.
Print SUBST.
Implicit Arguments SUBST [[ST] [RType_typ] [OF] [ILF] [BILF] [EF] [BF] [Typ2_tyArr]].