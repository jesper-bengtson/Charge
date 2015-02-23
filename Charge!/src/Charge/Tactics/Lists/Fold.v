Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.AppN.
Require Import MirrorCore.Lambda.Red.
Require Import MirrorCore.Lambda.RedAll.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.RTac.Simplify.

Require Import Charge.ModularFunc.BaseFunc.
Require Import Charge.ModularFunc.ListFunc.
Require Import Charge.ModularFunc.BaseType.
Require Import Charge.ModularFunc.ListType.
Require Import Charge.ModularFunc.SemiEqDecTyp.
Require Import Charge.ModularFunc.Denotation.

Require Import ExtLib.Core.RelDec.

Section Fold.
  Context {typ func : Type} {RType_typ : RType typ} {RSym_func : RSym func}.
  Context {BT : BaseType typ} {BTD : BaseTypeD}.
  Context {LT : ListType typ} {LTD : ListTypeD}. 
  Context {BF : BaseFunc typ func} {LF: ListFunc typ func}.
  Context {Heq : RelDec (@eq typ)} {HC : RelDec_Correct Heq}.
  Context {Heqd : SemiEqDecTyp typ} {HeqdOk : SemiEqDecTypOk Heqd}.
  Context {Typ2_Fun : Typ2 RType_typ Fun}.
  Context {Typ0_Prop : Typ0 RType_typ Prop}.
  
  Context {BFOk : BaseFuncOk typ func} {LFOk : ListFuncOk typ func}.

  Context {RTypeOk_typ : RTypeOk}.
  Context {RSymOk_func : RSymOk RSym_func}.
  Context {Typ2Ok_Fun : Typ2Ok Typ2_Fun}.
Check typ2_match.
SearchAbout typ2_match.

  Definition foldTac (e : expr typ func) (args : list (expr typ func)) : expr typ func :=
    match listS e with
      | Some (pFold t u) =>
        match args with
          | f :: acc :: lst :: nil =>
            match baseS lst with
              | Some (pConst v lst) => 
		  	    match type_cast v (tyList u) with
		  	      | Some pf => 
                    fold_right (fun x acc => beta (beta (App (App f (mkConst u x)) acc))) acc 
                       (listD (eq_rect _ typD lst _ pf))
                  | None => apps e args
                end
		  	  | Some _ => apps e args
		  	  | None => 
		  	    let (lst', e') := expr_to_list lst in
		  	      fold_right (fun x acc => beta (beta (App (App f x) acc))) (apps e (f::acc::e'::nil)) lst'
            end
          | _ => apps e args
        end
      | _ => apps e args
    end.

  Definition FOLD := SIMPLIFY (typ := typ) (fun _ _ _ _ => (beta_all (fun _ => foldTac))).

Require Import ExtLib.Tactics.

  Ltac clear_eq := 
    match goal with 
      | H : ?x = ?x |- _ => clear H
    end.
    
  Ltac r_inj H :=
      first [
        let H1 := fresh "H" in let H2 := fresh "H" in
          apply typ2_inj in H as [H1 H2]; [unfold Rty in H1, H2; r_inj H1; r_inj H2 | apply _] |
        repeat subst].
  
  Ltac list_inj :=
    match goal with
      | H : tyList _ = tyList _ |- _ => apply tyList_inj in H; unfold Rty in H; subst
    end.
 Context {Expr_typ : Expr RType_typ (expr typ func)}.

Check Typ2Ok_Fun.
  Lemma beta_sound (tus tvs : list typ) (t : typ) (e : expr typ func) (df : ExprI.exprT tus tvs (typD t))
    (H : ExprDsimul.ExprDenote.exprD' tus tvs t e = Some df) :
    ExprDsimul.ExprDenote.exprD' tus tvs t (beta e) = Some df.
  Proof.
    pose proof (beta_sound tus tvs e t).
    rewrite H in H0.
    forward; inv_all; subst. 
    f_equal.
    Require Import FunctionalExtensionality.
    do 2 (apply functional_extensionality; intro).
    symmetry; apply H1.
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

Ltac run_forward_step H1 H2 type_tac expr_tac :=
  let H := fresh "H" in 
      pose proof type_tac as H; r_inj H; pose proof expr_tac; subst;
      clear H1 H2.

Ltac lf_forward_step :=
  match goal with 
    | H : Some _ = listS _ |- _ =>  symmetry in H
    | H : typ2 _ _ = typ2 _ _ |- _ => r_inj H; clear_eq
    | H : Rty (typ2 _ _) (typ2 _ _) |- _ => r_inj H; clear_eq
    | H : Rcast option _ (Some _) = Some _ |- _ => apply Rcast_option_inj in H; subst
	| H1 : listS ?e = Some (pNil _), H2 : ExprDsimul.ExprDenote.exprD' _ _ _ ?e = Some _|- _ =>
	  let H := fresh "H" in
	     pose proof (lf_nil_type_eq _ _ H1 H2) as H; r_inj H; pose proof(lf_nil_eq _ H1 H2); subst;
	     clear H1 H2
	| H1 : listS ?e = Some (pFold _ _), H2 : ExprDsimul.ExprDenote.exprD' _ _ _ ?e = Some _|- _ =>
	  let H := fresh "H" in
	     pose proof (lf_fold_type_eq _ _ H1 H2) as H; r_inj H; pose proof(lf_fold_eq _ H1 H2); subst;
	     clear H1 H2
    | _ => 
       first [
        progress (unfold foldD, fun_to_typ3 in *) |
        progress (repeat rewrite (exprT_App_wrap) in *)
      ]
  end.
 
Ltac lf_fold_step :=
  match goal with
    | H2 : ExprDsimul.ExprDenote.exprD' ?tus ?tvs
       (typ2 (typ2 ?u (typ2 ?t ?t)) (typ2 ?t (typ2 (tyList ?u) ?t))) ?e =
     Some (fun _ _ => foldD ?t ?u) |- _ => fail 1
	| H1 : listS ?e = Some (pFold _ _), H2 : ExprDsimul.ExprDenote.exprD' _ _ _ ?e = Some _|- _ =>
	  let H := fresh "H" in
	     pose proof (lf_fold_type_eq _ _ H1 H2) as H; r_inj H; repeat clear_eq; pose proof(lf_fold_eq _ H1 H2); subst
  end.

  
Ltac bf_forward_step :=
  match goal with 
    | H : Some _ = baseS _ |- _ =>  symmetry in H
	| H1 : baseS ?e = Some (pConst _ _), H2 : ExprDsimul.ExprDenote.exprD' _ _ _ ?e = Some _|- _ =>
	  let H := fresh "H" in
	     pose proof (bf_const_type_eq _ _ H1 H2) as H; r_inj H; repeat clear_eq; pose proof(bf_const_eq _ H1 H2); subst;
	     clear H1 H2
  end.
  
  Lemma foldTacOk : partial_reducer_ok foldTac.
  Proof.
    unfold partial_reducer_ok; intros.
    exists val; split; [|reflexivity].
    unfold foldTac.
    remember (listS e); destruct o; [|assumption].
    destruct l; try assumption.
    destruct es; try assumption.
    destruct es; try assumption.
    destruct es; try assumption.
    destruct es; try assumption.
    simpl in H.
    remember (baseS e2); destruct o.
    destruct b; try assumption.
    remember (type_cast t2 (tyList t1)).
    destruct o; [|assumption].
    simpl in H.
    autorewrite with exprD_rw in H; simpl in H; forward; inv_all; subst.
    autorewrite with exprD_rw in H0; simpl in H0; forward; inv_all; subst.
    autorewrite with exprD_rw in H2; simpl in H2; forward; inv_all; subst.
Check @lf_fold_eq.

	lf_forward_step.
	lf_fold_step.
	lf_fold_step.
  match goal with
    | H2 : ExprDsimul.ExprDenote.exprD' ?tus ?tvs
       (typ2 (typ2 ?u (typ2 ?t ?t)) (typ2 ?t (typ2 (tyList ?u) ?t))) ?e =
     Some (fun  (_ : HList.hlist typD tus) (_ : HList.hlist typD tvs) => foldD ?t ?u) |- _ => idtac "hej"
  end.
	lf_fold_step.
	progress lf_fold_step.
	progress lf_fold_step.
	repeat clear_eq.
	lf_forward_step.
    unfold Rty in r; subst.
    Opaque beta.
    bf_forward_step.
    bf_forward_step.
    clear_eq.
    lf_forward_step.
    lf_forward_step.
    simpl.
	remember (listD t3). clear Heql.
	induction l; intros; subst.
	+ simpl. assumption.
	+ simpl.
	  apply beta_sound.
	  apply beta_sound.
      autorewrite with exprD_rw; simpl. 
      pose proof (ExprTac.exprD_typeof_Some _ _ _ _ _ IHl).
      forward.
      autorewrite with exprD_rw; simpl; inv_all; subst.
      rewrite bf_typeof_const.
      forward; inv_all; subst.
      rewrite mkConst_sound.
      rewrite exprT_App_wrap_sym.
      rewrite exprT_App_wrap_sym.
      reflexivity.
    + remember (expr_to_list e2).
      destruct p.
      clear Heqo0.
      autorewrite with exprD_rw in H; simpl in H; forward; inv_all; subst.
      autorewrite with exprD_rw in H0; simpl in H0; forward; inv_all; subst.
      autorewrite with exprD_rw in H2; simpl in H2; forward; inv_all; subst.
      autorewrite with exprD_rw in H1; simpl in H1; forward; inv_all; subst.
      repeat lf_forward_step.
      generalize dependent e2. induction l. simpl. intros. 
      symmetry in Heqp. apply expr_to_list_nil in Heqp. subst.
      
      autorewrite with exprD_rw; simpl; forward; inv_all; subst.
      autorewrite with exprD_rw; simpl; forward; inv_all; subst.
      autorewrite with exprD_rw; simpl; forward; inv_all; subst.
      forward; inv_all; subst.
      forward; inv_all; subst.
      autorewrite with exprD_rw; simpl; forward; inv_all; subst.
       assumption.
      intros.
      symmetry in Heqp.
      simpl.
      apply beta_sound.
      apply beta_sound.


      lf_forward_step.
      lf_forward_step.
      lf_forward_step.
      lf_forward_step.
      repeat rewrite (exprT_App_wrap) in IHl.
      
      autorewrite with exprD_rw; simpl; forward; inv_all; subst.
      
      destruct (expr_to_list_cons tus tvs _ _ Heqp H) as [? [? ?]].
      subst.
      assert ( ExprDsimul.ExprDenote.exprD' tus tvs t0 (App (App (App e e0) e1) x) =
      Some
        (fun (us : HList.hlist typD tus) (vs : HList.hlist typD tvs) =>
         fold_right (typ_to_fun2 (e8 us vs)) (e7 us vs) (listD (e5 us vs)))).
      autorewrite with exprD_rw; simpl; forward; inv_all; subst.
      assert (typeof_expr tus tvs x = Some (tyList t1)) by admit.
      forward.
      autorewrite with exprD_rw; simpl; forward; inv_all; subst.
      autorewrite with exprD_rw; simpl; forward; inv_all; subst.
      
      lf_forward_step.
      pose proof (lf_nil_func_type_eq _ _ Heqo1 H1).
      subst.
      rewrite H4 in *.
      list_inj.
      pose proof (lf_nil_func_eq _ Heqo1 H1).
	  subst.
	  simpl.
	  
	  Lemma listD_nil (t : typ) : listD (nilD t) = nil.
	  Proof.
	    unfold listD, nilD, eq_rect_r, eq_rect, id, eq_sym.
	    generalize (btList t).
	    generalize dependent (tyList t).
	    generalize dependent (typD t).
		intros.
		generalize dependent (typD t0).
		intros; subst. reflexivity.
	  Qed.
	  
	  rewrite listD_nil. simpl. assumption.
	  
	  destruct e2_2; try assumption.
	  destruct e2_1; try assumption.
	  simpl.
	  remember (listS f). destruct o; try assumption.
	  destruct l; try assumption.

	  simpl in H.
	  autorewrite with exprD_rw in H; simpl in H; forward; inv_all; subst.
      autorewrite with exprD_rw in H0; simpl in H0; forward; inv_all; subst.
      autorewrite with exprD_rw in H2; simpl in H2; forward; inv_all; subst.
      autorewrite with exprD_rw in H1; simpl in H1; forward; inv_all; subst.
      autorewrite with exprD_rw in H11; simpl in H11; forward; inv_all; subst.
      autorewrite with exprD_rw in H10; simpl in H10; forward; inv_all; subst.
	  
      lf_forward_step.
      lf_forward_step.
      lf_forward_step.
      lf_forward_step.
      lf_forward_step.
      pose proof (lf_cons_func_type_eq _ _ Heqo1 H5).
      Check lf_cons_func_type_eq.
      r_inj H8.
      pose proof (lf_cons_func_eq _ Heqo1 H5).
	  subst.
	  simpl.


      lf_forward_step.
      Print type_of_apply.
      Check typ2_inj.
      Print Rty.
      Print Typ2Ok.
      SearchAbout type_of_apply.
      lf_forward_step.
      lf_forward_step.
	  
	  unfold nilD, listD, eq_rect_r, eq_rect, eq_sym. simpl.
	  remember (btList t2).
	  destruct e2.      
      lf_forward_step.
      simpl in H.
  Qed.

End Fold.