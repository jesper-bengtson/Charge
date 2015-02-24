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
		  	      match listS e' with
		  	        | Some (pNil t) => 
		  	          fold_right (fun x acc => beta (beta (App (App f x) acc))) acc lst'
		  	        | _ =>
		  	          fold_right (fun x acc => beta (beta (App (App f x) acc))) (apps e (f::acc::e'::nil)) lst'
		  	      end
            end
          | _ => apps e args
        end
      | _ => apps e args
    end.

  Definition FOLD := SIMPLIFY (typ := typ) (fun _ _ _ _ => (beta_all (fun _ => foldTac))).

 Context {Expr_typ : Expr RType_typ (expr typ func)}.
 
 Require Import Charge.Tactics.Lists.ListTacs.
 Require Import Charge.Tactics.Base.MirrorCoreTacs.
 

Ltac bf_forward_step :=
  match goal with 
    | H : Some _ = baseS _ |- _ =>  symmetry in H
	| _ : baseS ?e = Some (pConst ?t ?c),
	  _ : ExprDsimul.ExprDenote.exprD' _ _ ?t ?e = Some (fun _ _ => ?c) |- _ => fail 1
	| H1 : baseS ?e = Some (pConst _ _), H2 : ExprDsimul.ExprDenote.exprD' _ _ _ ?e = Some _|- _ =>
	  let H := fresh "H" in
	     pose proof (bf_const_type_eq _ _ H1 H2) as H; r_inj H; repeat clear_eq; pose proof(bf_const_eq _ H1 H2); subst
  end.
    
Ltac forward_step :=
  first [
    lf_forward_step | 
    bf_forward_step
  ].

Ltac destruct_match_goal tac :=
  match goal with 
    | |- context [match ?e with _ => _ end] =>
      destruct e eqn:?; try tac
  end; subst.

Ltac bf_rewrite_in_match :=
  match goal with 
    | |- context [typeof_sym (fConst ?t ?c)] =>
        rewrite (BaseFunc_typeOk _ (bf_fConstOk _ _)); simpl     
    | |- context [ExprDsimul.ExprDenote.exprD' _ _ ?t (mkConst ?t _)] =>
      rewrite mkConst_sound      
  end.

Opaque beta.

Ltac destruct_exprs tac :=
  destruct_match_goal tac; simpl;
  try Rty_elim; simpl.

Ltac reduce :=
  (try red_exprD_hyp); repeat forward_step; (repeat exprD_saturate_types); (repeat (first [rewrite_in_match | bf_rewrite_in_match])); (try red_exprD_goal); repeat (first [
        progress (unfold foldD, fun_to_typ3) |
        progress (unfold consD, fun_to_typ2) |
        progress (repeat rewrite (exprT_App_wrap) in *)]).

Require Import FunctionalExtensionality.
Opaque baseS listS.
  Lemma foldTacOk : partial_reducer_ok foldTac.
  Proof.
    unfold partial_reducer_ok; intros.
    exists val; split; [|reflexivity].
    unfold foldTac.
    do 8 (destruct_exprs assumption).
    destruct_exprs assumption.
    reduce.
    + remember (listD t3); clear Heql.
	  induction l; intros; subst; simpl.
	  * assumption.
	  * repeat reduce.
  	    do 2 rewrite exprT_App_wrap_sym.
	    reflexivity.
    + destruct_exprs assumption.
      destruct_exprs assumption.
      reduce. 
      clear Heqo0.
      generalize dependent e2; generalize dependent e5. 
      induction l; intros; simpl.
      * apply expr_to_list_nil in Heqp. subst.
        try (red_exprD_hyp).
		forward_step.
  match goal with
    | H : tyList _ = tyList _ |- _ => apply tyList_inj in H; unfold Rty in H; subst
  end.
		list_inj H0.
apply tyList_inj in H0; unfold Rty in H0; subst.
reduce.
		list_inj H0.
        reduce.
        forward_step.
        reduce. 
  	    pose proof(lf_nil_eq _ Heqo1 Heqo4); subst
        reflexivity.
      * reduce.
        destruct (expr_to_list_cons tus tvs _ _ Heqp Heqo1) as [? [? ?]]; subst.
        reduce; subst.

        specialize (IHl3 _ _ H0 H2 Heqo3).
        reduce.


        do 2 (rewrite exprT_App_wrap_sym).
        f_equal.
        do 2 (apply functional_extensionality; intro).
        rewrite listD_inv. reflexivity.
      * apply expr_to_list_nil in Heqp. subst.
        reduce. 
        reflexivity.
      * reduce.
        destruct (expr_to_list_cons tus tvs _ _ Heqp Heqo1) as [? [? ?]]; subst.
        reduce; subst.

        specialize (IHl3 _ _ H0 H2 Heqo3).
        reduce.


        do 2 (rewrite exprT_App_wrap_sym).
        f_equal.
        do 2 (apply functional_extensionality; intro).
        rewrite listD_inv. reflexivity.
  Qed.

End Fold.