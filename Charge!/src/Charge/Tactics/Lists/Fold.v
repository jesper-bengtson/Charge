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

  Ltac list_inj :=
    match goal with
      | H : tyList _ = tyList _ |- _ => apply tyList_inj in H; unfold Rty in H; subst
    end.
 Context {Expr_typ : Expr RType_typ (expr typ func)}.


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

Ltac lf_fold_type :=
  match goal with
    | _ : listS ?e = Some (pFold _ _), _ : ExprDsimul.ExprDenote.exprD' _ _
       (typ2 (typ2 ?u (typ2 ?t ?t)) (typ2 ?t (typ2 (tyList ?u) ?t))) ?e =
     Some _ |- _ => fail 1
	| H1 : listS ?e = Some (pFold _ _), H2 : ExprDsimul.ExprDenote.exprD' _ _ _ ?e = Some _|- _ =>
	  let H := fresh "H" in
	     pose proof (lf_fold_type_eq _ _ H1 H2) as H; r_inj H; repeat clear_eq; subst
  end.
  
Ltac lf_fold_expr :=
  match goal with
    | _ : listS ?e = Some (pFold ?t ?u),
      _ : ExprDsimul.ExprDenote.exprD' ?tus ?tvs
       (typ2 (typ2 ?u (typ2 ?t ?t)) (typ2 ?t (typ2 (tyList ?u) ?t))) ?e =
     Some (fun _ _ => foldD ?t ?u) |- _ => fail 1
	| H1 : listS ?e = Some (pFold _ _),
	  H2 : ExprDsimul.ExprDenote.exprD' _ _  (typ2 (typ2 ?u (typ2 ?t ?t)) (typ2 ?t (typ2 (tyList ?u) ?t))) ?e = Some _|- _ =>
	  let H := fresh "H" in pose proof(lf_fold_eq _ H1 H2); subst
  end.

Ltac lf_nil_type :=
  match goal with
    | _ : listS ?e = Some (pNil _), _ : ExprDsimul.ExprDenote.exprD' ?tus ?tvs (tyList ?t) ?e = Some _ |- _ => fail 1
	| H1 : listS ?e = Some (pNil _), H2 : ExprDsimul.ExprDenote.exprD' _ _ _ ?e = Some _ |- _ =>
	  let H := fresh "H" in
	     pose proof (lf_nil_type_eq _ _ H1 H2) as H; r_inj H; repeat clear_eq; subst
  end.

Ltac lf_nil_expr :=
  match goal with
    | _ : ExprDsimul.ExprDenote.exprD' _ _ (tyList ?t) ?e = Some (fun _ _ => nilD ?t) |- _ => fail 1
	| H1 : listS ?e = Some (pNil _), H2 : ExprDsimul.ExprDenote.exprD' _ _ (tyList ?t) ?e = Some _|- _ =>
	  pose proof(lf_nil_eq _ H1 H2); subst
  end.

Ltac destruct_match_oneres :=
    match goal with
      | H : context[match ?x with _ => _ end] |- _ =>
        (destruct x eqn:?; try intuition congruence); [ idtac ]      
      | |- context[match ?x with _ => _ end] =>
        (destruct x eqn:?; try intuition congruence); [ idtac ]     
    end.

Ltac lf_cons_expr :=
  match goal with
    | _ : listS ?e = Some (pCons ?t),
      _ : ExprDsimul.ExprDenote.exprD' ?tus ?tvs  ?e =
     Some (fun _ _ => consD ?t) |- _ => fail 1
	| H1 : listS ?e = Some (pCons ?t),
	  H2 : ExprDsimul.ExprDenote.exprD' ?tus ?tvs (typ2 ?t (typ2 (tyList ?t) (tyList ?t))) ?e = Some _|- _ =>
	  let H := fresh "H" in pose proof(lf_cons_eq _ H1 H2); subst
	| H : ExprDsimul.ExprDenote.exprD' _ _ (tyList ?t) (mkCons ?t _ _) = Some _ |- _ =>
	  pose proof (mkConsD _ _ _ H); clear H; (repeat destruct_match_oneres)
  end.

Ltac lf_forward_step :=
  match goal with 
    | H : Some _ = listS _ |- _ =>  symmetry in H
    | H : Rcast option _ (Some _) = Some _ |- _ => apply Rcast_option_inj in H; subst
    | _ => 
       first [
        lf_nil_type |
        lf_fold_type |
        lf_nil_expr |
        lf_cons_expr |
        lf_fold_expr
      ]
  end.

Ltac bf_forward_step :=
  match goal with 
    | H : Some _ = baseS _ |- _ =>  symmetry in H
	| _ : baseS ?e = Some (pConst ?t ?c),
	  _ : ExprDsimul.ExprDenote.exprD' _ _ ?t ?e = Some (fun _ _ => ?c) |- _ => fail 1
	| H1 : baseS ?e = Some (pConst _ _), H2 : ExprDsimul.ExprDenote.exprD' _ _ _ ?e = Some _|- _ =>
	  let H := fresh "H" in
	     pose proof (bf_const_type_eq _ _ H1 H2) as H; r_inj H; repeat clear_eq; pose proof(bf_const_eq _ H1 H2); subst
  end.
  
Ltac saturate_exprD_types :=
  match goal with
    | H : ExprDsimul.ExprDenote.exprD' ?tus ?tvs ?t ?e = Some _ |- _ =>
      match goal with
        | _ : typeof_expr tus tvs e = Some t |- _ => fail 1
        | H1 : typeof_expr tus tvs e = Some ?u |- _ =>
          let H2 := fresh "H" in
            assert (t = u) as H1 by
              (let H3 := fresh "H" in
                 pose proof (ExprTac.exprD_typeof_Some _ _ _ _ _ H) as H3;
                 rewrite H3 in H1; inv_all; subst; reflexivity);
            subst 
        | _ => pose proof (ExprTac.exprD_typeof_Some _ _ _ _ _ H)
      end
  end. 
  
Ltac forward_step :=
  first [
    lf_forward_step | 
    bf_forward_step
  ].

Ltac destruct_match_goal tac :=
  repeat (
    match goal with 
      | |- context [match ?e with _ => _ end] =>
        destruct e eqn:?; try tac
    end
  ); subst.

Ltac bf_rewrite_in_match :=
  match goal with 
    | |- context [typeof_sym (fConst ?t ?c)] =>
        rewrite (BaseFunc_typeOk _ (bf_fConstOk _ _)); simpl     
    | |- context [ExprDsimul.ExprDenote.exprD' _ _ ?t (mkConst ?t _)] =>
      rewrite mkConst_sound      
  end.

Ltac rewrite_in_match :=
  match goal with 
    | [ H : ?x = _ |- context[match ?x with _ => _ end]] => 
       rewrite H
    | [ H : ?x = _, H1 : context[match ?x with _ => _ end] |- _] => 
       rewrite H in H1
    | _ => bf_rewrite_in_match
  end.

Ltac red_exprD_hyp := 
  repeat (
    match goal with
      |  H : ExprDsimul.ExprDenote.exprD' _ _ _ (apps _ _) = Some _ |- _ =>
        simpl in H
      |  H : ExprDsimul.ExprDenote.exprD' _ _ _ (App _ _) = Some _ |- _ =>
        rewrite exprD'_App in H; simpl in H; (repeat (first [
          rewrite_in_match | 
          destruct_match_oneres])); inv_all; subst
    end).

Ltac red_exprD_goal := 
  repeat (
    match goal with
      | |- context [ExprDsimul.ExprDenote.exprD' _ _ _ (apps _ _)] =>
        simpl
      | |- ExprDsimul.ExprDenote.exprD' _ _ _ (beta _) = Some _ =>
        apply beta_sound
      | |- context [ExprDsimul.ExprDenote.exprD' _ _ _ (App _ _)] =>
        rewrite exprD'_App; simpl; (repeat rewrite_in_match); inv_all; subst
    end).

Ltac Rty_elim :=
  match goal with
    | H : typ2 _ _ = typ2 _ _ |- _ => r_inj H; clear_eq
    | H : Rty (typ2 _ _) (typ2 _ _) |- _ => r_inj H; clear_eq
    | H : Rty _ _ |- _ => unfold Rty in H; subst
  end.
  
Opaque beta.

Ltac destruct_exprs tac :=
  destruct_match_goal tac; simpl;
  try Rty_elim; simpl.

Ltac reduce :=
  (try red_exprD_hyp); repeat forward_step; repeat saturate_exprD_types; (try red_exprD_goal); repeat (first [
        progress (unfold foldD, fun_to_typ3) |
        progress (unfold consD, fun_to_typ2) |
        progress (repeat rewrite (exprT_App_wrap) in *)]).

  Lemma foldTacOk : partial_reducer_ok foldTac.
  Proof.
    unfold partial_reducer_ok; intros.
    exists val; split; [|reflexivity].
    unfold foldTac.
    destruct_exprs assumption.
    reduce.
    + remember (listD t3); clear Heql.
	  induction l; intros; subst; simpl.
	  * assumption.
	  * reduce.
  	    do 2 rewrite exprT_App_wrap_sym.
	    reflexivity.
    + reduce. 
      clear Heqo0.
      generalize dependent e2; generalize dependent e5. 
      induction l3; intros; simpl. 
      * apply expr_to_list_nil in Heqp. subst.
        reduce. 
        reflexivity.
      * reduce.
        destruct (expr_to_list_cons tus tvs _ _ Heqp Heqo1) as [? [? ?]]; subst.
        reduce; subst.

        specialize (IHl3 _ _ H0 H2 Heqo3).
        reduce.
        rewrite H1.
        
        reduce.
        do 2 (rewrite exprT_App_wrap_sym).
        f_equal.
        do 2 (apply functional_extensionality; intro).
        rewrite listD_inv. reflexivity.
  Qed.

End Fold.