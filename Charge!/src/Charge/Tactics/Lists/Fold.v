Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.AppN.
Require Import MirrorCore.Lambda.Red.
Require Import MirrorCore.Lambda.RedAll.
Require Import MirrorCore.RTac.Simplify.

Require Import Charge.ModularFunc.BaseFunc.
Require Import Charge.ModularFunc.ListFunc.
Require Import Charge.ModularFunc.BaseType.
Require Import Charge.ModularFunc.ListType.
Require Import Charge.ModularFunc.SemiEqDecTyp.

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
              | _ => apps e args
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
  
  Lemma foldTacOk : partial_reducer_ok foldTac.
  Proof.
    unfold partial_reducer_ok; intros.
    unfold foldTac.
    remember (listS e); destruct o; [| exists val; tauto].
    destruct l; try (exists val; tauto).
    destruct es; try (exists val; tauto).
    destruct es; try (exists val; tauto).
    destruct es; try (exists val; tauto).
    destruct es; try (exists val; tauto).
    remember (baseS e2); destruct o; try (exists val; tauto).
    destruct b; try (exists val; tauto).
    remember (type_cast t2 (tyList t1)).
    destruct o; [|exists val; tauto].
    simpl in H.
    autorewrite with exprD_rw in H; simpl in H; forward; inv_all; subst.
    autorewrite with exprD_rw in H0; simpl in H0; forward; inv_all; subst.
    autorewrite with exprD_rw in H2; simpl in H2; forward; inv_all; subst.
    unfold Rty in r; subst.
    
    eexists; split; [|reflexivity].
    
    Opaque beta.
    
    simpl.
    symmetry in Heqo.
    pose proof (lf_fold_type_eq _ _ Heqo H4).
    r_inj H6.
    pose proof (lf_fold_eq _ Heqo H4).
	subst.
	unfold foldD.
	
	clear H4.
	Require Import Charge.ModularFunc.Denotation.
	unfold Denotation.fun_to_typ3.    
	repeat rewrite exprT_App_wrap.
	
	Check @bf_const_type_eq.
	symmetry in Heqo0.
	pose proof (bf_const_eq _ Heqo0 H1).
	subst. clear H1.	
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
  Qed.

End Fold.