Require Import ExtLib.Data.HList.
Require Import ExtLib.Core.RelDec.

Require Import Charge.Logics.ILogic.
Require Import Charge.ModularFunc.ListType.
Require Import Charge.ModularFunc.BaseType.
Require Import Charge.ModularFunc.ListFunc.
Require Import Charge.ModularFunc.BaseFunc.
Require Import Charge.ModularFunc.ILogicFunc.
Require Import Charge.ModularFunc.SemiEqDecTyp.
Require Import Charge.Tactics.Base.DenotationTacs.
Require Import Charge.Tactics.Base.MirrorCoreTacs.
Require Import ExtLib.Tactics.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.Lambda.Expr.
(*
Section In.
  Context {typ func : Type} {RType_typ : RType typ} {RSym_func : RSym func}
          {BT : BaseType typ} {BTD : BaseTypeD}
          {LT : ListType typ} {LTD: ListTypeD LT}.
          
  Context {BF : BaseFunc typ func} {LF : ListFunc typ func} {ILF : ILogicFunc typ func}.
  Context {RelDec_eq : RelDec (@eq typ)} {RelDecOk_eq : RelDec_Correct RelDec_eq}.
  Context {Heqd : SemiEqDecTyp typ} {HeqdOk : SemiEqDecTypOk Heqd}.
  
   Context {EU : ExprUVar (expr typ func)}.

  Context {RType_typOk : RTypeOk} {RsymOk_func : RSymOk RSym_func}.

  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Typ2_tyArr : Typ2 _ Fun}.
  
  Context {Typ2Ok_tyARr : Typ2Ok Typ2_tyArr}.
    
  Context {BFOk : BaseFuncOk typ func } {LFOk : ListFuncOk typ func}.

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.
  Let tyProp := @typ0 typ RType_typ Prop Typ0_Prop.

  Fixpoint in_dec {t : typ} (e : typD t) (xs : list (typD t)) : option bool :=
    match xs with
      | nil => Some false
      | x :: xs =>
        match semi_eq_dec_typ e x with
          | Some true => Some true
          | Some false => in_dec e xs
          | None => None
        end
    end.
    
  Lemma in_dec_true {t : typ} (e : typD t) (lst : list (typD t)) (H : in_dec e lst = Some true) : In e lst.
  Proof.
    induction lst.
    + simpl in H; congruence.
    + simpl in H. destruct_match_oneres.
      destruct b.
      * apply semi_eq_dec_typ_eq in Heqo. subst.
        left; reflexivity.
      * apply semi_eq_dec_typ_neq in Heqo.
        right; apply IHlst; apply H.
  Qed.
    
  Lemma in_dec_false {t : typ} (e : typD t) (lst : list (typD t)) (H : in_dec e lst = Some false) (HIn : In e lst) : False.
  Proof.
    induction lst.
    + destruct HIn.
    + destruct HIn as [Heq | HIn]; subst.
      * simpl in H.
        remember (semi_eq_dec_typ e e).
        destruct o; [|inversion H].
        symmetry in Heqo.
        apply semi_eq_dec_typ_refl in Heqo; subst. inversion H.
      * simpl in H. destruct (semi_eq_dec_typ e a); subst; [|inversion H].
        destruct b; [inversion H|].
        apply IHlst; assumption.
  Qed.

  Existing Instance Expr_expr.
  Existing Instance ExprOk_expr.
  Require Import MirrorCore.Lambda.ExprUnify.
  Check MirrorCore.Lambda.ExprUnify.exprUnify.
  SearchAbout exprUnify.
  
Print RSymOk.
  
Check expr_
  Fixpoint IN_aux (a lst : expr typ func) : option bool :=
    match lst with
      | App (App f x) xs =>
        match listS f with
          | Some (pCons _) =>
            match sym_eqb a x with
              | Some true => Some true
              | Some false => IN_aux a xs
              | None => None
            end
          | _ => None
        end
      | _ => None
    end.

  Definition IN : rtac typ (expr typ func) :=
    fun tus tvs nus nvs ctx s e =>
    match e with
	  | App (App f x) lst =>
	    match listS f, baseS x, baseS lst with
	      | Some (pIn t), Some (pConst u x'), Some (pConst v lst') =>
		    match type_cast t u, type_cast (tyList t) v with
		  	  | Some pf, Some pf' => 
	            match in_dec (eq_rect_r typD x' pf) (listD (eq_rect_r typD lst' pf')) with
	              | Some true => Solved s
	              | Some false => More s (GGoal (mkFalse tyProp))
	              | _ => Fail
		        end
		      | _, _ => Fail
		    end
	      | _, _, _ => Fail
	    end
	  | _ => Fail
    end.
    
 
  Lemma IN_sound : rtac_sound IN.
  Proof.
    unfold rtac_sound; intros; subst.
    destruct g; simpl; try apply I.
    do 11 (destruct_exprs; try apply I).
    intros.
    split; [assumption|].
    repeat destruct_match_oneres.
    split; [reflexivity|]; intros; subst.
    
    SearchAbout WellFormed_ctx_subst pctxD.
    eapply pctxD_substD'; try eassumption.
    apply _.
    SearchAbout ctx_substD pctxD.
    unfold propD, exprD'_typ0 in Heqo4.
    destruct_match_oneres; inv_all; subst.
    simpl in Heqo5.
    reduce.
    unfold NoDupD.
    rewrite Denotation.exprT_App_wrap.
 Qed.

  match goal with
    | H1 : listS ?e = Some (pNoDup ?t) |- _ =>
      match goal with
        | _ : ExprDsimul.ExprDenote.exprD' _ _ (typ2 (tyList t) (typ0 (F := Prop))) _ =
          Some (fun _ _ => zipD t u) |- _ => fail 3
        | _ : ExprDsimul.ExprDenote.funcAs _ (typ2 (tyList t) (typ0 (F := Prop))) =
   		  Some ( t) |- _ => fail 4
		| H2 : ExprDsimul.ExprDenote.funcAs e (typ2 (tyList t) (typ0 (F := Prop))) = Some _ |- _ =>
	 	  let H := fresh "H" in pose proof(lf_NoDup_func_eq _ H1 H2); subst
		| H2 : ExprDsimul.ExprDenote.exprD' _ _ (typ2 (tyList t) (typ0 (F := Prop))) e = Some _ |- _ =>
	  	  let H := fresh "H" in pose proof(lf_NoDup_eq _ H1 H2); subst
	 end
(*    | H : ExprDsimul.ExprDenote.exprD' _ _ (tyList ?t) (mkNoDup ?t _ _) = Some _ |- _ =>
	  pose proof (mkNoDupD _ _ _ H); clear H; (repeat destruct_match_oneres)*)
  end.

    lf_NoDup_expr.
  match goal with
    | H1 : listS ?e = Some (pNoDup ?t) |- _ =>
      match goal with
        | _ : ExprDsimul.ExprDenote.funcAs e (typ2 (tyList t) (typ0 (F := Prop))) = Some _ |- _ => fail 1
        | _ : ExprDsimul.ExprDenote.exprD' _ _ (typ2 (tyList t) typ0) e = Some _ |- _ => fail 1
        | H2 : ExprDsimul.ExprDenote.funcAs e _ = Some _ |- _ =>
  	  	  let H := fresh "H" in
	        pose proof (lf_NoDup_func_type_eq _ _ H1 H2) as H; try (r_inj H); try list_inj; repeat clear_eq; subst
	    | H2 : ExprDsimul.ExprDenote.exprD' _ _ _ e = Some _ |- _ =>
	      let H := fresh "H" in
	        pose proof (lf_NoDup_type_eq _ _ H1 H2) as H; try (r_inj H); try list_inj; repeat clear_eq; subst
	  end
  end.
    progress lf_NoDup_type.
    lf_NoDup_type.
  pose proof (bf_const_func_type_eq _ _ Heqo0 Heqo5).

  match goal with
    | H1 : baseS ?e = Some (pConst ?t ?c) |- _ =>
      match goal with
        | _ : ExprDsimul.ExprDenote.funcAs e t = Some _ |- _ => fail 3
        | _ : ExprDsimul.ExprDenote.exprD' _ _ t e = Some _ |- _ => fail 4
        | H2 : ExprDsimul.ExprDenote.funcAs e _ = Some _ |- _ => 
  	  	  let H := fresh "H" in
	        pose proof (bf_const_func_type_eq _ _ H1 H2) as H; repeat clear_eq; subst
	    | H2 : ExprDsimul.ExprDenote.exprD' _ _ _ e = Some _ |- _ =>
	      let H := fresh "H" in
	        pose proof (bf_const_type_eq _ _ H1 H2) as H; repeat clear_eq; subst
	  end
  end.
  
    
    bf_const_type.
    unfold propD, exprD'_typ0 in Heqo4.
    destruct_match_oneres; inv_all; subst.
    autorewrite with exprD_rw in Heqo5.
    Locate exprD'.
    rewrite exprD'_App in Heqo5.
    unfold ExprI.exprD' in Heqo5; simpl in Heqo5.
    forward.
    SearchAbout typ0_cast.
    subst.
    destruct (typ0_cast (F := Prop) (_ = T)).
    Print rtac_spec.

End In.

*)