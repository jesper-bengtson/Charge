Require Import ExtLib.Data.HList.
Require Import ExtLib.Core.RelDec.

Require Import Charge.Logics.ILogic.
Require Import Charge.ModularFunc.ListType.
Require Import Charge.ModularFunc.BaseType.
Require Import Charge.ModularFunc.ListFunc.
Require Import Charge.ModularFunc.BaseFunc.
Require Import Charge.ModularFunc.SemiEqDecTyp.
Require Import Charge.Tactics.Base.DenotationTacs.
Require Import Charge.Tactics.Base.MirrorCoreTacs.
Require Import ExtLib.Tactics.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.Lambda.Expr.

Section NoDup.
  Context {typ func : Type} {RType_typ : RType typ} {RSym_func : RSym func}
          {BT : BaseType typ} {BTD : BaseTypeD BT}
          {LT : ListType typ} {LTD: ListTypeD LT}.
  Context {BF : BaseFunc typ func} {LF : ListFunc typ func}.
  Context {RelDec_eq : RelDec (@eq typ)} {RelDecOk_eq : RelDec_Correct RelDec_eq}.
  Context {Heqd : SemiEqDecTyp typ} {HeqdOk : SemiEqDecTypOk Heqd}.
  
   Context {EU : ExprUVar (expr typ func)}.

  Context {RType_typOk : RTypeOk} {RsymOk_func : RSymOk RSym_func}.

  Context {Typ0_tyProp : Typ0 _ Prop}.
  Context {Typ2_tyArr : Typ2 _ Fun}.
  
  Context {Typ0Ok_tyProp : Typ0Ok Typ0_tyProp}.
  Context {Typ2Ok_tyArr : Typ2Ok Typ2_tyArr}.
    
  Context {BFOk : BaseFuncOk typ func } {LFOk : ListFuncOk typ func}.

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.
  Let tyProp := @typ0 typ RType_typ Prop Typ0_tyProp.

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
    
  Fixpoint no_dup {t : typ} (xs : list (typD t)) : option bool :=
    match xs with
      | nil => Some true
      | x :: xs =>
        match in_dec x xs with
          | Some true => Some false
          | Some false => no_dup xs
          | None => None
        end
    end.
    
  Lemma no_dup_sound (t : typ) (xs : list (typD t)) (H : no_dup xs = Some true) : NoDup xs.
  Proof.
    induction xs.
    + constructor.
    + simpl in H.
      do 2 destruct_match_oneres.
      constructor; [|apply IHxs; assumption]; subst.
      intros HIn.
      eapply in_dec_false; eassumption.
  Qed.

  Definition NODUP : rtac typ (expr typ func) := fun tus tvs nus nvs ctx s e => Fail.
  (*
    fun tus tvs nus nvs ctx s e =>
    match e with
	  | App f lst =>
	    match listS f, baseS lst with
	      | Some (pNoDup t), Some (pConst u lst') =>
		    match type_cast u (tyList t) with
		  	  | Some pf => 
	            match no_dup (listD (eq_rect _ typD lst' _ pf)) with
	              | Some true => Solved s
	              | _ => Fail
		        end
		      | None => Fail
		    end
	      | _, _ => Fail
	    end
	  | _ => Fail
    end.
    *)

  Existing Instance Expr_expr.
  Existing Instance ExprOk_expr.

  Lemma propD_to_exprD tus tvs e eD (H : propD tus tvs e = Some eD) : 
    exists eD', exprD' tus tvs tyProp e = Some eD' /\ eD = fun us vs => PropD (eD' us vs).
  Proof.
    admit.
    (*
    unfold propD, exprD'_typ0 in H.
    destruct_match_oneres; inv_all; subst.
    exists e0; split; [apply Heqo|].
    unfold PropD, eq_rect; simpl.
    pose proof typ0_match_zeta.
    specialize (H typ _ Prop _  _ (exprT tus tvs) (fun us vs => PropD (e0 us vs)) e0).
    unfold exprT, OpenT.
    generalize (typ0_cast (F := Prop)). intros.
    destruct e1. reflexivity.
*)
  Admitted.

  Lemma NODUP_sound : rtac_sound NODUP.
  Proof.
    admit.
    (*
    unfold rtac_sound; intros; subst.
    destruct g; simpl; try apply I.
    do 7 (destruct_exprs; try apply I).
    intros.
    split; [assumption|].
    repeat destruct_match_oneres.
    split; [reflexivity|]; intros; subst.
    eapply Pure_pctxD; [eassumption|]; intros.
    apply propD_to_exprD in Heqo4.
    destruct Heqo4 as [? [? ?]]; subst.
    simpl in *.
    reduce.
    unfold PropD, NoDupD, PropR. reduce.
    apply no_dup_sound. assumption.
*)
  Admitted.

End NoDup.