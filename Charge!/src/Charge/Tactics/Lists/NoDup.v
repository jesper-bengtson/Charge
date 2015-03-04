Require Import ExtLib.Data.HList.

Require Import Charge.Logics.ILogic.
Require Import Charge.ModularFunc.ListType.
Require Import Charge.ModularFunc.BaseType.
Require Import Charge.ModularFunc.ListFunc.
Require Import Charge.ModularFunc.BaseFunc.
Require Import Charge.ModularFunc.SemiEqDecTyp.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.Lambda.Expr.

Section NoDup.
  Context {typ func : Type} {RType_typ : RType typ} {RSym_func : RSym func}
          {BT : BaseType typ} {BTD : BaseTypeD}
          {LT : ListType typ} {LTD: ListTypeD LT}.
  Context {H : ListFunc typ func} {BF : BaseFunc typ func}.
  
  Context {Expr_func : Expr _ (expr typ func)}.
  Context {EU : ExprUVar (expr typ func)}.

  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Typ2_tyArr : Typ2 _ Fun}.
    
  Context {Heqd : SemiEqDecTyp typ} {HeqdOk : SemiEqDecTypOk Heqd}.

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

  Definition NODUP : rtac typ (expr typ func) :=
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
    
  Require Import Charge.Tactics.Base.DenotationTacs.
  Require Import Charge.Tactics.Base.MirrorCoreTacs.
  Require Import ExtLib.Tactics.

  Lemma NODUP_sound : rtac_sound NODUP.
  Proof.
    unfold rtac_sound; intros; subst.
    destruct g; simpl; try apply I.
    do 7 (destruct_exprs; try apply I).
    intros.
    split; [assumption|].
    repeat destruct_match_oneres.
    split; [reflexivity|]; intros; subst.
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

End NoDup.