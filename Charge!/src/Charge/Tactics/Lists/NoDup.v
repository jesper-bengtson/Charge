Require Import ExtLib.Data.HList.

Require Import Charge.Logics.ILogic.
Require Import Charge.ModularFunc.ListType.
Require Import Charge.ModularFunc.BaseType.
Require Import Charge.ModularFunc.ListFunc.
Require Import Charge.ModularFunc.BaseFunc.
Require Import Charge.ModularFunc.SemiDecEqTyp.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.Lambda.Expr.

Section NoDup.
  Context {typ func : Type} {RType_typ : RType typ} {RSym_func : RSym func}
          {HTB : BaseType typ} {HTBD : BaseTypeD}
          {HT : ListType typ} {HTD: ListTypeD}.
  Context {H : ListFunc typ func} {BF : BaseFunc typ func}.

  Context {Typ2_tyArr : Typ2 _ Fun}.
    
  Context {eqt : eq_dec_typ typ}.

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.

  Fixpoint in_dec {t : typ} (e : typD t) (xs : list (typD t)) : option bool :=
    match xs with
      | nil => Some false
      | x :: xs =>
        match eqt t e x with
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
	            match no_dup (listD _ (eq_rect _ typD lst' _ pf)) with
	              | Some true => Solved s
	              | _ => Fail
		        end
		      | None => Fail
		    end
	      | _, _ => Fail
	    end
	  | _ => Fail
    end.

End NoDup.