Require Import ExtLib.Data.HList.

Require Import Charge.Logics.ILogic.
Require Import Charge.Tactics.Base.EqDep.
Require Import Charge.ModularFunc.ListType.
Require Import Charge.ModularFunc.BaseType.
Require Import Charge.ModularFunc.ListFunc.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.Lambda.Expr.

Section NoDup.
	Context {typ func : Type} {RType_typ : RType typ} {RSym_func : RSym func}
	        {HTB : BaseType typ} {HTBD : BaseTypeD}
	        {HT : ListType typ} {HTD: ListTypeD}.
	Context {H : ListFunc typ func}.

    Context {Typ2_tyArr : Typ2 _ Fun}.
    
    Context {eqt : eqDec_typ}.

    Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.

Fixpoint search_NoDup
    {A} (A_dec: forall a b: A, {a=b}+{a=b->False}) (l: list A) : option (NoDup l) :=
  match l with
  | nil => Some (NoDup_nil A)
  | a::l' =>
      match search_NoDup A_dec l' with
      | Some nodup =>
          match In_dec A_dec a l' with
          | left isin => None
          | right notin => 
 			match search_NoDup A_dec l' with
 				| Some pf => Some (NoDup_cons _ notin pf)
 				| None => None         
            end
          end
      | None => None
      end
  end.

  Definition NODUP : rtac typ (expr typ func) :=
    fun tus tvs nus nvs ctx s e =>
    match e with
	  | App f lst =>
	    match listS f with
	      | Some (pNoDup t) =>
	        match eqt t with
	          | Some eq_dec =>
		        match exprD' nil nil (tyList t) e with
		          | Some lstD =>
		            match search_NoDup eq_dec (listD t (lstD HList.Hnil HList.Hnil)) with
		              | Some _ => Solved s
		              | None => Fail
		            end
		          | None => Fail
		        end
		    | None => Fail
		  end
	      | _ => Fail
	    end
	  | _ => Fail
    end.

End NoDup.