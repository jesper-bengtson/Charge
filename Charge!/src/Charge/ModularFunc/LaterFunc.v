Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Data.Bool.
Require Import ExtLib.Data.String.
Require Import ExtLib.Tactics.Consider.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.syms.SymEnv.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.SymI.

Require Import Charge.Logics.ILogic.
Require Import Charge.Logics.Later.
Require Import Charge.ModularFunc.ILogicFunc.

Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.


Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Class LaterFunc (typ func : Type) := {
  fLater : typ -> func
}.
    
Section LaterFuncSum.
	Context {typ func : Type} {H : LaterFunc typ func}.

	Global Instance LaterFuncSumL (A : Type) : 
	   LaterFunc typ (func + A) := {
		  fLater l := inl (fLater l)
       }.

	Global Instance LaterFuncSumR (A : Type) : 
		LaterFunc typ (A + func) := {
		  fLater l := inr (fLater l)
       }.

	Global Instance LaterFuncExpr : 
		LaterFunc typ (expr typ func) := {
		  fLater l := Inj (fLater l)
        }.

End LaterFuncSum.

Section LaterFuncInst.

	Context {typ func : Type}.
	Context {HR : RType typ} {Heq : RelDec (@eq typ)} {HC : RelDec_Correct Heq}.

    Variable Typ2_tyArr : Typ2 _ Fun.
    Variable Typ0_tyProp : Typ0 _ Prop.

    Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.
    Let tyProp : typ := @typ0 _ _ _ _.

  Inductive later_func :=
    | lilf_later (logic : typ).
    
	Global Instance LaterFuncInst : LaterFunc typ later_func := {
	  fLater := lilf_later
	}.
	
  Variable is : logic_ops.

  Definition later_ops := forall (t : typ),
    option (ILLOperators (typD t)).
  Definition bilogic_opsOk (l : later_ops) : Prop :=
    forall g, match is g, l g return Prop with
                | Some T, Some U => @ILLater _ T U
                | _, _ => True
              end.

  Variable gs : later_ops.
  
  Definition typeof_later_func (f : later_func) : option typ :=
    match f with
      | lilf_later t => match gs t with
				  	      | Some _ => Some (tyArr t t)
				  	      | None => None
				  	   end
  	end.

  Global Instance RelDec_later_func : RelDec (@eq later_func) :=
  { rel_dec := fun a b =>
	         match a, b with
	  	       | lilf_later t, lilf_later t' => t ?[eq] t'
	         end
  }.

  Global Instance RelDec_Correct_later_func : RelDec_Correct RelDec_later_func.
  Proof.
    constructor.
    destruct x; destruct y; simpl;
    repeat rewrite rel_dec_correct; intuition congruence.
  Qed.
  
  Definition typ2_cast' (a b : typ)
  	: (typD a -> typD b) -> typD (tyArr a b) := 
  		fun f =>
  		match eq_sym (typ2_cast a b) in _ = t return t with
  			| eq_refl => f
  		end.

  Definition typ2_cast_bin (a b c : typ)
  : (typD a -> typD b -> typD c) -> typD (tyArr a (tyArr b c)) :=
    fun f =>
      match eq_sym (typ2_cast a (tyArr b c)) in _ = t
            return t with
        | eq_refl => match eq_sym (typ2_cast b c) in _ = t
                           return _ -> t with
                       | eq_refl => f
                     end
        end.

 Definition funcD (f : later_func) : match typeof_later_func f return Type with
							           | Some t => typD t
							           | None => unit
							         end :=
    match f as f
          return match typeof_later_func f return Type with
		   | Some t => typD t
		   | None => unit
		 end
    with
      | lilf_later t =>
        match gs t as x
              return (match match x with
			      | Some _ => Some (tyArr t t)
			      | None => None
			    end with
			| Some t0 => typD t0
			| None => unit
		      end) with
	  | Some t0 => typ2_cast' _ _ illater
	  | None => tt
        end
    end.

  Global Instance RSym_later_func : SymI.RSym later_func :=
  { typeof_sym := typeof_later_func
  ; sym_eqb := fun a b => Some (rel_dec a b)
  ; symD := funcD
  }.

  Global Instance RSymOk_later_func : SymI.RSymOk RSym_later_func.
  Proof.
    constructor.
    intros. unfold sym_eqb; simpl.
    consider (a ?[ eq ] b); auto.
  Qed.

End LaterFuncInst.

Section MakeLater.
	Context {typ func : Type} {H : LaterFunc typ func}.

	Definition mkLater (t : typ) (P : expr typ func) : expr typ func := App (fLater t) P.

End MakeLater.
