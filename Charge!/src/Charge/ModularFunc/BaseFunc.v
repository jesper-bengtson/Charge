Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Data.Bool.
Require Import ExtLib.Data.String.
Require Import ExtLib.Tactics.Consider.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.syms.SymEnv.
Require Import MirrorCore.Lambda.Expr.

Require Import Charge.Logics.ILogic.
Require Import Charge.ModularFunc.BaseType.

Require Import Coq.Strings.String.


Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Inductive base_func typ :=
  | pNat : nat -> base_func typ
  | pBool : bool -> base_func typ
  | pString : string -> base_func typ
  | pEq : typ -> base_func typ
  | pPair : typ -> typ -> base_func typ.

Class BaseFunc (typ func : Type) := {
  fNat  : nat -> func;
  fBool : bool -> func;
  fString : string -> func;
  
  fEq : typ -> func;
  fPair : typ -> typ -> func;
  
  baseS : func -> option (base_func typ)
}.

    
Section BaseFuncSum.
	Context {typ func : Type} {H : BaseFunc typ func}.

	Global Instance BaseFuncSumL (A : Type) : 
		BaseFunc typ (func + A) := {
		  fNat n := inl (fNat n)
	    ; fBool b := inl (fBool b)
	    ; fString s := inl (fString s)
        ; fEq t := inl (fEq t)
        ; fPair t1 t2 := inl (fPair t1 t2)
        ; baseS f := match f with
        			   | inl a => baseS a
        			   | inr _ => None
        			 end
        }.

	Global Instance BaseFuncSumR (A : Type) : 
		BaseFunc typ (A + func) := {
		  fNat n := inr (fNat n)
	    ; fBool b := inr (fBool b)
	    ; fString s := inr (fString s)
        ; fEq t := inr (fEq t)
        ; fPair t1 t2 := inr (fPair t1 t2)
        ; baseS f := match f with
        			   | inr a => baseS a
        			   | inl _ => None
        			 end
        }.
        
    Global Instance BaseFuncExpr :
    	BaseFunc typ (expr typ func) := {
    	  fNat n := Inj (fNat n);
    	  fBool b := Inj (fBool b);
    	  fString s := Inj (fString s);
    	  fEq t := Inj (fEq t);
    	  fPair t1 t2 := Inj (fPair t1 t2);
    	  baseS f := match f with
    	  			   | Inj f => baseS f
    	  			   | _     => None
    	  			 end
    }.

End BaseFuncSum.

Section BaseFuncInst.
	Context {typ : Type} {HR : RType typ} 
	        {HT : BaseType typ} {HTD: BaseTypeD}.
	Context {func : Type} {H : BaseFunc typ func}.
	Context {Heq : RelDec (@eq typ)} {HC : RelDec_Correct Heq}.

    Variable Typ2_tyArr : Typ2 _ Fun.
    Variable Typ0_tyProp : Typ0 _ Prop.

    Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.
    Let tyProp : typ := @typ0 _ _ _ _.

	Global Instance BaseFuncInst : BaseFunc typ (base_func typ) := {
	  fNat := pNat typ;
	  fBool := pBool typ;
	  fString := pString typ;
	  fEq := pEq;
	  fPair := pPair;
	  baseS f := Some f 
	}.

	Definition typeof_base_func bf :=
		match bf with
		  | pNat _ => Some tyNat
		  | pBool _ => Some tyBool
		  | pString _ => Some tyString
		  | pEq t => Some (tyArr t (tyArr t tyProp))
		  | pPair t1 t2 => Some (tyArr t1 (tyArr t2 (tyPair t1 t2)))
		end.

	Definition base_func_eq (a b : base_func typ) : option bool :=
	  match a , b with
	    | pNat a, pNat b => Some (a ?[ eq ] b)
	    | pBool a, pBool b => Some (a ?[ eq ] b)
	    | pString a, pString b => Some (a ?[ eq ] b)
	    | pEq t1, pEq t2 => Some (t1 ?[ eq ] t2)
	    | pPair t1 t2, pPair t3 t4 => Some (t1 ?[ eq ] t3 &&
	      								    t2 ?[ eq ] t4)%bool
	    | _, _ => None
	  end.

    Global Instance RelDec_base_func : RelDec (@eq (base_func typ)) := {
      rel_dec a b := match base_func_eq a b with 
    	  		       | Some b => b 
    		 	       | None => false 
    			     end
    }.

    Global Instance RelDec_Correct_ilfunc : RelDec_Correct RelDec_base_func.
    Proof.
      constructor.
      destruct x; destruct y; simpl;
      try solve [ try rewrite Bool.andb_true_iff ;
                  repeat rewrite rel_dec_correct; intuition congruence ].
    Qed.
  
	 Definition base_func_symD bf :=
		match bf as bf return match typeof_base_func bf with
								| Some t => typD t
								| None => unit
							  end with
	    | pNat n => eq_rect_r id n btNat
	    | pBool b => eq_rect_r id b btBool
	    | pString s => eq_rect_r id s btString
	    | pEq t => 
	       eq_rect_r id
             (eq_rect_r (fun T : Type => typD t -> T)
               (fun A B : typD t => eq_rect_r id (A = B)
                                    (typ0_cast (F:=Prop)))
               (typ2_cast t tyProp))
             (typ2_cast t (typ2 t tyProp))
        | pPair t1 t2 => 
           eq_rect_r id 
             (eq_rect_r (fun T : Type => typD t1 -> T)
               (fun (A : typD t1) (B : typD t2) => 
               	     eq_rect_r id (A, B) (btPair t1 t2))
               (typ2_cast t2 (tyPair t1 t2)))
             (typ2_cast t1 (typ2 t2 (tyPair t1 t2)))
	end.

	Global Instance RSym_BaseFunc : SymI.RSym (base_func typ) := {
	  typeof_sym := typeof_base_func;
	  symD := base_func_symD;
	  sym_eqb := base_func_eq
	}.

	Global Instance RSymOk_BaseFunc : SymI.RSymOk RSym_BaseFunc.
	Proof.
		split; intros.
		destruct a, b; simpl; try apply I.
		+ consider (n ?[ eq ] n0); intuition congruence.
		+ consider (b0 ?[ eq ] b); intuition congruence.
		+ consider (s ?[ eq ] s0); intuition congruence.
		+ consider (t ?[ eq ] t0); intuition congruence.
		+ consider (t ?[ eq ] t1 && t0 ?[ eq ] t2)%bool; 
		  intuition congruence.
	Qed.

End BaseFuncInst.

Section MakeBase.
	Context {typ func : Type} {H : BaseFunc typ func}.

	Definition mkNat n : expr typ func := Inj (fNat n).
	Definition mkBool b : expr typ func := Inj (fBool b).
	Definition mkString s : expr typ func := Inj (fString s).
	Definition mkEq (t : typ) (a b : expr typ func) := App (App (fEq t) a) b.
	Definition mkPair t u a b := App (App (fPair t u) a) b.

End MakeBase.