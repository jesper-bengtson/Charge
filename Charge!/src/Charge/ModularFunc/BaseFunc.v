Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Data.Bool.
Require Import ExtLib.Data.String.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.

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

Section BaseFuncOk.
  Context {typ func : Type} {BF: BaseFunc typ func}.
  Context {RType_typ : RType typ} {RSym_func : RSym func}.
  Context {RelDec_eq : RelDec (@eq typ)}.
  Context {BT : BaseType typ} {BTD : BaseTypeD}.

  Context {Typ2_tyArr : Typ2 _ Fun}.
  Context {Typ0_Prop : Typ0 _ Prop}.

  Class BaseFuncOk := {
    bf_funcAsOk (f : func) (e : base_func typ) : baseS f = Some e -> 
      forall t, funcAs f t = funcAs (RSym_func := RSym_BaseFunc Typ2_tyArr Typ0_Prop) e t;
    bf_fNatOk n : baseS (fNat n) = Some (pNat typ n);
    bf_fBoolOk b : baseS (fBool b) = Some (pBool typ b);
    bf_fStringOk s : baseS (fString s) = Some (pString typ s);
    bf_fEqOk t : baseS (fEq t) = Some (pEq t);
    bf_fPairOk t u : baseS (fPair t u) = Some (pPair t u)
  }.

End BaseFuncOk.

Implicit Arguments BaseFuncOk [[BF] [RType_typ] [RSym_func] [RelDec_eq] [BT] [BTD] [Typ2_tyArr] [Typ0_Prop]].

Section BaseFuncBaseOk.
  Context {typ func : Type} {BF: BaseFunc typ func}.
  Context {RType_typ : RType typ} {RSym_func : RSym func}.
  Context {RelDec_eq : RelDec (@eq typ)}.
  Context {BT : BaseType typ}.
  Context {BTD : BaseTypeD}.

  Context {Typ2_tyArr : Typ2 _ Fun}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.
  
  Global Program Instance BaseFuncBaseOk : BaseFuncOk typ (RSym_func := RSym_BaseFunc Typ2_tyArr Typ0_Prop) (base_func typ) := {
    bf_funcAsOk := fun _ _ _ _ => eq_refl;
    bf_fNatOk n := eq_refl;
    bf_fBoolOk b := eq_refl;
    bf_fStringOk s := eq_refl;
    bf_fEqOk t := eq_refl;
    bf_fPairOk t u := eq_refl
  }.

End BaseFuncBaseOk.

Section BaseFuncExprOk.
  Context {typ func : Type} `{HOK : BaseFuncOk typ func}.
  Context {HROk : RTypeOk}.
  Context {A : Type} {RSymA : RSym A}.

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.
  Let tyProp : typ := @typ0 _ _ _ _.

  Lemma BaseFunc_typeOk (f : func) (e : base_func typ) (H : baseS f = Some e) :
    typeof_sym f = typeof_base_func _ _ e.
  Proof.
    destruct HOK as [H1 H2 _ _ _ _ _ _ _].
    specialize (H1 _ _ H).
    destruct e; simpl in *;
    match goal with 
      | |- typeof_sym ?f = Some ?t => 
	 	specialize (H1 t);
	 	simpl in H1;
	 	unfold funcAs in H1; simpl in H1 ; rewrite type_cast_refl in H1; [|apply _];
	    generalize dependent (symD f);
	 	destruct (typeof_sym f); simpl; intros; [forward|]; inversion H1
 	end.
  Qed.
  
  Lemma bf_nat_type_eq (f : func) n t df
    (H1 : baseS f = Some (fNat n)) (H2 : funcAs f t = Some df) :
    t = tyNat.
  Proof.
    rewrite (bf_funcAsOk _ H1) in H2.
    unfold funcAs in H2; simpl in *.
    forward.
  Qed.

  Lemma bf_bool_type_eq (f : func) b t df
    (H1 : baseS f = Some (fBool b)) (H2 : funcAs f t = Some df) :
    t = tyBool.
  Proof.
    rewrite (bf_funcAsOk _ H1) in H2.
    unfold funcAs in H2; simpl in *.
    forward.
  Qed.

  Lemma bf_string_type_eq (f : func) s t df
    (H1 : baseS f = Some (fString s)) (H2 : funcAs f t = Some df) :
    t = tyString.
  Proof.
    rewrite (bf_funcAsOk _ H1) in H2.
    unfold funcAs in H2; simpl in *.
    forward.
  Qed.

  Lemma bf_eq_type_eq (f : func) t u df
    (H1 : baseS f = Some (fEq t)) (H2 : funcAs f u = Some df) :
    u = tyArr t (tyArr t tyProp).
  Proof.
    rewrite (bf_funcAsOk _ H1) in H2.
    unfold funcAs in H2; simpl in *.
    forward.
    rewrite <- r; reflexivity.
  Qed.

  Lemma bf_pair_type_eq (f : func) t u v df
    (H1 : baseS f = Some (fPair t u)) (H2 : funcAs f v = Some df) :
    v = tyArr t (tyArr u (tyPair t u)).
  Proof.
    rewrite (bf_funcAsOk _ H1) in H2.
    unfold funcAs in H2; simpl in *.
    forward.
    rewrite <- r; reflexivity.
  Qed.
Require Import MirrorCore.syms.SymSum.

  Existing Instance RSym_sum.

  Global Program Instance BaseFuncOkSumR : BaseFuncOk typ ((A + func)%type) := {
    bf_funcAsOk := 
      fun a f H t => 
        match a with
          | inl b => _
          | inr b => _
        end;
    bf_fNatOk n := bf_fNatOk (func := func) n;
    bf_fBoolOk b := bf_fBoolOk (func := func) b;
    bf_fStringOk s := bf_fStringOk (func := func) s;
    bf_fEqOk t := bf_fEqOk (func := func) t;
    bf_fPairOk t u := bf_fPairOk (func := func) t u
  }.
  Next Obligation.
    apply (bf_funcAsOk (func := func)).
    apply H.
  Qed.

  Global Program Instance BaseFuncOkSumL : BaseFuncOk typ ((func + A)%type) := {
    bf_funcAsOk := 
      fun a f H t => 
        match a with
          | inl b => _
          | inr b => _
        end;
    bf_fNatOk n := bf_fNatOk (func := func) n;
    bf_fBoolOk b := bf_fBoolOk (func := func) b;
    bf_fStringOk s := bf_fStringOk (func := func) s;
    bf_fEqOk t := bf_fEqOk (func := func) t;
    bf_fPairOk t u := bf_fPairOk (func := func) t u
  }.
  Next Obligation.
    apply (bf_funcAsOk (func := func)).
    apply H.
  Qed.


End BaseFuncExprOk.

Section TypeOfFunc.
  Context {typ func : Type}.
  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {RSym_func : RSym func}.
  
  Lemma typeof_funcAs f t e (H : funcAs f t = Some e) : typeof_sym f = Some t.
  Proof.
    unfold funcAs in H.
    generalize dependent (symD f).
    destruct (typeof_sym f); intros; [|congruence].
    destruct (type_cast t0 t); [|congruence].
    destruct r; reflexivity.
  Qed.
    
  Lemma funcAs_Some f t (pf : typeof_sym f = Some t) :
    funcAs f t =
    Some (match pf in (_ = z)
      return match z with
               | Some z' => typD z'
               | None => unit
             end
      with
      | eq_refl => symD f
      end).
  Proof.
    unfold funcAs.
    generalize (symD f).
    rewrite pf. intros.
    rewrite type_cast_refl. reflexivity. apply _.
  Qed.

End TypeOfFunc.

Section MakeBaseFuncSound.
  Context {typ func : Type} `{HOK : BaseFuncOk typ func}.
  Context {HROk : RTypeOk} {Typ2_tyArrOk : Typ2Ok Typ2_tyArr}
          {RSym_funcOk : RSymOk RSym_func0}.

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.

  Lemma mkNat_sound (n : nat) (tus tvs : tenv typ) (f : func)
    (df : typD tyNat)
    (Ho : baseS f = Some (pNat typ n))
    (Hf : funcAs f tyNat = Some df) :
    exprD' tus tvs tyNat (mkNat n) = Some (fun _ _ => df).
  Proof.
    unfold mkNat; simpl.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    pose proof (bf_funcAsOk _ Ho) as H; rewrite H in Hf.
    pose proof (bf_fNatOk n) as H1.
    pose proof (bf_funcAsOk _ H1) as H2. rewrite <- H2 in Hf.
    pose proof (BaseFunc_typeOk _ H1) as H3. simpl in H3.
    rewrite (funcAs_Some _ H3).
    rewrite (funcAs_Some _ H3) in Hf.
    inv_all; subst. reflexivity.
  Qed.
    
  Lemma mkBool_sound (b : bool) (tus tvs : tenv typ) (f : func)
    (df : typD tyBool)
    (Ho : baseS f = Some (pBool typ b))
    (Hf : funcAs f tyBool = Some df) :
    exprD' tus tvs tyBool (mkBool b) = Some (fun _ _ => df).
  Proof.
    unfold mkBool; simpl.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    pose proof (bf_funcAsOk _ Ho) as H; rewrite H in Hf.
    pose proof (bf_fBoolOk b) as H1.
    pose proof (bf_funcAsOk _ H1) as H2. rewrite <- H2 in Hf.
    pose proof (BaseFunc_typeOk _ H1) as H3. simpl in H3.
    rewrite (funcAs_Some _ H3).
    rewrite (funcAs_Some _ H3) in Hf.
    inv_all; subst. reflexivity.
  Qed.

  Lemma mkString_sound (s : string) (tus tvs : tenv typ) (f : func)
    (df : typD tyString)
    (Ho : baseS f = Some (pString typ s))
    (Hf : funcAs f tyString = Some df) :
    exprD' tus tvs tyString (mkString s) = Some (fun _ _ => df).
  Proof.
    unfold mkString; simpl.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    pose proof (bf_funcAsOk _ Ho) as H; rewrite H in Hf.
    pose proof (bf_fStringOk s) as H1.
    pose proof (bf_funcAsOk _ H1) as H2. rewrite <- H2 in Hf.
    pose proof (BaseFunc_typeOk _ H1) as H3. simpl in H3.
    rewrite (funcAs_Some _ H3).
    rewrite (funcAs_Some _ H3) in Hf.
    inv_all; subst. reflexivity.
  Qed.
  
End MakeBaseFuncSound.