Add Rec LoadPath "/Users/jebe/git/coq-ext-lib/theories" as ExtLib.
Add Rec LoadPath "/Users/jebe/git/mirror-core/theories" as MirrorCore.
Add Rec LoadPath "/Users/jebe/git/Charge/Charge!/bin/Charge" as Charge.

Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Data.Bool.
Require Import ExtLib.Data.String.
Require Import ExtLib.Data.Map.FMapPositive.
Require Import ExtLib.Data.SumN.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.syms.SymEnv.
Require Import MirrorCore.syms.SymSum.
Require Import MirrorCore.Lambda.Expr.

Require Import Charge.Logics.ILogic.
Require Import Charge.ModularFunc.Denotation.

Require Import Coq.Strings.String.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Inductive base_func {typ : Type} :=
  | pNat : nat -> base_func
  | pBool : bool -> base_func
  | pString : string -> base_func
  | pEq : typ -> base_func
  | pPair : typ -> typ -> base_func.

Implicit Arguments base_func [].

Class BaseFunc (typ func : Type) := {
  fNat : nat -> func;
  fBool : bool -> func;
  fString : string -> func;
  
  fEq : typ -> func;
  fPair : typ -> typ -> func;
  
  baseS : func -> option (base_func typ)
}.

Section BaseFuncSum.
	Context {typ func : Type} {H : BaseFunc typ func}.
	
	Global Instance BaseFuncPMap (p : positive) (m : pmap Type) 
	  (pf : Some func = pmap_lookup' m p) :
	  BaseFunc typ (OneOf m) := {
	    fNat n := Into (fNat n) p pf;
	    fBool b := Into (fBool b) p pf;
	    fString s := Into (fString s) p pf;
	    fEq t := Into (fEq t) p pf;
	    fPair t u := Into (fPair t u) p pf;
	    
	    baseS f :=
	      match f with
	        | Build_OneOf _ p' pf1 =>
	          match Pos.eq_dec p p' with
	            | left Heq => 
	              baseS (eq_rect_r (fun o => match o with | Some T => T | None => Empty_set end) pf1 
	                (eq_rect _ (fun p =>  Some func = pmap_lookup' m p) pf _ Heq))
	            | right _ => None
	          end
	      end
	}.

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
          {BT : BaseType typ} {HTD : BaseTypeD BT}.
  Context {func : Type} {H : BaseFunc typ func}.
  Context {Heq : RelDec (@eq typ)} {HC : RelDec_Correct Heq}.

  Context {Hseq : SemiEqDecTyp typ}.
  Context {HseqOk : SemiEqDecTypOk Hseq}.

  Context {Typ2_tyArr : Typ2 _ Fun}.
  Context {Typ0_tyProp : Typ0 _ Prop}.

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.
  Let tyProp : typ := @typ0 _ _ _ _.

  Global Instance BaseFuncInst : BaseFunc typ (base_func typ) := {
	fNat := pNat;
	fBool := pBool;
	fString := pString;
	
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
      | pPair t1 t2 => Some (tyArr t1 (tyArr t2 (tyProd t1 t2)))
    end.

  Definition rel_dec_cases {T A : Type} {RelDec_T : RelDec (@eq T)} {HROk : RelDec_Correct RelDec_T} (x y : T)
    (f_true : x = y -> A) (f_false : x <> y -> A) : A :=
  match Reflect_RelDecCorrect T eq RelDec_T HROk x y with
	| reflect_true _ _ H => (fun eq : x = y => f_true eq) H
	| reflect_false _ _ H => (fun neq : x <> y => f_false neq) H
  end.
  
  Implicit Arguments rel_dec_cases [[T] [A] [RelDec_T] [HROk]].


	  Definition base_func_eq (a b : base_func typ) : option bool :=
	  match a , b with
	    | pNat n, pNat m => Some (n ?[ eq ] m)
	    | pBool b1, pBool b2 => Some (b1 ?[ eq ] b2) 
	    | pString s1, pString s2 => Some (s1 ?[ eq ] s2)
	    | pEq t1, pEq t2 => Some (t1 ?[ eq ] t2)
	    | pPair t1 t2, pPair t3 t4 => Some (t1 ?[ eq ] t3 &&
	      					   t2 ?[ eq ] t4)%bool
	    | _, _ => None
	  end.
	
	Definition PropD (P : typD tyProp) : Prop :=
	  trmD P (typ0_cast (Typ0 := Typ0_tyProp)).
	  
	Definition PropR (P : Prop) : typD tyProp :=
	  trmR P (typ0_cast (Typ0 := Typ0_tyProp)).
	  	  
	 Definition eqD (t : typ) : typD (tyArr t (tyArr t tyProp)) :=
	   (tyArrR2 (fun a b => PropR (@eq (typD t) a b))).

	 Definition pairD (t u : typ) : typD (tyArr t (tyArr u (tyProd t u))) :=
	   (tyArrR2 (fun a b => prodR t u (a, b))).

	 Definition base_func_symD bf :=
	   match bf as bf return match typeof_base_func bf return Type with
				 | Some t => typD t
				 | None => unit
				 end with
         | pNat n => trmR n btNat
         | pBool b => trmR b btBool
         | pString s => trmR s btString
	     | pEq t => eqD t
         | pPair t u => pairD t u
	   end.

	Global Instance RSym_BaseFunc
        : SymI.RSym (base_func typ) := {
	  typeof_sym := typeof_base_func;
	  symD := base_func_symD ;
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
	Context {typ func : Type} {RType_typ : RType typ}.
	Context {HT : BaseType typ} {HF : BaseFunc typ func}.

	Definition mkNat (n : nat) : expr typ func := Inj (fNat n).
	Definition mkBool (b : bool) : expr typ func := Inj (fBool b).
	Definition mkString (s : string) : expr typ func := Inj (fString s).
	Definition mkEq (t : typ) (a b : expr typ func) := App (App (fEq t) a) b.
	Definition mkPair t u a b := App (App (fPair t u) a) b.

End MakeBase.

Section BaseFuncOk.
  Context {typ func : Type} {RType_typ : RType typ}.
  Context {BF: BaseFunc typ func} {RSym_func : RSym func}.
  Context {RelDec_eq : RelDec (@eq typ)}.
  Context {RelDec_eqOk : RelDec_Correct RelDec_eq}.
  Context {BT : BaseType typ} {BTD : BaseTypeD BT}.
  Context {Heqd : SemiEqDecTyp typ}.

  Context {Typ2_tyArr : Typ2 _ Fun}.
  Context {Typ0_Prop : Typ0 _ Prop}.

  Class BaseFuncOk := {
    bf_funcAsOk (f : func) (e : @base_func typ) : baseS f = Some e -> 
      forall t, 
        funcAs f t = 
        funcAs (RSym_func := RSym_BaseFunc) e t;
	bf_fNatOk n : baseS (fNat n) = Some (pNat n);
	bf_fBoolOk b : baseS (fBool b) = Some (pBool b);
	bf_fStringOk s : baseS (fString s) = Some (pString s);
    bf_fEqOk t : baseS (fEq t) = Some (pEq t);
    bf_fPairOk t u : baseS (fPair t u) = Some (pPair t u)
  }.

End BaseFuncOk.

Implicit Arguments BaseFuncOk [[BF] [RType_typ] [RSym_func] [RelDec_eq] [BT] [BTD]
                               [Typ2_tyArr] [Typ0_Prop]].

Section BaseFuncBaseOk.
  Context {typ func : Type} {RType_typ : RType typ}.
  Context {BF: BaseFunc typ func} {RSym_func : RSym func}.
  Context {RelDec_eq : RelDec (@eq typ)}.
  Context {RelDec_eqOk : RelDec_Correct RelDec_eq}.
  Context {Heqd : SemiEqDecTyp typ}.
  Context {BT : BaseType typ}.
  Context {BTD : BaseTypeD BT}.

  Context {Typ2_tyArr : Typ2 _ Fun}.
  Context {Typ0_Prop : Typ0 _ Prop}.

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.
  
  Global Program Instance BaseFuncBaseOk : 
  	BaseFuncOk typ (RSym_func := RSym_BaseFunc) (base_func typ) := {
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

  Context {Typ2_tyArrOk : Typ2Ok Typ2_tyArr}
          {RSym_funcOk : RSymOk RSym_func0}.

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.
  Let tyProp : typ := @typ0 _ _ _ _.

  Lemma BaseFunc_typeOk (f : func) (e : base_func typ) (H : baseS f = Some e) :
    typeof_sym f = typeof_base_func e.
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
  
  Lemma bf_typeof_nat (n : nat) : typeof_sym (fNat n) = Some tyNat.
  Proof.
    pose proof (BaseFunc_typeOk _ (bf_fNatOk n)).
    rewrite H. reflexivity.
  Qed.
  
  Lemma bf_typeof_bool (b : bool) : typeof_sym (fBool b) = Some tyBool.
  Proof.
    pose proof (BaseFunc_typeOk _ (bf_fBoolOk b)).
    rewrite H. reflexivity.
  Qed.
  
  Lemma bf_typeof_string (s : string) : typeof_sym (fString s) = Some tyString.
  Proof.
    pose proof (BaseFunc_typeOk _ (bf_fStringOk s)).
    rewrite H. reflexivity.
  Qed.
  
  Lemma bf_nat_func_type_eq (f : func) n t df
    (H1 : baseS f = Some (pNat n)) (H2 : funcAs f t = Some df) :
    t = tyNat.
  Proof.
    rewrite (bf_funcAsOk _ H1) in H2.
    unfold funcAs in H2; simpl in *.
    forward.
  Qed.

  Lemma bf_nat_type_eq (e : expr typ func) t n tus tvs de
    (H1 : baseS e = Some (pNat n)) (H2 : exprD' tus tvs t e = Some de) :
    t = tyNat.
  Proof.
   destruct e; simpl in *; try congruence.
   autorewrite with exprD_rw in H2; simpl in H2; forward; inv_all; subst.
   apply (bf_nat_func_type_eq _ _ H1 H).
  Qed.

  Lemma bf_bool_func_type_eq (f : func) b t df
    (H1 : baseS f = Some (pBool b)) (H2 : funcAs f t = Some df) :
    t = tyBool.
  Proof.
    rewrite (bf_funcAsOk _ H1) in H2.
    unfold funcAs in H2; simpl in *.
    forward.
  Qed.

  Lemma bf_bool_type_eq (e : expr typ func) t b tus tvs de
    (H1 : baseS e = Some (pBool b)) (H2 : exprD' tus tvs t e = Some de) :
    t = tyBool.
  Proof.
   destruct e; simpl in *; try congruence.
   autorewrite with exprD_rw in H2; simpl in H2; forward; inv_all; subst.
   apply (bf_bool_func_type_eq _ _ H1 H).
  Qed.

  Lemma bf_string_func_type_eq (f : func) s t df
    (H1 : baseS f = Some (pString s)) (H2 : funcAs f t = Some df) :
    t = tyString.
  Proof.
    rewrite (bf_funcAsOk _ H1) in H2.
    unfold funcAs in H2; simpl in *.
    forward.
  Qed.

  Lemma bf_string_type_eq (e : expr typ func) t s tus tvs de
    (H1 : baseS e = Some (pString s)) (H2 : exprD' tus tvs t e = Some de) :
    t = tyString.
  Proof.
   destruct e; simpl in *; try congruence.
   autorewrite with exprD_rw in H2; simpl in H2; forward; inv_all; subst.
   apply (bf_string_func_type_eq _ _ H1 H).
  Qed.

  Lemma bf_eq_func_type_eq (f : func) t u df
    (H1 : baseS f = Some (pEq t)) (H2 : funcAs f u = Some df) :
    u = tyArr t (tyArr t tyProp).
  Proof.
    rewrite (bf_funcAsOk _ H1) in H2.
    unfold funcAs in H2; simpl in *.
    forward.
    rewrite <- r; reflexivity.
  Qed.

  Lemma bf_eq_type_eq tus tvs (e : expr typ func) t u de
    (H1 : baseS e = Some (pEq t)) (H2 : exprD' tus tvs u e = Some de) :
    u = tyArr t (tyArr t tyProp).
  Proof.
   destruct e; simpl in *; try congruence.
   autorewrite with exprD_rw in H2; simpl in H2; forward; inv_all; subst.
   apply (bf_eq_func_type_eq _ _ H1 H).
  Qed.

  Lemma bf_pair_func_type_eq (f : func) t u v df
    (H1 : baseS f = Some (pPair t u)) (H2 : funcAs f v = Some df) :
    v = tyArr t (tyArr u (tyProd t u)).
  Proof.
    rewrite (bf_funcAsOk _ H1) in H2.
    unfold funcAs in H2; simpl in *.
    forward.
    rewrite <- r; reflexivity.
  Qed.

  Lemma bf_pair_type_eq tus tvs (e : expr typ func) t u v df
    (H1 : baseS e = Some (pPair t u)) (H2 : exprD' tus tvs v e = Some df) :
    v = tyArr t (tyArr u (tyProd t u)).
  Proof.
   destruct e; simpl in *; try congruence.
   autorewrite with exprD_rw in H2; simpl in H2; forward; inv_all; subst.
   apply (bf_pair_func_type_eq _ _ H1 H).
  Qed.

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

  Let tyProp : typ := @typ0 _ _ _ _.
  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.

  Lemma bf_nat_func_eq (n : nat) (f : func) (fD : typD tyNat)
    (Ho : baseS f = Some (pNat n))
    (Hf : funcAs f tyNat = Some fD) :
    fD = trmR n btNat.
  Proof.
   rewrite (bf_funcAsOk _ Ho) in Hf.
   unfold funcAs in Hf; simpl in *.
   rewrite type_cast_refl in Hf; [|apply HROk].
   unfold Rcast, Relim_refl in Hf.
   inversion Hf. reflexivity.
  Qed.

  Lemma bf_nat_eq (n : nat) (e : expr typ func) tus tvs
    (eD : ExprI.exprT tus tvs (typD tyNat))
    (Ho : baseS e = Some (pNat n))
    (Hf : exprD' tus tvs tyNat e = Some eD) :
    eD = fun us vs => trmR n btNat.
  Proof.
   destruct e; simpl in *; try congruence.
   autorewrite with exprD_rw in Hf; simpl in Hf; forward; inv_all; subst.
   rewrite (bf_nat_func_eq _ Ho H); reflexivity.
  Qed.

  Lemma bf_bool_func_eq (b : bool) (f : func) (fD : typD tyBool)
    (Ho : baseS f = Some (pBool b))
    (Hf : funcAs f tyBool = Some fD) :
    fD = trmR b btBool.
  Proof.
   rewrite (bf_funcAsOk _ Ho) in Hf.
   unfold funcAs in Hf; simpl in *.
   rewrite type_cast_refl in Hf; [|apply HROk].
   unfold Rcast, Relim_refl in Hf.
   inversion Hf. reflexivity.
  Qed.

  Lemma bf_bool_eq (b : bool) (e : expr typ func) tus tvs
    (eD : ExprI.exprT tus tvs (typD tyBool))
    (Ho : baseS e = Some (pBool b))
    (Hf : exprD' tus tvs tyBool e = Some eD) :
    eD = fun us vs => trmR b btBool.
  Proof.
   destruct e; simpl in *; try congruence.
   autorewrite with exprD_rw in Hf; simpl in Hf; forward; inv_all; subst.
   rewrite (bf_bool_func_eq _ Ho H); reflexivity.
  Qed.

  Lemma bf_string_func_eq (s : string) (f : func) (fD : typD tyString)
    (Ho : baseS f = Some (pString s))
    (Hf : funcAs f tyString = Some fD) :
    fD = trmR s btString.
  Proof.
   rewrite (bf_funcAsOk _ Ho) in Hf.
   unfold funcAs in Hf; simpl in *.
   rewrite type_cast_refl in Hf; [|apply HROk].
   unfold Rcast, Relim_refl in Hf.
   inversion Hf. reflexivity.
  Qed.

  Lemma bf_string_eq (s : string) (e : expr typ func) tus tvs
    (eD : ExprI.exprT tus tvs (typD tyString))
    (Ho : baseS e = Some (pString s))
    (Hf : exprD' tus tvs tyString e = Some eD) :
    eD = fun us vs => trmR s btString.
  Proof.
   destruct e; simpl in *; try congruence.
   autorewrite with exprD_rw in Hf; simpl in Hf; forward; inv_all; subst.
   rewrite (bf_string_func_eq _ Ho H); reflexivity.
  Qed.

  Lemma bf_eq_func_eq (t : typ) (f : func) (fD : typD (tyArr t (tyArr t tyProp)))
    (Ho : baseS f = Some (pEq t))
    (Hf : funcAs f (tyArr t (tyArr t tyProp)) = Some fD) :
    fD = eqD t.
  Proof.
   rewrite (bf_funcAsOk _ Ho) in Hf.
   unfold funcAs in Hf; simpl in *.
   rewrite type_cast_refl in Hf; [|apply HROk].
   unfold Rcast, Relim_refl in Hf.
   inversion Hf. reflexivity.
  Qed.

  Lemma bf_eq_eq tus tvs (t : typ) (e : expr typ func) 
    (eD : ExprI.exprT tus tvs (typD (tyArr t (tyArr t tyProp))))
    (Ho : baseS e = Some (pEq t))
    (Hf : exprD' tus tvs (tyArr t (tyArr t tyProp)) e = Some eD) :
    eD = (fun us vs => eqD t).
  Proof.
   destruct e; simpl in *; try congruence.
   autorewrite with exprD_rw in Hf; simpl in Hf; forward; inv_all; subst.
   rewrite (bf_eq_func_eq _ Ho H); reflexivity.
  Qed.
 
  Lemma bf_pair_func_eq (t u : typ) (f : func) (fD : typD (tyArr t (tyArr u (tyProd t u))))
    (Ho : baseS f = Some (pPair t u))
    (Hf : funcAs f (tyArr t (tyArr u (tyProd t u))) = Some fD) :
    fD = pairD t u.
  Proof.
   rewrite (bf_funcAsOk _ Ho) in Hf.
   unfold funcAs in Hf; simpl in *.
   rewrite type_cast_refl in Hf; [|apply HROk].
   unfold Rcast, Relim_refl in Hf.
   inversion Hf. reflexivity.
  Qed.

  Lemma bf_pair_eq tus tvs (t u : typ) (e : expr typ func) 
    (eD : ExprI.exprT tus tvs (typD (tyArr t (tyArr u (tyProd t u)))))
    (Ho : baseS e = Some (pPair t u))
    (Hf : exprD' tus tvs (tyArr t (tyArr u (tyProd t u))) e = Some eD) :
    eD = (fun us vs => pairD t u).
  Proof.
   destruct e; simpl in *; try congruence.
   autorewrite with exprD_rw in Hf; simpl in Hf; forward; inv_all; subst.
   rewrite (bf_pair_func_eq _ Ho H); reflexivity.
  Qed.
 
  Lemma mkNat_sound (n : nat) (tus tvs : tenv typ) :
    exprD' tus tvs tyNat (mkNat n) = Some (fun _ _ => trmR n btNat).
  Proof.
    unfold mkNat; simpl.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    pose proof (bf_fNatOk n) as H1.
    pose proof (bf_funcAsOk _ H1) as H2. rewrite H2.
    unfold funcAs; simpl; rewrite type_cast_refl; [|apply _].
    reflexivity.
  Qed.
  
  Lemma mkBool_sound (b : bool) (tus tvs : tenv typ) :
    exprD' tus tvs tyBool (mkBool b) = Some (fun _ _ => trmR b btBool).
  Proof.
    unfold mkBool; simpl.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    pose proof (bf_fBoolOk b) as H1.
    pose proof (bf_funcAsOk _ H1) as H2. rewrite H2.
    unfold funcAs; simpl; rewrite type_cast_refl; [|apply _].
    reflexivity.
  Qed.
  
  Lemma mkString_sound (s : string) (tus tvs : tenv typ) :
    exprD' tus tvs tyString (mkString s) = Some (fun _ _ => trmR s btString).
  Proof.
    unfold mkString; simpl.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    pose proof (bf_fStringOk s) as H1.
    pose proof (bf_funcAsOk _ H1) as H2. rewrite H2.
    unfold funcAs; simpl; rewrite type_cast_refl; [|apply _].
    reflexivity.
  Qed.
  
  Lemma mkEq_sound (t : typ) (tus tvs : tenv typ) a b
    (aD : ExprI.exprT tus tvs (typD t)) 
    (bD : ExprI.exprT tus tvs (typD t)) 
    (Ha : exprD' tus tvs t a = Some aD) 
    (Hb : exprD' tus tvs t b = Some bD)  :
    exprD' tus tvs tyProp (mkEq t a b) = Some (exprT_App (exprT_App (fun _ _ => eqD t) aD) bD).
  Proof.
    unfold mkEq; simpl.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ b _ Hb).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ a _ Ha).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    pose proof (bf_fEqOk t) as Ho.
    pose proof (bf_funcAsOk _ Ho) as H1.
    rewrite H1. unfold funcAs; simpl.
    rewrite type_cast_refl; [reflexivity | apply _].
  Qed.

  Lemma mkPair_sound (t u : typ) (tus tvs : tenv typ) a b
    (aD : ExprI.exprT tus tvs (typD t)) 
    (bD : ExprI.exprT tus tvs (typD u)) 
    (Ha : exprD' tus tvs t a = Some aD) 
    (Hb : exprD' tus tvs u b = Some bD)  :
    exprD' tus tvs (tyProd t u) (mkPair t u a b) = Some (exprT_App (exprT_App (fun _ _ => pairD t u) aD) bD).
  Proof.
    unfold mkPair; simpl.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ b _ Hb).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ a _ Ha).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    pose proof (bf_fPairOk t u) as Ho.
    pose proof (bf_funcAsOk _ Ho) as H1.
    rewrite H1. unfold funcAs; simpl.
    rewrite type_cast_refl; [reflexivity | apply _].
  Qed.

End MakeBaseFuncSound.
