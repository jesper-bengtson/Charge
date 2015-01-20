Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Data.Bool.
Require Import ExtLib.Data.String.
Require Import ExtLib.Tactics.
Require Import ExtLib.Tactics.Consider.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.syms.SymEnv.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.SymI.
Require Import MirrorCore.syms.SymSum.

Require Import Charge.Logics.ILogic.

Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Inductive ilfunc typ :=
  | ilf_entails (logic : typ)
  | ilf_true (logic : typ)
  | ilf_false (logic : typ)
  | ilf_and (logic : typ)
  | ilf_or (logic : typ)
  | ilf_impl (logic : typ)
  | ilf_exists (arg logic : typ)
  | ilf_forall (arg logic : typ).
  
Definition ilfunc_logic typ (x : ilfunc typ) : typ :=
  match x with
    | ilf_entails t => t
    | ilf_true t => t
    | ilf_false t => t
    | ilf_and t => t
    | ilf_or t => t
    | ilf_impl t => t
    | ilf_exists _ t => t
    | ilf_forall _ t => t
  end.

Class ILogicFunc (typ func : Type) := {
  fEntails  : typ -> func;
  fTrue : typ -> func;
  fFalse : typ -> func;
  fAnd : typ -> func;
  fOr : typ -> func;
  fImpl : typ -> func;
  fExists : typ -> typ -> func;
  fForall : typ -> typ -> func;
  ilogicS : func -> option (ilfunc typ)
}.
    
Section ILogicFuncSum.
	Context {typ func : Type} {H : ILogicFunc typ func}.

	Global Instance ILogicFuncSumL (A : Type) : 
		ILogicFunc typ (func + A) := {
		  fEntails l := inl (fEntails l);
		  fTrue l := inl (fTrue l);
		  fFalse l := inl (fFalse l);
		  fAnd l := inl (fAnd l);
		  fOr l := inl (fOr l);
		  fImpl l := inl (fImpl l);
		  fExists t l := inl (fExists t l);
		  fForall t l := inl (fForall t l);
		  ilogicS f := match f with
		  				 | inl a => ilogicS a
		  		   	 	 | _     => None
		  			   end 
        }.

	Global Instance ILogicFuncSumR (A : Type) : 
		ILogicFunc typ (A + func) := {
		  fEntails l := inr (fEntails l);
		  fTrue l := inr (fTrue l);
		  fFalse l := inr (fFalse l);
		  fAnd l := inr (fAnd l);
		  fOr l := inr (fOr l);
		  fImpl l := inr (fImpl l);
		  fExists t l := inr (fExists t l);
		  fForall t l := inr (fForall t l);
		  ilogicS f := match f with
		  				 | inr a => ilogicS a
		  		   	 	 | _     => None
		  			   end 
        }.
        
	Global Instance ILogicFuncExpr : 
		ILogicFunc typ (expr typ func) := {
		  fEntails l := Inj (fEntails l);
		  fTrue l := Inj (fTrue l);
		  fFalse l := Inj (fFalse l);
		  fAnd l := Inj (fAnd l);
		  fOr l := Inj (fOr l);
		  fImpl l := Inj (fImpl l);
		  fExists t l := Inj (fExists t l);
		  fForall t l := Inj (fForall t l);
		  ilogicS f := match f with
		  				 | Inj a => ilogicS a
		  		   	 	 | _     => None
		  			   end 
        }.

End ILogicFuncSum.

Section ILogicFuncInst.

	Context {typ func : Type}.
	Context {HR : RType typ} {Heq : RelDec (@eq typ)} {HC : RelDec_Correct Heq}.

    Variable Typ2_tyArr : Typ2 _ Fun.
    Variable Typ0_tyProp : Typ0 _ Prop.

    Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.
    Let tyProp : typ := @typ0 _ _ _ _.

	Global Instance ILogicFuncInst : ILogicFunc typ (ilfunc typ) := {
	  fEntails := ilf_entails;
	  fTrue := ilf_true;
	  fFalse := ilf_false;
	  fAnd := ilf_and;
	  fOr := ilf_or;
	  fImpl := ilf_impl;
	  fExists := ilf_exists;
	  fForall := ilf_forall;
	  ilogicS f := Some f
	}.

  Definition logic_ops := forall (t : typ),
    option (ILogicOps (typD t)).
  Definition logic_opsOk (l : logic_ops) : Prop :=
    forall g, match l g return Prop with
                | Some T => @ILogic _ T
                | None => True
              end.

  Variable gs : logic_ops.
  
  Definition typeof_ilfunc (f : ilfunc typ) : option typ :=
    match f with
      | ilf_true t
      | ilf_false t => match gs t with
  				   	     | Some _ => Some t
				  	     | None => None
  					   end
      | ilf_entails t => match gs t with
					  	   | Some _ => Some (tyArr t (tyArr t tyProp))
					  	   | None => None
					   	 end
      | ilf_and t
      | ilf_or t
      | ilf_impl t => match gs t with
				  	    | Some _ => Some (tyArr t (tyArr t t))
				  	    | None => None
				  	  end
      | ilf_forall a t
      | ilf_exists a t => match gs t with
					  	    | Some _ => Some (tyArr (tyArr a t) t)
					  	    | None => None
					  	  end
  	end.

  Global Instance RelDec_ilfunc : RelDec (@eq (ilfunc typ)) :=
  { rel_dec := fun a b =>
	         match a, b with
		   | ilf_entails t, ilf_entails t'
		   | ilf_true t, ilf_true t'
		   | ilf_false t, ilf_false t'
		   | ilf_and t, ilf_and t'
		   | ilf_or t, ilf_or t'
		   | ilf_impl t, ilf_impl t' => t ?[eq] t'
		   | ilf_forall a t, ilf_forall a' t'
		   | ilf_exists a t, ilf_exists a' t' => (a ?[eq] a' && t ?[eq] t')%bool
		   | _, _ => false
	         end
  }.

  Global Instance RelDec_Correct_ilfunc : RelDec_Correct RelDec_ilfunc.
  Proof.
    constructor.
    destruct x; destruct y; simpl;
    try solve [ try rewrite Bool.andb_true_iff ;
                repeat rewrite rel_dec_correct; intuition congruence ].
  Qed.

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

  Definition typ2_cast_quant (a b c : typ)
  : ((typD a -> typD b) -> typD c) -> typD (tyArr (tyArr a b) c) :=
    fun f =>
      match eq_sym (typ2_cast (tyArr a b) c) in _ = t
            return t with
        | eq_refl => match eq_sym (typ2_cast a b) in _ = t
                           return t -> _ with
                       | eq_refl => f
                     end
      end.
 
 Definition funcD (f : ilfunc typ) : match typeof_ilfunc f with
							       | Some t => typD t
							       | None => unit
							      end :=
    match f as f
          return match typeof_ilfunc f with
		   | Some t => typD t
		   | None => unit
		 end
    with
      | ilf_true t => match gs t as x return (match match x with
											          | Some _ => Some t
											          | None => None
											        end with
				                                 | Some t0 => typD t0
											 	 | None => unit
											       end) with
					    | Some t => @ltrue _ t
					    | None => tt
				      end
      | ilf_false t =>
        match gs t as x
              return (match match x with
			      | Some _ => Some t
			      | None => None
			    end with
			| Some t0 => typD t0
			| None => unit
		      end) with
	  | Some t => @lfalse _ t
	  | None => tt
        end
      | ilf_entails t =>
        match gs t as x
              return (match match x with
			      | Some _ => Some (tyArr t (tyArr t tyProp))
			      | None => None
			    end with
			| Some t0 => typD t0
			| None => unit
		      end) with
	  | Some C =>
            match eq_sym (typ2_cast t (tyArr t tyProp)) in _ = t
                  return t with
              | eq_refl =>
                match eq_sym (typ2_cast t tyProp) in _ = t
                      return _ -> t with
                  | eq_refl =>
                    match eq_sym (typ0_cast (F := Prop)) in _ = t
                          return _ -> _ -> t
                    with
                      | eq_refl => @lentails _ _
                    end
                end
            end
	  | None => tt
        end
      | ilf_and t =>
        match gs t as x
              return (match match x with
			      | Some _ => Some (tyArr t (tyArr t t))
			      | None => None
			    end with
			| Some t0 => typD t0
			| None => unit
		      end) with
	  | Some t => typ2_cast_bin _ _ _ (@land _ _)
	  | None => tt
        end
      | ilf_impl t =>
        match gs t as x
              return (match match x with
			      | Some _ => Some (tyArr t (tyArr t t))
			      | None => None
			    end with
			| Some t0 => typD t0
			| None => unit
		      end) with
	  | Some t => typ2_cast_bin _ _ _ (@limpl _ _)
	  | None => tt
        end
      | ilf_or t =>
        match gs t as x
              return (match match x with
			      | Some _ => Some (tyArr t (tyArr t t))
			      | None => None
			    end with
			| Some t0 => typD t0
			| None => unit
		      end) with
	  | Some t => typ2_cast_bin _ _ _ (@lor _ _)
	  | None => tt
        end
      | ilf_exists a t =>
        match gs t as x return (match match x with
					| Some _ => Some (tyArr (tyArr a t) t)
					| None => None
				      end with
				  | Some t0 => typD t0
				  | None => unit
				end) with
	  | Some t0 => typ2_cast_quant _ _ _ (@lexists _ _ _)
	  | None => tt
        end
      | ilf_forall a t =>
        match gs t as x return (match match x with
					| Some _ => Some (tyArr (tyArr a t) t)
					| None => None
				      end with
				  | Some t0 => typD t0
				  | None => unit
				end) with
	  | Some t0 => typ2_cast_quant _ _ _ (@lforall _ _ _)
	  | None => tt
        end
    end.

  Global Instance RSym_ilfunc : SymI.RSym (ilfunc typ) :=
  { typeof_sym := typeof_ilfunc
  ; sym_eqb := fun a b => Some (rel_dec a b)
  ; symD := funcD
  }.

  Global Instance RSymOk_ilfunc : SymI.RSymOk RSym_ilfunc.
  Proof.
    constructor.
    intros. unfold sym_eqb; simpl.
    consider (a ?[ eq ] b); auto.
  Qed.

End ILogicFuncInst.

Section MakeILogic.
	Context {typ func : Type} {H : ILogicFunc typ func}.

	Definition mkEntails (t : typ) (P Q : expr typ func) := App (App (fEntails t) P) Q.
	Definition mkTrue t : expr typ func := Inj (fTrue t).
	Definition mkFalse t : expr typ func := Inj (fFalse t).
	Definition mkAnd (t : typ) (P Q : expr typ func) := App (App (fAnd t) P) Q.
	Definition mkOr (t : typ) (P Q : expr typ func) := App (App (fOr t) P) Q.
	Definition mkImpl (t : typ) (P Q : expr typ func) := App (App (fImpl t) P) Q.
	Definition mkExists (t l : typ) (f : expr typ func) := App (fExists t l) (Abs t f).
	Definition mkForall (t l : typ) (f : expr typ func) := App (fForall t l) (Abs t f).

End MakeILogic.

Implicit Arguments RSym_ilfunc [[typ] [HR] [Heq] [Typ2_tyArr] [Typ0_tyProp]].

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

Section ILogicFuncOk.
  Context {typ func : Type} {HO: ILogicFunc typ func}.
  Context {RType_typ : RType typ} {RSym_func : RSym func}.
  Context {RelDec_eq : RelDec (@eq typ)}.

  Context {Typ2_tyArr : Typ2 _ Fun}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.
  
  Variable gs : logic_ops.

  Class ILogicFuncOk := {
    ilf_funcAsOk (f : func) e : ilogicS f = Some e -> 
      forall t, funcAs f t = funcAs (RSym_func := RSym_ilfunc gs) e t;
    ilf_fEntailsOk t : ilogicS (fEntails t) = Some (ilf_entails t);
    ilf_fTrueOk t : ilogicS (fTrue t) = Some (ilf_true t);
    ilf_fFalseOk t : ilogicS (fFalse t) = Some (ilf_false t);
    ilf_fAndOk t : ilogicS (fAnd t) = Some (ilf_and t);
    ilf_fOrOk t : ilogicS (fOr t) = Some (ilf_or t);
    ilf_fImplOk t : ilogicS (fImpl t) = Some (ilf_impl t);
    ilf_fExistsOk t l : ilogicS (fExists t l) = Some (ilf_exists t l);
    ilf_fForallOk t l : ilogicS (fForall t l) = Some (ilf_forall t l)
  }.

End ILogicFuncOk.

Implicit Arguments ILogicFuncOk [[HO] [RType_typ] [RSym_func] [RelDec_eq] [Typ2_tyArr] [Typ0_Prop]].

Section ILogicFuncBaseOk.
  Context {typ func : Type} {HO: ILogicFunc typ func}.
  Context {RType_typ : RType typ} {RSym_func : RSym func}.
  Context {RelDec_eq : RelDec (@eq typ)}.

  Context {Typ2_tyArr : Typ2 _ Fun}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.
  
  Variable gs : logic_ops.

  Global Program Instance ILogicFuncBaseOk : ILogicFuncOk (RSym_func := RSym_ilfunc gs) typ (ilfunc typ) gs := {
    ilf_funcAsOk := fun _ _ _ _ => eq_refl;
    ilf_fEntailsOk t := eq_refl;
    ilf_fTrueOk t := eq_refl;
    ilf_fFalseOk t := eq_refl;
    ilf_fAndOk t := eq_refl;
    ilf_fOrOk t := eq_refl;
    ilf_fImplOk t := eq_refl;
    ilf_fExistsOk t l := eq_refl;
    ilf_fForallOk t l := eq_refl
  }.

End ILogicFuncBaseOk.

Section ILogicFuncExprOk.
  Context {typ func : Type} `{HOK : ILogicFuncOk typ func}.
  Context {HROk : RTypeOk}.
  Context {A : Type} {RSymA : RSym A}.

  Lemma ILogicFunc_typeOk (f : func) (e : ilfunc typ) (H : ilogicS f = Some e) :
    typeof_sym f = typeof_ilfunc _ _ gs e.
  Proof.
    destruct HOK as [H1 H2 _ _ _ _ _ _ _].
    specialize (H1 _ _ H).
    destruct e; simpl in *;
    remember (gs logic) as o;
    destruct o; try
    match goal with 
      | |- typeof_sym ?f = Some ?t => 
	 	specialize (H1 t);
	 	simpl in H1;
	 	unfold funcAs in H1; simpl in H1; rewrite <- Heqo, type_cast_refl in H1; [|apply _];
	 	generalize dependent (symD f);
	 	destruct (typeof_sym f); simpl; intros; [forward|]; inversion H1
 	end;
 	unfold funcAs in H1; simpl in H1; rewrite <- Heqo in H1;
 	generalize dependent (symD f);
 	remember (typeof_sym f);
 	(destruct o; intros; [|reflexivity]);
 	specialize (H1 t); (rewrite type_cast_refl in H1; [|apply _]);
 	inversion H1. 
  Qed.
  
  Lemma ilogicS_is_ilogic (f : func) (e : ilfunc typ) t df
  	(H1 : ilogicS f = Some e) (H2 : funcAs f t = Some df) :
    exists IL, gs (ilfunc_logic e) = Some IL.
  Proof.
    pose proof (ilf_funcAsOk _ H1) as H; 
    rewrite H in H2; clear H;
    destruct e; simpl in *;
    unfold funcAs in H2; simpl in H2;
    (destruct (gs logic); [eexists; reflexivity | congruence]).
  Qed.
  
  Lemma ilf_true_type_eq (f : func) t u df
    (H1 : ilogicS f = Some (ilf_true t)) (H2 : funcAs f u = Some df) :
    t = u.
  Proof.
    rewrite (ilf_funcAsOk _ H1) in H2.
    unfold funcAs in H2; simpl in *.
    forward.
  Qed.

  Lemma ilf_false_type_eq (f : func) t u df
    (H1 : ilogicS f = Some (ilf_false t)) (H2 : funcAs f u = Some df) :
    t = u.
  Proof.
    rewrite (ilf_funcAsOk _ H1) in H2.
    unfold funcAs in H2; simpl in *.
    forward.
  Qed.

  Existing Instance RSym_sum.

  Global Program Instance ILogicFuncOkSumR : ILogicFuncOk typ ((A + func)%type) gs := {
    ilf_funcAsOk := 
      fun a f H t => 
        match a with
          | inl b => _
          | inr b => _
        end;
    ilf_fEntailsOk t := ilf_fEntailsOk (func := func) t;
    ilf_fTrueOk t := ilf_fTrueOk (func := func) t;
    ilf_fFalseOk t := ilf_fFalseOk (func := func) t;
    ilf_fAndOk t := ilf_fAndOk (func := func) t;
    ilf_fOrOk t := ilf_fOrOk (func := func) t;
    ilf_fImplOk t := ilf_fImplOk (func := func) t;
    ilf_fExistsOk t l := ilf_fExistsOk (func := func) t l;
    ilf_fForallOk t l := ilf_fForallOk (func := func) t l       
  }.
  Next Obligation.
    apply (ilf_funcAsOk (func := func)).
    apply H.
  Qed.

  Global Program Instance ILogicFuncOkSumL : ILogicFuncOk typ ((func + A)%type) gs := {
    ilf_funcAsOk := 
      fun a f H t => 
        match a with
          | inl b => _
          | inr b => _
        end;
    ilf_fEntailsOk t := ilf_fEntailsOk (func := func) t;
    ilf_fTrueOk t := ilf_fTrueOk (func := func) t;
    ilf_fFalseOk t := ilf_fFalseOk (func := func) t;
    ilf_fAndOk t := ilf_fAndOk (func := func) t;
    ilf_fOrOk t := ilf_fOrOk (func := func) t;
    ilf_fImplOk t := ilf_fImplOk (func := func) t;
    ilf_fExistsOk t l := ilf_fExistsOk (func := func) t l;
    ilf_fForallOk t l := ilf_fForallOk (func := func) t l       
  }.
  Next Obligation.
    apply (ilf_funcAsOk (func := func)).
    apply H.
  Qed.

End ILogicFuncExprOk.

Require Import ExtLib.Tactics.

Section MakeILogicSound.
  Context {typ func : Type} `{HOK : ILogicFuncOk typ func}.
  Context {HROk : RTypeOk} {Typ2_tyArrOk : Typ2Ok Typ2_tyArr}
          {RSym_funcOk : RSymOk RSym_func0}.

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.

  Lemma mkTrue_sound (t : typ) (tus tvs : tenv typ) (f : func)
    (df : typD t)
    (Ho : ilogicS f = Some (ilf_true t))
    (Hf : funcAs f t = Some df) :
    exprD' tus tvs t (mkTrue t) = Some (fun _ _ => df).
  Proof.
    unfold mkTrue; simpl.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    pose proof (ilf_funcAsOk _ Ho) as H; rewrite H in Hf.
    pose proof (ilf_fTrueOk t) as H1.
    pose proof (ilf_funcAsOk _ H1) as H2. rewrite <- H2 in Hf.
    pose proof (ILogicFunc_typeOk _ H1) as H3. simpl in H3.
    destruct (ilogicS_is_ilogic _ _ H1 Hf) as [x H4]; simpl in H4; rewrite H4 in H3.
    rewrite (funcAs_Some _ H3).
    rewrite (funcAs_Some _ H3) in Hf.
    inv_all; subst. reflexivity.
  Qed.
    
  Lemma mkFalse_sound (t : typ) (tus tvs : tenv typ) (f : func)
    (df : typD t)
    (Ho : ilogicS f = Some (ilf_false t))
    (Hf : funcAs f t = Some df) :
    exprD' tus tvs t (mkFalse t) = Some (fun _ _ => df).
  Proof.
    unfold mkFalse; simpl.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    pose proof (ilf_funcAsOk _ Ho) as H; rewrite H in Hf.
    pose proof (ilf_fFalseOk t) as H1.
    pose proof (ilf_funcAsOk _ H1) as H2. rewrite <- H2 in Hf.
    pose proof (ILogicFunc_typeOk _ H1) as H3. simpl in H3.
    destruct (ilogicS_is_ilogic _ _ H1 Hf) as [x H4]; simpl in H4; rewrite H4 in H3.
    rewrite (funcAs_Some _ H3).
    rewrite (funcAs_Some _ H3) in Hf.
    inv_all; subst. reflexivity.
  Qed.
    
  Lemma mkAnd_sound (t : typ) (tus tvs : tenv typ) (f : func) p q
    (df : typD (tyArr t (tyArr t t))) (dp dq : ExprI.exprT tus tvs (typD t))
    (Ho : ilogicS f = Some (ilf_and t))
    (Hf : funcAs f (tyArr t (tyArr t t)) = Some df)
    (Hp : exprD' tus tvs t p = Some dp)
    (Hq : exprD' tus tvs t q = Some dq) :
    exprD' tus tvs t (mkAnd t p q) = Some (exprT_App (exprT_App (fun _ _ => df) dp) dq).
  Proof.
    unfold mkAnd; simpl.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ q _ Hq).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ p _ Hp).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    pose proof (ilf_funcAsOk _ Ho) as Hfunc; rewrite Hfunc in Hf.
    pose proof (ilf_fAndOk t) as HfuncOk.
    pose proof (ilf_funcAsOk _ HfuncOk) as Heq. rewrite <- Heq in Hf.
    pose proof (ILogicFunc_typeOk _ HfuncOk) as Htype. simpl in Htype.
    destruct (ilogicS_is_ilogic _ _ HfuncOk Hf) as [x Hgs]; simpl in Hgs; rewrite Hgs in Htype.
    rewrite (funcAs_Some _ Htype).
    unfold tyArr in Hf.
    rewrite (funcAs_Some _ Htype) in Hf.
    inv_all; subst. reflexivity.
  Qed.
    
  Lemma mkOr_sound (t : typ) (tus tvs : tenv typ) (f : func) p q
    (df : typD (tyArr t (tyArr t t))) (dp dq : ExprI.exprT tus tvs (typD t))
    (Ho : ilogicS f = Some (ilf_or t))
    (Hf : funcAs f (tyArr t (tyArr t t)) = Some df)
    (Hp : exprD' tus tvs t p = Some dp)
    (Hq : exprD' tus tvs t q = Some dq) :
    exprD' tus tvs t (mkOr t p q) = Some (exprT_App (exprT_App (fun _ _ => df) dp) dq).
  Proof.
    unfold mkOr; simpl.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ q _ Hq).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ p _ Hp).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    pose proof (ilf_funcAsOk _ Ho) as Hfunc; rewrite Hfunc in Hf.
    pose proof (ilf_fOrOk t) as HfuncOk.
    pose proof (ilf_funcAsOk _ HfuncOk) as Heq. rewrite <- Heq in Hf.
    pose proof (ILogicFunc_typeOk _ HfuncOk) as Htype. simpl in Htype.
    destruct (ilogicS_is_ilogic _ _ HfuncOk Hf) as [x Hgs]; simpl in Hgs; rewrite Hgs in Htype.
    rewrite (funcAs_Some _ Htype).
    unfold tyArr in Hf.
    rewrite (funcAs_Some _ Htype) in Hf.
    inv_all; subst. reflexivity.
  Qed.
    
  Lemma mkImpl_sound (t : typ) (tus tvs : tenv typ) (f : func) p q
    (df : typD (tyArr t (tyArr t t))) (dp dq : ExprI.exprT tus tvs (typD t))
    (Ho : ilogicS f = Some (ilf_impl t))
    (Hf : funcAs f (tyArr t (tyArr t t)) = Some df)
    (Hp : exprD' tus tvs t p = Some dp)
    (Hq : exprD' tus tvs t q = Some dq) :
    exprD' tus tvs t (mkImpl t p q) = Some (exprT_App (exprT_App (fun _ _ => df) dp) dq).
  Proof.
    unfold mkImpl; simpl.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ q _ Hq).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ p _ Hp).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    pose proof (ilf_funcAsOk _ Ho) as Hfunc; rewrite Hfunc in Hf.
    pose proof (ilf_fImplOk t) as HfuncOk.
    pose proof (ilf_funcAsOk _ HfuncOk) as Heq. rewrite <- Heq in Hf.
    pose proof (ILogicFunc_typeOk _ HfuncOk) as Htype. simpl in Htype.
    destruct (ilogicS_is_ilogic _ _ HfuncOk Hf) as [x Hgs]; simpl in Hgs; rewrite Hgs in Htype.
    rewrite (funcAs_Some _ Htype).
    unfold tyArr in Hf.
    rewrite (funcAs_Some _ Htype) in Hf.
    inv_all; subst. reflexivity.
  Qed.
(*
  Lemma mkExists_sound (t a : typ) (tus tvs : tenv typ) (f : func) g
    (df : typD (tyArr (tyArr a t) t)) (dg : ExprI.exprT tus (a::tvs) (typD t))
    (Ho : ilogicS f = Some (ilf_exists a t))
    (Hf : funcAs f (tyArr (tyArr a t) t) = Some df)
    (Hg : exprD' tus (a::tvs) t g = Some dg) :
    exprD' tus tvs t (mkExists a t g) = Some (exprT_App (fun _ _ => df) (exprT_Abs dg)).
  Proof.
    unfold mkExists; simpl.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ g _ Hg).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    pose proof (ilf_funcAsOk _ Ho) as Hfunc; rewrite Hfunc in Hf.
    pose proof (ilf_fExistsOk a t) as HfuncOk.
    pose proof (ilf_funcAsOk _ HfuncOk) as Heq. rewrite <- Heq in Hf.
    pose proof (ILogicFunc_typeOk _ HfuncOk) as Htype. simpl in Htype.
    destruct (ilogicS_is_ilogic _ _ HfuncOk Hf) as [x Hgs]; simpl in Hgs; rewrite Hgs in Htype.
    unfold tyArr in Hf. rewrite Hf.
	(* Stuck here *)
  Qed.
    *)
    
End MakeILogicSound.