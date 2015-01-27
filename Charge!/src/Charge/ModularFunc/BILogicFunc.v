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
Require Import Charge.Logics.BILogic.
Require Import Charge.ModularFunc.Denotation.
Require Import Charge.ModularFunc.ILogicFunc.

Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Inductive bilfunc typ :=
  | bilf_emp (logic : typ)
  | bilf_star (logic : typ)
  | bilf_wand (logic : typ).

Definition bilfunc_logic typ (x : bilfunc typ) : typ :=
  match x with
    | bilf_emp t => t
    | bilf_star t => t
    | bilf_wand t => t
  end.
 
Class BILogicFunc (typ func : Type) := {
  fEmp : typ -> func;
  fStar : typ -> func;
  fWand : typ -> func;
  bilogicS : func -> option (bilfunc typ)
}.
    
Section BILogicFuncSum.
	Context {typ func : Type} {H : BILogicFunc typ func}.

	Global Instance BILogicFuncSumL (A : Type) : 
		BILogicFunc typ (func + A) := {
		  fEmp l := inl (fEmp l);
		  fStar l := inl (fStar l);
		  fWand l := inl (fWand l);
		  bilogicS f := match f with
		  				  | inl a => bilogicS a
		  				  | _     => None
		  				end 
       }.

	Global Instance BILogicFuncSumR (A : Type) : 
		BILogicFunc typ (A + func) := {
		  fEmp l := inr (fEmp l);
		  fStar l := inr (fStar l);
		  fWand l := inr (fWand l);
		  bilogicS f := match f with
		  				  | inr a => bilogicS a
		  				  | _     => None
		  				end 
       }.

	Global Instance BILogicFuncExpr : 
		BILogicFunc typ (expr typ func) := {
		  fEmp l := Inj (fEmp l);
		  fStar l := Inj (fStar l);
		  fWand l := Inj (fWand l);
		  bilogicS f := match f with
		  				  | Inj a => bilogicS a
		  				  | _ => None
		  				end 
        }.

End BILogicFuncSum.

Section BILogicFuncInst.

	Context {typ func : Type}.
	Context {HR : RType typ} {Heq : RelDec (@eq typ)} {HC : RelDec_Correct Heq}.

    Variable Typ2_tyArr : Typ2 _ Fun.
    Variable Typ0_tyProp : Typ0 _ Prop.

    Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.
    Let tyProp : typ := @typ0 _ _ _ _.

	Global Instance BILogicFuncInst : BILogicFunc typ (bilfunc typ) := {
	  fEmp := bilf_emp;
	  fStar := bilf_star;
	  fWand := bilf_wand;
	  bilogicS f := Some f 
	}.
	
  Variable is : logic_ops.

  Definition bilogic_ops := forall (t : typ),
    option (BILOperators (typD t)).
  Definition bilogic_opsOk (l : bilogic_ops) : Prop :=
    forall g, match is g, l g return Prop with
                | Some T, Some U => @BILogic _ T U
                | _, _ => True
              end.

  Variable gs : bilogic_ops.
  
  Definition typeof_bilfunc (f : bilfunc typ) : option typ :=
    match f with
      | bilf_emp t => match gs t with
  				   	     | Some _ => Some t
				  	     | None => None
  					   end
      | bilf_star t
      | bilf_wand t => match gs t with
				  	     | Some _ => Some (tyArr t (tyArr t t))
				  	     | None => None
				  	  end
  	end.

  Global Instance RelDec_bilfunc : RelDec (@eq (bilfunc typ)) :=
  { rel_dec := fun a b =>
	         match a, b with
		   | bilf_emp t, bilf_emp t'
		   | bilf_star t, bilf_star t'
		   | bilf_wand t, bilf_wand t' => t ?[eq] t'
		   | _, _ => false
	         end
  }.

  Global Instance RelDec_Correct_bilfunc : RelDec_Correct RelDec_bilfunc.
  Proof.
    constructor.
    destruct x; destruct y; simpl;
    repeat rewrite rel_dec_correct; intuition congruence.
  Qed.

 Definition empD t BIL := @empSP (typD t) BIL.
 Definition starD t BIL := fun_to_typ2 (@sepSP (typD t) BIL).
 Definition wandD t BIL := fun_to_typ2 (@wandSP (typD t) BIL).
 
 Definition funcD (f : bilfunc typ) : match typeof_bilfunc f with
							       | Some t => typD t
							       | None => unit
							      end :=
    match f as f
          return match typeof_bilfunc f with
		   | Some t => typD t
		   | None => unit
		 end
    with
      | bilf_emp t =>
        match gs t as x
          return (match match x with
                          | Some _ => Some t
                          | None => None
                        end with
                    | Some t0 => typD t0
                    | None => unit
                  end) with
        | Some BIL => empD _ BIL
        | None => tt
        end
      | bilf_star t =>
        match gs t as x
              return (match match x with
			      | Some _ => Some (tyArr t (tyArr t t))
			      | None => None
			    end with
			| Some t0 => typD t0
			| None => unit
		      end) with
	  | Some t => starD _ t
	  | None => tt
        end
      | bilf_wand t =>
        match gs t as x
              return (match match x with
			      | Some _ => Some (tyArr t (tyArr t t))
			      | None => None
			    end with
			| Some t0 => typD t0
			| None => unit
		      end) with
	  | Some t => wandD _ t
	  | None => tt
        end
    end.

  Global Instance RSym_bilfunc : SymI.RSym (bilfunc typ) :=
  { typeof_sym := typeof_bilfunc
  ; sym_eqb := fun a b => Some (rel_dec a b)
  ; symD := funcD
  }.

  Global Instance RSymOk_bilfunc : SymI.RSymOk RSym_bilfunc.
  Proof.
    constructor.
    intros. unfold sym_eqb; simpl.
    consider (a ?[ eq ] b); auto.
  Qed.
  
End BILogicFuncInst.

Section MakeBILogic.
	Context {typ func : Type} {H : BILogicFunc typ func}.

	Definition mkEmp t : expr typ func:= Inj (fEmp t).
	Definition mkStar (t : typ) (P Q : expr typ func) := App (App (fStar t) P) Q.
	Definition mkWand (t : typ) (P Q : expr typ func) := App (App (fWand t) P) Q.

End MakeBILogic.

Section BILogicFuncOk.
  Context {typ func : Type} {HO: BILogicFunc typ func}.
  Context {RType_typ : RType typ} {RSym_func : RSym func}.
  Context {RelDec_eq : RelDec (@eq typ)}.

  Context {Typ2_tyArr : Typ2 _ Fun}.
  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.
  
  Variable gs : bilogic_ops.
  
  Class BILogicFuncOk := {
    bilf_funcAsOk (f : func) e : bilogicS f = Some e -> 
      forall t, funcAs f t = funcAs (RSym_func := RSym_bilfunc _ gs) e t;
    bilf_fEmpOk t : bilogicS (fEmp t) = Some (bilf_emp t);
    bilf_fStarOk t : bilogicS (fStar t) = Some (bilf_star t);
    bilf_fWandOk t : bilogicS (fWand t) = Some (bilf_wand t)
  }.

End BILogicFuncOk.

Implicit Arguments BILogicFuncOk [[HO] [RType_typ] [RSym_func] [RelDec_eq] [Typ2_tyArr]].

Section BILogicFuncBaseOk.
  Context {typ func : Type} {HO: ILogicFunc typ func}.
  Context {RType_typ : RType typ} {RSym_func : RSym func}.
  Context {RelDec_eq : RelDec (@eq typ)}.

  Context {Typ2_tyArr : Typ2 _ Fun}.
  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.
  
  Variable gs : bilogic_ops.

  Global Program Instance BILogicFuncBaseOk : BILogicFuncOk (RSym_func := RSym_bilfunc _ gs) typ (bilfunc typ) gs := {
    bilf_funcAsOk := fun _ _ _ _ => eq_refl;
    bilf_fEmpOk t := eq_refl;
    bilf_fStarOk t := eq_refl;
    bilf_fWandOk t := eq_refl
  }.

End BILogicFuncBaseOk.

Section BILogicFuncExprOk.
  Context {typ func : Type} `{HOK : BILogicFuncOk typ func}.
  Context {HROk : RTypeOk}.
  Context {A : Type} {RSymA : RSym A}.

  Lemma BILogicFunc_typeOk (f : func) (e : bilfunc typ) (H : bilogicS f = Some e) :
    typeof_sym f = typeof_bilfunc _ gs e.
  Proof.
    admit.
    (*
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
 	unfold funcAs in H1; simpl in H1; unfold empD in H1; rewrite <- Heqo in H1;
 	generalize dependent (symD f);
 	remember (typeof_sym f).
 	(destruct o; intros; [|]). specialize (H1 logic). forward. inv_all; subst.
 	specialize (H1 t); (rewrite type_cast_refl in H1; [|apply _]);
 	inversion H1. 
*)
  Qed.
  
  Lemma bilogicS_is_bilogic (f : func) (e : bilfunc typ) t df
  	(H1 : bilogicS f = Some e) (H2 : funcAs f t = Some df) :
    exists IL, gs (bilfunc_logic e) = Some IL.
  Proof.
    admit.
    (*
    pose proof (bilf_funcAsOk _ H1) as H; 
    rewrite H in H2; clear H;
    destruct e; simpl in *;
    unfold funcAs in H2; simpl in H2;
    (destruct (gs logic); [eexists; reflexivity | congruence]).
*)
  Qed.
  
  Lemma bilf_emp_type_eq (f : func) t u df
    (H1 : bilogicS f = Some (bilf_emp t)) (H2 : funcAs f u = Some df) :
    t = u.
  Proof.
    rewrite (bilf_funcAsOk _ H1) in H2.
    unfold funcAs, empD in H2; simpl in *.
    forward.
  Qed.

  Lemma bilf_wand_type_eq (f : func) t u df
    (H1 : bilogicS f = Some (bilf_wand t)) (H2 : funcAs f u = Some df) :
    u = typ2 t (typ2 t t).
  Proof.
    rewrite (bilf_funcAsOk _ H1) in H2.
    unfold funcAs, wandD in H2; simpl in *.
    forward.
  Qed.

  Lemma bilf_star_type_eq (f : func) t u df
    (H1 : bilogicS f = Some (bilf_star t)) (H2 : funcAs f u = Some df) :
    u = typ2 t (typ2 t t).
  Proof.
    rewrite (bilf_funcAsOk _ H1) in H2.
    unfold funcAs, starD in H2; simpl in *.
    forward.
  Qed.

  Existing Instance RSym_sum.

  Global Program Instance ILogicFuncOkSumR : BILogicFuncOk typ ((A + func)%type) gs := {
    bilf_funcAsOk := 
      fun a f H t => 
        match a with
          | inl b => _
          | inr b => _
        end;
    bilf_fEmpOk t := bilf_fEmpOk (func := func) t;
    bilf_fStarOk t := bilf_fStarOk (func := func) t;
    bilf_fWandOk t := bilf_fWandOk (func := func) t
  }.
  Next Obligation.
    apply (bilf_funcAsOk (func := func)).
    apply H.
  Qed.

  Global Program Instance ILogicFuncOkSumL : BILogicFuncOk typ ((func + A)%type) gs := {
    bilf_funcAsOk := 
      fun a f H t => 
        match a with
          | inl b => _
          | inr b => _
        end;
    bilf_fEmpOk t := bilf_fEmpOk (func := func) t;
    bilf_fStarOk t := bilf_fStarOk (func := func) t;
    bilf_fWandOk t := bilf_fWandOk (func := func) t
  }.
  Next Obligation.
    apply (bilf_funcAsOk (func := func)).
    apply H.
  Qed.

End BILogicFuncExprOk.

Section MakeBILogicSound.
  Context {typ func : Type} `{HOK : BILogicFuncOk typ func}.
  Context {HROk : RTypeOk} {Typ2_tyArrOk : Typ2Ok Typ2_tyArr}
          {RSym_funcOk : RSymOk RSym_func0}.

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.

  Lemma mkEmp_sound (t : typ) (tus tvs : tenv typ) BIL
    (Hgs : gs t = Some BIL) :
    exprD' tus tvs t (mkEmp t) = Some (fun _ _ => empD _ BIL).
  Proof.
    unfold mkEmp; simpl.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    pose proof (bilf_fEmpOk t) as Ho.
    pose proof (bilf_funcAsOk _ Ho) as H.
    rewrite H.
    unfold funcAs. simpl. 
    rewrite Hgs, type_cast_refl; [reflexivity | apply _].
  Qed.

  Lemma mkStar_sound (t : typ) (tus tvs : tenv typ) p q BIL
    (dp dq : ExprI.exprT tus tvs (typD t))
    (Hgs : gs t = Some BIL)
    (Hp : exprD' tus tvs t p = Some dp)
    (Hq : exprD' tus tvs t q = Some dq) :
    exprD' tus tvs t (mkStar t p q) = Some (exprT_App (exprT_App (fun _ _ => starD _ _ BIL) dp) dq).
  Proof.
    unfold mkStar; simpl.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ q _ Hq).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ p _ Hp).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    pose proof (bilf_fStarOk t) as Ho.
    pose proof (bilf_funcAsOk _ Ho) as H1.
    rewrite H1. unfold funcAs; simpl.
    rewrite Hgs. rewrite type_cast_refl; [reflexivity | apply _].
  Qed.
    
  Lemma mkWand_sound (t : typ) (tus tvs : tenv typ) p q BIL
    (dp dq : ExprI.exprT tus tvs (typD t))
    (Hgs : gs t = Some BIL)
    (Hp : exprD' tus tvs t p = Some dp)
    (Hq : exprD' tus tvs t q = Some dq) :
    exprD' tus tvs t (mkWand t p q) = Some (exprT_App (exprT_App (fun _ _ => wandD _ _ BIL) dp) dq).
  Proof.
    unfold mkWand; simpl.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ q _ Hq).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ p _ Hp).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    pose proof (bilf_fWandOk t) as Ho.
    pose proof (bilf_funcAsOk _ Ho) as H1.
    rewrite H1. unfold funcAs; simpl.
    rewrite Hgs. rewrite type_cast_refl; [reflexivity | apply _].
  Qed.

End MakeBILogicSound.