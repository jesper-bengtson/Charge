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
Require Import FunctionalExtensionality.

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

    Context {Typ2_tyArr : Typ2 _ Fun}.
    Context {Typ0_tyProp : Typ0 _ Prop}.
    
    Context {Typ2Ok_tyArr : Typ2Ok Typ2_tyArr}.

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
  
  Definition bil_pointwise := typ -> bool.

  Definition bil_pointwiseOk (bilp : bil_pointwise) :=
    forall t,
    typ2_match (fun T : Type => Prop) t
    (fun d r : typ =>
    match bilp (tyArr d r) with
      | true =>
        match gs (tyArr d r), gs r with
          | Some BILOps, Some _ => 
            match eq_sym (typ2_cast d r)  in (_ = t) return BILOperators t -> Prop with
              | eq_refl => 
                fun _ => 
                  (forall a, empSP a = empSP) /\
                  (forall (P Q : typD d -> typD r) a, (P ** Q) a = (P a ** Q a)) /\
                  (forall (P Q : typD d -> typD r) a, (wandSP P Q) a = wandSP (P a) (Q a))
            end BILOps
          | _, _ => False
        end
      | false => True
    end) True.

  Lemma bil_pointwise_bilogic (bilp : bil_pointwise) (bilpOk : bil_pointwiseOk bilp) (t u : typ)
    (H : bilp (tyArr t u) = true) : exists BIL, gs (tyArr t u) = Some BIL. 
  Proof.
    specialize (bilpOk (tyArr t u)).
    rewrite typ2_match_zeta in bilpOk; [|apply _].
    rewrite H in bilpOk.
    unfold eq_sym in bilpOk.
    revert bilpOk H. unfold tyArr. 
    generalize (typ2_cast t u).
    generalize (typ2 t u).
    generalize dependent (typD t).
    generalize dependent (gs u).
    generalize dependent (typD u).
    intros ? ? ? ?.
    generalize dependent (gs t0).
    generalize (typD t0).
    intros; subst. 
    forward. eexists. subst. reflexivity.
  Qed.

  Lemma bil_pointwise_bilogic_range (bilp : bil_pointwise) (bilpOk : bil_pointwiseOk bilp) (t u : typ)
    (H : bilp (tyArr t u) = true) : exists BIL, gs u = Some BIL. 
  Proof.
    specialize (bilpOk (tyArr t u)).
    rewrite typ2_match_zeta in bilpOk; [|apply _].
    rewrite H in bilpOk.
    unfold eq_sym in bilpOk.
    revert bilpOk H. unfold tyArr. 
    generalize (typ2_cast t u).
    generalize (typ2 t u).
    generalize dependent (typD t).
    generalize dependent (gs u).
    generalize dependent (typD u).
    intros ? ? ? ?.
    generalize dependent (gs t0).
    generalize (typD t0).
    intros; subst. 
    forward. eexists. subst. reflexivity.
  Qed.
  
  Lemma bil_pointwise_empD (bilp : bil_pointwise) (bilpOk : bil_pointwiseOk bilp) (t u : typ) 
    (H : bilp (tyArr t u) = true) BIL1 BIL2
    (gstu : gs (tyArr t u) = Some BIL1) (gsu : gs u = Some BIL2) a :
    (tyArrD empSP) a = empSP.
  Proof.
    unfold tyArrD, tyArrD', trmD, funE, eq_rect, id.
    specialize (bilpOk (tyArr t u)).
    rewrite typ2_match_zeta in bilpOk; [|apply _].
    rewrite H in bilpOk.
    unfold eq_sym in bilpOk.
    revert bilpOk.
    rewrite gstu.
    rewrite gsu.
    clear.
    generalize (typ2_cast t u).
    revert BIL1 BIL2.
    unfold tyArr.
    generalize dependent (typD (typ2 t u)).
    generalize dependent (typD t).
    generalize dependent (typD u).
    intros; subst.
    destruct bilpOk as [HEmp _].
    apply HEmp.
  Qed.    

  Lemma bil_pointwise_empR (bilp : bil_pointwise) (bilpOk : bil_pointwiseOk bilp) (t u : typ) 
    (H : bilp (tyArr t u) = true) BIL1 BIL2
    (gstu : gs (tyArr t u) = Some BIL1) (gsu : gs u = Some BIL2) :
    tyArrR (fun _ => empSP) = empSP.
  Proof.
    unfold tyArrR, tyArrR', trmR, funE, eq_rect_r, eq_rect, eq_sym, id.
    specialize (bilpOk (tyArr t u)).
    rewrite typ2_match_zeta in bilpOk; [|apply _].
    rewrite H in bilpOk.
    unfold eq_sym in bilpOk.
    revert bilpOk.
    rewrite gstu.
    rewrite gsu.
    clear.
    generalize (typ2_cast t u).
    revert BIL1 BIL2.
    unfold tyArr.
    generalize dependent (typD (typ2 t u)).
    generalize dependent (typD t).
    generalize dependent (typD u).
    intros; subst.
    destruct bilpOk as [HEmp _].
    unfold Fun in *.
	apply functional_extensionality; intros; rewrite HEmp; reflexivity.
  Qed.    

  Lemma bil_pointwise_starD (bilp : bil_pointwise) (bilpOk : bil_pointwiseOk bilp) (t u : typ)
    (H : bilp (tyArr t u) = true) BIL1 BIL2
    (gstu : gs (tyArr t u) = Some BIL1) (gsu : gs u = Some BIL2) (a b : typD (tyArr t u)) s :
    (tyArrD (sepSP a b)) s = sepSP (tyArrD a s) (tyArrD b s).
  Proof.
    unfold tyArrD, tyArrD', trmD, funE, eq_rect, id.
    specialize (bilpOk (tyArr t u)).
    rewrite typ2_match_zeta in bilpOk; [|apply _].
    rewrite H in bilpOk.
    unfold eq_sym in bilpOk.
    revert bilpOk.
    rewrite gstu.
    rewrite gsu.
    clear.
    generalize (typ2_cast t u).
    revert BIL1 BIL2 a b.
    unfold tyArr.
    generalize dependent (typD (typ2 t u)).
    generalize dependent (typD t).
    generalize dependent (typD u).
    intros; subst.
    destruct bilpOk as [_ [HStar _]].
    apply HStar.
  Qed.    

  Lemma bil_pointwise_starR (bilp : bil_pointwise) (bilpOk : bil_pointwiseOk bilp) (t u : typ) 
    (H : bilp (tyArr t u) = true) BIL1 BIL2
    (gstu : gs (tyArr t u) = Some BIL1) (gsu : gs u = Some BIL2) (a b : typD t -> typD u) :
    (tyArrR (fun s => sepSP (a s) (b s))) = sepSP (tyArrR a) (tyArrR b).
  Proof.
    unfold tyArrR, tyArrR', trmR, funE, eq_rect_r, eq_rect, eq_sym, id.
    specialize (bilpOk (tyArr t u)).
    rewrite typ2_match_zeta in bilpOk; [|apply _].
    rewrite H in bilpOk.
    unfold eq_sym in bilpOk.
    revert bilpOk.
    rewrite gstu.
    rewrite gsu.
    clear.
    generalize (typ2_cast t u).
    revert BIL1 BIL2.
    unfold tyArr.
    generalize dependent (typD (typ2 t u)).
    generalize dependent (typD t).
    generalize dependent (typD u).
    intros; subst.
    destruct bilpOk as [_ [HStar _]].
	apply functional_extensionality; intros; rewrite HStar; reflexivity.
  Qed.    

  Lemma bil_pointwise_wandD (bilp : bil_pointwise) (bilpOk : bil_pointwiseOk bilp) (t u : typ)
    (H : bilp (tyArr t u) = true) BIL1 BIL2
    (gstu : gs (tyArr t u) = Some BIL1) (gsu : gs u = Some BIL2) (a b : typD (tyArr t u)) s :
    (tyArrD (wandSP a b)) s = wandSP (tyArrD a s) (tyArrD b s).
  Proof.
    unfold tyArrD, tyArrD', trmD, funE, eq_rect, id.
    specialize (bilpOk (tyArr t u)).
    rewrite typ2_match_zeta in bilpOk; [|apply _].
    rewrite H in bilpOk.
    unfold eq_sym in bilpOk.
    revert bilpOk.
    rewrite gstu.
    rewrite gsu.
    clear.
    generalize (typ2_cast t u).
    revert BIL1 BIL2 a b.
    unfold tyArr.
    generalize dependent (typD (typ2 t u)).
    generalize dependent (typD t).
    generalize dependent (typD u).
    intros; subst.
    destruct bilpOk as [_ [_ HWand]].
    apply HWand.
  Qed.    

  Lemma bil_pointwise_wandR (bilp : bil_pointwise) (bilpOk : bil_pointwiseOk bilp) (t u : typ) 
    (H : bilp (tyArr t u) = true) BIL1 BIL2
    (gstu : gs (tyArr t u) = Some BIL1) (gsu : gs u = Some BIL2) (a b : typD t -> typD u) :
    (tyArrR (fun s => wandSP (a s) (b s))) = wandSP (tyArrR a) (tyArrR b).
  Proof.
    unfold tyArrR, tyArrR', trmR, funE, eq_rect_r, eq_rect, eq_sym, id.
    specialize (bilpOk (tyArr t u)).
    rewrite typ2_match_zeta in bilpOk; [|apply _].
    rewrite H in bilpOk.
    unfold eq_sym in bilpOk.
    revert bilpOk.
    rewrite gstu.
    rewrite gsu.
    clear.
    generalize (typ2_cast t u).
    revert BIL1 BIL2.
    unfold tyArr.
    generalize dependent (typD (typ2 t u)).
    generalize dependent (typD t).
    generalize dependent (typD u).
    intros; subst.
    destruct bilpOk as [_ [_ HWand]].
	apply functional_extensionality; intros; rewrite HWand; reflexivity.
  Qed.    

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
 Definition starD t BIL := tyArrR2 (@sepSP (typD t) BIL).
 Definition wandD t BIL := tyArrR2 (@wandSP (typD t) BIL).
 
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
      forall t, funcAs f t = funcAs (RSym_func := RSym_bilfunc gs) e t;
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

  Global Program Instance BILogicFuncBaseOk : BILogicFuncOk (RSym_func := RSym_bilfunc gs) typ (bilfunc typ) gs := {
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

  Context {Typ2Ok_tyArr : Typ2Ok Typ2_tyArr}.
  Context {RSymOk_func : RSymOk RSym_func0}.

  Lemma BILogicFunc_typeOk (f : func) (e : bilfunc typ) (H : bilogicS f = Some e) :
    typeof_sym f = typeof_bilfunc gs e.
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
  
  Lemma bilf_emp_func_type_eq (f : func) t u df
    (H1 : bilogicS f = Some (bilf_emp t)) (H2 : funcAs f u = Some df) :
    t = u.
  Proof.
    rewrite (bilf_funcAsOk _ H1) in H2.
    unfold funcAs, empD in H2; simpl in *.
    forward.
  Qed.

  Lemma bilf_wand_func_type_eq (f : func) t u df
    (H1 : bilogicS f = Some (bilf_wand t)) (H2 : funcAs f u = Some df) :
    u = typ2 t (typ2 t t).
  Proof.
    rewrite (bilf_funcAsOk _ H1) in H2.
    unfold funcAs, wandD in H2; simpl in *.
    forward.
  Qed.

  Lemma bilf_star_func_type_eq (f : func) t u df
    (H1 : bilogicS f = Some (bilf_star t)) (H2 : funcAs f u = Some df) :
    u = typ2 t (typ2 t t).
  Proof.
    rewrite (bilf_funcAsOk _ H1) in H2.
    unfold funcAs, starD in H2; simpl in *.
    forward.
  Qed.
	
  Lemma bilf_emp_type_eq tus tvs (e : expr typ func) t u df
    (H1 : bilogicS e = Some (bilf_emp t)) (H2 : exprD' tus tvs u e = Some df) :
    t = u.
  Proof.
    destruct e; simpl in *; try congruence.
    autorewrite with exprD_rw in H2; simpl in H2; forward; inv_all; subst.
    eapply bilf_emp_func_type_eq; eassumption.
  Qed.

  Lemma bilf_wand_type_eq tus tvs (e : expr typ func) t u df
    (H1 : bilogicS e = Some (bilf_wand t)) (H2 : exprD' tus tvs u e = Some df) :
    u = typ2 t (typ2 t t).
  Proof.
    destruct e; simpl in *; try congruence.
    autorewrite with exprD_rw in H2; simpl in H2; forward; inv_all; subst.
    eapply bilf_wand_func_type_eq; eassumption.
  Qed.

  Lemma bilf_star_type_eq tus tvs (e : expr typ func) t u df
    (H1 : bilogicS e = Some (bilf_star t)) (H2 : exprD' tus tvs u e = Some df) :
    u = typ2 t (typ2 t t).
  Proof.
    destruct e; simpl in *; try congruence.
    autorewrite with exprD_rw in H2; simpl in H2; forward; inv_all; subst.
    eapply bilf_star_func_type_eq; eassumption.
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

  Lemma bilf_emp_func_eq (t : typ) (f : func) (df : typD t) BIL
    (H : gs t = Some BIL)
    (Ho : bilogicS f = Some (bilf_emp t))
    (Hf : funcAs f t = Some df) :
    df = empSP.
  Proof.
   rewrite (bilf_funcAsOk _ Ho) in Hf.
   unfold funcAs in Hf; simpl in *.
   rewrite H in Hf.
   rewrite type_cast_refl in Hf; [|apply HROk].
   unfold Rcast, Relim_refl in Hf.
   inversion Hf. reflexivity.
  Qed.

  Lemma bilf_emp_eq tus tvs (t : typ) (e : expr typ func) (df : ExprI.exprT tus tvs (typD t)) BIL
    (H : gs t = Some BIL)
    (Ho : bilogicS e = Some (bilf_emp t))
    (Hf : exprD' tus tvs t e = Some df) :
    df = fun us vs => empSP.
  Proof.
   destruct e; simpl in *; try congruence.
   autorewrite with exprD_rw in Hf; simpl in Hf; forward; inv_all; subst.
   erewrite <- bilf_emp_func_eq; try eassumption; reflexivity.
  Qed.

  Lemma bilf_star_func_eq (t : typ) (f : func) (df : typD (tyArr t (tyArr t t))) BIL
    (H : gs t = Some BIL)
    (Ho : bilogicS f = Some (bilf_star t))
    (Hf : funcAs f (tyArr t (tyArr t t)) = Some df) :
    df = tyArrR2 sepSP.
  Proof.
   rewrite (bilf_funcAsOk _ Ho) in Hf.
   unfold funcAs in Hf; simpl in *.
   rewrite H in Hf.
   rewrite type_cast_refl in Hf; [|apply HROk].
   unfold Rcast, Relim_refl in Hf.
   inversion Hf. reflexivity.
  Qed.

  Lemma bilf_star_eq tus tvs (t : typ) (e : expr typ func) 
    (df : ExprI.exprT tus tvs (typD (tyArr t (tyArr t t)))) BIL
    (H : gs t = Some BIL)
    (Ho : bilogicS e = Some (bilf_star t))
    (Hf : exprD' tus tvs (tyArr t (tyArr t t)) e = Some df) :
    df = fun us vs => tyArrR2 sepSP.
  Proof.
   destruct e; simpl in *; try congruence.
   autorewrite with exprD_rw in Hf; simpl in Hf; forward; inv_all; subst.
   erewrite <- bilf_star_func_eq; try eassumption; reflexivity.
  Qed.
  
  Lemma bilf_wand_func_eq (t : typ) (f : func) (df : typD (tyArr t (tyArr t t))) BIL
    (H : gs t = Some BIL)
    (Ho : bilogicS f = Some (bilf_wand t))
    (Hf : funcAs f (tyArr t (tyArr t t)) = Some df) :
    df = tyArrR2 wandSP.
  Proof.
   rewrite (bilf_funcAsOk _ Ho) in Hf.
   unfold funcAs in Hf; simpl in *.
   rewrite H in Hf.
   rewrite type_cast_refl in Hf; [|apply HROk].
   unfold Rcast, Relim_refl in Hf.
   inversion Hf. reflexivity.
  Qed.

  Lemma bilf_wand_eq tus tvs (t : typ) (e : expr typ func) 
    (df : ExprI.exprT tus tvs (typD (tyArr t (tyArr t t)))) BIL
    (H : gs t = Some BIL)
    (Ho : bilogicS e = Some (bilf_wand t))
    (Hf : exprD' tus tvs (tyArr t (tyArr t t)) e = Some df) :
    df = fun us vs => tyArrR2 wandSP.
  Proof.
   destruct e; simpl in *; try congruence.
   autorewrite with exprD_rw in Hf; simpl in Hf; forward; inv_all; subst.
   erewrite <- bilf_wand_func_eq; try eassumption; reflexivity.
  Qed.
  
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
    exprD' tus tvs t (mkStar t p q) = Some (exprT_App (exprT_App (fun _ _ => starD _ BIL) dp) dq).
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
    exprD' tus tvs t (mkWand t p q) = Some (exprT_App (exprT_App (fun _ _ => wandD _ BIL) dp) dq).
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