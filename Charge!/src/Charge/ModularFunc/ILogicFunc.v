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

Require Import Charge.ModularFunc.Denotation.
Require Import Charge.Logics.ILogic.
Require Import Charge.Tactics.Base.MirrorCoreTacs.

Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import FunctionalExtensionality.

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

Section ILogicCast.
  Context {typ : Type} {RType_typ : RType typ}.
  Context {Typ2_tyArr : Typ2 RType_typ Fun}.
  
  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.

  Definition ILOps_tyArrD t u (IL : ILogicOps (typD (tyArr t u))) : ILogicOps (typD t -> typD u) :=
    eq_rect_r ILogicOps IL (eq_sym (typ2_cast t u)).

  Definition ILOps_tyArrR t u (IL : ILogicOps (typD t -> typD u)) : ILogicOps (typD (tyArr t u)) :=
    eq_rect_r ILogicOps IL (typ2_cast t u).

End ILogicCast.

Section ILogicFuncInst.

	Context {typ func : Type}.
	Context {HR : RType typ} {Heq : RelDec (@eq typ)} {HC : RelDec_Correct Heq}.

    Context {Typ2_tyArr : Typ2 _ Fun}.
    Context {Typ0_tyProp : Typ0 _ Prop}.

    Context {Typ2Ok_tyArr : Typ2Ok Typ2_tyArr}.

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

  Definition il_pointwise := typ -> bool.

  Definition il_pointwiseOk (ilp : il_pointwise) :=
    forall t,
    typ2_match (fun T : Type => Prop) t
    (fun d r : typ =>
    match ilp (tyArr d r) with
      | true =>
        match gs (tyArr d r), gs r with
          | Some ILOps, Some _ => 
            match eq_sym (typ2_cast d r)  in (_ = t) return ILogicOps t -> Prop with
              | eq_refl => 
                fun _ => 
                  (forall a, ltrue a = ltrue) /\
                  (forall a, lfalse a = lfalse) /\
                  (forall (P Q : typD d -> typD r) a, (P //\\ Q) a = (P a //\\ Q a)) /\
                  (forall (P Q : typD d -> typD r) a, (P \\// Q) a = (P a \\// Q a)) /\
                  (forall (P Q : typD d -> typD r) a, (P -->> Q) a = (P a -->> Q a)) /\
                  (forall (A : Type) (f : A -> typD d -> typD r) a, 
                    (lexists f) a = lexists (fun x => f x a)) /\
                  (forall (A : Type) (f : A -> typD d -> typD r) a, 
                    (lforall f) a = lforall (fun x => f x a))
            end ILOps
          | _, _ => False
        end
      | false => True
    end) True.
 
  Lemma il_pointwise_ilogic (ilp : il_pointwise) (ilpOk : il_pointwiseOk ilp) (t u : typ) (H : ilp (tyArr t u) = true) : exists IL, gs (tyArr t u) = Some IL. 
  Proof.
    specialize (ilpOk (tyArr t u)).
    rewrite typ2_match_zeta in ilpOk; [|apply _].
    rewrite H in ilpOk.
    unfold eq_sym in ilpOk.
    revert ilpOk H. unfold tyArr. 
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

  Lemma il_pointwise_ilogic_range (ilp : il_pointwise) (ilpOk : il_pointwiseOk ilp) (t u : typ) (H : ilp (tyArr t u) = true) : exists IL, gs u = Some IL. 
  Proof.
    specialize (ilpOk (tyArr t u)).
    rewrite typ2_match_zeta in ilpOk; [|apply _].
    rewrite H in ilpOk.
    unfold eq_sym in ilpOk.
    revert ilpOk H. unfold tyArr. 
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
  
  Lemma il_pointwise_trueD (ilp : il_pointwise) (ilpOk : il_pointwiseOk ilp) (t u : typ) (H : ilp (tyArr t u) = true) IL1 IL2
    (gstu : gs (tyArr t u) = Some IL1) (gsu : gs u = Some IL2) a :
    (tyArrD ltrue) a = ltrue.
  Proof.
    unfold tyArrD, tyArrD', trmD, funE, eq_rect, id.
    specialize (ilpOk (tyArr t u)).
    rewrite typ2_match_zeta in ilpOk; [|apply _].
    rewrite H in ilpOk.
    unfold eq_sym in ilpOk.
    revert ilpOk.
    rewrite gstu.
    rewrite gsu.
    clear.
    generalize (typ2_cast t u).
    revert IL1 IL2.
    unfold tyArr.
    generalize dependent (typD (typ2 t u)).
    generalize dependent (typD t).
    generalize dependent (typD u).
    intros; subst.
    destruct ilpOk as [HTrue _].
    apply HTrue.
  Qed.

  Lemma il_pointwise_trueR (ilp : il_pointwise) (ilpOk : il_pointwiseOk ilp) (t u : typ) (H : ilp (tyArr t u) = true) IL1 IL2
    (gstu : gs (tyArr t u) = Some IL1) (gsu : gs u = Some IL2) :
    tyArrR (fun _ => ltrue) = ltrue.
  Proof.
    unfold tyArrR, tyArrR', trmR, funE, eq_rect_r, eq_rect, eq_sym, id.
    specialize (ilpOk (tyArr t u)).
    rewrite typ2_match_zeta in ilpOk; [|apply _].
    rewrite H in ilpOk.
    unfold eq_sym in ilpOk.
    revert ilpOk.
    rewrite gstu.
    rewrite gsu.
    clear.
    generalize (typ2_cast t u).
    revert IL1 IL2.
    unfold tyArr.
    generalize dependent (typD (typ2 t u)).
    generalize dependent (typD t).
    generalize dependent (typD u).
    intros; subst.
    destruct ilpOk as [HTrue _].
    unfold Fun in *.
	apply functional_extensionality; intros; rewrite HTrue; reflexivity.
  Qed.    

  Lemma il_pointwise_falseD (ilp : il_pointwise) (ilpOk : il_pointwiseOk ilp) (t u : typ) (H : ilp (tyArr t u) = true) IL1 IL2
    (gstu : gs (tyArr t u) = Some IL1) (gsu : gs u = Some IL2) a :
     (tyArrD lfalse) a = lfalse.
  Proof.
    unfold tyArrD, tyArrD', trmD, funE, eq_rect, id.
    specialize (ilpOk (tyArr t u)).
    rewrite typ2_match_zeta in ilpOk; [|apply _].
    rewrite H in ilpOk.
    unfold eq_sym in ilpOk.
    revert ilpOk.
    rewrite gstu.
    rewrite gsu.
    clear.
    generalize (typ2_cast t u).
    revert IL1 IL2.
    unfold tyArr.
    generalize dependent (typD (typ2 t u)).
    generalize dependent (typD t).
    generalize dependent (typD u).
    intros; subst.
    destruct ilpOk as [_ [HFalse _]].
    apply HFalse.
  Qed.    

  Lemma il_pointwise_falseR (ilp : il_pointwise) (ilpOk : il_pointwiseOk ilp) (t u : typ) (H : ilp (tyArr t u) = true) IL1 IL2
    (gstu : gs (tyArr t u) = Some IL1) (gsu : gs u = Some IL2) :
    tyArrR (fun _ => lfalse) = lfalse.
  Proof.
    unfold tyArrR, tyArrR', trmR, funE, eq_rect_r, eq_rect, eq_sym, id.
    specialize (ilpOk (tyArr t u)).
    rewrite typ2_match_zeta in ilpOk; [|apply _].
    rewrite H in ilpOk.
    unfold eq_sym in ilpOk.
    revert ilpOk.
    rewrite gstu.
    rewrite gsu.
    clear.
    generalize (typ2_cast t u).
    revert IL1 IL2.
    unfold tyArr.
    generalize dependent (typD (typ2 t u)).
    generalize dependent (typD t).
    generalize dependent (typD u).
    intros; subst.
    destruct ilpOk as [_ [HFalse _]].
    unfold Fun in *.
	apply functional_extensionality; intros; rewrite HFalse; reflexivity.
  Qed.    

  Lemma il_pointwise_andD (ilp : il_pointwise) (ilpOk : il_pointwiseOk ilp) (t u : typ) (H : ilp (tyArr t u) = true) IL1 IL2
    (gstu : gs (tyArr t u) = Some IL1) (gsu : gs u = Some IL2) (a b : typD (tyArr t u)) s :
    (tyArrD (land a b)) s = land (tyArrD a s) (tyArrD b s).
  Proof.
    unfold tyArrD, tyArrD', trmD, funE, eq_rect, id.
    specialize (ilpOk (tyArr t u)).
    rewrite typ2_match_zeta in ilpOk; [|apply _].
    rewrite H in ilpOk.
    unfold eq_sym in ilpOk.
    revert ilpOk.
    rewrite gstu.
    rewrite gsu.
    clear.
    generalize (typ2_cast t u).
    revert IL1 IL2 a b.
    unfold tyArr.
    generalize dependent (typD (typ2 t u)).
    generalize dependent (typD t).
    generalize dependent (typD u).
    intros; subst.
    destruct ilpOk as [_ [_ [HAnd _]]].
    apply HAnd.
  Qed.    

  Lemma il_pointwise_andR (ilp : il_pointwise) (ilpOk : il_pointwiseOk ilp) (t u : typ) (H : ilp (tyArr t u) = true) IL1 IL2
    (gstu : gs (tyArr t u) = Some IL1) (gsu : gs u = Some IL2) (a b : typD t -> typD u) :
    (tyArrR (fun s => land (a s) (b s))) = land (tyArrR a) (tyArrR b).
  Proof.
    unfold tyArrR, tyArrR', trmR, funE, eq_rect_r, eq_rect, eq_sym, id.
    specialize (ilpOk (tyArr t u)).
    rewrite typ2_match_zeta in ilpOk; [|apply _].
    rewrite H in ilpOk.
    unfold eq_sym in ilpOk.
    revert ilpOk.
    rewrite gstu.
    rewrite gsu.
    clear.
    generalize (typ2_cast t u).
    revert IL1 IL2.
    unfold tyArr.
    generalize dependent (typD (typ2 t u)).
    generalize dependent (typD t).
    generalize dependent (typD u).
    intros; subst.
    destruct ilpOk as [_ [_ [HAnd _]]].
	apply functional_extensionality; intros; rewrite HAnd; reflexivity.
  Qed.    

  Lemma il_pointwise_orD (ilp : il_pointwise) (ilpOk : il_pointwiseOk ilp) (t u : typ) (H : ilp (tyArr t u) = true) IL1 IL2
    (gstu : gs (tyArr t u) = Some IL1) (gsu : gs u = Some IL2) (a b : typD (tyArr t u)) s :
    (tyArrD (lor a b)) s = lor (tyArrD a s) (tyArrD b s).
  Proof.
    unfold tyArrD, tyArrD', trmD, funE, eq_rect, id.
    specialize (ilpOk (tyArr t u)).
    rewrite typ2_match_zeta in ilpOk; [|apply _].
    rewrite H in ilpOk.
    unfold eq_sym in ilpOk.
    revert ilpOk.
    rewrite gstu.
    rewrite gsu.
    clear.
    generalize (typ2_cast t u).
    revert IL1 IL2 a b.
    unfold tyArr.
    generalize dependent (typD (typ2 t u)).
    generalize dependent (typD t).
    generalize dependent (typD u).
    intros; subst.
    destruct ilpOk as [_ [_ [_ [HOr _]]]].
    apply HOr.
  Qed.    

  Lemma il_pointwise_orR (ilp : il_pointwise) (ilpOk : il_pointwiseOk ilp) (t u : typ) (H : ilp (tyArr t u) = true) IL1 IL2
    (gstu : gs (tyArr t u) = Some IL1) (gsu : gs u = Some IL2) (a b : typD t -> typD u) :
    (tyArrR (fun s => lor (a s) (b s))) = lor (tyArrR a) (tyArrR b).
  Proof.
    unfold tyArrR, tyArrR', trmR, funE, eq_rect_r, eq_rect, eq_sym, id.
    specialize (ilpOk (tyArr t u)).
    rewrite typ2_match_zeta in ilpOk; [|apply _].
    rewrite H in ilpOk.
    unfold eq_sym in ilpOk.
    revert ilpOk.
    rewrite gstu.
    rewrite gsu.
    clear.
    generalize (typ2_cast t u).
    revert IL1 IL2.
    unfold tyArr.
    generalize dependent (typD (typ2 t u)).
    generalize dependent (typD t).
    generalize dependent (typD u).
    intros; subst.
    destruct ilpOk as [_ [_ [_ [HOr _]]]].
	apply functional_extensionality; intros; rewrite HOr; reflexivity.
  Qed.    

  Lemma il_pointwise_implD (ilp : il_pointwise) (ilpOk : il_pointwiseOk ilp) (t u : typ) (H : ilp (tyArr t u) = true) IL1 IL2
    (gstu : gs (tyArr t u) = Some IL1) (gsu : gs u = Some IL2) (a b : typD (tyArr t u)) s :
    (tyArrD (limpl a b)) s = limpl (tyArrD a s) (tyArrD b s).
  Proof.
    unfold tyArrD, tyArrD', trmD, funE, eq_rect, id.
    specialize (ilpOk (tyArr t u)).
    rewrite typ2_match_zeta in ilpOk; [|apply _].
    rewrite H in ilpOk.
    unfold eq_sym in ilpOk.
    revert ilpOk.
    rewrite gstu.
    rewrite gsu.
    clear.
    generalize (typ2_cast t u).
    revert IL1 IL2 a b.
    unfold tyArr.
    generalize dependent (typD (typ2 t u)).
    generalize dependent (typD t).
    generalize dependent (typD u).
    intros; subst.
    destruct ilpOk as [_ [_ [_ [_ [HImpl _]]]]].
    apply HImpl.
  Qed.    

  Lemma il_pointwise_implR (ilp : il_pointwise) (ilpOk : il_pointwiseOk ilp) (t u : typ) (H : ilp (tyArr t u) = true) IL1 IL2
    (gstu : gs (tyArr t u) = Some IL1) (gsu : gs u = Some IL2) (a b : typD t -> typD u) :
    (tyArrR (fun s => limpl (a s) (b s))) = limpl (tyArrR a) (tyArrR b).
  Proof.
    unfold tyArrR, tyArrR', trmR, funE, eq_rect_r, eq_rect, eq_sym, id.
    specialize (ilpOk (tyArr t u)).
    rewrite typ2_match_zeta in ilpOk; [|apply _].
    rewrite H in ilpOk.
    unfold eq_sym in ilpOk.
    revert ilpOk.
    rewrite gstu.
    rewrite gsu.
    clear.
    generalize (typ2_cast t u).
    revert IL1 IL2.
    unfold tyArr.
    generalize dependent (typD (typ2 t u)).
    generalize dependent (typD t).
    generalize dependent (typD u).
    intros; subst.
    destruct ilpOk as [_ [_ [_ [_ [HImpl _]]]]].
	apply functional_extensionality; intros; rewrite HImpl; reflexivity.
  Qed.    

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
 
 Definition trueD {t IL} (H : gs t = Some IL) := @ltrue (typD t) IL.
 Definition falseD {t IL} (H : gs t = Some IL) := @lfalse (typD t) IL.
 Definition andD {t IL} (H : gs t = Some IL) := tyArrR2 (@land (typD t) IL).
 Definition orD {t IL} (H : gs t = Some IL) := tyArrR2 (@lor (typD t) IL).
 Definition implD {t IL} (H : gs t = Some IL) := tyArrR2 (@limpl (typD t) IL).
 
 Implicit Arguments trueD [[t] [IL]].
 Implicit Arguments falseD [[t] [IL]].
 Implicit Arguments andD [[t] [IL]]. 
 Implicit Arguments orD [[t] [IL]].
 Implicit Arguments implD [[t] [IL]].
 
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
	  | Some t => lfalse
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
	  | Some t => tyArrR2 land
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
	  | Some t => tyArrR2 limpl
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
	  | Some t => tyArrR2 lor
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
  Context {RSymOk_func : RSymOk RSym_func0}.
  Context {Typ2Ok_tyArr : Typ2Ok Typ2_tyArr}.

  Lemma ILogicFunc_typeOk (f : func) (e : ilfunc typ) (H : ilogicS f = Some e) :
    typeof_sym f = typeof_ilfunc gs e.
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
  
  Lemma ilf_true_func_type_eq (f : func) t u df
    (H1 : ilogicS f = Some (ilf_true t)) (H2 : funcAs f u = Some df) :
    t = u.
  Proof.
    rewrite (ilf_funcAsOk _ H1) in H2.
    unfold funcAs in H2; simpl in *.
    forward.
  Qed.

  Lemma ilf_true_type_eq tus tvs (e : expr typ func) t u df
    (H1 : ilogicS e = Some (ilf_true t)) (H2 : exprD' tus tvs u e = Some df) :
    t = u.
  Proof.
    destruct e; simpl in *; try congruence.
    autorewrite with exprD_rw in H2; simpl in H2; forward; inv_all; subst.
    eapply ilf_true_func_type_eq; eassumption.
  Qed.

  Lemma ilf_false_func_type_eq (f : func) t u df
    (H1 : ilogicS f = Some (ilf_false t)) (H2 : funcAs f u = Some df) :
    t = u.
  Proof.
    rewrite (ilf_funcAsOk _ H1) in H2.
    unfold funcAs in H2; simpl in *.
    forward.
  Qed.

  Lemma ilf_false_type_eq tus tvs (e : expr typ func) t u df
    (H1 : ilogicS e = Some (ilf_false t)) (H2 : exprD' tus tvs u e = Some df) :
    t = u.
  Proof.
    destruct e; simpl in *; try congruence.
    autorewrite with exprD_rw in H2; simpl in H2; forward; inv_all; subst.
    eapply ilf_false_func_type_eq; eassumption.
  Qed.

  Lemma ilf_and_func_type_eq (f : func) t u df
    (H1 : ilogicS f = Some (ilf_and t)) (H2 : funcAs f u = Some df) :
    u = typ2 t (typ2 t t).
  Proof.
    rewrite (ilf_funcAsOk _ H1) in H2.
    unfold funcAs in H2; simpl in *.
    forward.
  Qed.

  Lemma ilf_and_type_eq tus tvs (e : expr typ func) t u df
    (H1 : ilogicS e = Some (ilf_and t)) (H2 : exprD' tus tvs u e = Some df) :
    u = typ2 t (typ2 t t).
  Proof.
    destruct e; simpl in *; try congruence.
    autorewrite with exprD_rw in H2; simpl in H2; forward; inv_all; subst.
    eapply ilf_and_func_type_eq; eassumption.
  Qed.

  Lemma ilf_or_func_type_eq (f : func) t u df
    (H1 : ilogicS f = Some (ilf_or t)) (H2 : funcAs f u = Some df) :
    u = typ2 t (typ2 t t).
  Proof.
    rewrite (ilf_funcAsOk _ H1) in H2.
    unfold funcAs in H2; simpl in *.
    forward.
  Qed.

  Lemma ilf_or_type_eq tus tvs (e : expr typ func) t u df
    (H1 : ilogicS e = Some (ilf_or t)) (H2 : exprD' tus tvs u e = Some df) :
    u = typ2 t (typ2 t t).
  Proof.
    destruct e; simpl in *; try congruence.
    autorewrite with exprD_rw in H2; simpl in H2; forward; inv_all; subst.
    eapply ilf_or_func_type_eq; eassumption.
  Qed.

  Lemma ilf_impl_func_type_eq (f : func) t u df
    (H1 : ilogicS f = Some (ilf_impl t)) (H2 : funcAs f u = Some df) :
    u = typ2 t (typ2 t t).
  Proof.
    rewrite (ilf_funcAsOk _ H1) in H2.
    unfold funcAs in H2; simpl in *.
    forward.
  Qed.

  Lemma ilf_impl_type_eq tus tvs (e : expr typ func) t u df
    (H1 : ilogicS e = Some (ilf_impl t)) (H2 : exprD' tus tvs u e = Some df) :
    u = typ2 t (typ2 t t).
  Proof.
    destruct e; simpl in *; try congruence.
    autorewrite with exprD_rw in H2; simpl in H2; forward; inv_all; subst.
    eapply ilf_impl_func_type_eq; eassumption.
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

  Lemma ilf_true_func_eq (t : typ) (f : func) (df : typD t) IL
    (H : gs t = Some IL)
    (Ho : ilogicS f = Some (ilf_true t))
    (Hf : funcAs f t = Some df) :
    df = trueD gs H.
  Proof.
   rewrite (ilf_funcAsOk _ Ho) in Hf.
   unfold funcAs in Hf; simpl in *.
   rewrite H in Hf.
   rewrite type_cast_refl in Hf; [|apply HROk].
   unfold Rcast, Relim_refl in Hf.
   inversion Hf. reflexivity.
  Qed.

  Lemma ilf_true_eq tus tvs (t : typ) (e : expr typ func) (df : ExprI.exprT tus tvs (typD t)) IL
    (H : gs t = Some IL)
    (Ho : ilogicS e = Some (ilf_true t))
    (Hf : exprD' tus tvs t e = Some df) :
    df = fun us vs => trueD gs H.
  Proof.
   destruct e; simpl in *; try congruence.
   autorewrite with exprD_rw in Hf; simpl in Hf; forward; inv_all; subst.
   erewrite <- ilf_true_func_eq; try eassumption; reflexivity.
  Qed.

  Lemma ilf_false_func_eq (t : typ) (f : func) (df : typD t) IL
    (H : gs t = Some IL)
    (Ho : ilogicS f = Some (ilf_false t))
    (Hf : funcAs f t = Some df) :
    df = falseD gs H.
  Proof.
   rewrite (ilf_funcAsOk _ Ho) in Hf.
   unfold funcAs in Hf; simpl in *.
   rewrite H in Hf.
   rewrite type_cast_refl in Hf; [|apply HROk].
   unfold Rcast, Relim_refl in Hf.
   inversion Hf. reflexivity.
  Qed.

  Lemma ilf_false_eq tus tvs (t : typ) (e : expr typ func) (df : ExprI.exprT tus tvs (typD t)) IL
    (H : gs t = Some IL)
    (Ho : ilogicS e = Some (ilf_false t))
    (Hf : exprD' tus tvs t e = Some df) :
    df = fun us vs => falseD gs H.
  Proof.
   destruct e; simpl in *; try congruence.
   autorewrite with exprD_rw in Hf; simpl in Hf; forward; inv_all; subst.
   erewrite <- ilf_false_func_eq; try eassumption; reflexivity.
  Qed.

  Lemma ilf_and_func_eq (t : typ) (f : func) (df : typD (tyArr t (tyArr t t))) IL
    (H : gs t = Some IL)
    (Ho : ilogicS f = Some (ilf_and t))
    (Hf : funcAs f (tyArr t (tyArr t t)) = Some df) :
    df = andD gs H.
  Proof.
   rewrite (ilf_funcAsOk _ Ho) in Hf.
   unfold funcAs in Hf; simpl in *.
   rewrite H in Hf.
   rewrite type_cast_refl in Hf; [|apply HROk].
   unfold Rcast, Relim_refl in Hf.
   inversion Hf. reflexivity.
  Qed.

  Lemma ilf_and_eq tus tvs (t : typ) (e : expr typ func) 
    (df : ExprI.exprT tus tvs (typD (tyArr t (tyArr t t)))) IL
    (H : gs t = Some IL)
    (Ho : ilogicS e = Some (ilf_and t))
    (Hf : exprD' tus tvs (tyArr t (tyArr t t)) e = Some df) :
    df = fun us vs => andD gs H.
  Proof.
   destruct e; simpl in *; try congruence.
   autorewrite with exprD_rw in Hf; simpl in Hf; forward; inv_all; subst.
   erewrite <- ilf_and_func_eq; try eassumption; reflexivity.
  Qed.

  Lemma ilf_or_func_eq (t : typ) (f : func) (df : typD (tyArr t (tyArr t t))) IL
    (H : gs t = Some IL)
    (Ho : ilogicS f = Some (ilf_or t))
    (Hf : funcAs f (tyArr t (tyArr t t)) = Some df) :
    df = orD gs H.
  Proof.
   rewrite (ilf_funcAsOk _ Ho) in Hf.
   unfold funcAs in Hf; simpl in *.
   rewrite H in Hf.
   rewrite type_cast_refl in Hf; [|apply HROk].
   unfold Rcast, Relim_refl in Hf.
   inversion Hf. reflexivity.
  Qed.

  Lemma ilf_or_eq tus tvs (t : typ) (e : expr typ func) 
    (df : ExprI.exprT tus tvs (typD (tyArr t (tyArr t t)))) IL
    (H : gs t = Some IL)
    (Ho : ilogicS e = Some (ilf_or t))
    (Hf : exprD' tus tvs (tyArr t (tyArr t t)) e = Some df) :
    df = fun us vs => orD gs H.
  Proof.
   destruct e; simpl in *; try congruence.
   autorewrite with exprD_rw in Hf; simpl in Hf; forward; inv_all; subst.
   erewrite <- ilf_or_func_eq; try eassumption; reflexivity.
  Qed.

  Lemma ilf_impl_func_eq (t : typ) (f : func) (df : typD (tyArr t (tyArr t t))) IL
    (H : gs t = Some IL)
    (Ho : ilogicS f = Some (ilf_impl t))
    (Hf : funcAs f (tyArr t (tyArr t t)) = Some df) :
    df = implD gs H.
  Proof.
   rewrite (ilf_funcAsOk _ Ho) in Hf.
   unfold funcAs in Hf; simpl in *.
   rewrite H in Hf.
   rewrite type_cast_refl in Hf; [|apply HROk].
   unfold Rcast, Relim_refl in Hf.
   inversion Hf. reflexivity.
  Qed.

  Lemma ilf_impl_eq tus tvs (t : typ) (e : expr typ func) 
    (df : ExprI.exprT tus tvs (typD (tyArr t (tyArr t t)))) IL
    (H : gs t = Some IL)
    (Ho : ilogicS e = Some (ilf_impl t))
    (Hf : exprD' tus tvs (tyArr t (tyArr t t)) e = Some df) :
    df = fun us vs => implD gs H.
  Proof.
   destruct e; simpl in *; try congruence.
   autorewrite with exprD_rw in Hf; simpl in Hf; forward; inv_all; subst.
   erewrite <- ilf_impl_func_eq; try eassumption; reflexivity.
  Qed.

  Lemma mkTrue_sound (t : typ) (tus tvs : tenv typ) IL
    (Hgs : gs t = Some IL) :
    exprD' tus tvs t (mkTrue t) = Some (fun _ _ => ltrue).
  Proof.
    unfold mkTrue; simpl.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    pose proof (ilf_fTrueOk t) as Ho.
    pose proof (ilf_funcAsOk _ Ho) as H.
    rewrite H.
    unfold funcAs. simpl. 
    SearchAbout Rrefl.
    rewrite Hgs, type_cast_refl; [
      unfold Rcast; rewrite Relim_sym, Relim_refl; try apply _; reflexivity |
      apply _
    ].
  Qed.

  Lemma mkFalse_sound (t : typ) (tus tvs : tenv typ) IL
    (Hgs : gs t = Some IL) :
    exprD' tus tvs t (mkFalse t) = Some (fun _ _ => lfalse).
  Proof.
    unfold mkFalse; simpl.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    pose proof (ilf_fFalseOk t) as Ho.
    pose proof (ilf_funcAsOk _ Ho) as H.
    rewrite H.
    unfold funcAs. simpl. 
    SearchAbout Rrefl.
    rewrite Hgs, type_cast_refl; [
      unfold Rcast; rewrite Relim_sym, Relim_refl; try apply _; reflexivity |
      apply _
    ].
  Qed.

  Lemma mkAnd_sound (t : typ) (tus tvs : tenv typ) p q IL
    (dp dq : ExprI.exprT tus tvs (typD t))
    (Hgs : gs t = Some IL)
    (Hp : exprD' tus tvs t p = Some dp)
    (Hq : exprD' tus tvs t q = Some dq) :
    exprD' tus tvs t (mkAnd t p q) = Some (exprT_App (exprT_App (fun _ _ => tyArrR2 land) dp) dq).
  Proof.
    unfold mkAnd; simpl.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ q _ Hq).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ p _ Hp).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    pose proof (ilf_fAndOk t) as Ho.
    pose proof (ilf_funcAsOk _ Ho) as H1.
    rewrite H1. unfold funcAs; simpl.
    rewrite Hgs. rewrite type_cast_refl; [reflexivity | apply _].
  Qed.
  
  Lemma mkOr_sound (t : typ) (tus tvs : tenv typ) p q IL
    (dp dq : ExprI.exprT tus tvs (typD t))
    (Hgs : gs t = Some IL)
    (Hp : exprD' tus tvs t p = Some dp)
    (Hq : exprD' tus tvs t q = Some dq) :
    exprD' tus tvs t (mkOr t p q) = Some (exprT_App (exprT_App (fun _ _ => tyArrR2 lor) dp) dq).
  Proof.
    unfold mkOr; simpl.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ q _ Hq).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ p _ Hp).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    pose proof (ilf_fOrOk t) as Ho.
    pose proof (ilf_funcAsOk _ Ho) as H1.
    rewrite H1. unfold funcAs; simpl.
    rewrite Hgs. rewrite type_cast_refl; [reflexivity | apply _].
  Qed.
  
  Lemma mkImpl_sound (t : typ) (tus tvs : tenv typ) p q IL
    (dp dq : ExprI.exprT tus tvs (typD t))
    (Hgs : gs t = Some IL)
    (Hp : exprD' tus tvs t p = Some dp)
    (Hq : exprD' tus tvs t q = Some dq) :
    exprD' tus tvs t (mkImpl t p q) = Some (exprT_App (exprT_App (fun _ _ => tyArrR2 limpl) dp) dq).
  Proof.
    unfold mkImpl; simpl.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ q _ Hq).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ p _ Hp).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    pose proof (ilf_fImplOk t) as Ho.
    pose proof (ilf_funcAsOk _ Ho) as H1.
    rewrite H1. unfold funcAs; simpl.
    rewrite Hgs. rewrite type_cast_refl; [reflexivity | apply _].
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