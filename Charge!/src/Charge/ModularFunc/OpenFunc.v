Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.String.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.syms.SymEnv.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprVariables.
Require Import MirrorCore.Lambda.ExprTac.
Require Import MirrorCore.SymI.
Require Import MirrorCore.syms.SymSum.

Set Printing Universes.
Require Import Charge.ModularFunc.Denotation.

Require Import Charge.ModularFunc.ILogicFunc.
Print Charge.Logics.ILogic.ILogic.

Require Import Charge.ModularFunc.BaseType.
Require Import Charge.Open.Stack.
Require Import Charge.Open.Subst.
Require Import Charge.ModularFunc.Denotation.
Require Import Charge.ModularFunc.ListType.
Require Import Charge.ModularFunc.SubstType.
Require Import Charge.ModularFunc.ListFunc.
Require Import Charge.ModularFunc.BILogicFunc.
Require Import Charge.ModularFunc.BaseFunc.
Require Import Charge.ModularFunc.EmbedFunc.
Require Import Charge.Rel.

Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import FunctionalExtensionality.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

  Inductive open_func typ {RType_typ : RType typ} {HST : SubstType typ} :=
    | of_const (_ : typ)
    | of_ap (_ _ : typ)
    | of_null
    | of_stack_get
    | of_stack_set
    | of_apply_subst (_ : typ)
    | of_single_subst
    | of_subst
    | of_trunc_subst.
    
Implicit Arguments open_func [[RType_typ] [HST]].
    
 Class OpenFunc (typ func : Type) {RType_typ : RType typ} {HST : SubstType typ} := {
  fConst : typ -> func;
  fAp : typ -> typ -> func;
  
  fNull : func;
  
  fStackGet : func;
  fStackSet : func;
  
  fApplySubst : typ -> func;
  fSingleSubst : func;
  fSubst : func;
  fTruncSubst : func;
  
  open_funcS : func -> option (open_func typ)
}.

Implicit Arguments OpenFunc [[RType_typ] [HST]].

Section OpenFuncSum.
	Context {typ func : Type} `{H : OpenFunc typ func}.

	Global Instance OpenFuncSumL (A : Type) : 
	   OpenFunc typ (func + A) := {
		  fConst t := inl (fConst t);
		  fAp t u := inl (fAp t u);
		  
		  fNull := inl fNull;
		  
		  fStackGet := inl fStackGet;
		  fStackSet := inl fStackSet;
		  
		  fApplySubst t := inl (fApplySubst t);
		  fSingleSubst := inl fSingleSubst;
		  fSubst := inl fSubst;
		  fTruncSubst := inl fTruncSubst;
		  
		  open_funcS f := match f with
		  				    | inl f => open_funcS f
		  				    | inr _ => None
		  				  end
       }.

	Global Instance OpenFuncSumR (A : Type) : 
	   OpenFunc typ (A + func) := {
		  fConst t := inr (fConst t);
		  fAp t u := inr (fAp t u);
		  
		  fNull := inr fNull;
		  
		  fStackGet := inr fStackGet;
		  fStackSet := inr fStackSet;
		  
		  fApplySubst t := inr (fApplySubst t);
		  fSingleSubst := inr fSingleSubst;
		  fSubst := inr fSubst;
		  fTruncSubst := inr fTruncSubst;
		  
		  open_funcS f := match f with
		  				    | inr f => open_funcS f
		  				    | inl _ => None
		  				  end
		  
       }.

	Global Instance OpenFuncExpr : 
	   OpenFunc typ (expr typ func) := {
		  fConst t := Inj (fConst t);
		  fAp t u := Inj (fAp t u);
		  
		  fNull := Inj fNull;
		  
		  fStackGet := Inj fStackGet;
		  fStackSet := Inj fStackSet;
		  
		  fApplySubst t := Inj (fApplySubst t);
		  fSingleSubst := Inj fSingleSubst;
		  fSubst := Inj fSubst;
		  fTruncSubst := Inj fTruncSubst;
		  
		  open_funcS f := match f with
		  				    | Inj f => open_funcS f
		  				    | _ => None
		  				  end
		  
       }.

End OpenFuncSum.

Section OpenFuncInst.

	Context {typ func : Type} {BT : BaseType typ} {LT : ListType typ}.
	Context {RType_typ : RType typ} {Heq : RelDec (@eq typ)} {HC : RelDec_Correct Heq}.

    Context {Typ2_tyArr : Typ2 _ Fun}.
    Context {Typ0_tyProp : Typ0 _ Prop}.
    
    Context {ST : SubstType typ} {HV : ValNull (typD tyVal)}.
    Context {BTD : BaseTypeD BT} {LTD : ListTypeD LT}.
    	
    Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.
    Let tyProp : typ := @typ0 _ _ _ _.

	Local Notation "'tyStack'" := (tyArr tyString tyVal).
    Local Notation "'tySubst'" := (tyArr tyString (tyArr tyStack tyVal)).
	Local Notation "'tyExpr'" := (tyArr tyStack tyVal).
	Local Notation "'tySubstList'" := (tyList (tyProd tyString (tyArr tyStack tyVal))).

	Definition stack := @stack (typD tyString) (typD tyVal).

	Global Instance OpenFuncInst : OpenFunc typ (open_func typ) := {
	  fConst := of_const;
	  fAp := of_ap;
	  fNull := of_null;
	  fStackGet := of_stack_get;
	  fStackSet := of_stack_set;
	  fApplySubst := of_apply_subst;
	  fSingleSubst := of_single_subst;
	  fSubst := of_subst;
	  fTruncSubst := of_trunc_subst;
	  
	  open_funcS f := Some f
	}.
Set Printing Universes.

  Definition typeof_open_func (f : open_func typ) : option typ :=
    match f with
    | of_const t => Some (tyArr t (tyArr tyStack t))
    | of_ap t u => Some (tyArr (tyArr tyStack (tyArr t u)) (tyArr (tyArr tyStack t) (tyArr tyStack u)))
    | of_apply_subst t => Some (tyArr (tyArr tyStack t) (tyArr tySubst (tyArr tyStack t)))
	| of_null => Some tyVal
    | of_stack_get => Some (tyArr tyString tyExpr)
    | of_stack_set => Some (tyArr tyString (tyArr tyVal (tyArr tyStack tyStack)))
    | of_single_subst => Some (tyArr tyExpr (tyArr tyString tySubst))
    | of_subst => Some (tyArr tySubstList tySubst)
    | of_trunc_subst => Some (tyArr tySubstList tySubst)
	end.

  Global Instance RelDec_open_func : RelDec (@eq (open_func typ)) :=
  { rel_dec := fun a b =>
	         match a, b with
	  	       | of_const t, of_const t'
	  	       | of_apply_subst t, of_apply_subst t' => t ?[eq] t'
	  	       | of_ap t u, of_ap t' u' => (t ?[eq] t' && u ?[eq] u')%bool
	  	       | of_null, of_null
	  	       | of_stack_get, of_stack_get
	  	       | of_stack_set, of_stack_set
	  	       | of_single_subst, of_single_subst
	  	       | of_subst, of_subst
	  	       | of_trunc_subst, of_trunc_subst => true
	  	       | _, _ => false
	         end
  }.

  Global Instance RelDec_Correct_open_func : RelDec_Correct RelDec_open_func.
  Proof.
    constructor.
    destruct x; destruct y; simpl; try rewrite andb_true_iff;
    repeat rewrite rel_dec_correct; try intuition congruence.
  Qed.
  
	Local Instance Applicative_Fun A : Applicative (Fun A) :=
	{ pure := fun _ x _ => x
	; ap := fun _ _ f x y => (f y) (x y)
	}.

    Definition substListD (lst : typD tySubstList) : substlist (A := typD tyString) (val := (typD tyVal)) :=
      trmD lst (listE (pairE eq_refl (funE (funE eq_refl eq_refl) eq_refl))).
   
	 Definition substD (s : typD tySubst) : subst := 
	   (fun e f => (tyArrD2 s) e (tyArrR f)).

	 Definition substR (s : subst) : typD tySubst :=
	   tyArrR2 (fun a b => s a (tyArrD b)). 


	 Definition constD t : typD (tyArr t (tyArr tyStack t)) :=
	   tyArrR (fun x => (tyArrR (pure x))). 
	
	 Definition stack_getD : typD (tyArr tyString (tyArr tyStack tyVal)) :=
	   tyArrR2 (fun x s => (tyArrD s) x).

	 Definition stack_setD : typD (tyArr tyString (tyArr tyVal (tyArr tyStack tyStack))) :=
	   tyArrR4 (fun a b c d => stack_add a b (tyArrD c) d).

	 Definition apD t u : typD (tyArr (tyArr tyStack (tyArr t u)) (tyArr (tyArr tyStack t) (tyArr tyStack u))) :=
	   tyArrR3 (fun a b c => @ap (Fun (typD tyStack)) (Applicative_Fun _) (typD t) (typD u)
	   	 (tyArrD2 a) (tyArrD b) c).

	 Definition applySubstD (t : typ) : typD (tyArr (tyArr tyStack t) (tyArr tySubst (tyArr tyStack t))) :=
	   tyArrR3 (fun a b c => apply_subst
	     (fun x => tyArrD a (tyArrR x)) (substD b)
	     (tyArrD c)).
	 
	 Definition singleSubstD :=
	   tyArrR2 (fun a b => substR (subst1 (fun x => tyArrD a (tyArrR x)) b)).
	   
	 Definition parSubstD :=
	   tyArrR (fun a => substR (substl_aux (substListD a))).

	 Definition truncSubstD :=
	   tyArrR (fun a => substR (substl_trunc_aux (substListD a))).

	 Definition open_func_symD f : match typeof_open_func f return Type with
	                                 | Some t => typD t
	                                 | None => unit
	                               end :=
		match f as f return match typeof_open_func f return Type with
								| Some t => typD t
								| None => unit
							  end with
	      | of_const t => constD t
	      | of_ap t u => apD t u
	      | of_null => null
	      | of_stack_get => stack_getD
	      | of_stack_set => stack_setD
	      | of_apply_subst t => applySubstD t
	      | of_single_subst => singleSubstD
	      | of_subst => parSubstD
	      | of_trunc_subst => truncSubstD
	    end.

	Global Instance RSym_OpenFunc : SymI.RSym (open_func typ) := {
	  typeof_sym := typeof_open_func;
	  symD := open_func_symD;
	  sym_eqb := (fun a b => Some (rel_dec a b))
	}.

  Global Instance RSymOk_lopen_func : SymI.RSymOk RSym_OpenFunc.
  Proof.
    constructor.
    intros. unfold sym_eqb; simpl.
    consider (a ?[ eq ] b); auto.
  Qed.

End OpenFuncInst.

Section OpenFuncOk.
  Context {typ func : Type} {BT : BaseType typ} {LT : ListType typ} {ST : SubstType typ}.
  Context {RType_typ : RType typ} {HO: OpenFunc typ func} {Heq : RelDec (@eq typ)}. 
  Context {RSym_func : RSym func}.
  Context {HV : ValNull (typD tyVal)}.

  Context {BTD : BaseTypeD BT} {LTD : ListTypeD LT}.

  Context  {Typ2_tyArr : Typ2 _ Fun}.
  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.

  Class OpenFuncOk := {
    of_funcAsOk f e : open_funcS f = Some e -> forall t, funcAs f t = funcAs e t;
    of_fConstOk t : open_funcS (fConst t) = Some (of_const t);
    of_fApOk t u : open_funcS (fAp t u) = Some (of_ap t u);
    of_fNullOk : open_funcS fNull = Some of_null;
    of_fStackGetOk : open_funcS fStackGet = Some of_stack_get;
    of_fStackSetOk : open_funcS fStackSet = Some of_stack_set;
    of_fApplySubstOk t : open_funcS (fApplySubst t) = Some (of_apply_subst t);
    of_fSingleSubstOk : open_funcS fSingleSubst = Some of_single_subst;
    of_fSubstOk : open_funcS fSubst = Some of_subst;
    of_fTruncSubstOk : open_funcS fTruncSubst = Some of_trunc_subst
  }.

End OpenFuncOk.

Implicit Arguments OpenFuncOk [[BT] [LT] [ST] [RType_typ] [HO] [RSym_func] [Heq] [HV] [BTD] [LTD] [Typ2_tyArr]].

Section OpenFuncBaseOk.
  Context {typ func : Type} {BT : BaseType typ} {LT : ListType typ} {ST : SubstType typ}.
  Context {RType_typ : RType typ} {HO: OpenFunc typ func} {Heq' : RelDec (@eq typ)}. 
  Context {RSym_func : RSym func}.
  Context {HV : ValNull (typD tyVal)}.

  Context {BTD : BaseTypeD BT} {LTD : ListTypeD LT}.

  Context  {Typ2_tyArr : Typ2 _ Fun}.
  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.

  Program Instance open_funcOk : OpenFuncOk typ (open_func typ) := {
    of_funcAsOk := fun _ _ _ _ => eq_refl;
    of_fConstOk t := eq_refl;
    of_fApOk t u := eq_refl;
    of_fNullOk := eq_refl;
    of_fStackGetOk := eq_refl;
    of_fStackSetOk := eq_refl;
    of_fApplySubstOk t := eq_refl;
    of_fSingleSubstOk := eq_refl;
    of_fSubstOk := eq_refl;
    of_fTruncSubstOk := eq_refl
  }.
  
End OpenFuncBaseOk.

Section OpenFuncExprOk.
  Context {typ func : Type} `{HOK : OpenFuncOk typ func}.
  Context {HROk : RTypeOk}.

  Lemma open_funcSome (f : func) (e : open_func typ) (t : typ)
    (H : open_funcS f = Some e) : 
      match typeof_open_func e with
        | Some t => funcAs f t <> None
        | None => False
      end.
  Proof.
    destruct HOK as [H1].
    specialize (H1 _ _ H).
    destruct e; simpl in *; intros H2;
    match goal with 
      | H : funcAs _ ?t = None |- _ => 
        specialize (H1 t); rewrite H in H1; clear H;
              unfold funcAs in H1; simpl in H1; 
              rewrite type_cast_refl in H1; [|apply _]; inversion H1
    end.
  Qed.

  Lemma OpenFunc_typeOk (f : func) (e : open_func typ) (H : open_funcS f = Some e) :
    typeof_sym f = typeof_open_func e.
  Proof.
    destruct HOK as [H1].
    specialize (H1 _ _ H).
 	destruct e; simpl in *;
    match goal with 
      | |- typeof_sym ?f = Some ?t => 
	 	specialize (H1 t);
	 	simpl in H1;
 	 	unfold funcAs in H1; simpl in H1; rewrite type_cast_refl in H1; [|apply _];
 		generalize dependent (symD f);
 		destruct (typeof_sym f); simpl; intros; [forward|]; inversion H1
    end.
  Qed.

  Existing Instance RSym_sum.
  Existing Instance RSymOk_sum.

  Context {A : Type} {RSymA : RSym A}.


  Global Program Instance OpenFuncOkSumR : OpenFuncOk typ (A + func) := {
    of_funcAsOk := 
      fun a f H t => 
        match a with
          | inl b => _
          | inr b => _
        end;
    of_fConstOk t := of_fConstOk t (func := func);
    of_fApOk t u := of_fApOk t u (func := func);
    of_fNullOk := of_fNullOk (func := func);
    of_fStackGetOk := of_fStackGetOk (func := func);
    of_fStackSetOk := of_fStackSetOk (func := func);
    of_fApplySubstOk t := of_fApplySubstOk t (func := func);
    of_fSingleSubstOk := of_fSingleSubstOk (func := func);
    of_fSubstOk := of_fSubstOk (func := func);
    of_fTruncSubstOk := of_fTruncSubstOk (func := func)
  }.
  Next Obligation.
    apply (of_funcAsOk _ H).
  Qed.

  Global Program Instance OpenFuncOkSumL : OpenFuncOk typ (func + A) := {
    of_funcAsOk := 
      fun a f H t => 
        match a with
          | inl b => _
          | inr b => _
        end;
    of_fConstOk t := of_fConstOk t (func := func);
    of_fApOk t u := of_fApOk t u (func := func);
    of_fNullOk := of_fNullOk (func := func);
    of_fStackGetOk := of_fStackGetOk (func := func);
    of_fStackSetOk := of_fStackSetOk (func := func);
    of_fApplySubstOk t := of_fApplySubstOk t (func := func);
    of_fSingleSubstOk := of_fSingleSubstOk (func := func);
    of_fSubstOk := of_fSubstOk (func := func);
    of_fTruncSubstOk := of_fTruncSubstOk (func := func)
  }.
  Next Obligation.
    apply (of_funcAsOk _ H).
  Qed.
  
End OpenFuncExprOk.

Section MakeOpen.
	Context {typ func : Type} {HR : RType typ} {HS : SubstType typ}.
	Context {H : OpenFunc typ func} {H1 : ListFunc typ func}
	        {HBT : BaseType typ}.

    Context  {Typ2_tyArr : Typ2 _ Fun}.
    Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.

	Local Notation "'tyStack'" := (tyArr tyString tyVal).

    Definition mkNull : expr typ func := Inj fNull.
	Definition mkConst (t : typ) (e : expr typ func) := App (fConst t) e.
	Definition mkAp (t u : typ) (f e : expr typ func) := App (App (fAp t u) f) e.
	Definition mkStackGet (x s : expr typ func) := App (App fStackGet x) s.
	Definition mkStackSet (x v s : expr typ func) := App (App (App fStackSet x) v) s.
	Definition mkApplySubst (t : typ) (P s : expr typ func) := App (App (fApplySubst t) P) s.
	Definition mkSingleSubst (e x : expr typ func) := App (App fSingleSubst e) x.
	Definition mkApplySingleSubst t P x e := mkApplySubst t P (mkSingleSubst x e).	
	Definition mkSubst (s : expr typ func) := App fSubst s.
	Definition mkTruncSubst (s : expr typ func) := App fTruncSubst s.
	Definition mkApplyTruncSubst t P s := mkApplySubst t P (mkTruncSubst s).
			
	Fixpoint mkAps f es t :=
		match es with 
			| nil => mkConst t f
			| (e, t')::es => mkAp t' t (mkAps f es (tyArr t' t)) e
		end.

	Context {HSf : RSym func}.
(*
	Fixpoint ap_lift_aux tus tvs (e : expr typ func) (t : typ) : option (expr typ func) :=
	  match e with
		| App f a => 
		  match typeof_expr tus tvs a with
		    | Some u => 
		        match ap_lift_aux tus tvs f (tyArr u t), ap_lift_aux tus tvs a u with
		    	  | Some f', Some a' => Some (mkAp u t f' a')
		    	  | _, _ => None
		    	end		
		    | None => None
		  end
		| Inj f => Some (mkConst t (Inj f))
		| Abs u f => match (ap_lift_aux tus (u::tvs) f (tyArr u t)) with
					   | Some f' => Some (Abs (tyArr tyStack u) f')
					   | None => None
					 end
						
		| _ => Some e
	  end.

	Definition ap_lift2 tus tvs (e : expr typ func) :=
		match typeof_expr tus tvs e with
		  | Some t => ap_lift_aux tus tvs e t
		  | None => None
		end.
*)

	Context {HIL : ILogicFunc typ func}.
	Context {HBIL : BILogicFunc typ func}.

	Fixpoint il_lift tus tvs (e : expr typ func) :=
	  match e with
	    | App (App f a) b => 
	      match ilogicS f with
	        | Some (ilf_entails t) =>
	          match il_lift tus tvs a, il_lift tus tvs b with
	            | Some a', Some b' => Some (mkEntails (tyArr tyStack t) a' b')
	            | _, _ => None
	          end
	        | Some (ilf_and t) =>
	          match il_lift tus tvs a, il_lift tus tvs b with
	            | Some a', Some b' => Some (mkAnd (tyArr tyStack t) a' b')
	            | _, _ => None
	          end
	        | Some (ilf_or t) =>
	          match il_lift tus tvs a, il_lift tus tvs b with
	            | Some a', Some b' => Some (mkOr (tyArr tyStack t) a' b')
	            | _, _ => None
	          end
	        | Some (ilf_impl t) =>
	          match il_lift tus tvs a, il_lift tus tvs b with
	            | Some a', Some b' => Some (mkImpl (tyArr tyStack t) a' b')
	            | _, _ => None
	          end
	        | _ => 
	          match bilogicS f with
	            | Some (bilf_star t) =>
		          match il_lift tus tvs a, il_lift tus tvs b with
		            | Some a', Some b' => Some (mkStar (tyArr tyStack t) a' b')
		            | _, _ => None
		          end
	            | Some (bilf_wand t) =>
		          match il_lift tus tvs a, il_lift tus tvs b with
		            | Some a', Some b' => Some (mkWand (tyArr tyStack t) a' b')
		            | _, _ => None
		          end
	            | _ => 
	              match typeof_expr tus tvs e, typeof_expr tus tvs a, typeof_expr tus tvs b with
	                | Some t, Some u, Some v =>
	            	  match il_lift tus tvs f, il_lift tus tvs a, il_lift tus tvs b with
	            	    | Some f', Some a', Some b' =>
	            	      Some (mkAp v t (mkAp u (tyArr v t) f' a') b')
	            	    | _, _, _ => None 
	            	  end
	            	| _, _, _ => None
	              end
	          end
	      end
	    | App f a =>
	      match ilogicS f with
	        | Some (ilf_exists u v) =>
	          match il_lift tus tvs a with
	            | Some a' => Some (App (fExists (tyArr tyStack u) (tyArr tyStack v)) a')
	            | None => None
	          end
	        | Some (ilf_forall u v) =>
	          match il_lift tus tvs a with
	            | Some a' => Some (App (fForall (tyArr tyStack u) (tyArr tyStack v)) a')
	            | None => None
	          end
	        | _ =>
	          match typeof_expr tus tvs e, typeof_expr tus tvs a with
	            | Some t, Some u =>
	              match il_lift tus tvs f, il_lift tus tvs a with
	                | Some f', Some a' => Some (mkAp u t f' a')
	                | _, _ => None
	              end 
	            | _, _ => None
	          end
	      end
	    | Inj f =>
	      match ilogicS f with
	        | Some (ilf_true t) => Some (mkTrue (tyArr tyStack t))
	        | Some (ilf_false t) => Some (mkFalse (tyArr tyStack t))
	        | _ => 
	          match bilogicS f with
	            | Some (bilf_emp t) => Some (mkEmp (tyArr tyStack t))
	            | _ =>
	              match typeof_expr tus tvs e with
	                | Some t => Some (mkConst t e)
	                | None => None
	              end
	          end
	      end
		| Abs t f => 
		  match il_lift tus (t::tvs) f with
		    | Some f' => Some (Abs (tyArr tyStack t) f')
		    | None => None
		  end
	    | _ => Some e
	  end.
(*	   
	with ap_lift tus tvs (e : expr typ func) {struct e} :=
		match e with
		  | Abs t f => 
		    match il_lift tus (t::tvs) f with
		      | Some f' => Some (Abs (tyArr tyStack t) f')
		      | None => None
		    end
		  | Inj f =>
		    match typeof_expr tus tvs e with
		      | Some t => Some (mkConst t (Inj f))
		      | None => None
		    end
		  | App f a =>
		    match typeof_expr tus tvs e, typeof_expr tus tvs a with
		      | Some t, Some u =>
		        match il_lift tus tvs f, il_lift tus tvs a with
		          | Some f', Some a' => Some (mkAp u t f' a')
		          | _, _ => None
		        end
		      | _, _ => None
		    end 
		  | _ => Some e
		end.
*)	
End MakeOpen.

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

Section MakeOpenSound.
  Context {typ func : Type} {ST : SubstType typ} {BT : BaseType typ} {RType_typ : RType typ}.
  Context {OF : OpenFunc typ func} {ILF : ILogicFunc typ func} {BILF : BILogicFunc typ func} {BF : BaseFunc typ func}.
  Context {LT : ListType typ}.
  Context {EF : EmbedFunc typ func}.
  Context {RelDec_typ : RelDec (@eq typ)}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {RSym_func : RSym func}.
  Context {RSym_funcOk : RSymOk RSym_func}.
  Context {Typ2_tyArr : Typ2 _ Fun}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Typ2_tyArrOk : Typ2Ok Typ2_tyArr}.
  Context {HV : ValNull (typD tyVal)}.
  Context {BTD : BaseTypeD BT} {LTD : ListTypeD LT}.
  Context {OFOK : OpenFuncOk typ func}.

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.

  Let Expr_expr := Expr_expr.
  Let ExprOk_expr := ExprOk_expr.
  Let ExprUVar_expr := ExprUVar_expr (typ := typ) (func := func).
  
  Local Existing Instance Expr_expr.
  Local Existing Instance ExprOk_expr.
  Local Existing Instance ExprUVar_expr.

  Local Notation "'tyStack'" := (tyArr tyString tyVal).
  Local Notation "'tySubst'" := (tyArr tyString (tyArr tyStack tyVal)).
  Local Notation "'tyExpr'" := (tyArr tyStack tyVal).
  Local Notation "'tySubstList'" := (tyList (tyProd tyString (tyArr tyStack tyVal))).
  
  Lemma funcAs_fNull_eq : funcAs fNull tyVal = Some null.
  Proof.
   rewrite (of_funcAsOk _ of_fNullOk).
   unfold funcAs; simpl.
   rewrite type_cast_refl; [reflexivity | apply _].
  Qed.    
  
  Lemma funcAs_fConst_eq t : funcAs (fConst t) (tyArr t (tyArr tyStack t)) = Some (constD t).
  Proof.
   rewrite (of_funcAsOk _ (of_fConstOk t)).
   unfold funcAs; simpl.
   rewrite type_cast_refl; [reflexivity | apply _].
  Qed.
  
  Lemma funcAs_fAp_eq t u : funcAs (fAp t u) (tyArr (tyArr tyStack (tyArr t u)) (tyArr (tyArr tyStack t) (tyArr tyStack u))) = Some (apD t u).
  Proof.
   rewrite (of_funcAsOk _ (of_fApOk t u)).
   unfold funcAs; simpl.
   rewrite type_cast_refl; [reflexivity | apply _].
  Qed.
  
  Lemma funcAs_fStackGet_eq : funcAs fStackGet (tyArr tyString (tyArr (tyArr tyString tyVal) tyVal)) = Some stack_getD.
  Proof.
   rewrite (of_funcAsOk _ of_fStackGetOk).
   unfold funcAs; simpl.
   rewrite type_cast_refl; [reflexivity | apply _].
  Qed.
  
  Lemma funcAs_fStackSet_eq : funcAs fStackSet (tyArr tyString (tyArr tyVal (tyArr tyStack tyStack))) = Some stack_setD.
  Proof.
   rewrite (of_funcAsOk _ of_fStackSetOk).
   unfold funcAs; simpl.
   rewrite type_cast_refl; [reflexivity | apply _].
  Qed.
  
  Lemma funcAs_fApplySubst_eq t : funcAs (fApplySubst t) (tyArr (tyArr tyStack t) (tyArr tySubst (tyArr tyStack t))) = Some (applySubstD t).
  Proof.
   rewrite (of_funcAsOk _ (of_fApplySubstOk t)).
   unfold funcAs; simpl.
   rewrite type_cast_refl; [reflexivity | apply _].
  Qed.
  
  Lemma funcAs_fSingleSubst_eq : funcAs fSingleSubst (tyArr (tyArr tyStack tyVal) (tyArr tyString tySubst)) = Some singleSubstD.
  Proof.
   rewrite (of_funcAsOk _ of_fSingleSubstOk).
   unfold funcAs; simpl.
   rewrite type_cast_refl; [reflexivity | apply _].
  Qed.

  Lemma funcAs_fSubst_eq : funcAs fSubst (tyArr (tyList (tyProd tyString tyExpr)) (tyArr tyString tyExpr)) = Some parSubstD.
  Proof.
   rewrite (of_funcAsOk _ of_fSubstOk).
   unfold funcAs; simpl.
   rewrite type_cast_refl; [reflexivity | apply _].
  Qed.
  
  Lemma funcAs_fTruncSubst_eq : funcAs fTruncSubst (tyArr (tyList (tyProd tyString tyExpr)) (tyArr tyString tyExpr)) = Some truncSubstD.
  Proof.
   rewrite (of_funcAsOk _ of_fTruncSubstOk).
   unfold funcAs; simpl.
   rewrite type_cast_refl; [reflexivity | apply _].
  Qed.

  Lemma typeof_fNull_eq : typeof_sym fNull = Some tyVal.
  Proof.
    eapply typeof_funcAs; apply funcAs_fNull_eq.
  Qed.

  Lemma typeof_fConst_eq t : typeof_sym (fConst t) = Some (tyArr t (tyArr tyStack t)).
  Proof.
    eapply typeof_funcAs; apply funcAs_fConst_eq.
  Qed.

  Lemma typeof_fAp_eq t u : typeof_sym (fAp t u) = Some (tyArr (tyArr tyStack (tyArr t u)) (tyArr (tyArr tyStack t) (tyArr tyStack u))).
  Proof.
    eapply typeof_funcAs; apply funcAs_fAp_eq.
  Qed.

  Lemma typeof_fStackGet_eq : typeof_sym fStackGet = Some (tyArr tyString (tyArr (tyArr tyString tyVal) tyVal)).
  Proof.
    eapply typeof_funcAs; apply funcAs_fStackGet_eq.
  Qed.

  Lemma typeof_fStackSet_eq : typeof_sym fStackSet = Some (tyArr tyString (tyArr tyVal (tyArr tyStack tyStack))).
  Proof.
    eapply typeof_funcAs; apply funcAs_fStackSet_eq.
  Qed.

  Lemma typeof_fStackApplySubst_eq t : typeof_sym (fApplySubst t) = Some (tyArr (tyArr tyStack t) (tyArr tySubst (tyArr tyStack t))).
  Proof.
    eapply typeof_funcAs; apply funcAs_fApplySubst_eq.
  Qed.

  Lemma typeof_fSingleSubst_eq : typeof_sym fSingleSubst = Some (tyArr (tyArr tyStack tyVal) (tyArr tyString tySubst)).
  Proof.
    eapply typeof_funcAs; apply funcAs_fSingleSubst_eq.
  Qed.

  Lemma typeof_fSubst_eq : typeof_sym fSubst = Some (tyArr (tyList (tyProd tyString tyExpr)) (tyArr tyString tyExpr)).
  Proof.
    eapply typeof_funcAs; apply funcAs_fSubst_eq.
  Qed.

  Lemma typeof_fTruncSubst_eq : typeof_sym fTruncSubst = Some (tyArr (tyList (tyProd tyString tyExpr)) (tyArr tyString tyExpr)).
  Proof.
    eapply typeof_funcAs; apply funcAs_fTruncSubst_eq.
  Qed.

  Lemma of_const_func_type_eq (t u : typ) (f : func) (df : typD u)
    (Ho : open_funcS f = Some (of_const t))
    (Hf : funcAs f u = Some df) :
    Rty u (tyArr t (tyArr tyStack t)).
  Proof.
    pose proof (of_funcAsOk _ Ho) as H; rewrite H in Hf.
    unfold funcAs in Hf. simpl in Hf. 
    forward; inv_all; subst.
    rewrite <- r. reflexivity.
  Qed.   

  Lemma of_const_type_eq tus tvs (e : expr typ func) t u df
    (Ho : open_funcS e = Some (of_const t)) 
    (Hf : exprD' tus tvs u e = Some df) :
    Rty u (tyArr t (tyArr tyStack t)).
  Proof.
    destruct e; simpl in *; try congruence.
    autorewrite with exprD_rw in Hf; simpl in Hf; forward; inv_all; subst.
    eapply of_const_func_type_eq; eassumption.
  Qed.

  Lemma of_ap_func_type_eq (t u v : typ) (f : func) (df : typD v)
    (Ho : open_funcS f = Some (of_ap t u))
    (Hf : funcAs f v = Some df) :
    Rty v (tyArr (tyArr tyStack (tyArr t u)) (tyArr (tyArr tyStack t) (tyArr tyStack u))).
  Proof.
    pose proof (of_funcAsOk _ Ho) as H; rewrite H in Hf.
    unfold funcAs in Hf. simpl in Hf. 
    forward; inv_all; subst.
    rewrite <- r. reflexivity.
  Qed.   

  Lemma of_ap_type_eq tus tvs (e : expr typ func) t u v df
    (Ho : open_funcS e = Some (of_ap t u)) 
    (Hf : exprD' tus tvs v e = Some df) :
    Rty v (tyArr (tyArr tyStack (tyArr t u)) (tyArr (tyArr tyStack t) (tyArr tyStack u))).
  Proof.
    destruct e; simpl in *; try congruence.
    autorewrite with exprD_rw in Hf; simpl in Hf; forward; inv_all; subst.
    eapply of_ap_func_type_eq; eassumption.
  Qed.

  Lemma of_stack_get_func_type_eq t (f : func) (df : typD t) 
    (Ho : open_funcS f = Some of_stack_get) 
    (Hf : funcAs f t = Some df) :
    Rty t (tyArr tyString (tyArr (tyArr tyString tyVal) tyVal)).
  Proof.
    pose proof (of_funcAsOk _ Ho) as H; rewrite H in Hf.
    unfold funcAs in Hf. simpl in Hf. 
    forward; inv_all; subst.
    rewrite <- r. reflexivity.
  Qed.

  Lemma of_stack_get_type_eq tus tvs (e : expr typ func) t df
    (Ho : open_funcS e = Some of_stack_get) 
    (Hf : exprD' tus tvs t e = Some df) :
    Rty t (tyArr tyString (tyArr (tyArr tyString tyVal) tyVal)).
  Proof.
    destruct e; simpl in *; try congruence.
    autorewrite with exprD_rw in Hf; simpl in Hf; forward; inv_all; subst.
    eapply of_stack_get_func_type_eq; eassumption.
  Qed.

  Lemma of_apply_subst_func_type_eq t u (f : func) (df : typD u) 
    (Ho : open_funcS f = Some (of_apply_subst t)) 
    (Hf : funcAs f u = Some df) :
    Rty u (tyArr (tyArr tyStack t) (tyArr tySubst (tyArr tyStack t))).
  Proof.
    pose proof (of_funcAsOk _ Ho) as H; rewrite H in Hf.
    unfold funcAs in Hf. simpl in Hf. 
    forward; inv_all; subst.
    rewrite <- r. reflexivity.
  Qed.

  Lemma of_apply_subst_type_eq tus tvs (e : expr typ func) t u df
    (Ho : open_funcS e = Some (of_apply_subst t)) 
    (Hf : exprD' tus tvs u e = Some df) :
    Rty u (tyArr (tyArr tyStack t) (tyArr tySubst (tyArr tyStack t))).
  Proof.
    destruct e; simpl in *; try congruence.
    autorewrite with exprD_rw in Hf; simpl in Hf; forward; inv_all; subst.
    eapply of_apply_subst_func_type_eq; eassumption.
  Qed.

  Lemma of_single_subst_func_type_eq t (f : func) (df : typD t) 
    (Ho : open_funcS f = Some of_single_subst) 
    (Hf : funcAs f t = Some df) :
    Rty t (tyArr (tyArr tyStack tyVal) (tyArr tyString tySubst)).
  Proof.
    pose proof (of_funcAsOk _ Ho) as H; rewrite H in Hf.
    unfold funcAs in Hf. simpl in Hf. 
    forward; inv_all; subst.
    rewrite <- r. reflexivity.
  Qed.
  
  Lemma of_single_subst_type_eq tus tvs (e : expr typ func) t df
    (Ho : open_funcS e = Some of_single_subst) 
    (Hf : exprD' tus tvs t e = Some df) :
    Rty t (tyArr (tyArr tyStack tyVal) (tyArr tyString tySubst)).
  Proof.
    destruct e; simpl in *; try congruence.
    autorewrite with exprD_rw in Hf; simpl in Hf; forward; inv_all; subst.
    eapply of_single_subst_func_type_eq; eassumption.
  Qed.

  Lemma of_trunc_subst_func_type_eq t (f : func) (df : typD t) 
    (Ho : open_funcS f = Some of_trunc_subst) 
    (Hf : funcAs f t = Some df) :
    Rty t (tyArr (tyList (tyProd tyString tyExpr)) (tyArr tyString tyExpr)).
  Proof.
    pose proof (of_funcAsOk _ Ho) as H; rewrite H in Hf.
    unfold funcAs in Hf. simpl in Hf. 
    forward; inv_all; subst.
    symmetry. apply r.
  Qed.
  
  Lemma of_trunc_subst_type_eq tus tvs t (e : expr typ func) df
    (Ho : open_funcS e = Some of_trunc_subst) 
    (Hf : exprD' tus tvs t e = Some df) :
    Rty t (tyArr (tyList (tyProd tyString tyExpr)) (tyArr tyString tyExpr)).
  Proof.
    destruct e; simpl in *; try congruence.
    autorewrite with exprD_rw in Hf; simpl in Hf; forward; inv_all; subst.
    eapply of_trunc_subst_func_type_eq; eassumption.
  Qed.
  
  Lemma of_apply_subst_func_eq (t : typ) (f : func) (df : typD (tyArr (tyArr tyStack t) (tyArr tySubst (tyArr tyStack t))))
    (Ho : open_funcS f = Some (of_apply_subst t))
    (Hf : funcAs f (tyArr (tyArr tyStack t) (tyArr tySubst (tyArr tyStack t))) = Some df) :
    df = applySubstD t.
  Proof.
   rewrite (of_funcAsOk _ Ho) in Hf.
   unfold funcAs in Hf; simpl in *.
   rewrite type_cast_refl in Hf; [| apply _].
   unfold Rcast, Relim_refl in Hf.
   inversion Hf. reflexivity.
  Qed.

  Lemma of_apply_subst_eq tus tvs (t : typ) (e : expr typ func)
    (df : ExprI.exprT tus tvs (typD  (tyArr (tyArr tyStack t) (tyArr tySubst (tyArr tyStack t)))))
    (Ho : open_funcS e = Some (of_apply_subst t))
    (Hf : exprD' tus tvs (tyArr (tyArr tyStack t) (tyArr tySubst (tyArr tyStack t))) e = Some df) :
    df = fun us vs => applySubstD t.
  Proof.
   destruct e; simpl in *; try congruence.
   autorewrite with exprD_rw in Hf; simpl in Hf; forward; inv_all; subst.
   erewrite <- of_apply_subst_func_eq; try eassumption; reflexivity.
  Qed.

  Lemma of_ap_func_eq (t u : typ) (f : func) 
    (df : typD (tyArr (tyArr tyStack (tyArr t u)) (tyArr (tyArr tyStack t) (tyArr tyStack u))))
    (Ho : open_funcS f = Some (of_ap t u))
    (Hf : funcAs f (tyArr (tyArr tyStack (tyArr t u)) (tyArr (tyArr tyStack t) (tyArr tyStack u))) = Some df) :
    df = apD t u.
  Proof.
   rewrite (of_funcAsOk _ Ho) in Hf.
   unfold funcAs in Hf; simpl in *.
   rewrite type_cast_refl in Hf; [| apply _].
   unfold Rcast, Relim_refl in Hf.
   inversion Hf. reflexivity.
  Qed.

  Lemma of_ap_eq tus tvs (t u : typ) (e : expr typ func)
    (df : ExprI.exprT tus tvs (typD  (tyArr (tyArr tyStack (tyArr t u)) (tyArr (tyArr tyStack t) (tyArr tyStack u)))))
    (Ho : open_funcS e = Some (of_ap t u))
    (Hf : exprD' tus tvs (tyArr (tyArr tyStack (tyArr t u)) (tyArr (tyArr tyStack t) (tyArr tyStack u))) e = Some df) :
    df = fun us vs => apD t u.
  Proof.
   destruct e; simpl in *; try congruence.
   autorewrite with exprD_rw in Hf; simpl in Hf; forward; inv_all; subst.
   erewrite <- of_ap_func_eq; try eassumption; reflexivity.
  Qed.

  Lemma of_const_func_eq (t : typ) (f : func) 
    (df : typD (tyArr t (tyArr tyStack t)))
    (Ho : open_funcS f = Some (of_const t))
    (Hf : funcAs f (tyArr t (tyArr tyStack t)) = Some df) :
    df = constD t.
  Proof.
   rewrite (of_funcAsOk _ Ho) in Hf.
   unfold funcAs in Hf; simpl in *.
   rewrite type_cast_refl in Hf; [| apply _].
   unfold Rcast, Relim_refl in Hf.
   inversion Hf. reflexivity.
  Qed.

  Lemma of_const_eq tus tvs (t : typ) (e : expr typ func)
    (df : ExprI.exprT tus tvs (typD (tyArr t (tyArr tyStack t))))
    (Ho : open_funcS e = Some (of_const t))
    (Hf : exprD' tus tvs (tyArr t (tyArr tyStack t)) e = Some df) :
    df = fun us vs => constD t.
  Proof.
   destruct e; simpl in *; try congruence.
   autorewrite with exprD_rw in Hf; simpl in Hf; forward; inv_all; subst.
   erewrite <- of_const_func_eq; try eassumption; reflexivity.
  Qed.

  Lemma of_stack_get_func_eq (f : func) 
    (df : typD (tyArr tyString (tyArr tyStack tyVal)))
    (Ho : open_funcS f = Some of_stack_get)
    (Hf : funcAs f (tyArr tyString (tyArr tyStack tyVal)) = Some df) :
    df = stack_getD.
  Proof.
   rewrite (of_funcAsOk _ Ho) in Hf.
   unfold funcAs in Hf; simpl in *.
   rewrite type_cast_refl in Hf; [| apply _].
   unfold Rcast, Relim_refl in Hf.
   inversion Hf. reflexivity.
  Qed.

  Lemma of_stack_get_eq tus tvs (e : expr typ func) 
    (df : ExprI.exprT tus tvs (typD (tyArr tyString (tyArr tyStack tyVal))))
    (Ho : open_funcS e = Some of_stack_get)
    (Hf : exprD' tus tvs (tyArr tyString (tyArr tyStack tyVal)) e = Some df) :
    df = fun us vs => stack_getD.
  Proof.
   destruct e; simpl in *; try congruence.
   autorewrite with exprD_rw in Hf; simpl in Hf; forward; inv_all; subst.
   erewrite <- of_stack_get_func_eq; try eassumption; reflexivity.
  Qed.

  Lemma of_trunc_subst_func_eq (f : func) 
    (df : typD (tyArr (tyList (tyProd tyString tyExpr)) (tyArr tyString tyExpr)))
    (Ho : open_funcS f = Some of_trunc_subst)
    (Hf : funcAs f (tyArr (tyList (tyProd tyString tyExpr)) (tyArr tyString tyExpr)) = Some df) :
    df = truncSubstD.
  Proof.
   rewrite (of_funcAsOk _ Ho) in Hf.
   unfold funcAs in Hf; simpl in *.
   rewrite type_cast_refl in Hf; [| apply _].
   unfold Rcast, Relim_refl in Hf.
   inversion Hf. reflexivity.
  Qed.

  Lemma of_trunc_subst_eq tus tvs (e : expr typ func) 
    (df : ExprI.exprT tus tvs (typD (tyArr (tyList (tyProd tyString tyExpr)) (tyArr tyString tyExpr))))
    (Ho : open_funcS e = Some of_trunc_subst)
    (Hf :exprD' tus tvs (tyArr (tyList (tyProd tyString tyExpr)) (tyArr tyString tyExpr)) e = Some df) :
    df = fun us vs => truncSubstD.
  Proof.
   destruct e; simpl in *; try congruence.
   autorewrite with exprD_rw in Hf; simpl in Hf; forward; inv_all; subst.
   erewrite <- of_trunc_subst_func_eq; try eassumption; reflexivity.
  Qed.

  Lemma of_single_subst_func_eq (f : func) 
    (df : typD  (tyArr (tyArr tyStack tyVal) (tyArr tyString tySubst)))
    (Ho : open_funcS f = Some of_single_subst)
    (Hf : funcAs f (tyArr (tyArr tyStack tyVal) (tyArr tyString tySubst)) = Some df) :
    df = singleSubstD.
  Proof.
   rewrite (of_funcAsOk _ Ho) in Hf.
   unfold funcAs in Hf; simpl in *.
   rewrite type_cast_refl in Hf; [| apply _].
   unfold Rcast, Relim_refl in Hf.
   inversion Hf. reflexivity.
  Qed.

  Lemma of_single_subst_eq tus tvs (e : expr typ func) 
    (df : ExprI.exprT tus tvs (typD (tyArr(tyArr tyStack tyVal) (tyArr tyString tySubst))))
    (Ho : open_funcS e = Some of_single_subst)
    (Hf :exprD' tus tvs (tyArr (tyArr tyStack tyVal) (tyArr tyString tySubst)) e = Some df) :
    df = fun us vs => singleSubstD.
  Proof.
   destruct e; simpl in *; try congruence.
   autorewrite with exprD_rw in Hf; simpl in Hf; forward; inv_all; subst.
   erewrite <- of_single_subst_func_eq; try eassumption; reflexivity.
  Qed.

  Lemma mkNull_sound (tus tvs : tenv typ) :
    exprD' tus tvs tyVal mkNull = Some (fun _ _ => null).
  Proof.
    unfold mkNull; simpl.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    pose proof of_fNullOk as Ho.
    pose proof (of_funcAsOk _ Ho) as H.
    rewrite H.
    unfold funcAs. simpl. 
    rewrite type_cast_refl; [reflexivity | apply _].
  Qed.
  
  Lemma mkConst_sound (tus tvs : tenv typ) (t : typ) (c : expr typ func)
    (dc : ExprI.exprT tus tvs (typD t)) (Hc : exprD' tus tvs t c = Some dc) : 
    exprD' tus tvs (tyArr tyStack t) (mkConst t c) = Some (exprT_App (fun _ _ => constD t) dc).
  Proof.
    unfold mkConst; simpl.
    pose proof (exprD_typeof_Some _ _ _ _ _ Hc) as Htc.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    pose proof (of_fConstOk t) as Ho.
    pose proof (of_funcAsOk _ Ho) as H1.
    rewrite H1.
    unfold funcAs; simpl.
    rewrite type_cast_refl; [reflexivity|apply _].
  Qed. 
   
  Lemma mkAp_sound (tus tvs : tenv typ) (t u : typ) (p q : expr typ func)
    (dp : ExprI.exprT tus tvs (typD (tyArr tyStack (tyArr t u))))
    (dq : ExprI.exprT tus tvs (typD (tyArr tyStack t)))
    (Hp : exprD' tus tvs (tyArr tyStack (tyArr t u)) p = Some dp)
    (Hq : exprD' tus tvs (tyArr tyStack t) q = Some dq) : 
    exprD' tus tvs (tyArr tyStack u) (mkAp t u p q) =
      Some (exprT_App (exprT_App (fun _ _ => apD t u) dp) dq).
  Proof.
    unfold mkAp; simpl.
    pose proof (exprD_typeof_Some _ _ _ _ _ Hp) as Htp.
    pose proof (exprD_typeof_Some _ _ _ _ _ Hq) as Htq.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    pose proof (of_fApOk t u) as Ho.
    pose proof (of_funcAsOk _ Ho) as H3; rewrite H3.
    unfold funcAs; simpl; rewrite type_cast_refl; [reflexivity | apply _].
  Qed.

  Lemma mkApplySubst_sound (tus tvs : tenv typ) (t : typ) (e s : expr typ func)
    (de : ExprI.exprT tus tvs (typD (tyArr tyStack t)))
    (ds : ExprI.exprT tus tvs (typD tySubst))
    (Hs : exprD' tus tvs tySubst s = Some ds)
    (He : exprD' tus tvs (tyArr tyStack t) e = Some de) : 
    exprD' tus tvs (tyArr tyStack t) (mkApplySubst t e s) =
      Some (exprT_App (exprT_App (fun _ _ => applySubstD t) de) ds).
  Proof.
    unfold mkApplySubst; simpl.
    pose proof (exprD_typeof_Some _ _ _ _ _ Hs) as Hts.
    pose proof (exprD_typeof_Some _ _ _ _ _ He) as Hte.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    pose proof (of_fApplySubstOk t) as Ho.
    pose proof (of_funcAsOk _ Ho) as H3; rewrite H3.
    unfold funcAs; simpl; rewrite type_cast_refl; [reflexivity | apply _].
  Qed.

  Lemma mkTruncSubst_sound (tus tvs : tenv typ) (s : expr typ func)
    (ds : ExprI.exprT tus tvs (typD tySubstList))
    (Hs : exprD' tus tvs tySubstList s = Some ds) :
    exprD' tus tvs tySubst (mkTruncSubst s) =
      Some (exprT_App (fun _ _ => truncSubstD) ds).
  Proof.
    unfold mkTruncSubst; simpl.
    pose proof (exprD_typeof_Some _ _ _ _ _ Hs) as Hts.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    pose proof (of_fTruncSubstOk) as Ho.
    pose proof (of_funcAsOk _ Ho) as H3; rewrite H3.
    unfold funcAs; simpl; rewrite type_cast_refl; [reflexivity | apply _].
  Qed.

End MakeOpenSound.
