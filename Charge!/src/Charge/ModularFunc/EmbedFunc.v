Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Data.Bool.
Require Import ExtLib.Data.String.
Require Import ExtLib.Tactics.
Require Import ExtLib.Tactics.Consider.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.syms.SymEnv.
Require Import MirrorCore.syms.SymSum.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.SymI.

Require Import Charge.Logics.ILogic.
Require Import Charge.Logics.ILEmbed.
Require Import Charge.ModularFunc.Denotation.
Require Import Charge.ModularFunc.ILogicFunc.

Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.


Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Inductive embed_func typ :=
  | eilf_embed (_ _ : typ).
    
Class EmbedFunc (typ func : Type) := {
  fEmbed : typ -> typ -> func;
  embedS : func -> option (embed_func typ)
}.
    
Section EmbedFuncSum.
	Context {typ func : Type} {H : EmbedFunc typ func}.

	Global Instance EmbedFuncSumL (A : Type) : 
	   EmbedFunc typ (func + A) := {
		  fEmbed t u := inl (fEmbed t u);
		  embedS f := match f with
		  				| inl f => embedS f
		  				| inr _ => None
		  			  end
       }.

	Global Instance EmbedFuncSumR (A : Type) : 
		EmbedFunc typ (A + func) := {
		  fEmbed t u := inr (fEmbed t u);
		  embedS f := match f with
		  				| inr f => embedS f
		  				| inl _ => None
		  			  end
       }.

	Global Instance EmbedFuncExpr : 
		EmbedFunc typ (expr typ func) := {
		  fEmbed t u := Inj (fEmbed t u);
		  embedS f := match f with
		  				| Inj f => embedS f
		  				| _ => None
		  			  end
        }.

End EmbedFuncSum.

Section EmbedFuncInst.

	Context {typ func : Type} {H : EmbedFunc typ func}.
	Context {HR : RType typ} {Heq : RelDec (@eq typ)} {HC : RelDec_Correct Heq}.

    Variable Typ2_tyArr : Typ2 _ Fun.
    Variable Typ0_tyProp : Typ0 _ Prop.

    Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.
    Let tyProp : typ := @typ0 _ _ _ _.

	Global Instance EmbedFuncInst : EmbedFunc typ (embed_func typ) := {
	  fEmbed := eilf_embed;
	  embedS f := Some f
	}.
	
  Variable is : logic_ops.

 
  Definition embed_ops := forall (t u : typ),
    option (EmbedOp (typD t) (typD u)).
  Definition embed_opsOk (es : embed_ops) : Prop :=
    forall t t',
      match is t , is t' , es t t' return Prop with
        | Some a , Some b , Some T => @Embed _ a _ _ T
        | _ , _ , _ => True
      end.

  Variable gs : embed_ops.
  
  Definition typeof_embed_func (f : embed_func typ) : option typ :=
    match f with
      | eilf_embed t u => match gs t u with
				  	        | Some _ => Some (tyArr t u)
				  	        | None => None
				  	      end
  	end.

  Global Instance RelDec_embed_func : RelDec (@eq (embed_func typ)) :=
  { rel_dec := fun a b =>
	         match a, b with
	  	       | eilf_embed t u, eilf_embed t' u' => (t ?[eq] t' && u ?[ eq ] u')%bool
	         end
  }.

  Global Instance RelDec_Correct_embed_func : RelDec_Correct RelDec_embed_func.
  Proof.
    constructor.
    destruct x; destruct y; simpl; rewrite andb_true_iff;
    repeat rewrite rel_dec_correct; intuition congruence.
  Qed.

 Definition embedD t u (EIL : EmbedOp (typD t) (typD u)) := fun_to_typ (@embed _ _ EIL).

 Definition funcD (f : embed_func typ) : match typeof_embed_func f with
							              | Some t => typD t
							              | None => unit
							             end :=
    match f as f
          return match typeof_embed_func f with
		   | Some t => typD t
		   | None => unit
		 end
    with
      | eilf_embed t u =>
        match gs t u as x
              return match match x with
			     | Some _ => Some (tyArr t u)
			     | None => None
			   end with
		       | Some t0 => typD t0
		       | None => unit
		     end
        with
	  | Some t0 => embedD t u t0
	  | None => tt
        end
    end.

  Global Instance RSym_embed_func : SymI.RSym (embed_func typ) :=
  { typeof_sym := typeof_embed_func
  ; sym_eqb := fun a b => Some (rel_dec a b)
  ; symD := funcD
  }.

  Global Instance RSymOk_embed_func : SymI.RSymOk RSym_embed_func.
  Proof.
    constructor.
    intros. unfold sym_eqb; simpl.
    consider (a ?[ eq ] b); auto.
  Qed.

End EmbedFuncInst.

Section MakeEmbed.
	Context {typ func : Type} {H : EmbedFunc typ func}.

	Definition mkEmbed (t u : typ) P := App (fEmbed t u) P.

End MakeEmbed.

Section EmbedFuncOk.
  Context {typ func : Type} {HO: EmbedFunc typ func}.
  Context {RType_typ : RType typ} {RSym_func : RSym func}.
  Context {RelDec_eq : RelDec (@eq typ)}.

  Context {Typ2_tyArr : Typ2 _ Fun}.
  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.
  
  Variable gs : embed_ops.
  
  Class EmbedFuncOk := {
    eilf_funcAsOk (f : func) e : embedS f = Some e -> 
      forall t, funcAs f t = funcAs (RSym_func := RSym_embed_func _ gs) e t;
    eilf_fEmbedOk t u : embedS (fEmbed t u) = Some (eilf_embed t u)
  }.

End EmbedFuncOk.

Implicit Arguments EmbedFuncOk [[HO] [RType_typ] [RSym_func] [RelDec_eq] [Typ2_tyArr]].

Section EmbedFuncBaseOk.
  Context {typ func : Type} {HO: EmbedFunc typ func}.
  Context {RType_typ : RType typ} {RSym_func : RSym func}.
  Context {RelDec_eq : RelDec (@eq typ)}.

  Context {Typ2_tyArr : Typ2 _ Fun}.
  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.
  
  Variable gs : embed_ops.

  Global Program Instance EmbedFuncBaseOk : EmbedFuncOk (RSym_func := RSym_embed_func _ gs) typ (embed_func typ) gs := {
    eilf_funcAsOk := fun _ _ _ _ => eq_refl;
    eilf_fEmbedOk t u := eq_refl
  }.

End EmbedFuncBaseOk.

Section EmbedFuncExprOk.
  Context {typ func : Type} `{HOK : EmbedFuncOk typ func}.
  Context {HROk : RTypeOk}.
  Context {A : Type} {RSymA : RSym A}.

  Lemma BILogicFunc_typeOk (f : func) (e : embed_func typ) (H : embedS f = Some e) :
    typeof_sym f = typeof_embed_func _ gs e.
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
  (*
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
  *)
  Lemma eilf_embed_type_eq (f : func) t u v df
    (H1 : embedS f = Some (eilf_embed t u)) (H2 : funcAs f v = Some df) :
    v = typ2 t u.
  Proof.
    rewrite (eilf_funcAsOk _ H1) in H2.
    unfold funcAs in H2. simpl in *.
    
    
    forward. 
  Qed.

  Existing Instance RSym_sum.

  Global Program Instance EmbedFuncOkSumR : EmbedFuncOk typ ((A + func)%type) gs := {
    eilf_funcAsOk := 
      fun a f H t => 
        match a with
          | inl b => _
          | inr b => _
        end;
    eilf_fEmbedOk t u := eilf_fEmbedOk (func := func) t u
  }.
  Next Obligation.
    apply (eilf_funcAsOk (func := func)).
    apply H.
  Qed.

  Global Program Instance EmbedFuncOkSumL : EmbedFuncOk typ ((func + A)%type) gs := {
    eilf_funcAsOk := 
      fun a f H t => 
        match a with
          | inl b => _
          | inr b => _
        end;
    eilf_fEmbedOk t u := eilf_fEmbedOk (func := func) t u
  }.
  Next Obligation.
    apply (eilf_funcAsOk (func := func)).
    apply H.
  Qed.

End EmbedFuncExprOk.

Section MakeEmbedSound.
  Context {typ func : Type} `{HOK : EmbedFuncOk typ func}.
  Context {HROk : RTypeOk} {Typ2_tyArrOk : Typ2Ok Typ2_tyArr}
          {RSym_funcOk : RSymOk RSym_func0}.

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.

  Lemma mkEmbed_sound (t u : typ) (tus tvs : tenv typ) p EIL
    (dp: ExprI.exprT tus tvs (typD t))
    (Hgs : gs t u = Some EIL)
    (Hp : exprD' tus tvs t p = Some dp) :
    exprD' tus tvs u (mkEmbed t u p) = Some (exprT_App (fun _ _ => embedD _ _ _ EIL) dp).
  Proof.
    unfold mkEmbed; simpl.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ p _ Hp).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    pose proof (eilf_fEmbedOk t u) as Ho.
    pose proof (eilf_funcAsOk _ Ho) as H1.
    rewrite H1. unfold funcAs; simpl.
    rewrite Hgs. rewrite type_cast_refl; [reflexivity | apply _].
  Qed.

End MakeEmbedSound.
  
