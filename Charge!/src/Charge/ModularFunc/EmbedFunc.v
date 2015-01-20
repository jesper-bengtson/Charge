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
Require Import Charge.Logics.ILEmbed.
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
	  | Some t0 =>
            match eq_sym (typ2_cast t u) in _ = t return t
            with
              | eq_refl => @embed _ _ _
            end
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
