Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.POption.
Require Import ExtLib.Tactics.Consider.

Require Import MirrorCore.SymI.
Require Import MirrorCore.CTypes.CoreTypes.
Require Import MirrorCore.CTypes.CTypeUnify.

Require Import ChargeCore.Logics.ILogic.
Require Import ChargeCore.Logics.ILEmbed.

Require Import Charge.Views.ILogicView.

Require Import Coq.Bool.Bool.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Inductive embed_func (typ : Set) : Set :=
  | eilf_embed (_ _ : typ).

Section EmbedFuncInst.

  Context {typ func : Set}.
  Context {RType_typ : RType typ} {Heq : RelDec (@eq typ)} {HC : RelDec_Correct Heq}.
  Context {RType_typOk : RTypeOk}.

  Context {Typ2_tyArr : Typ2 _ RFun}.
  Context {Typ0_tyProp : Typ0 _ Prop}.

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.
  Let tyProp : typ := @typ0 _ _ _ _.

  Context {Typ2_tyArrOk : Typ2Ok Typ2_tyArr}.

  Variable is : logic_ops.

  Definition embed_ops := forall (t u : typ),
    option (EmbedOp (typD t) (typD u)).
  Definition embed_opsOk (es : embed_ops) : Prop :=
    forall t t',
      match is t , is t' , es t t' return Prop with
        | pSome a , pSome b , Some T => @Embed _ a _ _ T
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

 Definition embedD t u (EIL : EmbedOp (typD t) (typD u)) :=
   castR id (RFun (typD t) (typD u)) (@embed _ _ EIL).

 Definition funcD (f : embed_func typ) : match typeof_embed_func f return Type with
					 | Some t => typD t
					 | None => unit
					 end :=
   match f as f
         return match typeof_embed_func f return Type with
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

  Definition eil_pointwise := typ -> typ -> bool.

End EmbedFuncInst.

Section BILogicUnify.
  Context {typ' : nat -> Set}.
  
  Let typ := ctyp typ'.

  Definition embed_func_unify (a b : embed_func typ) (s : FMapPositive.pmap typ) : 
    option (FMapPositive.pmap typ) :=
    match a, b with
	| eilf_embed t u, eilf_embed t' u' => 
      match ctype_unify_slow _ t t' s with
      | Some s' => ctype_unify_slow _ u u' s'
      | None => None
      end
    end.
    
End BILogicUnify.
