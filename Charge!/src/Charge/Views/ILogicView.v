Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Data.Bool.
Require Import ExtLib.Data.String.
Require Import ExtLib.Data.POption.
Require Import ExtLib.Data.Map.FMapPositive.
Require Import ExtLib.Data.SumN.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Tactics.
Require Import ExtLib.Tactics.Consider.

Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.syms.SymEnv.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.Ptrns.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.TCLemma.
Require Import MirrorCore.PLemma.
Require Import MirrorCore.Polymorphic.
Require Import MirrorCore.syms.SymSum.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.Reify.ReifyClass.
Require Import MirrorCore.Reify.Reify.
Require Import MirrorCore.Reify.ReifyView.

Require Import MirrorCore.Lambda.RewriteRelations.
Require Import MirrorCore.Lambda.Rewrite.Respectful.
Require Import MirrorCore.Lambda.Rewrite.Core.
Require Import MirrorCore.Lambda.Rewrite.HintDbs.
Require Import MirrorCore.Lambda.PolyInst.

Require Import MirrorCore.CTypes.CTypeUnify.
Require Import MirrorCore.CTypes.CoreTypes.
Require Import MirrorCore.CTypes.BaseType.

Require Import ChargeCore.Logics.ILogic.

Require Import Charge.Tactics.Rtac.EApply.

Require Import Coq.Bool.Bool.


Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Inductive ilfunc (typ : Set) : Set :=
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

Section ILogicFuncInst.  
  Context {typ : Set}.
  
  Context {HR : RType typ} {Heq : RelDec (@eq typ)} {HC : RelDec_Correct Heq}.

  Context {Typ2_tyArr : Typ2 _ RFun}.
  Context {Typ0_tyProp : Typ0 _ Prop}.

  Context {Typ2Ok_tyArr : Typ2Ok Typ2_tyArr}.

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.
  Let tyProp : typ := @typ0 _ _ _ _.

  Definition logic_ops := forall (t : typ),
    poption (ILogicOps (typD t)).
    
  Definition logic_opsOk (l : logic_ops) : Prop :=
    forall g, match l g return Prop with
                | pSome T => @ILogic _ T
                | pNone => True
              end.

  Variable gs : logic_ops.

  Definition typeof_ilfunc (f : ilfunc typ) : option typ :=
    match f with
    | ilf_true t
    | ilf_false t => match gs t with
  		     | pSome _ => Some t
		     | pNone => None
  		     end
    | ilf_entails t => match gs t with
		       | pSome _ => Some (tyArr t (tyArr t tyProp))
		       | pNone => None
		       end
    | ilf_and t
    | ilf_or t
    | ilf_impl t => match gs t with
		    | pSome _ => Some (tyArr t (tyArr t t))
		    | pNone => None
		    end
    | ilf_forall a t
    | ilf_exists a t => match gs t with
			| pSome _ => Some (tyArr (tyArr a t) t)
			| pNone => None
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

 Definition trueR {t : typ} {IL : ILogicOps (typD t)} := @ltrue (typD t) IL.
 Definition falseR {t : typ} {IL : ILogicOps (typD t)} := @lfalse (typD t) IL.
 Definition andR {t : typ} {IL : ILogicOps (typD t)} :=
   castR id (RFun (typD t) (RFun (typD t) (typD t))) (@land (typD t) IL).
 Definition orR {t : typ} {IL : ILogicOps (typD t)} :=
   castR id (RFun (typD t) (RFun (typD t) (typD t))) (@lor (typD t) IL).
 Definition implR {t : typ} {IL : ILogicOps (typD t)} :=
   castR id (RFun (typD t) (RFun (typD t) (typD t))) (@limpl (typD t) IL).
 Definition entailsR {t : typ} {IL : ILogicOps (typD t)} :=
   castR id (RFun (typD t) (RFun (typD t) Prop)) (@lentails (typD t) IL).
 Definition existsR {t u : typ} {IL : ILogicOps (typD t)} :=
   castR id (RFun (RFun (typD u) (typD t)) (typD t)) (@lexists (typD t) IL (typD u)).
 Definition forallR {t u : typ} {IL : ILogicOps (typD t)} :=
   castR id (RFun (RFun (typD u) (typD t)) (typD t)) (@lforall (typD t) IL (typD u)).
 
 Arguments trueR {_ _}.
 Arguments andR {_ _}.
 Arguments orR {_ _}.
 Arguments implR {_ _}.
  
 Definition funcD (f : ilfunc typ) : match typeof_ilfunc f return Type with
				     | Some t => typD t
				     | None => unit
				     end :=
   match f as f
         return match typeof_ilfunc f return Type with
		| Some t => typD t
		| None => unit
		end
   with
   | ilf_true t => match gs t as x return (match match x with
						 | pSome _ => Some t
						 | pNone => None
						 end with
				           | Some t0 => typD t0
					   | None => unit
					   end) with
		   | pSome t => @ltrue _ t
		   | pNone => tt
		   end
   | ilf_false t =>
     match gs t as x
           return (match match x with
			 | pSome _ => Some t
			 | pNone => None
			 end with
		   | Some t0 => typD t0
		   | None => unit
		   end) with
     | pSome t => lfalse
     | pNone => tt
     end
   | ilf_entails t =>
     match gs t as x
           return (match match x with
			 | pSome _ => Some (tyArr t (tyArr t tyProp))
			 | pNone => None
			 end with
		   | Some t0 => typD t0
		   | None => unit
		   end) with
     | pSome t => entailsR
     | pNone => tt
     end
   | ilf_and t =>
     match gs t as x
           return (match match x with
			 | pSome _ => Some (tyArr t (tyArr t t))
			 | pNone => None
			 end with
		   | Some t0 => typD t0
		   | None => unit
		   end) with
     | pSome t => andR
     | pNone => tt
     end
   | ilf_impl t =>
     match gs t as x
           return (match match x with
			 | pSome _ => Some (tyArr t (tyArr t t))
			 | pNone => None
			 end with
		   | Some t0 => typD t0
		   | None => unit
		   end) with
     | pSome t => implR
     | pNone => tt
     end
   | ilf_or t =>
     match gs t as x
           return (match match x with
			 | pSome _ => Some (tyArr t (tyArr t t))
			 | pNone => None
			 end with
		   | Some t0 => typD t0
		   | None => unit
		   end) with
     | pSome t => orR
     | pNone => tt
     end
   | ilf_exists a t =>
     match gs t as x return (match match x with
				   | pSome _ => Some (tyArr (tyArr a t) t)
				   | pNone => None
				   end with
			     | Some t0 => typD t0
			     | None => unit
			     end) with
     | pSome t0 => existsR
     | pNone => tt
     end
   | ilf_forall a t =>
     match gs t as x return (match match x with
				   | pSome _ => Some (tyArr (tyArr a t) t)
				   | pNone => None
				   end with
			     | Some t0 => typD t0
			     | None => unit
			     end) with
     | pSome t0 => forallR
     | pNone => tt
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

Section ILogicUnify.
  Context {typ' : nat -> Set}.
  
  Let typ := ctyp typ'.

  Definition unify_ilfunc (n : nat) (a b : ilfunc typ) (s : FMapPositive.pmap typ) : 
    option (FMapPositive.pmap typ) :=
    match a, b with
    | ilf_entails t, ilf_entails t'
    | ilf_true t, ilf_true t'
 	| ilf_false t, ilf_false t'
	| ilf_and t, ilf_and t'
	| ilf_or t, ilf_or t'
	| ilf_impl t, ilf_impl t' => 
	  match ctype_unify _ 1 t t' s with
      | Some (s', _) => Some s'
      | None => None
      end
	| ilf_forall a t, ilf_forall a' t'
	| ilf_exists a t, ilf_exists a' t' => 
      match ctype_unify _ n a a' s with
      | Some (s', _) =>
        match ctype_unify _ n t t' s' with
        | Some (s'', _) => Some s''
        | None => None
        end
      | None => None
      end
    | _, _ => None
    end.
    
End ILogicUnify.