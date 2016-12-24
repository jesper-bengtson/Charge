Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.
Require Import ExtLib.Data.POption.

Require Import MirrorCore.SymI.
Require Import MirrorCore.CTypes.CoreTypes.
Require Import MirrorCore.CTypes.CTypeUnify.

Require Import ChargeCore.Logics.ILogic.
Require Import ChargeCore.Logics.BILogic.

Require Import Charge.Views.ILogicView.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Inductive bilfunc (typ : Set) : Set :=
  | bilf_emp (logic : typ)
  | bilf_star (logic : typ)
  | bilf_wand (logic : typ).

Definition bilfunc_logic typ (x : bilfunc typ) : typ :=
  match x with
    | bilf_emp t => t
    | bilf_star t => t
    | bilf_wand t => t
  end.

Section BILogicFuncInst.

  Context {typ func : Set}.
  Context {HR : RType typ} {Heq : RelDec (@eq typ)} {HC : RelDec_Correct Heq}.

  Context {Typ2_tyArr : Typ2 _ RFun}.
  Context {Typ0_tyProp : Typ0 _ Prop}.

  Context {Typ2Ok_tyArr : Typ2Ok Typ2_tyArr}.

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.
  Let tyProp : typ := @typ0 _ _ _ _.

  Variable is : logic_ops.

  Definition bilogic_ops := forall (t : typ),
    poption (BILOperators (typD t)).

  Definition bilogic_opsOk (l : bilogic_ops) : Prop :=
    forall g, match is g, l g return Prop with
                | pSome T, pSome U => BILogic (typD g)
                | _, _ => True
              end.

  Variable gs : bilogic_ops.

  Definition typeof_bilfunc (f : bilfunc typ) : option typ :=
    match f with
    | bilf_emp t => match gs t with
  		    | pSome _ => Some t
		    | pNone => None
  		    end
    | bilf_star t
    | bilf_wand t => match gs t with
		     | pSome _ => Some (tyArr t (tyArr t t))
		     | pNone => None
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

 Definition empR t BIL := @empSP (typD t) BIL.
 Definition starR t BIL := castR id (RFun (typD t) (RFun (typD t) (typD t))) (@sepSP (typD t) BIL).
 Definition wandR t BIL := castR id (RFun (typD t) (RFun (typD t) (typD t))) (@wandSP (typD t) BIL).

 Definition funcD (f : bilfunc typ) : match typeof_bilfunc f return Type with
							       | Some t => typD t
							       | None => unit
							      end :=
    match f as f
          return match typeof_bilfunc f return Type with
		   | Some t => typD t
		   | None => unit
		 end
    with
      | bilf_emp t =>
        match gs t as x
          return (match match x with
                          | pSome _ => Some t
                          | pNone => None
                        end with
                    | Some t0 => typD t0
                    | None => unit
                  end) with
        | pSome BIL => empR _ BIL
        | pNone => tt
        end
      | bilf_star t =>
        match gs t as x
              return (match match x with
			      | pSome _ => Some (tyArr t (tyArr t t))
			      | pNone => None
			    end with
			| Some t0 => typD t0
			| None => unit
		      end) with
	  | pSome t => starR _ t
	  | pNone => tt
        end
      | bilf_wand t =>
        match gs t as x
              return (match match x with
			      | pSome _ => Some (tyArr t (tyArr t t))
			      | pNone => None
			    end with
			| Some t0 => typD t0
			| None => unit
		      end) with
	  | pSome t => wandR _ t
	  | pNone => tt
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

Section BILogicUnify.
  Context {typ' : nat -> Set}.
  
  Let typ := ctyp typ'.

  Definition unify_bilfunc (n : nat) (a b : bilfunc typ) (s : FMapPositive.pmap typ) : 
    option (FMapPositive.pmap typ) :=
    match a, b with
    | bilf_emp t, bilf_emp t'
	| bilf_star t, bilf_star t'
	| bilf_wand t, bilf_wand t' => 
	  match ctype_unify _ 1 t t' s with
      | Some (s', _) => Some s'
      | None => None
      end
    | _, _ => None
    end.
    
End BILogicUnify.