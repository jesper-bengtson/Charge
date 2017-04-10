Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Map.FMapPositive.
Require Import ExtLib.Data.SumN.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Data.POption.
Require Import ExtLib.Tactics.
Require Import ExtLib.Tactics.Consider.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.syms.SymEnv.
Require Import MirrorCore.syms.SymSum.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.Ptrns.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.Reify.ReifyClass.

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

Section MakeEmbed.

  Context {typ func : Set} {FV : PartialView func (embed_func typ)}.

  Definition fEmbed t u := f_insert (eilf_embed t u).

  Definition mkEmbed (t u : typ) (p : expr typ func): expr typ func :=
    App (Inj (fEmbed t u)) p.

  Definition fptrnEmbed {T : Type} (p : Ptrns.ptrn (typ * typ) T) : ptrn (embed_func typ) T :=
    fun f U good bad =>
      match f with
        | eilf_embed t u => p (t, u) U good (fun x => bad f)
      end.

  Global Instance fptrnEmbed_ok {T : Type} {p : ptrn (typ * typ) T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnEmbed p).
  Proof.
    red; intros.
    destruct x; try (right; unfold Fails; reflexivity); destruct (Hok (t, t0)).
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
  Qed.

  Lemma Succeeds_fptrnEmbed {T : Type} (f : embed_func typ) (p : ptrn (typ * typ) T) (res : T)
        {pok : ptrn_ok p} (H : Succeeds f (fptrnEmbed p) res) :
    exists t u, Succeeds (t, u) p res /\ f = eilf_embed t u.
  Proof.
    unfold Succeeds, fptrnEmbed in H.
    unfold ptrn_ok in pok.
    specialize (H (option T) Some (fun _ => None)).
    destruct f; try congruence.
    specialize (pok (t, t0)).
    destruct pok; [|rewrite H0 in H; congruence].
    destruct H0.
    rewrite H0 in H; inv_all; subst.
    exists t, t0; split; [assumption | reflexivity].
  Qed.

  Global Instance fptrnEmbed_SucceedsE {T : Type} {f : embed_func typ}
         {p : ptrn (typ * typ) T} {res : T} {pok : ptrn_ok p} :
    SucceedsE f (fptrnEmbed p) res := {
      s_result := exists t u, Succeeds (t, u) p res /\ f = eilf_embed t u;
      s_elim := @Succeeds_fptrnEmbed T f p res pok
    }.

End MakeEmbed.

Section EmbedPtrn.
  Context {typ func : Set} {FV : PartialView func (embed_func typ)}.

  Definition ptrnEmbed {A T : Type}
             (p : ptrn (typ * typ) T)
             (a : ptrn (expr typ func) A) : ptrn (expr typ func) (T * A) :=
    app (inj (ptrn_view _ (fptrnEmbed p))) a.

End EmbedPtrn.

Section ReifyEmbed.
  Context {typ func : Set} {FV : PartialView func (embed_func typ)}.
  Context {t : Reify typ}.

  Definition reify_eilf_embed : Command (expr typ func) :=
    CPattern (ls := (typ:Type)::(typ:Type)::nil)
             (RApp (RApp (RApp (RExact (@embed)) (RGet 0 RIgnore)) (RGet 1 RIgnore)) RIgnore)
             (fun (x y : function (CCall (reify_scheme typ))) => Inj (fEmbed x y)).

  Definition reify_embed : Command (expr typ func) :=
    CFirst (reify_eilf_embed :: nil).

End ReifyEmbed.

Arguments reify_embed _ _ {_ _}.