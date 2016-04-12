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

Require Import ChargeCore.Logics.ILogic.
Require Import ChargeCore.Logics.ILEmbed.

Require Import Charge.Views.ILogicView.

Require Import Coq.Bool.Bool.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Inductive embed_func typ :=
  | eilf_embed (_ _ : typ).

Section EmbedFuncInst.

  Context {typ func : Type}.
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
(*
  Definition eil_pointwiseOk (eilp : eil_pointwise) :=
    forall t u,
      typ2_simple_match t
        (fun dt rt : typ =>
          typ2_simple_match u
            (fun du ru : typ =>
              match type_cast dt du with
                | Some pf =>
                  match gs (tyArr dt rt) (tyArr dt ru), gs rt ru with
                    | Some EOps1, Some EOps2 =>
                      forall (P : typD dt -> typD rt) (a : typD dt),
                        tyArrD (embed (tyArrR P)) a = embed (P a)
                    | _, _ => False
                  end
                | _ => False
              end)
            True)
        True.
 
  Lemma eil_pointwise_embed (eilp : eil_pointwise) (eilpOk : eil_pointwiseOk eilp) (t u v w : typ) 
  	(H : eilp (tyArr t u) (tyArr v w) = true) : exists EIL, gs (tyArr t u) (tyArr v w) = Some EIL. 
  Proof.
    specialize (eilpOk (tyArr t u) (tyArr v w)).
    unfold tyArr in eilpOk.
    do 2 rewrite typ2_simple_match_iota in eilpOk.
    forward.
    unfold Rty in r. subst.
    exists e. assumption.
  Qed.

  Lemma eil_pointwise_embed_range (eilp : eil_pointwise) (eilpOk : eil_pointwiseOk eilp) (t u v w : typ) (H : eilp (tyArr t u) (tyArr v w) = true) : exists EIL, gs u w = Some EIL. 
  Proof.
    specialize (eilpOk (tyArr t u) (tyArr v w)).
    unfold tyArr in *.
    do 2 rewrite typ2_simple_match_iota in eilpOk.
    forward.
    exists e0. reflexivity.
  Qed.
  
  Lemma eilf_pointwise_embed_eq (eilp : eil_pointwise) (eilpOk : eil_pointwiseOk eilp) (t u v : typ) (H : eilp (tyArr t u) (tyArr t v) = true) EIL1 EIL2
    (gstu : gs (tyArr t u) (tyArr t v) = Some EIL1) (gsu : gs u v = Some EIL2) (a : typD (tyArr t u)) s :
    (tyArrD (embed a)) s = embed (tyArrD a s).
  Proof.
    specialize (eilpOk (tyArr t u) (tyArr t v)).
    unfold tyArr in *.
    do 2 rewrite typ2_simple_match_iota in eilpOk.
    rewrite type_cast_refl in eilpOk.
    rewrite gstu, gsu in eilpOk. rewrite <- eilpOk, tyArrRD. reflexivity.
    apply _.
  Qed.    
  
  Lemma eilf_pointwise_embed_eq2 (eilp : eil_pointwise) (eilpOk : eil_pointwiseOk eilp) (t u v : typ) (H : eilp (tyArr t u) (tyArr t v) = true) EIL1 EIL2
    (gstu : gs (tyArr t u) (tyArr t v) = Some EIL1) (gsu : gs u v = Some EIL2) (a : typD t -> typD u) :
    tyArrR (fun s => embed (a s)) = embed (tyArrR a).
  Proof.
    specialize (eilpOk (tyArr t u) (tyArr t v)).
    unfold tyArr in *.
    do 2 rewrite typ2_simple_match_iota in eilpOk.
    rewrite type_cast_refl in eilpOk; [|apply _].
    rewrite gstu, gsu in eilpOk.
    symmetry in eilpOk.
    Require Import Charge.Tactics.Base.MirrorCoreTacs.
    rewriteD eilpOk. rewrite tyArrRD. reflexivity.
  Qed.    
*)

End EmbedFuncInst.

Section MakeEmbed.

  Context {typ func : Type} {FV : PartialView func (embed_func typ)}.

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
  Context {typ func : Type} {FV : PartialView func (embed_func typ)}.
  
  Definition ptrnEmbed {A T : Type}
             (p : ptrn (typ * typ) T)
             (a : ptrn (expr typ func) A) : ptrn (expr typ func) (T * A) :=
    app (inj (ptrn_view _ (fptrnEmbed p))) a.

End EmbedPtrn.