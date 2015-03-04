(* All tactics in this file should appear in MirrorCore or ExtLib. *)

Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.Red.
Require Import MirrorCore.Lambda.AppN.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.ExprI.

Require Import ExtLib.Tactics.

Require Import FunctionalExtensionality.

Section Tactics.
  Context {typ func : Type} {RType_typ : RType typ} {RSym_func : RSym func}.
  Context {Typ2_Fun : Typ2 RType_typ Fun}.
    
  Context {RType_typOk : RTypeOk} {RSym_funcOk : RSymOk RSym_func} {Typ2_FunOk : Typ2Ok Typ2_Fun}.

  Local Instance Expr_expr : Expr _ (expr typ func) := Expr_expr (RT := RType_typ).

  Lemma beta_sound (tus tvs : list typ) (t : typ) (e : expr typ func) (df : exprT tus tvs (typD t))
    (H : exprD' tus tvs e t = Some df) :
    exprD' tus tvs (beta e) t = Some df.
  Proof.
    pose proof (beta_sound tus tvs e t).
    simpl in *.
    rewrite H in H0.
    forward; inv_all; subst. 
    f_equal.
    Require Import FunctionalExtensionality.
    do 2 (apply functional_extensionality; intro).
    symmetry; apply H1.
  Qed.

  Lemma Rcast_option_inj (t u : typ) r (a : typD t) (b : typD u)
    (H : Rcast option r (Some a) = Some b) :
    b = Rcast id r a.
  Proof.
    clear -H.
    unfold Rcast, Relim, Rsym, eq_sym in *.
    destruct r; inv_all; subst. reflexivity.
  Qed.

  Lemma Rcast_id t f : 
    Rcast id (Rrefl t) f = f.
  Proof.
    reflexivity.
  Qed.

End Tactics.

Ltac clear_eq := 
  match goal with 
    | H : ?x = ?x |- _ => clear H
  end.
    
Ltac r_inj H :=
  first [
    let H1 := fresh "H" in let H2 := fresh "H" in
      apply typ2_inj in H as [H1 H2]; [unfold Rty in H1, H2; r_inj H1; r_inj H2 | apply _] |
    repeat subst].
  



Ltac destruct_match_oneres :=
    match goal with
      | H : context[match ?x with _ => _ end] |- _ =>
        (destruct x eqn:?; try intuition congruence); [ idtac ]      
      | |- context[match ?x with _ => _ end] =>
        (destruct x eqn:?; try intuition congruence); [ idtac ]     
    end.

Ltac exprD_saturate_types :=
  match goal with
    | H : ExprDsimul.ExprDenote.exprD' ?tus ?tvs ?t ?e = Some _ |- _ =>
      match goal with
        | _ : typeof_expr tus tvs e = Some t |- _ => fail 1
        | H1 : typeof_expr tus tvs e = Some ?u |- _ =>
          let H2 := fresh "H" in
            assert (t = u) as H1 by
              (let H3 := fresh "H" in
                 pose proof (ExprTac.exprD_typeof_Some _ _ _ _ _ H) as H3;
                 rewrite H3 in H1; inv_all; subst; reflexivity);
            subst 
        | _ => pose proof (ExprTac.exprD_typeof_Some _ _ _ _ _ H)
      end
  end. 

Ltac rewrite_in_match :=
  match goal with 
    | [ H : ?x = _ |- context[match ?x with _ => _ end]] => 
       rewrite H
    | [ H : ?x = _, H1 : context[match ?x with _ => _ end] |- _] => 
       rewrite H in H1
  end.

Ltac red_exprD_hyp := 
  repeat (
    match goal with
      |  H : ExprDsimul.ExprDenote.exprD' _ _ _ (apps _ _) = Some _ |- _ =>
        simpl in H
      |  H : ExprDsimul.ExprDenote.exprD' _ _ _ (App _ _) = Some _ |- _ =>
        rewrite exprD'_App in H; simpl in H; (repeat (first [
          rewrite_in_match | 
          destruct_match_oneres])); inv_all; subst
      |  H : ExprDsimul.ExprDenote.exprD' _ _ _ (Inj _) = Some _ |- _ =>
        rewrite exprD'_Inj in H; (try (apply _)); [idtac]; simpl in H; (repeat (first [
          rewrite_in_match | 
          destruct_match_oneres])); inv_all; subst
    end).

Ltac red_exprD_goal := 
  repeat (
    match goal with
      | |- context [ExprDsimul.ExprDenote.exprD' _ _ _ (apps _ _)] =>
        simpl
      | |- ExprDsimul.ExprDenote.exprD' _ _ _ (beta _) = Some _ =>
        apply beta_sound
      | |- context [ExprDsimul.ExprDenote.exprD' _ _ _ (App _ _)] =>
        rewrite exprD'_App; simpl; (repeat rewrite_in_match); inv_all; subst
      | |- context [ExprDsimul.ExprDenote.exprD' _ _ _ (Inj _)] =>
        rewrite exprD'_Inj; simpl; (repeat rewrite_in_match); inv_all; subst; try apply _; try reflexivity
    end).

Ltac Rty_elim :=
  match goal with
    | H : Rcast option _ (Some _) = Some _ |- _ => apply Rcast_option_inj in H; subst
    | H : typ2 _ _ = typ2 _ _ |- _ => r_inj H; clear_eq
    | H : Rty (typ2 _ _) (typ2 _ _) |- _ => r_inj H; clear_eq
    | H : Rty _ _ |- _ => unfold Rty in H; subst
  end.
  
Ltac rewriteD tac := 
  first [
    rewrite tac |
    match goal with
      | |- context [fun x => @?P x] =>
          let H := fresh "H" in 
    	  let t := type of P in evar (H : t);
    	  let x := eval unfold H in H in 
    	  let H1 := fresh "H" in 
    	    assert (P = x) as H1 
    	      by (apply functional_extensionality; intro; rewriteD tac; reflexivity);
    	    rewrite H1; clear H1 H
    end
  ].
  
  
