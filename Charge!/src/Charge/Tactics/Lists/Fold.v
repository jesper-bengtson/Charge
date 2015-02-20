Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.AppN.
Require Import MirrorCore.Lambda.Red.
Require Import MirrorCore.Lambda.RedAll.
Require Import MirrorCore.RTac.Simplify.

Require Import Charge.ModularFunc.BaseFunc.
Require Import Charge.ModularFunc.ListFunc.
Require Import Charge.ModularFunc.ListType.

Section Fold.
  Context {typ func : Type} {RType_typ : RType typ}.
  Context {LT : ListType typ} {LTD : ListTypeD}. 
  Context {BF : BaseFunc typ func} {LF: ListFunc typ func}.
  Context {RSym_func : RSym func}.
  Context {Typ2_Fun : Typ2 RType_typ Fun}.

  Context {RTypeOk_typ : RTypeOk}.
  Context {RSymOk_func : RSymOk RSym_func}.
  Context {Typ2Ok_Fun : Typ2Ok Typ2_Fun}.

  Definition foldTac (e : expr typ func) (args : list (expr typ func)) : expr typ func :=
    match listS e with
      | Some (pFold t u) =>
        match args with
          | f :: acc :: lst :: nil =>
            match baseS lst with
              | Some (pConst v lst) => 
		  	    match type_cast v (tyList u) with
		  	      | Some pf => 
                    fold_right (fun x acc => beta (beta (App (App f (mkConst u x)) acc))) acc 
                       (listD _ (eq_rect _ typD lst _ pf))
		  	      | None => apps e args
		  	    end
              | _ => apps e args
            end
          | _ => apps e args
        end
      | _ => apps e args
    end.

  Definition FOLD := SIMPLIFY (typ := typ) (fun _ _ _ _ => (beta_all (fun _ => foldTac))).

Require Import ExtLib.Tactics.

  Lemma foldTacOk : partial_reducer_ok foldTac.
  Proof.
    unfold partial_reducer_ok; intros.
    unfold foldTac.
    remember (listS e); destruct o; [| exists val; tauto].
    destruct l; try (exists val; tauto).
    destruct es; try (exists val; tauto).
    destruct es; try (exists val; tauto).
    destruct es; try (exists val; tauto).
    destruct es; try (exists val; tauto).
    remember (baseS e2); destruct o; try (exists val; tauto).
    destruct b; try (exists val; tauto).
    remember (type_cast t2 (tyList t1)).
    destruct o; [|exists val; tauto].
    simpl in H.
    autorewrite with exprD_rw in H; simpl in H; forward; inv_all; subst.
    autorewrite with exprD_rw in H0; simpl in H0; forward; inv_all; subst.
    autorewrite with exprD_rw in H2; simpl in H2; forward; inv_all; subst.
    
    
    Opaque beta.
    
    unfold Rty in r.
    subst.
    
    unfold eq_rect.
    
    
    unfold ExprDsimul.ExprDenote.exprT_App, eq_sym. simpl.
    
    autorewrite with exprD_rw in H1; simpl in H1; forward; inv_all; subst.
    autorewrite with exprD_rw in H4; simpl in H4; forward; inv_all; subst.
    autorewrite with exprD_rw in H2; simpl in H2; forward; inv_all; subst.
    
    unfold Rty in r. subst.
    
    unfold type_cast in Heqo1. simpl in Heqo1.
    SearchAbout type_cast.
    
    destruct e2; try (exists val; tauto).
    destruct f; try (exists val; tauto).
    
    destruct j; try (exists val; tauto).
    destruct es; try (exists val; tauto).
    destruct e; simpl in Heqo; try congruence.
    destruct f; simpl in Heqo; try congruence.
    destruct s; simpl in Heqo; try congruence.
    destruct s; simpl in Heqo; try congruence.
    destruct s; simpl in Heqo; try congruence.
    destruct s; simpl in Heqo; try congruence.
    inv_all; subst.
    autorewrite with exprD_rw in H; simpl in H; forward; inv_all; subst.
    autorewrite with exprD_rw in H; simpl in H; forward; inv_all; subst; [|apply _].
    autorewrite with exprD_rw in H; simpl in H; forward; inv_all; subst; [|apply _].
    autorewrite with exprD_rw in H0; simpl in H0; forward; inv_all; subst; [|apply _].
    autorewrite with exprD_rw in H2; simpl in H2; forward; inv_all; subst; [|apply _].
    unfold funcAs in H2. 
    Opaque type_cast.
    simpl in H2. forward; inv_all; subst. red in r. inv_all.
    inversion r; subst.
    rewrite (UIP_refl r) in H4. unfold Rcast in H4; simpl in H4.
    inversion H4; unfold eq_rect_r in H6; simpl in H6.
    subst. clear H4.
    clear H2 r.
    Opaque beta.
    simpl.
    unfold exprT_App, eq_rect_r. simpl.
    cut (exists val' : exprT tus tvs (typD t),
  ExprDsimul.ExprDenote.exprD' tus tvs t
    (fold_right
       (fun (x : string) (acc : expr typ func) =>
        beta (beta (App (App e0 (mkString x)) acc))) e1 l) = Some val' /\
  (forall (us : hlist typD tus) (vs : hlist typD tvs),
   fold_right (e4 us vs) (e3 us vs) (exprT_Inj tus tvs l us vs) = val' us vs)).
   intros [? [? ?]].
   eexists; split; [eassumption | intros; apply H4].
    induction l; simpl; intros.

    + exists e3; tauto.
    + destruct IHl as [? [? ?]].
      eexists; split; [|intros; reflexivity].

  Lemma exprD'_remove_beta tus tvs t e de (H : exprD' tus tvs e t = Some de) :
    exprD' tus tvs (beta e) t = Some de.
  Proof.
    pose proof (beta_sound tus tvs e t).
    unfold exprD' in *. simpl in *. forward; inv_all; subst.
	Require Import FunctionalExtensionality.
	f_equal. symmetry.
    apply functional_extensionality; intros.
    apply functional_extensionality; intros.
    apply H2.
  Qed.

End Fold.