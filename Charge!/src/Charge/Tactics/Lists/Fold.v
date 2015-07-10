Require Import Charge.ModularFunc.BaseFunc.
Require Import Charge.ModularFunc.ListFunc.
Require Import Charge.ModularFunc.BaseType.
Require Import Charge.ModularFunc.ListType.
Require Import Charge.ModularFunc.SemiEqDecTyp.
Require Import Charge.ModularFunc.Denotation.

Require Import Charge.Tactics.Lists.ListTacs.
Require Import Charge.Tactics.Base.MirrorCoreTacs.
Require Import Charge.Tactics.Base.DenotationTacs.

Require Import ExtLib.Core.RelDec.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.AppN.
Require Import MirrorCore.Lambda.Red.
Require Import MirrorCore.Lambda.RedAll.
Require Import MirrorCore.Lambda.Expr.

Require Import MirrorCore.RTac.Simplify.
Section Fold.
  Context {typ func : Type} {RType_typ : RType typ} {RSym_func : RSym func}.
  Context {BT : BaseType typ} {BTD : BaseTypeD BT}.
  Context {LT : ListType typ} {LTD : ListTypeD LT}. 
  Context {BF : BaseFunc typ func} {LF: ListFunc typ func}.
  Context {Heq : RelDec (@eq typ)} {HC : RelDec_Correct Heq}.
  Context {Heqd : SemiEqDecTyp typ} {HeqdOk : SemiEqDecTypOk Heqd}.
  Context {Typ2_Fun : Typ2 RType_typ Fun}.
  Context {Typ0_Prop : Typ0 RType_typ Prop}.
  
  Context {BFOk : BaseFuncOk typ func} {LFOk : ListFuncOk typ func}.

  Context {RTypeOk_typ : RTypeOk}.
  Context {RSymOk_func : RSymOk RSym_func}.
  Context {Typ2Ok_Fun : Typ2Ok Typ2_Fun}.

  Definition foldTac (e : expr typ func) (args : list (expr typ func)) : expr typ func :=
    match listS e with
      | Some (pFold t u) =>
        match args with
          | f :: acc :: lst :: nil =>
	         let (lst', e') := expr_to_list lst in
		  	      match listS e' with
		  	        | Some (pNil v) =>
		  	          match type_cast u v with
		  	            | Some pf => fold_right (fun x acc => beta (beta (App (App f x) acc))) acc lst'
		  	            | _ => fold_right (fun x acc => beta (beta (App (App f x) acc))) (apps e (f::acc::e'::nil)) lst'
		  	          end
		  	        | _ =>
		  	          fold_right (fun x acc => beta (beta (App (App f x) acc))) (apps e (f::acc::e'::nil)) lst'
		  	      end
          | _ => apps e args
        end
      | _ => apps e args
    end.

  Definition FOLD := SIMPLIFY (typ := typ) (fun _ _ _ _ => (beta_all (fun _ => foldTac))).

(*
  Lemma exprD_fold_const tus tvs (t u : typ) (f acc : expr typ func) (lst : list (typD u))
    (fD : exprT tus tvs (typD (typ2 u (typ2 t t)))) (accD : exprT tus tvs (typD t)) 
    (Hf : ExprDsimul.ExprDenote.exprD' tus tvs (typ2 u (typ2 t t)) f = Some fD)
    (Hacc : ExprDsimul.ExprDenote.exprD' tus tvs t acc = Some accD) :
    ExprDsimul.ExprDenote.exprD' tus tvs
      t (fold_right (fun x acc => beta (beta (App (App f (mkConst u x)) acc))) acc lst) =
    Some
      (fun us vs => fold_right (tyArrD2 (fD us vs)) (accD us vs) lst).
  Proof.
    admit. (*
    induction lst; intros; subst; simpl.
    + assumption.
    + repeat reduce. 
      reduce.
      rewrite bf_typeof_const.
      reduce.
      rewrite mkConst_sound.
      reduce. reflexivity.
*)
  Admitted.

  Lemma exprD_fold_expr_nil tus tvs (t u : typ) (f acc : expr typ func) (lst : list (expr typ func)) (xs ys g : expr typ func)
    (fD : exprT tus tvs (typD (typ2 u (typ2 t t)))) (accD : exprT tus tvs (typD t))
    (xsD ysD : exprT tus tvs (typD (tyList u))) 
    (Hf : ExprDsimul.ExprDenote.exprD' tus tvs (typ2 u (typ2 t t)) f = Some fD)
    (Hacc : ExprDsimul.ExprDenote.exprD' tus tvs t acc = Some accD) 
    (Hlst : expr_to_list ys = (lst, xs))
    (Hg : ExprDsimul.ExprDenote.exprD' tus tvs (typ2 (typ2 u (typ2 t t)) (typ2 t (typ2 (tyList u) t))) g =
        Some (fun _ _ => foldD t u))
    (Hxs : listS xs = Some (pNil u))
    (Hys : ExprDsimul.ExprDenote.exprD' tus tvs (tyList u) ys = Some ysD) :
    ExprDsimul.ExprDenote.exprD' tus tvs t
      (fold_right (fun x acc => beta (beta (App (App f x) acc))) acc lst) =
    Some
      (fun us vs => fold_right (tyArrD2 (fD us vs)) (accD us vs) (listD (ysD us vs))).
  Proof.
    generalize dependent ys; generalize dependent ysD.
    induction lst; intros; subst; simpl.
    + apply expr_to_list_nil in Hlst; subst.
      reduce. simpl. assumption.
    + reduce.
      destruct (expr_to_list_cons tus tvs _ _ Hlst H) as [? [? ?]]; subst.
      reduce; subst.
      specialize (IHlst _ _ H3 Heqo0).
      reduce. reflexivity.
  Qed.
   
  Lemma exprD_fold_expr tus tvs (t u : typ) (f acc : expr typ func) (lst : list (expr typ func)) (xs ys g : expr typ func)
    (fD : exprT tus tvs (typD (typ2 u (typ2 t t)))) (accD : exprT tus tvs (typD t))
    (xsD ysD : exprT tus tvs (typD (tyList u))) 
    (Hf : ExprDsimul.ExprDenote.exprD' tus tvs (typ2 u (typ2 t t)) f = Some fD)
    (Hacc : ExprDsimul.ExprDenote.exprD' tus tvs t acc = Some accD) 
    (Hlst : expr_to_list ys = (lst, xs))
    (Hg : ExprDsimul.ExprDenote.exprD' tus tvs (typ2 (typ2 u (typ2 t t)) (typ2 t (typ2 (tyList u) t))) g =
        Some (fun _ _ => foldD t u))
    (Hys : ExprDsimul.ExprDenote.exprD' tus tvs (tyList u) ys = Some ysD) :
    ExprDsimul.ExprDenote.exprD' tus tvs t
      (fold_right (fun x acc => beta (beta (App (App f x) acc))) (App (App (App g f) acc) xs) lst) =
    Some
      (fun us vs => fold_right (tyArrD2 (fD us vs)) (accD us vs) (listD (ysD us vs))).
  Proof.
    generalize dependent ys; generalize dependent ysD.
    induction lst; intros; subst; simpl.
    + apply expr_to_list_nil in Hlst; subst.
      reduce. reflexivity.
    + reduce.
      destruct (expr_to_list_cons tus tvs _ _ Hlst H) as [? [? ?]]; subst.
      reduce; subst.
      specialize (IHlst _ _ H3 Heqo0).
      reduce.
      reflexivity.
  Qed.
  *)
  Lemma foldTacOk : partial_reducer_ok foldTac.
  Proof.
    admit.
    (*
    unfold partial_reducer_ok; intros.
    exists val; split; [|reflexivity].
    unfold foldTac.

    do 8 (destruct_exprs; try assumption).
    + destruct_exprs; reduce; try reflexivity.
      apply exprD_fold_const; assumption.
    + do 2 (destruct_exprs; try (reduce; eapply exprD_fold_expr; eassumption)).
      destruct_exprs; try (reduce; eapply exprD_fold_expr; eassumption).
      reduce.
	  eapply exprD_fold_expr_nil; try eassumption.
*)
  Admitted.

End Fold.