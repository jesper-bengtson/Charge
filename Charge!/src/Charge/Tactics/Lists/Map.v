Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.AppN.
Require Import MirrorCore.Lambda.Red.
Require Import MirrorCore.Lambda.RedAll.
Require Import MirrorCore.RTac.Simplify.

Require Import Charge.ModularFunc.BaseFunc.
Require Import Charge.ModularFunc.BaseType.
Require Import Charge.ModularFunc.ListFunc.
Require Import Charge.ModularFunc.ListType.
Require Import Charge.ModularFunc.SemiEqDecTyp.
Require Import Charge.ModularFunc.Denotation.

Require Import Charge.Tactics.Lists.ListTacs.
Require Import Charge.Tactics.Base.DenotationTacs.
Require Import Charge.Tactics.Base.MirrorCoreTacs.

Require Import ExtLib.Core.RelDec.

Section Map.
  Context {typ func : Type} {RType_typ : RType typ} {RSym_func : RSym func}.
  Context {BT : BaseType typ} {BTD : BaseTypeD}.
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
  
  Fixpoint mapTac_aux (t u : typ) (f : expr typ func) (lst : expr typ func) :=
    match listS lst with
      | Some (pNil v) =>
        match type_cast t v with 
          Some pf => mkNil u
          | _ => mkMap t u f lst
        end
      | _ =>
        match lst with
          | App (App g x) xs =>
            match listS g with
              | Some (pCons v) =>
                match type_cast t v with
                  | Some pf => mkCons u (beta (App f x)) (mapTac_aux t u f xs)
                  | None => mkMap t u f lst
                end
              | _ => mkMap t u f lst
            end
          | _ => mkMap t u f lst
       end
     end.

  Definition mapTac (e : expr typ func) (args : list (expr typ func)) : expr typ func :=
    match listS e with
      | Some (pMap t u) =>
        match args with
          | f :: lst :: nil =>
            match baseS lst with
              | Some (pConst v lst) => 
		  	    match type_cast v (tyList t) with
		  	      | Some pf => 
		  	        fold_right (mkCons u) (mkNil u) 
                      (map (fun x => beta (App f (mkConst t x))) 
                        (listD (eq_rect _ typD lst _ pf)))
		  	      | None => apps e args
		  	    end
		  	  | Some _ => apps e args
              | None => mapTac_aux t u f lst
            end
          | _ => apps e args
        end
      | _ => apps e args
    end.

  Definition MAP := SIMPLIFY (typ := typ) (fun _ _ _ _ => (beta_all (fun _ => mapTac))).


  Opaque beta.
  Opaque baseS.
  
  Lemma mapTac_auxOk tus tvs (t u : typ) (f lst : expr typ func) fD lstD
    (Hf : ExprDsimul.ExprDenote.exprD' tus tvs (typ2 t u) f = Some fD)
    (Hlst : ExprDsimul.ExprDenote.exprD' tus tvs (tyList t) lst = Some lstD) :
    ExprDsimul.ExprDenote.exprD' tus tvs (tyList u) (mapTac_aux t u f lst) = Some (fun us vs => typ_to_fun2 (mapD t u) (fD us vs) (lstD us vs)).
  Proof.
    Transparent listS.
    generalize dependent lstD.
    induction lst using expr_strong_ind; simpl; intros;
      try (erewrite mkMap_sound; try eassumption; do 2 rewrite exprT_App_wrap_sym; reflexivity).
    + do 3 (destruct_exprs; try (erewrite mkMap_sound; try eassumption; do 2 rewrite exprT_App_wrap_sym; reflexivity)).
      reduce. rewrite mkNil_sound.
      unfold typ_to_fun2, mapD, fun_to_typ2. repeat rewriteD fun_to_typ_inv.
      rewrite listD_nil; reflexivity.
    + do 4 (destruct_exprs; try (erewrite mkMap_sound; try eassumption; do 2 rewrite exprT_App_wrap_sym; reflexivity)).
      reduce.
      erewrite mkCons_sound; [| reduce; reflexivity | apply H; [repeat constructor | eassumption]].
      do 2 rewrite exprT_App_wrap_sym.
      unfold consD, fun_to_typ2.
      do 2 rewriteD fun_to_typ_inv.
      rewriteD exprT_App_wrap_sym.
      unfold mapD, fun_to_typ2, typ_to_fun2.
      repeat rewriteD fun_to_typ_inv.
      do 2 rewriteD listD_inv.
      reflexivity.
  Qed.

  Lemma mapTacOk : partial_reducer_ok mapTac.
  Proof.
    unfold partial_reducer_ok; intros.
    exists val; split; [|reflexivity].
    unfold mapTac.
    
    do 6 (destruct_exprs; try assumption).
	+ do 2 (destruct_exprs; try assumption). reduce. unfold mapD, Denotation.fun_to_typ2.
	  do 2 rewrite Denotation.exprT_App_wrap_sym.
	  rewrite Denotation.fun_to_typ_inv.
	  rewriteD Denotation.fun_to_typ_inv.
	  remember (listD t3); clear Heql.
	  induction l; simpl.
	  * simpl; rewrite mkNil_sound. reflexivity.
	  * erewrite mkCons_sound; [| do 2 reduce; reflexivity | eassumption].
	    reduce.
	    rewriteD listD_inv. 
	    rewriteD exprT_App_wrap_sym. reflexivity.
	+ reduce.
	  do 2 rewriteD exprT_App_wrap_sym.
	  apply mapTac_auxOk; assumption.
  Qed.

End Map.