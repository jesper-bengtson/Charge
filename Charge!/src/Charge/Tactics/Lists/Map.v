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
              | None =>
                let (lst', e') := expr_to_list lst in
                  match listS e' with
                    | Some (pNil v) =>
                      match type_cast u v with
                        | Some pf => fold_right (fun x acc => mkCons u (beta (App f x)) acc) (mkNil u) lst'
                        | _ => fold_right (fun x acc => mkCons u (beta (App f x)) acc) (apps e (f::e'::nil)) lst'
                      end
                    | _ => fold_right (fun x acc => mkCons u (beta (App f x)) acc) (apps e (f::e'::nil)) lst'
                 end
            end
          | _ => apps e args
        end
      | _ => apps e args
    end.

  Definition MAP := SIMPLIFY (typ := typ) (fun _ _ _ _ => (beta_all (fun _ => mapTac))).

  Opaque beta.
  Opaque listS.
  Opaque baseS.
  
  Lemma mapTacOk : partial_reducer_ok mapTac.
  Proof.
    unfold partial_reducer_ok; intros.
    exists val; split; [|reflexivity].
    unfold mapTac.

    do 8 (destruct_exprs; try assumption).
	+ reduce. unfold mapD, Denotation.fun_to_typ2.
	  do 2 rewrite Denotation.exprT_App_wrap_sym.
	  rewrite Denotation.fun_to_typ_inv.
	  rewriteD Denotation.fun_to_typ_inv.
	  remember (listD t3); clear Heql.
	  induction l; simpl.
	  * simpl; rewrite mkNil_sound; reflexivity.
	  * erewrite mkCons_sound; [| do 2 reduce; reflexivity | eassumption].
	    reduce.
	    rewriteD listD_inv. 
	    rewriteD exprT_App_wrap_sym. reflexivity.
	+ destruct_exprs.
	  destruct_exprs. simpl.
	   reduce. 
	    SearchAbout ExprDsimul.ExprDenote.exprT_App.
	    unfold ExprDsimul.ExprDenote.exprT_App. simpl.
	    Check listD_sym.
	    rewriteD IHl.
	    Focus 2.
	    reduce.
	    reduce. reflexivity.
	    eassumption.
	    rewrite mkNil_sound.
	    reflexivity.
	  setoid_rewrite Denotation.fun_to_typ_inv.
Check Denotation.fun_to_typ_inv.
	  rewrite Denotation.fun_to_typ_inv.
	  rewrite listD_sym_inv.
	lf_map_type.
	lf_map_expr.
	lf_map_type.
	lf_map_expr.
	pose proof (lf_map_type_eq _ _ Heqo Heqo6).
	Require Import Charge.Tactics.Base.BaseTacs.
	Require Import Charge.Tactics.Base.MirrorCoreTacs.
	reduce.
	
	Check bf_const_type_eq.
	     pose proof (bf_const_type_eq _ _ Heqo0 Heqo4) as H5; r_inj H5; repeat clear_eq; pose proof(bf_const_eq _ Heqo0 Heqo4); subst.

	  bf_forward_step.
      reduce.
End Map.