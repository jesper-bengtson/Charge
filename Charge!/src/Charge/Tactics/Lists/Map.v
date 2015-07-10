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
  
  Fixpoint mapTac_lc t u (f lst : expr typ func) : expr typ func :=
    @list_cases typ func _ lst _
      (fun _ _ _ _ => mkNil u)
      (fun _ _ x xs _ _ => mkCons u (beta (App f x)) (mapTac_lc t u f xs))
      (mkMap t u f lst).
  
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
          | f :: lst :: nil => mapTac_aux t u f lst
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
    ExprDsimul.ExprDenote.exprD' tus tvs (tyList u) (mapTac_aux t u f lst) = Some (fun us vs => tyArrD2 (mapD t u) (fD us vs) (lstD us vs)).
  Proof.
    admit. (*
    Transparent listS.
    generalize dependent lstD.
    induction lst using expr_strong_ind; simpl; intros;
      try (erewrite mkMap_sound; try eassumption; reduce; reflexivity).
    + do 3 (destruct_exprs; try (erewrite mkMap_sound; try eassumption; do 2 rewrite exprT_App_tyArrD; reflexivity)).
      reduce. rewrite mkNil_sound. reflexivity.
    + do 4 (destruct_exprs; try (erewrite mkMap_sound; try eassumption; do 2 rewrite exprT_App_tyArrD; reflexivity)).
      reduce.
      erewrite mkCons_sound; [| reduce; reflexivity | apply H; [repeat constructor | eassumption]].
      reduce.
      reflexivity.
*)
  Admitted.

  Lemma mapTacOk : partial_reducer_ok mapTac.
  Proof.
    admit.
    (*
    unfold partial_reducer_ok; intros.
    exists val; split; [|reflexivity].
    unfold mapTac.
    
    do 6 (destruct_exprs; try assumption).
	+ do 2 (destruct_exprs; try assumption). reduce. 
	  remember (trmD t3 (listE eq_refl)) as l; clear Heql.
	  induction l; simpl.
	  * simpl; rewrite mkNil_sound. reflexivity.
	  * erewrite mkCons_sound; [| reduce; rewrite bf_typeof_const; rewrite mkConst_sound; reduce; reflexivity | eassumption].
	    reduce. reflexivity.
	+ reduce. erewrite mapTac_auxOk; try eassumption. reduce; reflexivity.
*)
  Admitted.

End Map.