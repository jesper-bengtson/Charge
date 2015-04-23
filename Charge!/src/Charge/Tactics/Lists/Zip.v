Require Import FunctionalExtensionality.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.AppN.
Require Import MirrorCore.Lambda.Red.
Require Import MirrorCore.Lambda.RedAll.
Require Import MirrorCore.RTac.Simplify.

Require Import Charge.ModularFunc.BaseFunc.
Require Import Charge.ModularFunc.ListFunc.
Require Import Charge.ModularFunc.ListType.
Require Import Charge.ModularFunc.BaseType.
Require Import Charge.ModularFunc.SemiEqDecTyp.
Require Import Charge.ModularFunc.Denotation.

Require Import Charge.Tactics.Lists.ListTacs.
Require Import Charge.Tactics.Base.DenotationTacs.
Require Import Charge.Tactics.Base.MirrorCoreTacs.

Require Import ExtLib.Core.RelDec.

Section Zip.
  Context {typ func : Type} {RType_typ : RType typ} {RSym_func : RSym func}.
  Context {LT : ListType typ} {LTD : ListTypeD LT}. 
  Context {BT : BaseType typ} {BTD : BaseTypeD BT}.
  Context {BF : BaseFunc typ func} {LF: ListFunc typ func}.
  Context {Heq : RelDec (@eq typ)} {HC : RelDec_Correct Heq}.
  Context {Heqd : SemiEqDecTyp typ} {HeqdOk : SemiEqDecTypOk Heqd}.
  Context {Typ2_Fun : Typ2 RType_typ Fun}.
  Context {Typ0_Prop : Typ0 RType_typ Prop}.
  Context {BFOk : BaseFuncOk typ func} {LFOk : ListFuncOk typ func}.

  Context {RTypeOk_typ : RTypeOk}.
  Context {RSymOk_func : RSymOk RSym_func}.
  Context {Typ2Ok_Fun : Typ2Ok Typ2_Fun}.

  Fixpoint zipExpr (t u : typ) (e1 e2 : expr typ func) : expr typ func :=
    match e1 with
      | App (App (Inj f) x) xs =>
        match listS f with
          | Some (pCons _) =>
            match e2 with
              | App (App (Inj g) y) ys =>
                match listS g with
                  | Some (pCons _) => mkCons (tyProd t u) (mkPair t u x y) (zipExpr t u xs ys)
                  | _ => mkZip t u e1 e2
                end
              | Inj g =>
                match listS g with
                  | Some (pNil _) => mkNil (tyProd t u)
                  | _ => mkZip t u e1 e2
                end
              | _ => mkZip t u e1 e2
            end
          | _ => mkZip t u e1 e2
        end
      | Inj f =>
        match listS f with
          | Some (pNil _) => mkNil (tyProd t u)
          | _ => mkZip t u e1 e2
        end
      | _ => mkZip t u e1 e2
    end.
  
  (* This function should have lst is it's third arguments, but for reasons that I cannot figure out at the moment
     the function does not reduce with lst as the last argument. *)
     
  Fixpoint zipExprConst_left (t u : typ) (lst : list (typD u)) (e : expr typ func) : expr typ func :=
    match lst with
      | nil => mkNil (tyProd t u)
      | y :: ys => 
        match e with
	      | App (App (Inj f) x) xs =>
	        match listS f with
	          | Some (pCons _) => mkCons (tyProd t u) (mkPair t u x (mkConst u y)) (zipExprConst_left t u ys xs)
	          | _ => mkZip t u e (mkConst (tyList u) (listR lst))
	        end
	      | Inj f =>
	        match listS f with
	          | Some (pNil _) => mkNil (tyProd t u)
	          | _ => mkZip t u e (mkConst (tyList u) (listR lst))
	        end
	      | _ => mkZip t u e (mkConst (tyList u) (listR lst))
      end
    end.

  Fixpoint zipExprConst_right (t u : typ) (lst : list (typD t)) (e : expr typ func) : expr typ func :=
    match lst with
      | nil => mkNil (tyProd t u)
      | x :: xs => 
        match e with
	      | App (App (Inj f) y) ys =>
	        match listS f with
	          | Some (pCons _) => mkCons (tyProd t u) (mkPair t u (mkConst t x) y) (zipExprConst_right t u xs ys)
	          | _ => mkZip t u (mkConst (tyList t) (listR lst)) e
	        end
	      | Inj f =>
	        match listS f with
	          | Some (pNil _) => mkNil (tyProd t u)
	          | _ => mkZip t u (mkConst (tyList t) (listR lst)) e
	        end
	      | _ => mkZip t u (mkConst (tyList t) (listR lst)) e
      end
    end.
  
  Lemma combine_nil {A B : Type} (lst : list A) : combine lst (@nil B) = nil.
  Proof.
    destruct lst; reflexivity.
  Qed.

  Lemma trmR_nil_eq {T U : Type} {t : typ} (eq1 : typD t = T) (eq2 : typD t = U) :
    trmR nil (listE eq1) = trmR nil (listE eq2).
  Proof.
    clear.
    unfold listE, eq_ind, trmR, eq_rect_r, eq_rect, eq_sym, id.
    generalize (btList t).
    revert eq1 eq2.
    remember (tyList t).
    generalize dependent (typD t); intros; subst.
    destruct eq2.
    
    generalize dependent (typD (tyList t)).
    intros; subst. reflexivity.
  Qed.
   
    Lemma trmR_cons_eq (t : typ) T (x : T) (xs : list T) (e : typD t = T) :
      trmR (x :: xs) (listE e) = trmR ((trmR x e) :: (trmD (trmR xs (listE e)) (listE eq_refl))) (listE eq_refl).
    Proof.
      unfold trmR, trmD, listE, eq_ind, eq_rect_r, eq_rect, eq_sym, id.
      generalize (btList t).
      generalize dependent (typD t); intros; subst.
      generalize dependent (typD (tyList t)); intros; subst. reflexivity.
    Qed.


  Lemma zipExprConst_left_sound tus tvs (t u : typ) (xs : expr typ func) (ys : list (typD u))
    (xsD : ExprI.exprT tus tvs (typD (tyList t)))
    (Hxs : ExprDsimul.ExprDenote.exprD' tus tvs (tyList t) xs = Some xsD) :
	ExprDsimul.ExprDenote.exprD' tus tvs (tyList (tyProd t u)) (zipExprConst_left t u ys xs) =
	  Some (ExprDsimul.ExprDenote.exprT_App (ExprDsimul.ExprDenote.exprT_App (fun _ _ => zipD t u) xsD) (fun _ _ => listR ys)).
  Proof.
    generalize dependent xs. generalize dependent xsD.
    induction ys; simpl; intros.
    + rewrite listR_nil. 
      reduce. 
      rewriteD @combine_nil.
      rewrite mkNil_sound.
      erewrite trmR_nil_eq. reflexivity.
    + do 3 (destruct_exprs; try (apply mkZip_sound; [assumption | apply mkConst_sound])).
      * reduce.
        rewrite mkNil_sound.
        simpl.
        erewrite trmR_nil_eq. reflexivity.
      * do 2 (destruct_exprs; try (apply mkZip_sound; [assumption | apply mkConst_sound])).
        reduce.
        erewrite mkCons_sound; try eassumption; [| eapply mkPair_sound; [eassumption | apply mkConst_sound] | eapply IHys; eassumption].
        simpl. 
        unfold consD, zipD, pairD, tyArrR2, tyArrR2', tyArrR', tyArrD, tyArrD'.
        do 6 rewrite exprT_App_tyArrD.
        unfold tyArrD, tyArrD'.
        repeat rewriteD @trmDR.
        unfold listR. unfold listD.
        unfold prodR.
        rewriteD @trmDR.
        symmetry.
        rewriteD trmR_cons_eq. reflexivity.
  Qed.

  Lemma zipExprConst_right_sound tus tvs (t u : typ) (xs : list (typD t)) (ys : expr typ func) 
    (ysD : ExprI.exprT tus tvs (typD (tyList u)))
    (Hys : ExprDsimul.ExprDenote.exprD' tus tvs (tyList u) ys = Some ysD) :
	ExprDsimul.ExprDenote.exprD' tus tvs (tyList (tyProd t u)) (zipExprConst_right t u xs ys) =
	  Some (ExprDsimul.ExprDenote.exprT_App (ExprDsimul.ExprDenote.exprT_App (fun _ _ => zipD t u) (fun _ _ => listR xs)) ysD).
  Proof.
    generalize dependent ys. generalize dependent ysD.
    induction xs; simpl; intros.
    + rewrite listR_nil. 
      reduce.
      rewriteD mkNil_sound.
      simpl. erewrite trmR_nil_eq; reflexivity.
    + do 3 (destruct_exprs; try (apply mkZip_sound; [apply mkConst_sound| assumption])).
      * reduce.
        rewrite mkNil_sound.
        simpl.
        erewrite trmR_nil_eq; reflexivity.
      * do 2 (destruct_exprs; try (apply mkZip_sound; [apply mkConst_sound | assumption])).
        reduce.
        erewrite mkCons_sound; try eassumption; [| eapply mkPair_sound; [apply mkConst_sound | eassumption] | eapply IHxs; eassumption].
        unfold consD, zipD, pairD, tyArrR2, tyArrR2', tyArrR', tyArrD, tyArrD'.
        do 6 rewrite exprT_App_tyArrD.
        unfold tyArrD, tyArrD'.
        repeat rewriteD @trmDR.
        unfold listR. unfold listD.
        unfold prodR.
        rewriteD @trmDR. simpl.
        symmetry.
        rewriteD trmR_cons_eq. reflexivity.
  Qed.


  Lemma zipExprOk tus tvs (t u : typ) (xs ys : expr typ func) 
    (xsD : ExprI.exprT tus tvs (typD (tyList t))) (ysD : ExprI.exprT tus tvs (typD (tyList u)))
    (Hxs : ExprDsimul.ExprDenote.exprD' tus tvs (tyList t) xs = Some xsD)
    (Hys : ExprDsimul.ExprDenote.exprD' tus tvs (tyList u) ys = Some ysD) : 
    ExprDsimul.ExprDenote.exprD' tus tvs (tyList (tyProd t u)) (zipExpr t u xs ys) =
      Some (ExprDsimul.ExprDenote.exprT_App (ExprDsimul.ExprDenote.exprT_App (fun _ _ => zipD t u) xsD) ysD).
  Proof.
    generalize dependent ys; generalize dependent xsD; generalize dependent ysD.
    induction xs using expr_strong_ind; simpl; intros;
      try (apply mkZip_sound; eassumption).
    + do 2 (destruct_exprs; try (apply mkZip_sound; eassumption)).
      reduce.
      rewriteD mkNil_sound. simpl.
      erewrite trmR_nil_eq; reflexivity.
    + do 7 (destruct_exprs; try (apply mkZip_sound; eassumption)).
      * reduce.
        rewriteD @combine_nil.
        erewrite trmR_nil_eq. rewrite mkNil_sound. reflexivity.
      * do 2 (destruct_exprs; try (apply mkZip_sound; eassumption)).
        reduce. simpl.
        erewrite mkCons_sound; [| eapply mkPair_sound; eassumption | eapply H; [repeat constructor | eassumption | eassumption]].
        unfold consD, zipD, pairD, tyArrR2, tyArrR2', tyArrR', tyArrD, tyArrD'. simpl.
        repeat rewrite exprT_App_tyArrD.
        unfold tyArrD, tyArrD'.
        repeat rewrite @trmDR.
        unfold listR, listD, prodR.
        repeat rewriteD @trmDR. simpl.
        symmetry.
        rewriteD trmR_cons_eq. reflexivity.
  Qed.
    
  Definition zipTac  (_ : list (option (expr typ func))) (e : expr typ func) (args : list (expr typ func)) : expr typ func :=
    match listS e with
      | Some (pZip t u) =>
        match args with
          | xs :: ys :: nil =>
            match baseS xs, baseS ys with
              | Some (pConst v xs'), Some (pConst w ys') =>
                match type_cast v (tyList t), type_cast w (tyList u) with
                  | Some pfxs, Some pfys =>
                    mkConst (tyList (tyProd t u))
                      (listR (eq_rect _ list
                        (combine (listD (eq_rect _ typD xs' _ pfxs))
                           (listD (eq_rect _ typD ys' _ pfys))) _ (eq_sym (btProd t u))))
                  | _, _ => apps e args
                end 
              | Some (pConst v xs'), None => 
                match type_cast v (tyList t) with
                  | Some pf => zipExprConst_right t u (listD (eq_rect _ typD xs' _ pf)) ys
                  | None => apps e args
                end
              | None, Some (pConst v ys') => 
                match type_cast v (tyList u) with
                  | Some pf => zipExprConst_left t u (listD (eq_rect _ typD ys' _ pf)) xs
                  | None => apps e args
                end
              | _, _ => zipExpr t u xs ys
            end
          | _ => apps e args
        end
      | _ => apps e args
    end.
Require Import MirrorCore.Lambda.ExprD.
Check typeof_expr.
  Lemma zipTacOk : partial_reducer_ok (zipTac nil).
  Proof.
    unfold partial_reducer_ok; intros.
    eexists; split; [|reflexivity].
    unfold zipTac.
    do 6 (destruct_exprs; try assumption).
    destruct_exprs.
    Focus 2.
    (* Here we have a problem at H as we have to prove False from
       tyList = tyArr.
    *)
    (*
red_exprD_hyp.
forward_step.
forward_step.
forward_step.
Locate typ2_cast.
inversion H.
forward_step.
repeat forward_step.
  (try red_exprD_hyp); repeat forward_step; (repeat exprD_saturate_types); (repeat (first [rewrite_in_match | bf_rewrite_in_match])); (try red_exprD_goal); repeat (
        first [red_unfold | red_rewrite]).
    
    rewrite zipExprOk.
    destruct_exprs; [|apply zipExprOk].
    destruct_exprs; (try (reduce; apply zipExprOk; [reduce | eassumption])).
    destruct_exprs. destruct e1; try congruence.
    destruct_exprs; (try (reduce; apply zipExprOk; reduce)).
    destruct_exprs; try assumption.
    destruct_exprs; try assumption.
	+ reduce.
	  unfold zipD, fun_to_typ2.
	  do 2 rewrite exprT_App_wrap. reflexivity.
	+ destruct_exprs; try assumption.
	  reduce.
	  erewrite zipExprConst_right_sound; [|eassumption].
	  unfold zipD, fun_to_typ2.
	  do 4 rewrite exprT_App_wrap.
	  rewriteD listDR. reflexivity.
	+ do 2 (destruct_exprs; (try (reduce; apply zipExprOk; reduce; assumption))).
      destruct_exprs; try assumption.
      reduce.
	  erewrite zipExprConst_left_sound; [|eassumption].
	  unfold zipD, fun_to_typ2.
	  do 3 rewrite exprT_App_wrap.
	  rewrite listDR. reflexivity.
   *)
   admit.
   admit.
   admit.
   admit.
   
   
  Qed.
  
Definition ZIP := SIMPLIFY (typ := typ) (fun _ _ _ _ => beta_all zipTac).

End Zip.