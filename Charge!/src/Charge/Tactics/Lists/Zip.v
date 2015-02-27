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

Require Import ExtLib.Core.RelDec.

Section Zip.
  Context {typ func : Type} {RType_typ : RType typ} {RSym_func : RSym func}.
  Context {LT : ListType typ} {LTD : ListTypeD LT}. 
  Context {BT : BaseType typ} {BTD : BaseTypeD}.
  Context {BF : BaseFunc typ func} {LF: ListFunc typ func}.
  Context {Heq : RelDec (@eq typ)} {HC : RelDec_Correct Heq}.
  Context {Heqd : SemiEqDecTyp typ} {HeqdOk : SemiEqDecTypOk Heqd}.
  Context {Typ2_Fun : Typ2 RType_typ Fun}.
  Context {Typ0_Prop : Typ0 RType_typ Prop}.
  Check @BaseFuncOk.
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
                  | Some (pCons _) => mkCons (tyPair t u) (mkPair t u x y) (zipExpr t u xs ys)
                  | _ => mkZip t u e1 e2
                end
              | Inj g =>
                match listS g with
                  | Some (pNil _) => mkNil (tyPair t u)
                  | _ => mkZip t u e1 e2
                end
              | _ => mkZip t u e1 e2
            end
          | _ => mkZip t u e1 e2
        end
      | Inj f =>
        match listS f with
          | Some (pNil _) => mkNil (tyPair t u)
          | _ => mkZip t u e1 e2
        end
      | _ => mkZip t u e1 e2
    end.
  
  Lemma zipExprOk tus tvs (t u : typ) (xs ys : expr typ func) 
    (xsD : ExprI.exprT tus tvs (typD (tyList t))) (ysD : ExprI.exprT tus tvs (typD (tyList u)))
    (Hxs : ExprDsimul.ExprDenote.exprD' tus tvs (tyList t) xs = Some xsD)
    (Hys : ExprDsimul.ExprDenote.exprD' tus tvs (tyList u) ys = Some ysD) : 
    ExprDsimul.ExprDenote.exprD' tus tvs (tyList (tyPair t u)) (zipExpr t u xs ys) =
      Some (ExprDsimul.ExprDenote.exprT_App (ExprDsimul.ExprDenote.exprT_App (fun _ _ => zipD t u) xsD) ysD).
  Proof.
    generalize dependent ys; generalize dependent xsD; generalize dependent ysD.
    induction 

  Definition zipTac (e : expr typ func) (args : list (expr typ func)) : expr typ func :=
    match listS e with
      | Some (pZip t u) =>
        match args with
          | xs :: ys :: nil =>
            match baseS xs, baseS ys with
              | Some (pConst v xs'), Some (pConst w ys') =>
                match type_cast v (tyList t), type_cast w (tyList u) with
                  | Some pfxs, Some pfys =>
                    mkConst (tyList (tyPair t u))
                      (listD_inv _ (eq_rect _ list
                        (combine (listD _ (eq_rect _ typD xs' _ pfxs))
                           (listD _ (eq_rect _ typD ys' _ pfys))) _ (eq_sym (btPair t u))))
                  | _, _ => apps e args
                end 
              | Some (pConst v xs'), None => 
                match type_cast v (tyList t) with
                  | Some pf => zipExpr t u (list_const_to_expr t (listD _ (eq_rect _ typD xs' _ pf))) ys
                  | None => apps e args
                end
              | None, Some (pConst v ys') => 
                match type_cast v (tyList t) with
                  | Some pf => zipExpr t u xs (list_const_to_expr t (listD _ (eq_rect _ typD ys' _ pf)))
                  | None => apps e args
                end
              | _, _ => apps e args
            end
          | _ => apps e args
        end
      | _ => apps e args
    end.

Definition ZIP := SIMPLIFY (typ := typ) (fun _ _ _ _ => (beta_all (fun _ => zipTac))).

End Zip.