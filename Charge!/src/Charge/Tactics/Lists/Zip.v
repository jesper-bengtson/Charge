Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.AppN.
Require Import MirrorCore.Lambda.Red.

Require Import Charge.ModularFunc.BaseFunc.
Require Import Charge.ModularFunc.ListFunc.
Require Import Charge.ModularFunc.ListType.
Require Import Charge.ModularFunc.BaseType.

Section Zip.
  Context {typ func : Type} {RType_typ : RType typ}.
  Context {LT : ListType typ} {LTD : ListTypeD}. 
  Context {BT : BaseType typ} {BTD : BaseTypeD}.
  Context {BF : BaseFunc typ func} {LF: ListFunc typ func}.

  Fixpoint zipExpr (t u : typ) (e1 e2 : expr typ func) : expr typ func :=
    match e1, e2 with 
      | App (App (Inj f) x) xs, App (App (Inj g) y) ys =>
        match listS f, listS g with
          | Some mkZip t u e1 e2
      | _, _ => mkZip t u e1 e2
    end.
    match listS e1, listS e2 with
      | Some (pNil _), Some (pNil _) => mkNil (tyPair t u)
      | Some (pCons _), Some (pNil _) => mkNil (tyPair t u)
      | Some (pNil _), Some (pCons _) => mkNil (tyPair t u)
      | Some (pCons _ x xs), Some (pCons _ y ys) => mkCons (tyPair v w) (mkPair _ _ x y) (zipExpr t u xs ys)
      | _, _ => mkZip t u e1 e2
    end.

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
              | Some (pConst v xs'), None => apps e args
              | _, _ => apps e args
            end
          | _ => apps e args
        end
      | _ => apps e args
    end.

End Zip.