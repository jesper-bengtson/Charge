Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.AppN.
Require Import MirrorCore.Lambda.Red.
Require Import MirrorCore.Lambda.RedAll.
Require Import MirrorCore.RTac.Simplify.

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