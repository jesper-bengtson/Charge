Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.AppN.
Require Import MirrorCore.Lambda.Red.

Require Import Charge.ModularFunc.BaseFunc.
Require Import Charge.ModularFunc.ListFunc.
Require Import Charge.ModularFunc.ListType.

Section Fold.
  Context {typ func : Type} {RType_typ : RType typ}.
  Context {LT : ListType typ} {LTD : ListTypeD}. 
  Context {BF : BaseFunc typ func} {LF: ListFunc typ func}.

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

End Fold.