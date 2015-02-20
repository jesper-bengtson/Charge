Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.AppN.
Require Import MirrorCore.Lambda.Red.
Require Import MirrorCore.Lambda.RedAll.
Require Import MirrorCore.RTac.Simplify.

Require Import Charge.ModularFunc.BaseFunc.
Require Import Charge.ModularFunc.ListFunc.
Require Import Charge.ModularFunc.ListType.

Section Map.
  Context {typ func : Type} {RType_typ : RType typ}.
  Context {LT : ListType typ} {LTD : ListTypeD}. 
  Context {BF : BaseFunc typ func} {LF: ListFunc typ func}.

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
                        (listD _ (eq_rect _ typD lst _ pf)))
		  	      | None => apps e args
		  	    end
              | _ => apps e args
            end
          | _ => apps e args
        end
      | _ => apps e args
    end.

  Definition MAP := SIMPLIFY (typ := typ) (fun _ _ _ _ => (beta_all (fun _ => mapTac))).

End Map.