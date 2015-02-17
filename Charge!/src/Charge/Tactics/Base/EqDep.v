Require Import Charge.ModularFunc.BaseType.
Require Import Charge.ModularFunc.BaseFunc.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.Lambda.Expr.

Require Import ExtLib.Data.HList.

Section EqDecTyp.
  Context {typ : Type} {RType_typ : RType typ}.

  Definition eqDec_typ := forall t : typ, option (forall x y : typD t, {x = y} + {x <> y}).  
End EqDecTyp.

Section EqTac.
  Context {typ func : Type} {RType_typ : RType typ} {RSym_func : RSym func}.
  Context {Base_typ : BaseType typ} {Base_func : BaseFunc typ func}.
  Context {Typ2_typ : Typ2 RType_typ Fun}.  
  Context {eqt : eqDec_typ}.

  Definition EQ_REFL : rtac typ (expr typ func) :=
    fun tus tvs us vs c s e =>
    match e with
      | App (App (Inj f) a) b =>
        match baseS (typ := typ) f with
          | Some (pEq t) =>
            match exprD' nil nil t a, exprD' nil nil t b with
              | Some aD, Some bD =>
                match eqt t with
                  | Some eq_dec =>
                    match eq_dec (aD Hnil Hnil) (bD Hnil Hnil) with
                      | left _ => Solved s
                      | right _ => Fail
                    end
                  | None => Fail
                end
              | _, _ => Fail
            end
          | _ => Fail
        end
      | _ => Fail
	end.

End EqTac.