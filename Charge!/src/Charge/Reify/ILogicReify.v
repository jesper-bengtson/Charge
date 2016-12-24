Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.Reify.Reify.

Require Import ChargeCore.Logics.ILogic.

Require Import Charge.Views.ILogicView.
Require Import Charge.Patterns.ILogicPattern.

Section ReifyILogic.
  Context {typ func : Set} {FV : PartialView func (ilfunc typ)}.
  Context {t : Reify typ}.
  
  Definition reify_lentails : Command@{Set} (expr typ func) :=
    CPattern (ls := (typ:Type)::nil)
             (RApp (RApp (RExact (@lentails)) (RGet 0 RIgnore)) RIgnore)
             (fun (x : function (CCall (reify_scheme typ))) => Inj (fEntails x)).             

  Definition reify_ltrue : Command@{Set} (expr typ func) :=
    CPattern (ls := (typ:Type)::nil) 
             (RApp (RApp (RExact (@ltrue)) (RGet 0 RIgnore)) RIgnore)
             (fun (x : function (CCall (reify_scheme typ))) => mkTrue x).

  Definition reify_lfalse : Command@{Set} (expr typ func) :=
    CPattern (ls := (typ:Type)::nil) 
             (RApp (RApp (RExact (@lfalse)) (RGet 0 RIgnore)) RIgnore)
             (fun (x : function (CCall (reify_scheme typ))) => mkFalse x).

  Definition reify_land : Command@{Set} (expr typ func) :=
    CPattern (ls := (typ:Type)::nil) 
             (RApp (RApp (RExact (@land)) (RGet 0 RIgnore)) RIgnore)
             (fun (x : function (CCall (reify_scheme typ))) => Inj (fAnd x)).

  Definition reify_lor : Command@{Set} (expr typ func) :=
    CPattern (ls := (typ:Type)::nil) 
             (RApp (RApp (RExact (@lor)) (RGet 0 RIgnore)) RIgnore)
             (fun (x : function (CCall (reify_scheme typ))) => Inj (fOr x)).

  Definition reify_limpl : Command@{Set} (expr typ func) :=
    CPattern (ls := (typ:Type)::nil) 
             (RApp (RApp (RExact (@limpl)) (RGet 0 RIgnore)) RIgnore)
             (fun (x : function (CCall (reify_scheme typ))) => Inj (fImpl x)).

  Definition reify_lforall : Command@{Set} (expr typ func) :=
    CPattern (ls := (typ:Type)::(typ:Type)::nil) 
             (RApp (RApp (RApp (RExact (@lforall)) (RGet 0 RIgnore)) RIgnore) (RGet 1 RIgnore))
             (fun (x y : function (CCall (reify_scheme typ))) => Inj (fForall y x)).

  Definition reify_lexists : Command@{Set} (expr typ func) :=
    CPattern (ls := (typ:Type)::(typ:Type)::nil) 
             (RApp (RApp (RApp (RExact (@lexists)) (RGet 0 RIgnore)) RIgnore) (RGet 1 RIgnore))
             (fun (x y : function (CCall (reify_scheme typ))) => Inj (fExists y x)).

  Definition reify_ilogic : Command@{Set} (expr typ func) :=
    CFirst (reify_lentails :: reify_ltrue :: reify_lfalse :: reify_land :: reify_lor :: 
            reify_limpl :: reify_lforall :: reify_lexists :: nil).

End ReifyILogic.

Section ReifyProp.
  Context {typ func : Set} {FV : PartialView func (ilfunc typ)}.
  Context {RType_typ : RType typ}.
  Context {t : Reify typ}.
  Context {Typ0_tyProp : Typ0 _ Prop}.

  Let tyProp : typ := @typ0 _ _ _ Typ0_tyProp.
          
  Definition reify_ptrue : Command@{Set} (expr typ func) :=
    CPattern (ls := nil) (RExact True) (mkTrue tyProp).

  Definition reify_pfalse : Command@{Set} (expr typ func) :=
    CPattern (ls := nil) (RExact False) (mkFalse tyProp).

  Definition reify_pand : Command@{Set} (expr typ func) :=
    CPattern (ls := nil) (RExact and) (Inj (fAnd tyProp)).

  Definition reify_por : Command@{Set} (expr typ func) :=
    CPattern (ls := nil) (RExact or) (Inj (fOr tyProp)).

  Definition reify_pimpl : Command@{Set} (expr typ func) :=
    CPattern (ls := (expr typ func:Type)::(expr typ func:Type)::nil) 
             (RImpl (RGet 0 RIgnore) (RGet 1 RIgnore))
             (fun (x y : function (CRec 0)) => mkImpl tyProp x y).

  Definition reify_pexists : Command@{Set} (expr typ func) :=
    CPattern (ls := (typ : Type) :: nil)
             (RApp (RExact ex) (RGet 0 RIgnore))
             (fun (x : function (CCall (reify_scheme typ))) => Inj (fExists x tyProp)).

  Definition reify_pforall : Command@{Set} (expr typ func) :=
    CPattern (ls := (typ : Type) :: (expr typ func : Type) :: nil)
             (RPi (RGet 0 RIgnore) (RGet 1 RIgnore))
             (fun (x : function (CCall (reify_scheme typ))) (y : function (CRec 0)) =>
                mkForall x tyProp y).

  Definition reify_plogic : Command@{Set} (expr typ func) :=
    CFirst (reify_ptrue :: reify_pfalse :: reify_pand :: reify_por :: 
            reify_pimpl :: reify_pforall :: reify_pexists :: nil).

End ReifyProp.

Arguments reify_ilogic _ _ {_ _}.
Arguments reify_plogic _ _ {_ _ _ _}.
Arguments RSym_ilfunc {_ _ _ _ _} _.
