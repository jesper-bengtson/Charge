Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.Reify.ReifyClass.

Require Import ChargeCore.Logics.BILogic.

Require Import Charge.Views.BILogicView.
Require Import Charge.Patterns.BILogicPattern.


Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Section ReifyBILogic.
  Context {typ func : Set} {FV : PartialView func (bilfunc typ)}.
  Context {t : Reify typ}.

  Definition reify_emp : Command (expr typ func) :=
    CPattern (ls := (typ:Type)::nil)
             (RApp (RApp (RExact (@empSP)) (RGet 0 RIgnore)) RIgnore)
             (fun (x : function (CCall (reify_scheme typ))) => mkEmp x).

  Definition reify_star : Command (expr typ func) :=
    CPattern (ls := (typ:Type)::nil)
             (RApp (RApp (RExact (@sepSP)) (RGet 0 RIgnore)) RIgnore)
             (fun (x : function (CCall (reify_scheme typ))) => Inj (fStar x)).

  Definition reify_wand : Command (expr typ func) :=
    CPattern (ls := (typ:Type)::nil)
             (RApp (RApp (RExact (@wandSP)) (RGet 0 RIgnore)) RIgnore)
             (fun (x : function (CCall (reify_scheme typ))) => Inj (fWand x)).

  Definition reify_bilogic : Command (expr typ func) :=
    CFirst (reify_emp :: reify_star :: reify_wand :: nil).

End ReifyBILogic.

Section IgnoreILogic.

  Definition reify_BILogicOps : RPattern :=
    RApp (RExact (@BILogicOps)) RIgnore.
  
  Definition reify_BILogic : RPattern  :=
    RApp (RApp (RApp (RExact (@BILogic)) RIgnore) RIgnore) RIgnore.
 
End IgnoreILogic.


Arguments reify_bilogic _ _ {_ _}.