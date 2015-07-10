Require Import ExtLib.Data.HList.
Require Import ExtLib.Core.RelDec.

Require Import Charge.Logics.ILogic.
Require Import Charge.ModularFunc.ListType.
Require Import Charge.ModularFunc.BaseType.
Require Import Charge.ModularFunc.ListFunc.
Require Import Charge.ModularFunc.BaseFunc.
Require Import Charge.ModularFunc.SemiEqDecTyp.
Require Import Charge.Tactics.Base.DenotationTacs.
Require Import Charge.Tactics.Base.MirrorCoreTacs.
Require Import ExtLib.Tactics.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.Lambda.AppN.
Require Import MirrorCore.Lambda.Red.
Require Import MirrorCore.Lambda.RedAll.
Require Import MirrorCore.Lambda.Expr.

Section Length.
  Context {typ func : Type} {RType_typ : RType typ} {RSym_func : RSym func}
          {BT : BaseType typ} {BTD : BaseTypeD BT}
          {LT : ListType typ} {LTD: ListTypeD LT}.
  Context {BF : BaseFunc typ func} {LF : ListFunc typ func}.
  Context {RelDec_eq : RelDec (@eq typ)} {RelDecOk_eq : RelDec_Correct RelDec_eq}.
  Context {Heqd : SemiEqDecTyp typ} {HeqdOk : SemiEqDecTypOk Heqd}.
  
   Context {EU : ExprUVar (expr typ func)}.

  Context {RType_typOk : RTypeOk} {RsymOk_func : RSymOk RSym_func}.

  Context {Typ0_tyProp : Typ0 _ Prop}.
  Context {Typ2_tyArr : Typ2 _ Fun}.
  
  Context {Typ0Ok_tyProp : Typ0Ok Typ0_tyProp}.
  Context {Typ2Ok_tyArr : Typ2Ok Typ2_tyArr}.
    
  Context {BFOk : BaseFuncOk typ func } {LFOk : ListFuncOk typ func}.

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.
  Let tyProp := @typ0 typ RType_typ Prop Typ0_tyProp.

(* This function will return None unless lst eventually reaches nil. This means that we cannot partially evaluate a length of a list
   (length 1::2::3::lst = 3 + (length lst) for instance). To be able to do this, we need a language that supports arithmetic operations
   (at least +) on natural numbers. This is a perfectly natural thing to have, but it is not implemented at the moment. *)

  Fixpoint lengthTac (lst : expr typ func) : option nat :=
    @list_cases typ func _ lst _ 
      (fun _ _ _ _ => Some 0)
      (fun _ _ _ xs _ _ =>
        match lengthTac xs with
          | Some n => Some (S n)
          | None => None
        end)
      None.
      
  Existing Instance Expr_expr.
  Existing Instance ExprOk_expr.


End Length.