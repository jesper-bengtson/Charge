Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.Reify.Reify.

Require Import ChargeCore.Logics.ILEmbed.

Require Import Charge.Views.EmbedView.
Require Import Charge.Patterns.EmbedPattern.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Section ReifyEmbed.
  Context {typ func : Set} {FV : PartialView func (embed_func typ)}.
  Context {t : Reify typ}.

  Definition reify_eilf_embed : Command (expr typ func) :=
    CPattern (ls := (typ:Type)::(typ:Type)::nil)
             (RApp (RApp (RApp (RExact (@embed)) (RGet 0 RIgnore)) (RGet 1 RIgnore)) RIgnore)
             (fun (x y : function (CCall (reify_scheme typ))) => Inj (fEmbed x y)).

  Definition reify_embed : Command (expr typ func) :=
    CFirst (reify_eilf_embed :: nil).

End ReifyEmbed.

Arguments reify_embed _ _ {_ _}.