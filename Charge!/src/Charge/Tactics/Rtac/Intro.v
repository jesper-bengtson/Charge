Require Import ExtLib.Core.RelDec.

Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.Red.
Require Import MirrorCore.Lambda.Ptrns.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.Views.FuncView.

Require Import Charge.Views.ILogicView.

Section IntroTac.
  Context {typ func subst : Type}.
  Context {HIL : PartialView func (ilfunc typ)}.
  Context {EV : ExprVar (expr typ func)}.
  Context {EU : ExprUVar (expr typ func)}.

  Definition fintro : expr typ func -> option (@OpenAs typ (expr typ func)) :=
    ilogic_cases
      (fun _ => None)
      (fun _ => None)
      (fun _ _ _ => None)
      (fun _ _ _ => None)
      (fun _ P Q => Some (AsHy P Q))
      (fun t _ P => Some (AsEx t (fun x => beta (App P x))))
      (fun t _ P => Some (AsAl t (fun x => beta (App P x))))
      None.

    Definition INTRO := @INTRO typ (expr typ func) EV EU fintro.

End IntroTac.

Implicit Arguments INTRO [[HIL] [EU] [EV]].
