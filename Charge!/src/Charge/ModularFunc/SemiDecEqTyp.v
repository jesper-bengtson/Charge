Require Import ExtLib.Core.RelDec.

Require Import MirrorCore.Lambda.Expr.

Section SemiDecEqTyp.
  Variable typ : Type.
  Context {RType_typ : RType typ}.

  Definition eq_dec_typ := forall (t : typ) (a b : typD t), option bool.

  Definition eq_dec_typOk (edt : eq_dec_typ) :=
    forall t a b,
      match edt t a b with
        | Some true => a = b
        | Some false => a <> b
        | None => True
      end.

End SemiDecEqTyp.

Implicit Arguments eq_dec_typOk [[typ] [RType_typ]].
