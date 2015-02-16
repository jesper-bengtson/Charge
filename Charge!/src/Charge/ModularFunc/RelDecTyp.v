Require Import ExtLib.Core.RelDec.

Require Import MirrorCore.Lambda.Expr.

Section RelDecTyp.
  Context {typ : Type} {RType_typ : RType typ}.

  Definition rel_dec_typ := forall t, option (RelDec (@eq (typD t))).

  Definition rel_dec_typOk (rdt : rel_dec_typ) :=
	forall t,
      match rdt t with
        | Some rel_dec => RelDec_Correct rel_dec
        | None => True
      end.

End RelDecTyp.