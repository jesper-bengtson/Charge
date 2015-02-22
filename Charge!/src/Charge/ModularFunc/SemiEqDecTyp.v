Require Import MirrorCore.TypesI.

Section SemiEqDecTyp.
  Context (typ : Type) {RType_typ : RType typ}.

  Class SemiEqDecTyp := {
    semi_eq_dec_typ : forall t (a b : typD t), option bool
  }.

  Class SemiEqDecTypOk (SemEq : SemiEqDecTyp) := {
    semi_eq_dec_typOk :
      forall t a b,
        match semi_eq_dec_typ t a b with
          | Some true => a = b
          | Some false => a <> b
          | None => True
        end
  }.

End SemiEqDecTyp.

Implicit Arguments SemiEqDecTypOk [[typ] [RType_typ]].
Implicit Arguments semi_eq_dec_typ [[typ] [RType_typ] [t] [SemiEqDecTyp]].
Implicit Arguments semi_eq_dec_typOk [[typ] [RType_typ] [SemEq] [SemiEqDecTypOk]].
