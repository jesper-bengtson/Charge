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
          | None => False
        end
  }.

End SemiEqDecTyp.

Implicit Arguments SemiEqDecTypOk [[typ] [RType_typ]].
Implicit Arguments semi_eq_dec_typ [[typ] [RType_typ] [t] [SemiEqDecTyp]].
Implicit Arguments semi_eq_dec_typOk [[typ] [RType_typ] [SemEq] [SemiEqDecTypOk]].

Section SemiEqDecTypFacts.
  Context `{SemEqOk : SemiEqDecTypOk}.

  Lemma semi_eq_dec_typ_eq t (a b : typD t) (H : semi_eq_dec_typ a b = Some true) : a = b.
  Proof.
    destruct SemEqOk. specialize (semi_eq_dec_typOk0 t a b).
    rewrite H in semi_eq_dec_typOk0. apply semi_eq_dec_typOk0.
  Qed.
  
  Lemma semi_eq_dec_typ_neq t (a b : typD t) (H : semi_eq_dec_typ a b = Some false) : a <> b.
  Proof.
    destruct SemEqOk. specialize (semi_eq_dec_typOk0 t a b).
    rewrite H in semi_eq_dec_typOk0. apply semi_eq_dec_typOk0.
  Qed.
  
  Lemma semi_eq_dec_typ_refl t (a : typD t) b (H : semi_eq_dec_typ a a = Some b) : b = true.
  Proof.
    destruct SemEqOk. specialize (semi_eq_dec_typOk0 t a a).
    remember (semi_eq_dec_typ a a).
    destruct o; [destruct b0|]; inversion H.
    + reflexivity.
    + contradiction semi_eq_dec_typOk0. reflexivity.
  Qed.
   
End SemiEqDecTypFacts.