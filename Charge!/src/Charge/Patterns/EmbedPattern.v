Require Import ExtLib.Tactics.

Require Import MirrorCore.Lambda.Ptrns.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.Views.Ptrns.

Require Import Charge.Views.EmbedView.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Section MakeEmbed.
  Context {typ func : Set} {FV : PartialView func (embed_func typ)}.

  Definition fEmbed t u := f_insert (eilf_embed t u).

  Definition mkEmbed (t u : typ) (p : expr typ func): expr typ func :=
    App (Inj (fEmbed t u)) p.

  Definition fptrnEmbed {T : Type} (p : Ptrns.ptrn (typ * typ) T) : ptrn (embed_func typ) T :=
    fun f U good bad =>
      match f with
        | eilf_embed t u => p (t, u) U good (fun x => bad f)
      end.

  Global Instance fptrnEmbed_ok {T : Type} {p : ptrn (typ * typ) T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnEmbed p).
  Proof.
    red; intros.
    destruct x; try (right; unfold Fails; reflexivity); destruct (Hok (t, t0)).
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
  Qed.

  Lemma Succeeds_fptrnEmbed {T : Type} (f : embed_func typ) (p : ptrn (typ * typ) T) (res : T)
        {pok : ptrn_ok p} (H : Succeeds f (fptrnEmbed p) res) :
    exists t u, Succeeds (t, u) p res /\ f = eilf_embed t u.
  Proof.
    unfold Succeeds, fptrnEmbed in H.
    unfold ptrn_ok in pok.
    specialize (H (option T) Some (fun _ => None)).
    destruct f; try congruence.
    specialize (pok (t, t0)).
    destruct pok; [|rewrite H0 in H; congruence].
    destruct H0.
    rewrite H0 in H; inv_all; subst.
    exists t, t0; split; [assumption | reflexivity].
  Qed.

  Global Instance fptrnEmbed_SucceedsE {T : Type} {f : embed_func typ}
         {p : ptrn (typ * typ) T} {res : T} {pok : ptrn_ok p} :
    SucceedsE f (fptrnEmbed p) res := {
      s_result := exists t u, Succeeds (t, u) p res /\ f = eilf_embed t u;
      s_elim := @Succeeds_fptrnEmbed T f p res pok
    }.

End MakeEmbed.

Section EmbedPtrn.
  Context {typ func : Set} {FV : PartialView func (embed_func typ)}.

  Definition ptrnEmbed {A T : Type}
             (p : ptrn (typ * typ) T)
             (a : ptrn (expr typ func) A) : ptrn (expr typ func) (T * A) :=
    app (inj (ptrn_view _ (fptrnEmbed p))) a.

End EmbedPtrn.