(** This file implements cancellation for separation logic.
 **)
Require Coq.Lists.List.
Require ExtLib.Data.Option.
Require Import ExtLib.Tactics.

Set Implicit Arguments.
Set Strict Implicit.

Section iterated.
  Variable T : Type.
  Variable base : T.
  Variable join : T -> T -> T.

  Fixpoint iterated (ls : list T) : option T :=
    match ls with
      | nil => None
      | List.cons l ls => match iterated ls with
                            | None => Some l
                            | Some ls => Some (join l ls)
                          end
    end.

  Definition iterated_base (ls : list T) : T :=
    match iterated ls with
      | None => base
      | Some l => l
    end.

  Lemma iterated_None : forall ls, iterated ls = None -> ls = nil.
  Proof.
    destruct ls; simpl; intros; try congruence.
    destruct (iterated ls); congruence.
  Qed.

  Require Import Relations Morphisms.
  Require Import RelationClasses.

  Hypothesis R : relation T.
  Hypothesis Reflexive_R : Reflexive R.
  Hypothesis Transitive_R : Transitive R.
  Hypothesis join_assoc : forall a b c, R (join a (join b c)) (join (join a b) c).
  Hypothesis join_respects : Proper (R ==> R ==> R)%signature join.

  Definition option_R (a b : option T) : Prop :=
    match a , b with
      | None , None => True
      | Some a , Some b => R a b
      | _ , _ => False
    end.

  Local Instance Reflexive_optionR : Reflexive option_R.
  Proof.
    red. destruct x; simpl; reflexivity.
  Qed.
  Local Instance Transitive_optionR : Transitive option_R.
  Proof.
    red. destruct x; destruct y; destruct z; simpl; intros; auto.
    etransitivity; eauto. intuition.
  Qed.

  Theorem iterated_app
  : forall ls' ls,
      option_R (iterated (ls ++ ls'))
               (match iterated ls' with
                  | None => iterated ls
                  | Some ls' => match iterated ls with
                                  | None => Some ls'
                                  | Some ls => Some (join ls ls')
                                end
                end).
  Proof.
    induction ls; simpl.
    { intros. destruct (iterated ls'); reflexivity. }
    { intros. unfold option_R in *.
      repeat match goal with
               | |- context [ match ?X with _ => _ end ] =>
                 consider X; intros; try congruence
               | H : context [ match ?X with _ => _ end ] |- _ =>
                 consider X; intros; try congruence
               | H : R _ _ |- _ => rewrite H
             end; inv_all; subst; try solve [ congruence | intuition ].
      { rewrite IHls. etransitivity. 2: eapply join_assoc. reflexivity. }
      { rewrite H5. reflexivity. }
      { rewrite H4; reflexivity. }
      { subst. reflexivity. } }
  Qed.


  Hypothesis Rbase_LL : forall a, R (join base a) a.
  Hypothesis Rbase_LR : forall a, R (join a base) a.
  Hypothesis Rbase_RL : forall a, R a (join base a).
  Hypothesis Rbase_RR : forall a, R a (join a base).

  Theorem iterated_base_app
  : forall ls' ls,
      R (iterated_base (ls ++ ls'))
        (join (iterated_base ls) (iterated_base ls')).
  Proof.
    induction ls; simpl.
    { intros. unfold iterated_base. simpl.
      eapply Rbase_RL. }
    { unfold iterated_base in *; simpl in *.
      destruct (iterated (ls ++ ls')).
      { rewrite IHls.
        rewrite join_assoc.
        destruct (iterated ls); try reflexivity.
        rewrite Rbase_LR. reflexivity. }
      { destruct (iterated ls); destruct (iterated ls'); simpl.
        { rewrite <- join_assoc. rewrite <- IHls. eapply Rbase_RR. }
        { rewrite <- join_assoc. rewrite <- IHls. apply Rbase_RR. }
        { rewrite Rbase_LL in IHls.
          rewrite <- IHls. apply Rbase_RR. }
        { eapply Rbase_RR. } } }
  Qed.

  Theorem iterated_base_cons
  : forall l ls,
      R (iterated_base (l :: ls))
        (join l (iterated_base ls)).
  Proof.
    intros.
    change (l :: ls)%list with ((l :: nil) ++ ls)%list.
    etransitivity. eapply iterated_base_app.
    unfold iterated_base at 1. simpl. reflexivity.
  Qed.

  Variable P : T -> Prop.
  Hypothesis Pjoin : forall a b, P a -> P b -> P (join a b).

  Theorem iterated_inv
  : forall ls,
      List.Forall P ls ->
      match iterated ls with
        | None => ls = nil
        | Some e => P e
      end.
  Proof.
    clear - Pjoin. induction 1; simpl; intros; auto.
    destruct (iterated l); auto.
  Qed.

  Hypothesis Pbase : P base.

  Theorem iterated_base_inv
  : forall ls,
      List.Forall P ls ->
      P (iterated_base ls).
  Proof.
    clear - Pjoin Pbase.
    unfold iterated_base; intros.
    eapply iterated_inv in H. destruct (iterated ls); eauto.
  Qed.

End iterated.