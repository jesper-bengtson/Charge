Require Import ExtLib.Tactics.

Require Import MirrorCore.Lambda.Ptrns.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.Views.Ptrns.

Require Import Charge.Views.BILogicView.

Require Import Coq.Logic.FunctionalExtensionality.


Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Section MakeBILogic.
  Context {typ func : Set} {FV : PartialView func (bilfunc typ)}.

  Definition fEmp t := f_insert (bilf_emp t).
  Definition fStar t := f_insert (bilf_star t).
  Definition fWand t := f_insert (bilf_wand t).

  Definition mkEmp t : expr typ func := Inj (fEmp t).
  Definition mkStar (t : typ) (P Q : expr typ func) := App (App (Inj (fStar t)) P) Q.
  Definition mkWand (t : typ) (P Q : expr typ func) := App (App (Inj (fWand t)) P) Q.

  Definition fptrnEmp {T : Type} (p : Ptrns.ptrn typ T) : ptrn (bilfunc typ) T :=
    fun f U good bad =>
      match f with
        | bilf_emp t => p t U good (fun x => bad f)
        | _ => bad f
      end.

  Definition fptrnStar {T : Type} (p : Ptrns.ptrn typ T) : ptrn (bilfunc typ) T :=
    fun f U good bad =>
      match f with
        | bilf_star t => p t U good (fun x => bad f)
        | _ => bad f
      end.

  Definition fptrnWand {T : Type} (p : Ptrns.ptrn typ T) : ptrn (bilfunc typ) T :=
    fun f U good bad =>
      match f with
        | bilf_wand t => p t U good (fun x => bad f)
        | _ => bad f
      end.

  Global Instance fptrnEmp_ok {T : Type} {p : ptrn typ T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnEmp p).
  Proof.
    red; intros.
    destruct x; try (right; unfold Fails; reflexivity); destruct (Hok logic).
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
  Qed.

  Global Instance fptrnStar_ok {T : Type} {p : ptrn typ T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnStar p).
  Proof.
    red; intros.
    destruct x; try (right; unfold Fails; reflexivity); destruct (Hok logic).
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
  Qed.

  Global Instance fptrnWand_ok {T : Type} {p : ptrn typ T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnWand p).
  Proof.
    red; intros.
    destruct x; try (right; unfold Fails; reflexivity); destruct (Hok logic).
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
  Qed.

  Lemma Succeeds_fptrnEmp {T : Type} (f : bilfunc typ) (p : ptrn typ T) (res : T)
        {pok : ptrn_ok p} (H : Succeeds f (fptrnEmp p) res) :
    exists t, Succeeds t p res /\ f = bilf_emp t.
  Proof.
    unfold Succeeds, fptrnEmp in H.
    unfold ptrn_ok in pok.
    specialize (H (option T) Some (fun _ => None)).
    destruct f; try congruence.
    specialize (pok logic).
    destruct pok; [|rewrite H0 in H; congruence].
    destruct H0.
    rewrite H0 in H; inv_all; subst.
    exists logic; split; [assumption | reflexivity].
  Qed.

  Lemma Succeeds_fptrnStar {T : Type} (f : bilfunc typ) (p : ptrn typ T) (res : T)
        {pok : ptrn_ok p} (H : Succeeds f (fptrnStar p) res) :
    exists t, Succeeds t p res /\ f = bilf_star t.
  Proof.
    unfold Succeeds, fptrnStar in H.
    unfold ptrn_ok in pok.
    specialize (H (option T) Some (fun _ => None)).
    destruct f; try congruence.
    specialize (pok logic).
    destruct pok; [|rewrite H0 in H; congruence].
    destruct H0.
    rewrite H0 in H; inv_all; subst.
    exists logic; split; [assumption | reflexivity].
  Qed.

  Lemma Succeeds_fptrnWand {T : Type} (f : bilfunc typ) (p : ptrn typ T) (res : T)
        {pok : ptrn_ok p} (H : Succeeds f (fptrnWand p) res) :
    exists t, Succeeds t p res /\ f = bilf_wand t.
  Proof.
    unfold Succeeds, fptrnWand in H.
    unfold ptrn_ok in pok.
    specialize (H (option T) Some (fun _ => None)).
    destruct f; try congruence.
    specialize (pok logic).
    destruct pok; [|rewrite H0 in H; congruence].
    destruct H0.
    rewrite H0 in H; inv_all; subst.
    exists logic; split; [assumption | reflexivity].
  Qed.

  Global Instance fptrnEmp_SucceedsE {T : Type} {f : bilfunc typ}
         {p : ptrn typ T} {res : T} {pok : ptrn_ok p} :
    SucceedsE f (fptrnEmp p) res := {
      s_result := exists t, Succeeds t p res /\ f = bilf_emp t;
      s_elim := @Succeeds_fptrnEmp T f p res pok
    }.

  Global Instance fptrnAnd_SucceedsE {T : Type} {f : bilfunc typ}
         {p : ptrn typ T} {res : T} {pok : ptrn_ok p} :
    SucceedsE f (fptrnStar p) res := {
      s_result := exists t, Succeeds t p res /\ f = bilf_star t;
      s_elim := @Succeeds_fptrnStar T f p res pok
    }.

  Global Instance fptrnWand_SucceedsE {T : Type} {f : bilfunc typ}
         {p : ptrn typ T} {res : T} {pok : ptrn_ok p} :
    SucceedsE f (fptrnWand p) res := {
      s_result := exists t, Succeeds t p res /\ f = bilf_wand t;
      s_elim := @Succeeds_fptrnWand T f p res pok
    }.

End MakeBILogic.

Section BILogicPtrn.
  Context {typ func : Set} {FV : PartialView func (bilfunc typ)}.

 Definition ptrnEmp {T : Type}
             (p : ptrn typ T) : ptrn (expr typ func) T :=
    inj (ptrn_view _ (fptrnEmp p)).

  Definition ptrnStar {A B T : Type}
             (p : ptrn typ T)
             (a : ptrn (expr typ func) A)
             (b : ptrn (expr typ func) B) : ptrn (expr typ func) (T * A * B) :=
    app (app (inj (ptrn_view _ (fptrnStar p))) a) b.

  Definition ptrnWand {A B T : Type}
             (p : ptrn typ T)
             (a : ptrn (expr typ func) A)
             (b : ptrn (expr typ func) B) : ptrn (expr typ func) (T * A * B) :=
    app (app (inj (ptrn_view _ (fptrnWand p))) a) b.

  Definition bilogic_ptrn_cases {T : Type}
             (do_emp : typ -> T)
             (do_star : typ -> expr typ func -> expr typ func -> T)
             (do_wand : typ -> expr typ func -> expr typ func -> T) :=
    por (inj (ptrn_view _ (fptrnEmp (pmap do_emp Ptrns.get))))
        (appr (appr (inj (ptrn_view _ (por (fptrnStar (pmap do_star Ptrns.get))
                                           (fptrnWand (pmap do_wand Ptrns.get)))))
                    Ptrns.get)
              Ptrns.get).

  Definition bilogic_cases {T : Type}
             (do_emp : typ -> T)
             (do_star : typ -> expr typ func -> expr typ func -> T)
             (do_wand : typ -> expr typ func -> expr typ func -> T)
             (do_default : T) :=
      run_ptrn (bilogic_ptrn_cases
                  do_emp do_star do_wand)
               do_default.
End BILogicPtrn.

Section BILogicPointwiseRes.
  Context {typ func : Set} {FV : PartialView func (bilfunc typ)}.

  Definition bil_pointwise_red
    (f : typ -> expr typ func -> expr typ func) 
    (g : typ -> typ) :=
    bilogic_ptrn_cases
      (fun t => mkEmp (g t))
      (fun t p q => mkStar (g t) (f t p) (f t q))
      (fun t p q => mkWand (g t) (f t p) (f t q)).

End BILogicPointwiseRes.