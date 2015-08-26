Require Import ExtLib.Core.RelDec.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.ExprD.
Require Import MirrorCore.Lambda.RedAll.
Require Import MirrorCore.Lambda.AutoSetoidRewriteRtac.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.Lambda.Ptrns.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.RTac.IdtacK.
(*
Set Printing Universes.
Require Import Charge.Views.ILogicView.

Set Implicit Arguments.
Set Strict Implicit.

Section parametric.
  Context {typ func : Type}.
  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {RSym_func : RSym func}.
  Context {RSymOk_func : RSymOk RSym_func}.
  Context {Typ2_Fun : Typ2 _ Fun}.
  Context {Typ2Ok_Fun : Typ2Ok Typ2_Fun}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Typ0Ok_Fun : Typ0Ok Typ0_Prop}.
  Variable RelDec_typ : RelDec (@eq typ).
  Variable lops : logic_ops.
  Variable lopsOk : logic_opsOk lops.
  Context {ViewFunc_ilogic : FuncView func (ilfunc typ)}.
  Context {ViewFuncOk_ilogic : FuncViewOk ViewFunc_ilogic _ (RSym_ilfunc lops)}.

  Existing Instance RType_typ.
  Existing Instance Expr.Expr_expr.

  Definition Rbase := expr typ func.

  Instance Typ2_App2 (F : Type -> Type -> Type) (A B : Type)
  : Typ2 _ F -> Typ0 _ A -> Typ0 _ B -> Typ0 _ (F A B) := _.

  Instance Typ0_rel (t : typ) : Typ0 _ (typD t -> typD t -> Prop).
  eapply Typ2_App2 with (F:=Fun); eauto with typeclass_instances.
  eapply Typ2_App2 with (F:=Fun); eauto with typeclass_instances.
  Defined.

  Definition RbaseD (e : expr typ func) (t : typ)
  : option (TypesI.typD t -> TypesI.typD t -> Prop) :=
    castD option
          (TypesI.typD t -> TypesI.typD t -> Prop)
          (Typ0:=Typ0_rel t)
          (exprD nil nil e (typ0 (F:=TypesI.typD t -> TypesI.typD t -> Prop))).

  Require Import MirrorCore.Lambda.ExprTac.
  Require Import MirrorCore.Util.Compat.
  Require Import MirrorCore.Util.Forwardy.
  Require Import ExtLib.Tactics.


  (** TODO: This should move **)
  Section is_trans_refl.

    Lemma Refl_pointwise : forall {T U : Type} (R : T -> T -> Prop),
      Reflexive R -> Reflexive (pointwise_relation (A:=U) R).
    Proof using.
      compute. auto.
    Qed.

    Lemma Trans_pointwise : forall {T U : Type} (R : T -> T -> Prop),
        Transitive R -> Transitive (pointwise_relation (A:=U) R).
    Proof using.
      compute. eauto.
    Qed.

    Variable is_trans : expr typ func -> bool.
    Fixpoint is_transR (r : @R typ (expr typ func)) : bool :=
      match r with
      | Rinj r => is_trans r
      | Rpointwise _ x => is_transR x
      | Rflip r => is_transR r
      | _ => false
      end.

    Definition is_reflR := is_transR.

    Hypothesis is_transOk : forall r t rD,
        is_trans r = true -> RbaseD r t = Some rD -> Transitive rD.

    Theorem is_transROk : forall r t rD,
        is_transR r = true -> RD RbaseD r t = Some rD -> Transitive rD.
    Proof.
      induction r; simpl; intros; eauto; try congruence.
      { simpl. intros.
        arrow_case_any; try congruence.
        clear H1. red in x1; subst.
        simpl in H0.
        autorewrite_with_eq_rw_in H0.
        forwardy.
        inv_all. subst.
        red. intros.
        revert H1 H3.
        autorewrite_with_eq_rw.
        unfold pointwise_relation.
        eapply IHr in H; [ | eassumption ].
        intros. eauto. }
      { simpl. intros.
        forwardy.
        inv_all; subst.
        red. intros. unfold flip. eapply IHr; eauto. }
    Qed.

    Hypothesis is_reflOk : forall r t rD,
        is_trans r = true -> RbaseD r t = Some rD -> Reflexive rD.

    Theorem is_reflROk : forall r t rD,
        is_reflR r = true -> RD RbaseD r t = Some rD -> Reflexive rD.
    Proof using Typ2Ok_Fun is_reflOk.
      induction r; simpl; intros; eauto; try congruence.
      { arrow_case_any; try congruence.
        clear H1. red in x1; subst.
        simpl in H0.
        autorewrite_with_eq_rw_in H0.
        forwardy.
        inv_all. subst.
        red. intros.
        autorewrite_with_eq_rw.
        unfold pointwise_relation.
        eapply IHr in H; [ | eassumption ].
        intros. eauto. }
      { simpl. intros.
        forwardy.
        inv_all; subst.
        red. intros. unfold flip. eapply IHr; eauto. }
    Qed.

  End is_trans_refl.


  Definition mrw : Type -> Type :=
    @mrw typ func.

  Definition lem_pull_ex_nat_and_left (l_t : typ * typ)
  : rw_lemma (typ:=typ) (func:=func) (expr typ func) :=
    let '(l,t) := l_t in
  {| Lemma.vars := typ2 t l :: l :: nil
   ; Lemma.premises := nil
   ; Lemma.concl := {| lhs := App (App (Inj (fAnd l))
                                       (App (Inj (fExists t l)) (Var 0)))
                                  (Var 1)
                     ; rel := Rinj (Inj (fEntails l))
                     ; rhs := App (Inj (fExists t l))
                                  (Abs t
                                       (App (App (Inj (fAnd l))
                                                 (App (Var 1) (Var 0)))
                                            (Var 2)))
                    |}
  |}.

  Definition lem_pull_ex_nat_and_right (l_t : typ * typ)
  : rw_lemma (typ:=typ) (func:=func) (expr typ func) :=
    let '(l,t) := l_t in
  {| Lemma.vars := typ2 t l :: l :: nil
   ; Lemma.premises := nil
   ; Lemma.concl := {| lhs := App (App (Inj (fAnd l)) (Var 1))
                                  (App (Inj (fExists t l)) (Var 0))
                     ; rel := Rinj (Inj (fEntails l))
                     ; rhs := App (Inj (fExists t l))
                                  (Abs t
                                       (App (App (Inj (fAnd l))
                                                 (Var 2))
                                            (App (Var 1) (Var 0))))
                    |}
  |}.

  Definition is_refl :=
    is_reflR (run_default
                (inj (FuncView.ptrn_view _ (pmap (fun _ => true)
                                                 (fptrnEntails ignore))))
                false).


  Theorem run_default_sound
  : forall {X T} (P : X -> T -> Prop) (p : ptrn X T) (d : T) x,
      ptrn_ok p ->
      (forall res,
          Succeeds x p res ->
          P x res) ->
      P x d ->
      P x (run_default p d x).
  Proof using.
    intros.
    change (@run_default X T) with (fun p d => @run_tptrn X T (pdefault p d)).
    unfold run_tptrn.
    unfold pdefault.
    destruct (H x).
    { destruct H2. red in H2.
      rewrite H2. auto. }
    { red in H2. rewrite H2. auto. }
  Qed.

  Theorem is_reflOk
  : forall r t rD,
      is_refl r = true ->
      RD RbaseD r t = Some rD ->
      Reflexive rD.
  Proof.
    eapply is_reflROk.
    { do 3 intro.
      eapply (fun P => @run_default_sound _ _ P
                                              (inj (typ:=typ)
                                                   (ptrn_view ViewFunc_ilogic
                                                              (pmap (fun _ : unit => true) (fptrnEntails ignore)))) false r).
      { eapply ptrn_ok_inj.
        eapply ptrn_view_ok.
        eapply ptrn_ok_pmap.
        eapply fptrnEntails_ok. }
      { intros. ptrnE.
        eapply Succeeds_ptrn_view in H3. 2: eassumption.
        { forward_reason. ptrnE.
          unfold RbaseD, exprD in H1. simpl in H1.
          unfold ExprDsimul.ExprDenote.exprD' in H1.
          rewrite <- (@fv_compat _ _ ViewFunc_ilogic _ _ _ _ ViewFuncOk_ilogic) in H1.
          unfold symAs, typeof_sym in H1. simpl in H1.
          rewrite castD_option in H1.
          destruct (lops x2) eqn:Hlops; try congruence.
          forwardy; inv_all; subst.
          assert (t = x2).
          { clear - y2 Typ2Ok_Fun.
            eapply typ2_inj in y2. tauto. eauto. }
          subst.
          unfold entailsR.
          unfold exprT_Inj.
          rewrite (UIP_refl y2).
          simpl.
          rewrite castDR.
          specialize (lopsOk x2).
          rewrite Hlops in lopsOk.
          eauto. }
      { eapply ptrn_ok_pmap.
        eapply fptrnEntails_ok. } }
    { simpl. intros; congruence. } }
  Qed.


  Definition is_trans :=
    is_transR (run_default
                 (inj (FuncView.ptrn_view _ (pmap (fun _ => true) (fptrnEntails ignore))))
                 false).


(*
Definition get_respectful_only_all_ex :=
  do_respectful (expr_eq_sdec (typ:=typ) (func:=func) _ rel_dec)
    ((Inj (Ex tyNat), Rrespects (Rpointwise tyNat (Rinj (Inj Impl))) (Rinj (Inj Impl))) ::
     (Inj (All tyNat), Rrespects (Rpointwise tyNat (Rinj (Inj Impl))) (Rinj (Inj Impl))) ::
     nil).
*)

  (** TODO: Make patterns for relations **)
  Definition ptrnRinj {X T : Type} (p : ptrn X T) : ptrn (@R typ X) T :=
    fun r _T good bad =>
      match r with
      | Rinj a => p a _T good (fun x => bad (Rinj x))
      | Rrespects a b => bad (Rrespects a b)
      | Rpointwise a b => bad (Rpointwise a b)
      | Rflip a => bad (Rflip a)
      end.

  Definition ptrnRflip {X T : Type} (p : ptrn (@R typ X) T)
  : ptrn (@R typ X) T :=
    fun r _T good bad =>
      match r with
      | Rinj a => bad (Rinj a)
      | Rrespects a b => bad (Rrespects a b)
      | Rpointwise a b => bad (Rpointwise a b)
      | Rflip a => p a _T good (fun x => bad (Rflip x))
      end.

  Definition ptrnRrespectsL {X T U : Type}
             (pd : ptrn (@R typ X) (T -> U))
             (pr : ptrn (@R typ X) T)
  : ptrn (@R typ X) U :=
    fun r _T good bad =>
      match r with
      | Rinj a => bad (Rinj a)
      | Rrespects a b => pr b _T (fun x => pd a _T (fun y => good (y x))
                                              (fun a => bad (Rrespects a b)))
                            (fun b => bad (Rrespects a b))
      | Rpointwise a b => bad (Rpointwise a b)
      | Rflip a => bad (Rflip a)
      end.

  Definition ptrnRpointwiseL {X T U : Type}
             (pd : ptrn typ (T -> U))
             (pr : ptrn (@R typ X) T)
  : ptrn (@R typ X) U :=
    fun r _T good bad =>
      match r with
      | Rinj a => bad (Rinj a)
      | Rpointwise a b => pr b _T (fun x => pd a _T (fun y => good (y x))
                                              (fun a => bad (Rpointwise a b)))
                            (fun b => bad (Rpointwise a b))
      | Rrespects a b => bad (Rrespects a b)
      | Rflip a => bad (Rflip a)
      end.

  (** This function defines what terms respect what relations **)
  Definition get_respectful
             (e : expr typ func) (r : R (typ:=typ) (expr typ func))
  : list (R (typ:=typ) (expr typ func)) :=
    let if_entails Y X :=
        run_default (inj (ptrn_view _ (pmap (fun _ =>
                                               Y) (fptrnEntails get)))) nil X
    in
    run_default (Ptrns.inj (ptrn_view _
         (pors
           (pmap (fun l_t => let '(l,t) := l_t in
                             match r with
                             | Rinj X
                             | Rflip (Rinj X) =>
                               if_entails (Rrespects (Rpointwise t r) r :: nil)
                                          X
                             | _ => nil
                             end) (fptrnExists get) ::
            pmap (fun l => match r with
                            | Rinj X
                            | Rflip (Rinj X) =>
                              if_entails (Rrespects r (Rrespects r r) :: nil) X
                            | _ => nil
                            end) (por (fptrnAnd get) (fptrnOr get)) ::
            pmap (fun l => match r with
                            | Rinj X
                            | Rflip (Rinj X) =>
                              if_entails (Rrespects (Rflip' r) (Rrespects r r) :: nil) X
                            | _ => nil
                            end) (fptrnImpl get) ::
            nil))))
       nil
       e.

  (* This was necessary for post-processing the substitution *)
  Definition simple_reduce (e : expr typ func) : expr typ func :=
    run_default
      (pmap (fun abcd => let '(a,(b,(c,d),e)) := abcd in
                         App a (Abs c (App (App b d) e)))
            (app get (abs get (fun t =>
                                 app (app get (pmap (fun x => (t,Red.beta x)) get))
                                     (pmap Red.beta get)))))
      e e.

  Definition func_sdec (a b : func) : bool :=
    match sym_eqb a b with
    | Some x => x
    | _ => false
    end.

  Definition expr_sdec : expr typ func -> expr typ func -> bool :=
    @expr_eq_sdec typ func _ func_sdec.

  (** TODO(gmalecha): Move this *)
  Definition using_prewrite_db
             (ls : expr typ func ->
                   list (rw_lemma(typ:=typ) (func:=func) (expr typ func) *
                         CoreK.rtacK typ (expr typ func)))
    : expr typ func -> R (typ:=typ) Rbase -> mrw (expr typ func) :=
      fun e r =>
        for_tactic (fun e => using_rewrite_db' expr_sdec (ls e) e r) e.


  Definition the_rewrites
             (lems : list (rw_lemma (typ:=typ) (func:=func) (expr typ func) *
                           CoreK.rtacK typ (expr typ func)))
  : expr typ func -> R (typ:=typ) Rbase -> mrw (Progressing (expr typ func)) :=
    fun e r =>
      rw_bind
        (@using_rewrite_db typ func _ _ _ _ (expr typ func)
                           expr_sdec
                           lems (Red.beta e) r)
        (fun e' => rw_ret (Progress (simple_reduce e'))).

  Definition the_prewrites
             (lems : expr typ func ->
                     list ((rw_lemma(typ:=typ) (func:=func) (expr typ func) *
                         CoreK.rtacK typ (expr typ func))))
  : expr typ func -> R (typ:=typ) Rbase -> mrw (Progressing (expr typ func)) :=
    fun e r =>
      rw_bind
        (@using_prewrite_db lems (Red.beta e) r)
        (fun e' => rw_ret (Progress (simple_reduce e'))).

  Definition poly_apply
             (get : ptrn (expr typ func)
                         (list (rw_lemma (typ:=typ) (func:=func) (expr typ func) *
                                CoreK.rtacK typ (expr typ func))))
  : expr typ func -> list (rw_lemma (typ:=typ) (func:=func) (expr typ func)
                           * CoreK.rtacK typ (expr typ func)) :=
    run_default get nil.

  (** TODO(gmalecha): Move this *)
  Definition appl {typ func T U : Type}
        (f : ptrn (expr typ func) T)
        (g : ptrn (expr typ func) (T -> U)) : ptrn (expr typ func) U :=
          fun e _T good bad =>
      match e with
      | ExprCore.Var a => bad (ExprCore.Var a)
      | Inj a => bad (Inj a)
      | App l r =>
        Mbind (Mrebuild (fun x => App x r) (f l))
              (fun x : T =>
                 Mmap (fun y : T -> U => y x)
                      (Mrebuild (App l) (g r))) good bad
      | Abs a b => bad (Abs a b)
      | ExprCore.UVar a => bad (ExprCore.UVar a)
      end.

  Theorem ptrn_ok_appl
  : forall {typ func T U}
           (f : ptrn (expr typ func) T)
           (g : ptrn (expr typ func) (T -> U)),
      ptrn_ok f -> ptrn_ok g ->
      ptrn_ok (appl f g).
  Proof using.
    intros; red.
    destruct x; simpl;
    try solve [ right; compute; reflexivity ].
    destruct (H0 x2) as [ [ ? ? ] | ? ]; clear H0.
    { destruct (H x1) as [ [ ? ? ] | ? ]; clear H.
      { left. exists (x x0).
        unfold Succeeds in *.
        intros. simpl.
        unfold Mmap, Mbind, Mrebuild.
        setoid_rewrite H0. setoid_rewrite H1. reflexivity. }
      { right.
        unfold Succeeds, Fails in *.
        intros; simpl.
        unfold Mmap, Mbind, Mrebuild.
        setoid_rewrite H0. reflexivity. } }
    { right.
      destruct (H x1) as [ [ ? ? ] | ? ]; clear H.
      { unfold Succeeds, Fails in *.
        intros; simpl.
        unfold Mmap, Mbind, Mrebuild.
        setoid_rewrite H0. setoid_rewrite H1. reflexivity. }
      { unfold Succeeds, Fails in *.
        intros; simpl.
        unfold Mmap, Mbind, Mrebuild.
        setoid_rewrite H0. reflexivity. } }
  Qed.

  Definition the_lemmas
  : expr typ func -> list (rw_lemma (expr typ func) *
                           CoreK.rtacK typ (expr typ func)) :=
    poly_apply (por
                  (appr (appl (inj (ptrn_view _ (fptrnAnd ignore)))
                              (appr (inj (ptrn_view _ (fptrnExists (pmap (fun ts _ _ _ => (lem_pull_ex_nat_and_left ts, IDTACK) :: nil) get)))) ignore))
                        ignore)
                  (appl (appr (inj (ptrn_view _ (fptrnAnd (pmap (fun _ x => x) ignore)))) ignore)
                        (appr (inj (ptrn_view _ (fptrnExists (pmap (fun ts _ _ => (lem_pull_ex_nat_and_left ts, IDTACK) :: nil) get)))) ignore))).

  (** TODO(gmalecha): Move this **)
  Fixpoint repeatFunc (n : nat)
           (p : expr typ func -> Progressing (expr typ func))
  : (expr typ func -> R (typ:=typ) (expr typ func) ->
     mrw (Progressing (expr typ func))) ->
    expr typ func -> R (typ:=typ) (expr typ func) ->
    mrw (Progressing (expr typ func)) :=
    match n with
    | 0 => fun f e r =>
             rw_bind (f e r)
                     (fun e' =>
                        match e' with
                        | NoProgress _ => rw_ret (p e)
                        | Progress e' => rw_ret (Progress e')
                        end)
    | S n => fun f e r =>
               rw_bind
                 (f e r)
                 (fun e' =>
                    match e' with
                    | NoProgress _ => rw_ret (p e)
                    | Progress e' => repeatFunc n (@Progress _) f e' r
                    end)
    end.

  Require Import MirrorCore.Lambda.Red.

  Definition pull_all_quant :=
    repeatFunc 300 (fun _ => NoProgress _)
               (fun e r =>
                  bottom_up is_refl is_trans (the_prewrites the_lemmas)
                            (fun e r => rw_ret (get_respectful e r)) e r).

  Definition quant_pull (l : typ) (e : expr typ func)
  : mrw (Progressing (expr typ func)) :=
    bottom_up is_refl is_trans (pull_all_quant)
              (fun e r => rw_ret (get_respectful e r))
              e (Rinj (Inj (fEntails l))).

(*
  Time Eval vm_compute
    in match quant_pull (goal2 8 0) nil nil nil 0 0 (TopSubst _ nil nil) with
       | Some _ => tt
       | None => tt
       end.
*)
End parametric.
*)
