(** This file introduces a syntactic separation logic.
 **)
Require Import Coq.Classes.Morphisms.
Require Import ExtLib.Tactics.
Require Import ChargeCore.Logics.ILogic.
Require Import ChargeCore.Logics.BILogic.
Require Import ChargeCore.Logics.Pure.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.Lambda.Expr.

Require Import Charge.Tactics.SepLogFold.

Set Implicit Arguments.
Set Strict Implicit.

Section syn_sep_log.
  Variable typ : Type.
  Variable RType_typ : RType typ.
  Variable Typ2_Fun : Typ2 _ RFun.
  Variable sym : Type.
  Variable RSym_sym : RSym sym.

  Variable SL : typ.

  Variable SLS : SepLogSpec typ sym.
  Variable ILO : ILogicOps (typD SL).
  Variable BILO : BILOperators (typD SL).
  Variable IL : @ILogic _ ILO.
  Variable BIL : @BILogic _ ILO BILO.

  (** TODO: This seems to be defined at the wrong level of abstraction
   ** It is the only piece here that requires that I be in [Ext.expr] rather
   ** than an arbitrary [expr].
   **)
  Variable slsok : SepLogSpecOk _ RSym_sym SL SLS ILO BILO.

  Record SynSepLog : Type :=
  { e_star : expr typ sym -> expr typ sym -> expr typ sym
  ; e_and : expr typ sym -> expr typ sym -> expr typ sym
  ; e_emp : expr typ sym
  ; e_true : expr typ sym
  }.

  Variable SSL : SynSepLog.

  Record SynSepLogOk : Type :=
  { e_empOk : forall tus tvs,
              exists val,
                lambda_exprD tus tvs SL SSL.(e_emp) = Some val /\
                forall us vs, val us vs -|- empSP
  ; e_trueOk : forall tus tvs,
               exists val,
                 lambda_exprD tus tvs SL SSL.(e_true) = Some val /\
                 forall us vs, val us vs -|- ltrue
  ; e_starOk : forall tus tvs x y valx valy,
                 lambda_exprD tus tvs SL x = Some valx ->
                 lambda_exprD tus tvs SL y = Some valy ->
                 exists val,
                   lambda_exprD tus tvs SL (SSL.(e_star) x y) = Some val /\
                   forall us vs, val us vs -|- valx us vs ** valy us vs
  ; e_starValid : forall tus tvs x y val,
                    lambda_exprD tus tvs SL (SSL.(e_star) x y) = Some val ->
                    exists valx valy,
                      lambda_exprD tus tvs SL x = Some valx /\
                      lambda_exprD tus tvs SL y = Some valy /\
                      forall us vs, val us vs -|- valx us vs ** valy us vs
  ; e_andOk : forall tus tvs x y valx valy,
                lambda_exprD tus tvs SL x = Some valx ->
                lambda_exprD tus tvs SL y = Some valy ->
                exists val,
                  lambda_exprD tus tvs SL (SSL.(e_and) x y) = Some val /\
                  forall us vs, val us vs -|- valx us vs //\\ valy us vs
  ; e_andValid : forall tus tvs x y val,
                   lambda_exprD tus tvs SL (SSL.(e_and) x y) = Some val ->
                   exists valx valy,
                     lambda_exprD tus tvs SL x = Some valx /\
                     lambda_exprD tus tvs SL y = Some valy /\
                     forall us vs, val us vs -|- valx us vs //\\ valy us vs
  }.

  Variable SSLO : SynSepLogOk.

  (*
    Local Instance PureOp_it : @PureOp _  := slsok.(_PureOp).
    Local Instance Pure_it : @Pure _ _ _ slsok.(_PureOp) := _Pure slsok.
    Hypothesis pure_ltrue : Pure.pure ltrue.
    Hypothesis pure_land : forall p q, Pure.pure p -> Pure.pure q -> Pure.pure (land p q).
   *)

  Ltac forward_ex_and :=
    repeat match goal with
             | H : exists x, _ |- _ => destruct H
             | H : _ /\ _ |- _ => destruct H
           end.

(*
  (** Primed versions **)
  Lemma exprD'_e_andOk_None1
  : forall us tvs x y,
      exprD' us tvs x SL = None ->
      exprD' us tvs (SSL.(e_and) x y) SL = None.
  Proof.
    intros.
    consider (exprD' us tvs (SSL.(e_and) x y) SL); auto; intros.
    exfalso.
    eapply e_andValid in H0; eauto. forward_ex_and. congruence.
  Qed.

  Lemma exprD'_e_andOk_None2
  : forall us tvs x y,
      exprD' us tvs y SL = None ->
      exprD' us tvs (SSL.(e_and) x y) SL = None.
  Proof.
    intros.
    consider (exprD' us tvs (SSL.(e_and) x y) SL); auto; intros.
    exfalso.
    eapply e_andValid in H0; eauto. forward_ex_and. congruence.
  Qed.

  Lemma exprD'_e_starOk_None1
  : forall us tvs x y,
      exprD' us tvs x SL = None ->
      exprD' us tvs (SSL.(e_star) x y) SL = None.
  Proof.
    intros.
    consider (exprD' us tvs (SSL.(e_star) x y) SL); auto; intros.
    exfalso.
    eapply e_starValid in H0; eauto. forward_ex_and. congruence.
  Qed.

  Lemma exprD'_e_starOk_None2
  : forall us tvs x y,
      exprD' us tvs y SL = None ->
      exprD' us tvs (SSL.(e_star) x y) SL = None.
  Proof.
    intros.
    consider (exprD' us tvs (SSL.(e_star) x y) SL); auto; intros.
    exfalso.
    eapply e_starValid in H0; eauto. forward_ex_and. congruence.
  Qed.

  Lemma exprD'_e_and_None
  : forall us tvs a b,
      exprD' us tvs (SSL.(e_and) a b) SL = None ->
      exprD' us tvs a SL = None \/ exprD' us tvs b SL = None.
  Proof.
    intros.
    consider (exprD' us tvs a SL); intros; auto.
    consider (exprD' us tvs b SL); intros; auto.
    exfalso.
    destruct (@e_andOk SSLO _ _ _ _ _ _ H0 H1).
    intuition; congruence.
  Qed.

  Lemma exprD'_e_star_None
  : forall us tvs a b,
      exprD' us tvs (SSL.(e_star) a b) SL = None ->
      exprD' us tvs a SL = None \/ exprD' us tvs b SL = None.
  Proof.
    intros.
    consider (exprD' us tvs a SL); intros; auto.
    consider (exprD' us tvs b SL); intros; auto.
    exfalso.
    destruct (@e_starOk SSLO _ _ _ _ _ _ H0 H1).
    intuition; congruence.
  Qed.

  (** Unprimed versions **)
  Lemma exprD_e_andOk_None1
  : forall us vs x y,
      exprD us vs x SL = None ->
      exprD us vs (SSL.(e_and) x y) SL = None.
  Proof.
    intros.
    consider (exprD us vs (SSL.(e_and) x y) SL); auto; intros.
    exfalso.
    unfold exprD in *. destruct (split_env vs).
    forward.
    eapply e_andValid in H1; eauto. forward_ex_and. 
    simpl in *. congruence.
  Qed.

  Lemma exprD_e_andOk_None2
  : forall us vs x y,
      exprD us vs y SL = None ->
      exprD us vs (SSL.(e_and) x y) SL = None.
  Proof.
    intros.
    consider (exprD us vs (SSL.(e_and) x y) SL); auto; intros.
    exfalso.
    unfold exprD in *. destruct (split_env vs).
    forward.
    eapply e_andValid in H1; eauto. forward_ex_and. simpl in *; congruence.
  Qed.

  Lemma exprD_e_starOk_None1
  : forall us vs x y,
      exprD us vs x SL = None ->
      exprD us vs (SSL.(e_star) x y) SL = None.
  Proof.
    intros.
    consider (exprD us vs (SSL.(e_star) x y) SL); auto; intros.
    exfalso.
    unfold exprD in *. destruct (split_env vs).
    forward.
    eapply e_starValid in H1; eauto. forward_ex_and. simpl in *; congruence.
  Qed.

  Lemma exprD_e_starOk_None2
  : forall us vs x y,
      exprD us vs y SL = None ->
      exprD us vs (SSL.(e_star) x y) SL = None.
  Proof.
    intros.
    consider (exprD us vs (SSL.(e_star) x y) SL); auto; intros.
    exfalso.
    unfold exprD in *. destruct (split_env vs).
    forward.
    eapply e_starValid in H1; eauto. forward_ex_and. simpl in *; congruence.
  Qed.

  Lemma exprD_e_and_None
  : forall us vs a b,
      exprD us vs (SSL.(e_and) a b) SL = None ->
      exprD us vs a SL = None \/ exprD us vs b SL = None.
  Proof.
    intros.
    consider (exprD us vs a SL); intros; auto.
    consider (exprD us vs b SL); intros; auto.
    exfalso.
    unfold exprD in *. destruct (split_env vs).
    forward.
    destruct (@e_andOk SSLO _ _ _ _ _ _ H1 H2).
    simpl in *; intuition; congruence.
  Qed.

  Lemma exprD_e_star_None
  : forall us vs a b,
      exprD us vs (SSL.(e_star) a b) SL = None ->
      exprD us vs a SL = None \/ exprD us vs b SL = None.
  Proof.
    intros.
    consider (exprD us vs a SL); intros; auto.
    consider (exprD us vs b SL); intros; auto.
    exfalso.
    unfold exprD in *. destruct (split_env vs).
    forward.
    destruct (@e_starOk SSLO _ _ _ _ _ _ H1 H2).
    simpl in *; intuition; congruence.
  Qed.

  Lemma exprD_e_empOk
  : forall us vs,
    exists val : typD ts nil SL,
      exprD us vs SSL.(e_emp) SL = Some val /\
      (val -|- empSP).
  Proof.
    unfold exprD; intros; destruct (split_env vs); destruct (split_env us).
    destruct (SSLO.(e_empOk) x0 x) as [ ? [ ? ? ] ].
    simpl in *. rewrite H. eauto.
  Qed.

  Lemma exprD_e_trueOk
  : forall us vs,
    exists val,
      exprD us vs SSL.(e_true) SL = Some val /\
      (val -|- ltrue).
  Proof.
    unfold exprD; intros; destruct (split_env vs); destruct (split_env us).
    destruct (SSLO.(e_trueOk) x0 x) as [ ? [ ? ? ] ].
    simpl in *; rewrite H. eauto.
  Qed.

  Lemma exprD_e_starOk
  : forall us vs x y valx valy,
      exprD us vs x SL = Some valx ->
      exprD us vs y SL = Some valy ->
      exists val,
        exprD us vs (SSL.(e_star) x y) SL = Some val /\
        (val -|- valx ** valy).
  Proof.
    unfold exprD; intros; destruct (split_env vs); destruct (split_env us).
    forward.
    destruct (@e_starOk SSLO x1 x0 x y _ _ H H0) as [ ? [ ? ? ] ].
    simpl in *; rewrite H3. inv_all; subst. eauto.
  Qed.

  Lemma exprD_e_starValid
  : forall us vs x y val,
      exprD us vs (SSL.(e_star) x y) SL = Some val ->
      exists valx valy,
        exprD us vs x SL = Some valx /\
        exprD us vs y SL = Some valy /\
        (val -|- valx ** valy).
  Proof.
    unfold exprD; intros; destruct (split_env vs); destruct (split_env us).
    forward.
    edestruct (@e_starValid SSLO x1 x0 x) as [ ? [ ? [ ? [ ? ? ] ] ] ]; eauto.
    simpl in *; Cases.rewrite_all_goal.
    inv_all; subst. eauto.
  Qed.

  Lemma exprD_e_andOk
  : forall us vs x y valx valy,
      exprD us vs x SL = Some valx ->
      exprD us vs y SL = Some valy ->
      exists val,
        exprD us vs (SSL.(e_and) x y) SL = Some val /\
        (val -|- valx //\\ valy).
  Proof.
    unfold exprD; intros; destruct (split_env vs); destruct (split_env us).
    simpl in *; forward.
    destruct (@e_andOk SSLO x1 x0 x y _ _ H H0) as [ ? [ ? ? ] ].
    rewrite H3. inv_all; subst. eauto.
  Qed.

  Lemma exprD_e_andValid
  : forall us vs x y val,
      exprD us vs (SSL.(e_and) x y) SL = Some val ->
      exists valx valy,
        exprD us vs x SL = Some valx /\
        exprD us vs y SL = Some valy /\
        (val -|- valx //\\ valy).
  Proof.
    unfold exprD; intros; destruct (split_env vs); destruct (split_env us).
    simpl in *; forward.
    edestruct (@e_andValid SSLO x1 x0 x) as [ ? [ ? [ ? [ ? ? ] ] ] ]; eauto.
    Cases.rewrite_all_goal.
    inv_all; subst. eauto.
  Qed.

  Ltac go_crazy :=
    match goal with
      | H : exprD' _ _ _ _ = _ , H' : _ |- _ =>
        rewrite H in H'
      | H : exprD' _ _ _ _ = _ |- _ =>
        rewrite H
      | H : exprD' _ _ ?C _ = _
            , H' : exprD' _ _ ?D _ = _
        |- context [ exprD' ?A ?B (SSL.(e_and) ?C ?D) ?T ] =>
        destruct (@e_andOk SSLO _ _ _ _ _ _ H H') as [ ? [ ? ? ] ]
      | H : exprD' _ _ ?C _ = _
            , H' : exprD' _ _ ?D _ = _
        |- context [ exprD' ?A ?B (SSL.(e_star) ?C ?D) ?T ] =>
        destruct (@e_starOk SSLO _ _ _ _ _ _ H H') as [ ? [ ? ? ] ]
      | H : exprD' _ _ (SSL.(e_and) _ _) _ = _ |- _ =>
        eapply SSLO.(e_andValid) in H ; destruct H as [ ? [ ? [ ? [ ? ? ] ] ] ]
      | H : exprD' _ _ (SSL.(e_star) _ _) _ = _ |- _ =>
        eapply SSLO.(e_starValid) in H ; destruct H as [ ? [ ? [ ? [ ? ? ] ] ] ]
      | H : exprD' _ _ ?C _ = _
            , H' : exprD' _ _ ?D _ = _
                   , H'' : context [ exprD' ?A ?B (SSL.(e_star) ?C ?D) ?T ]
        |- _ =>
        destruct (@e_starOk SSLO _ _ _ _ _ _ H H') as [ ? [ ? ? ] ]
      | H : exprD' _ _ ?C _ = _
            , H' : exprD' _ _ ?D _ = _
                   , H'' : context [ exprD' ?A ?B (SSL.(e_and) ?C ?D) ?T ]
        |- _ =>
        destruct (@e_andOk SSLO _ _ _ _ _ _ H H') as [ ? [ ? ? ] ]
      | H : exprD' _ _ _ _ = None |- _ =>
        first [ erewrite (@exprD'_e_starOk_None1 _ _ _ _ H) in *
              | erewrite (@exprD'_e_starOk_None2 _ _ _ _ H) in *
              | erewrite (@exprD'_e_andOk_None1 _ _ _ _ H) in *
              | erewrite (@exprD'_e_andOk_None2 _ _ _ _ H) in * ]

      | H : exprD' _ _ _ _ = None |- _ =>
        first [ congruence
              | apply exprD'_e_star_None in H; destruct H; try congruence
              | apply exprD'_e_and_None in H; destruct H; try congruence ]

              (** **)
      | H : exprD _ _ _ _ = _ , H' : _ |- _ =>
        rewrite H in H'
      | H : exprD _ _ _ _ = _ |- _ =>
        rewrite H
      | H : exprD _ _ ?C _ = _
        , H' : exprD _ _ ?D _ = _
        |- context [ exprD ?A ?B (SSL.(e_and) ?C ?D) ?T ] =>
        destruct (@exprD_e_andOk _ _ _ _ _ _ H H') as [ ? [ ? ? ] ]
      | H : exprD _ _ ?C _ = _
        , H' : exprD _ _ ?D _ = _
        |- context [ exprD ?A ?B (SSL.(e_star) ?C ?D) ?T ] =>
        destruct (@exprD_e_starOk _ _ _ _ _ _ H H') as [ ? [ ? ? ] ]
      | H : exprD _ _ (SSL.(e_and) _ _) _ = _ |- _ =>
        eapply (@exprD_e_andValid) in H ; destruct H as [ ? [ ? [ ? [ ? ? ] ] ] ]
      | H : exprD _ _ (SSL.(e_star) _ _) _ = _ |- _ =>
        eapply (@exprD_e_starValid) in H ; destruct H as [ ? [ ? [ ? [ ? ? ] ] ] ]
      | H : exprD _ _ ?C _ = _
            , H' : exprD _ _ ?D _ = _
                   , H'' : context [ exprD ?A ?B (SSL.(e_star) ?C ?D) ?T ]
        |- _ =>
        destruct (@e_starOk SSLO _ _ _ _ _ _ H H') as [ ? [ ? ? ] ]
      | H : exprD _ _ ?C _ = _
            , H' : exprD _ _ ?D _ = _
                   , H'' : context [ exprD ?A ?B (SSL.(e_and) ?C ?D) ?T ]
        |- _ =>
        destruct (@e_andOk SSLO _ _ _ _ _ _ H H') as [ ? [ ? ? ] ]
      | H : exprD _ _ _ _ = None |- _ =>
        first [ erewrite (@exprD_e_starOk_None1 _ _ _ _ H) in *
              | erewrite (@exprD_e_starOk_None2 _ _ _ _ H) in *
              | erewrite (@exprD_e_andOk_None1 _ _ _ _ H) in *
              | erewrite (@exprD_e_andOk_None2 _ _ _ _ H) in * ]

      | H : exprD _ _ _ _ = None |- _ =>
        first [ congruence
              | apply exprD_e_star_None in H; destruct H; try congruence
              | apply exprD_e_and_None in H; destruct H; try congruence ]
    end.

  Local Instance Reflexive_lentails : Reflexive lentails.
  Proof.
    destruct IL. destruct lentailsPre. auto.
  Qed.

  Lemma Sem_equiv_e_and_assoc
  : forall us vs, forall a b c : expr sym,
      Sem_equiv _ SL lequiv us vs
                (SSL.(e_and) a (SSL.(e_and) b c))
                (SSL.(e_and) (SSL.(e_and) a b) c).
  Proof.
    clear - IL SSL SSLO. intros.
    red.
    repeat match goal with
             | |- context [ match ?X with _ => _ end ] =>
               consider X; intros; auto; repeat go_crazy; auto
           end.
    inv_all. subst. Cases.rewrite_all_goal.
    rewrite landA. reflexivity.
  Qed.

  Lemma Sem_equiv_e_star_assoc
  : forall us vs, forall a b c : expr sym,
      Sem_equiv _ SL lequiv us vs (SSL.(e_star) a (SSL.(e_star) b c)) (SSL.(e_star) (SSL.(e_star) a b) c).
  Proof.
    clear - IL SSL SSLO BIL. intros.
    red.
    repeat match goal with
             | |- context [ match ?X with _ => _ end ] =>
               consider X; intros; auto; repeat go_crazy; auto
           end.
    inv_all. subst. Cases.rewrite_all_goal.
    rewrite sepSPA. reflexivity.
  Qed.

  Lemma Sem_equiv_Proper_e_and
  : forall us vs,
      Proper (Sem_equiv _ SL lequiv us vs ==>
              Sem_equiv _ SL lequiv us vs ==>
              Sem_equiv _ SL lequiv us vs) SSL.(e_and).
  Proof.
    unfold Sem_equiv. do 3 red.
    intros; match goal with
              | |- match ?X with _ => _ end =>
                consider X; intros
            end; repeat go_crazy; forward; repeat go_crazy.
    inv_all; subst.
    Cases.rewrite_all_goal. reflexivity.
  Qed.

  Lemma Sem_equiv_Proper_e_star
  : forall us vs,
      Proper (Sem_equiv _ SL lequiv us vs ==>
              Sem_equiv _ SL lequiv us vs ==>
              Sem_equiv _ SL lequiv us vs) SSL.(e_star).
  Proof.
    unfold Sem_equiv. do 3 red.
    intros; match goal with
              | |- match ?X with _ => _ end =>
                consider X; intros
            end; repeat go_crazy; forward; repeat go_crazy.
    inv_all; subst.
    Cases.rewrite_all_goal. reflexivity.
  Qed.

  Lemma ltrue_unitL : forall a, land ltrue a -|- a.
  Proof.
    clear - IL; intros.
    split.
    { eapply landL2. reflexivity. }
    { eapply landR; try reflexivity. eapply ltrueR. }
  Qed.

  Lemma ltrue_unitR : forall a, land a ltrue -|- a.
  Proof.
    clear - IL; intros.
    split.
    { eapply landL1. reflexivity. }
    { eapply landR; try reflexivity. eapply ltrueR. }
  Qed.

  Lemma empSPR : forall a, a ** empSP -|- a.
  Proof.
    clear - BIL IL; intros.
    rewrite sepSPC. rewrite empSPL. reflexivity.
  Qed.

  Lemma Sem_equiv_e_true_e_and_unitLL
  : forall us vs, forall a : expr sym,
      Sem_equiv _ SL lequiv us vs (SSL.(e_and) SSL.(e_true) a) a.
  Proof.
    red; intros.
    destruct (exprD_e_trueOk us vs) as [ ? [ ? ? ] ].
    repeat match goal with
             | |- context [ match ?X with _ => _ end ] =>
               consider X; intros; auto; repeat go_crazy; auto
           end.
    inv_all; subst.
    Cases.rewrite_all_goal.
    rewrite ltrue_unitL. reflexivity.
  Qed.

  Lemma Sem_equiv_e_true_e_and_unitLR
  : forall us vs, forall a : expr sym,
      Sem_equiv _ SL lequiv us vs (SSL.(e_and) a SSL.(e_true)) a.
  Proof.
    red; intros.
    destruct (exprD_e_trueOk us vs) as [ ? [ ? ? ] ].
    repeat match goal with
             | |- context [ match ?X with _ => _ end ] =>
               consider X; intros; auto; repeat go_crazy; auto
           end.
    inv_all; subst.
    Cases.rewrite_all_goal.
    rewrite ltrue_unitR. reflexivity.
  Qed.

  Lemma Sem_equiv_e_true_e_and_unitRL
  : forall us vs, forall a : expr sym,
      Sem_equiv _ SL lequiv us vs a (SSL.(e_and) SSL.(e_true) a).
  Proof.
    red; intros.
    destruct (exprD_e_trueOk us vs) as [ ? [ ? ? ] ].
    repeat match goal with
             | |- context [ match ?X with _ => _ end ] =>
               consider X; intros; auto; repeat go_crazy; auto
           end.
    inv_all; subst.
    Cases.rewrite_all_goal.
    rewrite ltrue_unitL. reflexivity.
  Qed.

  Lemma Sem_equiv_e_true_e_and_unitRR
  : forall us vs, forall a : expr sym,
      Sem_equiv _ SL lequiv us vs a (SSL.(e_and) a SSL.(e_true)).
  Proof.
    red; intros.
    destruct (exprD_e_trueOk us vs) as [ ? [ ? ? ] ].
    repeat match goal with
             | |- context [ match ?X with _ => _ end ] =>
               consider X; intros; auto; repeat go_crazy; auto
           end.
    inv_all; subst.
    Cases.rewrite_all_goal.
    rewrite ltrue_unitR. reflexivity.
  Qed.

  Lemma Sem_equiv_e_emp_e_star_unitLL
  : forall us vs, forall a : expr sym,
      Sem_equiv _ SL lequiv us vs (SSL.(e_star) SSL.(e_emp) a) a.
  Proof.
    red; intros.
    destruct (exprD_e_empOk us vs) as [ ? [ ? ? ] ].
    repeat match goal with
             | |- context [ match ?X with _ => _ end ] =>
               consider X; intros; auto; repeat go_crazy; auto
           end.
    inv_all; subst.
    Cases.rewrite_all_goal.
    rewrite empSPL. reflexivity.
  Qed.

  Lemma Sem_equiv_e_emp_e_star_unitLR
  : forall us vs, forall a : expr sym,
      Sem_equiv _ SL lequiv us vs (SSL.(e_star) a SSL.(e_emp)) a.
  Proof.
    red; intros.
    destruct (exprD_e_empOk us vs) as [ ? [ ? ? ] ].
    repeat match goal with
             | |- context [ match ?X with _ => _ end ] =>
               consider X; intros; auto; repeat go_crazy; auto
           end.
    inv_all; subst.
    Cases.rewrite_all_goal.
    rewrite empSPR. reflexivity.
  Qed.

  Lemma Sem_equiv_e_emp_e_star_unitRL
  : forall us vs, forall a : expr sym,
      Sem_equiv _ SL lequiv us vs a (SSL.(e_star) SSL.(e_emp) a).
  Proof.
    red; intros.
    destruct (exprD_e_empOk us vs) as [ ? [ ? ? ] ].
    repeat match goal with
             | |- context [ match ?X with _ => _ end ] =>
               consider X; intros; auto; repeat go_crazy; auto
           end.
    inv_all; subst.
    Cases.rewrite_all_goal.
    rewrite empSPL. reflexivity.
  Qed.

  Lemma Sem_equiv_e_emp_e_star_unitRR
  : forall us vs, forall a : expr sym,
      Sem_equiv _ SL lequiv us vs a (SSL.(e_star) a SSL.(e_emp)).
  Proof.
    red; intros.
    destruct (exprD_e_empOk us vs) as [ ? [ ? ? ] ].
    repeat match goal with
             | |- context [ match ?X with _ => _ end ] =>
               consider X; intros; auto; repeat go_crazy; auto
           end.
    inv_all; subst.
    Cases.rewrite_all_goal.
    rewrite empSPR. reflexivity.
  Qed.
*)
End syn_sep_log.

(*
(** Ltac's local to a section are not re-introduced **)
Ltac go_crazy SSL SSLO :=
  match goal with
    | [ H : exprD' _ _ _ _ = _ , H' : _ |- _ ] =>
      rewrite H in H'
    | [ H : exprD' _ _ _ _ = _ |- _ ] =>
      rewrite H
    | [ H : exprD' _ _ ?C _ = _
      , H' : exprD' _ _ ?D _ = _
      |- context [ exprD' ?A ?B (SSL.(e_and) ?C ?D) ?T ] ] =>
      destruct (@e_andOk _ _ _ _ _ _ _ SSLO _ _ _ _ _ _ H H') as [ ? [ ? ? ] ]
    | [ H : exprD' _ _ ?C _ = _
      , H' : exprD' _ _ ?D _ = _
      |- context [ exprD' ?A ?B (SSL.(e_star) ?C ?D) ?T ] ] =>
      destruct (@e_starOk _ _ _ _ _ _ _ SSLO _ _ _ _ _ _ H H') as [ ? [ ? ? ] ]
    | [ H : exprD' _ _ (SSL.(e_and) _ _) _ = _ |- _ ] =>
      eapply SSLO.(e_andValid) in H ; destruct H as [ ? [ ? [ ? [ ? ? ] ] ] ]
    | [ H : exprD' _ _ (SSL.(e_star) _ _) _ = _ |- _ ] =>
      eapply SSLO.(e_starValid) in H ; destruct H as [ ? [ ? [ ? [ ? ? ] ] ] ]
    | [ H : exprD' _ _ ?C _ = _
      , H' : exprD' _ _ ?D _ = _
      , H'' : context [ exprD' ?A ?B (SSL.(e_star) ?C ?D) ?T ]
      |- _ ] =>
      destruct (@e_starOk _ _ _ _ _ _ _ SSLO _ _ _ _ _ _ H H') as [ ? [ ? ? ] ]
    | [ H : exprD' _ _ ?C _ = _
      , H' : exprD' _ _ ?D _ = _
      , H'' : context [ exprD' ?A ?B (SSL.(e_and) ?C ?D) ?T ]
      |- _ ] =>
      destruct (@e_andOk _ _ _ _ _ _ _ SSLO _ _ _ _ _ _ H H') as [ ? [ ? ? ] ]
    | [ H : exprD' _ _ _ _ = None |- _ ] =>
      first [ erewrite (@exprD'_e_starOk_None1 _ _ _ _ _ _ _ SSLO _ _ _ _ H) in *
            | erewrite (@exprD'_e_starOk_None2 _ _ _ _ _ _ _ SSLO _ _ _ _ H) in *
            | erewrite (@exprD'_e_andOk_None1 _ _ _ _ _ _ _ SSLO _ _ _ _ H) in *
            | erewrite (@exprD'_e_andOk_None2 _ _ _ _ _ _ _ SSLO _ _ _ _ H) in * ]
    | [ H : exprD' _ _ _ _ = None |- _ ] =>
      first [ congruence
            | apply (@exprD'_e_star_None _ _ _ _ _ _ _ _ SSLO) in H; destruct H; try congruence
            | apply (@exprD'_e_and_None _ _ _ _ _ _ _ _ SSLO) in H; destruct H; try congruence ]


    | [ H : exprD _ _ _ _ = _ , H' : _ |- _ ] =>
      rewrite H in H'
    | [ H : exprD _ _ _ _ = _ |- _ ] =>
      rewrite H
    | [ H : exprD _ _ ?C _ = _
      , H' : exprD _ _ ?D _ = _
      |- context [ exprD ?A ?B (SSL.(e_and) ?C ?D) ?T ] ] =>
      destruct (@exprD_e_andOk _ _ _ _ _ _ _ _ SSLO _ _ _ _ _ _ H H') as [ ? [ ? ? ] ]
    | [ H : exprD _ _ ?C _ = _
      , H' : exprD _ _ ?D _ = _
      |- context [ exprD ?A ?B (SSL.(e_star) ?C ?D) ?T ] ] =>
      destruct (@exprD_e_starOk _ _ _ _ _ _ _ _ SSLO _ _ _ _ _ _ H H') as [ ? [ ? ? ] ]
    | [ H : exprD _ _ (SSL.(e_and) _ _) _ = _ |- _ ] =>
      eapply (@exprD_e_andValid _ _ _ _ _ _ _ _ SSLO) in H ; destruct H as [ ? [ ? [ ? [ ? ? ] ] ] ]
    | [ H : exprD _ _ (SSL.(e_star) _ _) _ = _ |- _ ] =>
      eapply (@exprD_e_starValid _ _ _ _ _ _ _ _ SSLO) in H ; destruct H as [ ? [ ? [ ? [ ? ? ] ] ] ]
    | [ H : exprD _ _ ?C _ = _
      , H' : exprD _ _ ?D _ = _
      , H'' : context [ exprD ?A ?B (SSL.(e_star) ?C ?D) ?T ]
      |- _ ] =>
      destruct (@exprD_e_starOk _ _ _ _ _ _ _ SSLO _ _ _ _ _ _ H H') as [ ? [ ? ? ] ]
    | [ H : exprD _ _ ?C _ = _
      , H' : exprD _ _ ?D _ = _
      , H'' : context [ exprD ?A ?B (SSL.(e_and) ?C ?D) ?T ]
      |- _ ] =>
      destruct (@exprD_e_andOk _ _ _ _ _ _ _ SSLO _ _ _ _ _ _ H H') as [ ? [ ? ? ] ]

    | [ H : exprD _ _ _ _ = None |- _ ] =>
      first [ erewrite (@exprD_e_starOk_None1 _ _ _ _ _ _ _ SSLO _ _ _ _ H) in *
            | erewrite (@exprD_e_starOk_None2 _ _ _ _ _ _ _ SSLO _ _ _ _ H) in *
            | erewrite (@exprD_e_andOk_None1 _ _ _ _ _ _ _ SSLO _ _ _ _ H) in *
            | erewrite (@exprD_e_andOk_None2 _ _ _ _ _ _ _ SSLO _ _ _ _ H) in * ]

    | [ H : exprD _ _ _ _ = None |- _ ] =>
      first [ congruence
            | apply (@exprD_e_star_None _ _ _ _ _ _ _ _ SSLO) in H; destruct H; try congruence
            | apply (@exprD_e_and_None _ _ _ _ _ _ _ _ SSLO) in H; destruct H; try congruence ]
  end.
*)