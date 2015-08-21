Require Import ExtLib.Core.RelDec.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.ExprD.
Require Import MirrorCore.Lambda.RedAll.
Require Import MirrorCore.Lambda.AutoSetoidRewriteRtac.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.Lambda.Ptrns.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.RTac.IdtacK.
Require Import Charge.Tactics.Views.ILogicView.

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
  Variable RelDec_Correct_typ : RelDec_Correct RelDec_typ.
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

  Definition mrw : Type -> Type :=
    @mrw typ func.

  Definition lem_pull_ex_nat_and_left (l_t : typ * typ)
  : rw_lemma typ func (expr typ func) :=
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
  : rw_lemma typ func (expr typ func) :=
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

  Definition is_refl : expr typ func -> bool :=
    run_default
      (inj (FuncView.ptrn_view _ (pmap (fun _ => true)
                                       (fptrnEntails ignore))))
      false.

  Theorem is_reflOk
  : forall r t rD,
      is_refl r = true ->
      RbaseD r t = Some rD ->
      Reflexive rD.
  Proof.
    do 3 intro.
    unfold is_refl.
    eapply (fun P => @run_default_sound _ _ P
                       (inj (typ:=typ)
                            (ptrn_view ViewFunc_ilogic
                                       (pmap (fun _ : unit => true) (fptrnEntails ignore)))) false r).
    { (* This is a Coq bug *)
      eapply ptrn_ok_inj.
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
    { simpl. intros; congruence. }
  Qed.

  Definition is_trans : expr typ func -> bool :=
    is_refl.

  Theorem is_transOk
  : forall r t rD,
      is_trans r = true ->
      RbaseD r t = Some rD ->
      Transitive rD.
  Proof.
    do 3 intro.
    unfold is_trans, is_refl.
    eapply (fun P => @run_default_sound _ _ P
                       (inj (typ:=typ)
                            (ptrn_view ViewFunc_ilogic
                                       (pmap (fun _ : unit => true) (fptrnEntails ignore)))) false r).
    { (* This is a Coq bug *)
      eapply ptrn_ok_inj.
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
        eapply PreOrder_Transitive. }
      { eapply ptrn_ok_pmap.
        eapply fptrnEntails_ok. } }
    { simpl. intros; congruence. }
  Qed.

  Definition if_entails (t : typ) Y (X : expr typ func) : mrw (list (R typ (expr typ func))) :=
    run_default (inj (ptrn_view _ (pmap (fun t' => if t ?[ eq ] t' then rw_ret Y else rw_fail)
                                        (fptrnEntails get)))) (rw_fail) X.

  (** This function defines what terms respect what relations **)
  Definition get_respectful
             (e : expr typ func) (r : R typ (expr typ func))
  : mrw (list (R typ (expr typ func))) :=
    run_default (Ptrns.inj (ptrn_view _
         (pors
           (pmap (fun t_l => let '(t,l) := t_l in
                             match r with
                             | Rinj X
                             | Rflip (Rinj X) =>
                               if_entails l (Rpointwise t r :: nil) X
                             | _ => rw_fail
                             end) (fptrnExists get) ::
            pmap (fun l => match r with
                            | Rinj X
                            | Rflip (Rinj X) =>
                              if_entails l (r :: r :: nil) X
                            | _ => rw_fail
                            end) (por (fptrnAnd get) (fptrnOr get)) ::
            pmap (fun l => match r with
                            | Rinj X
                            | Rflip (Rinj X) =>
                              if_entails l (Rflip' r :: r :: nil) X
                            | _ => rw_fail
                            end) (fptrnImpl get) ::
            nil))))
       (rw_fail)
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
                   list (rw_lemma typ func (expr typ func) *
                         CoreK.rtacK typ (expr typ func)))
    : expr typ func -> R typ Rbase -> mrw (expr typ func) :=
      fun e r =>
        for_tactic (fun e => using_rewrite_db' expr_sdec (ls e) e r) e.


  Definition the_rewrites
             (lems : list (rw_lemma typ func (expr typ func) *
                           CoreK.rtacK typ (expr typ func)))
  : expr typ func -> R typ Rbase -> mrw (Progressing (expr typ func)) :=
    fun e r =>
      rw_bind
        (@using_rewrite_db typ func _ _ _ _ (expr typ func)
                           expr_sdec
                           lems (Red.beta e) r)
        (fun e' => rw_ret (Progress (simple_reduce e'))).

  Definition the_prewrites
             (lems : expr typ func ->
                     list (rw_lemma typ func (expr typ func) *
                           CoreK.rtacK typ (expr typ func)))
  : expr typ func -> R typ Rbase -> mrw (Progressing (expr typ func)) :=
    fun e r =>
      rw_bind
        (@using_prewrite_db lems (Red.beta e) r)
        (fun e' => rw_ret (Progress (simple_reduce e'))).

  Definition poly_apply
             (get : ptrn (expr typ func)
                         (list (rw_lemma typ func (expr typ func) *
                                CoreK.rtacK typ (expr typ func))))
  : expr typ func -> list (rw_lemma typ func (expr typ func)
                           * CoreK.rtacK typ (expr typ func)) :=
    run_default get nil.

  Definition the_lemmas
  : expr typ func -> list (rw_lemma typ func (expr typ func) *
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
  : (expr typ func -> R typ (expr typ func) ->
     mrw (Progressing (expr typ func))) ->
    expr typ func -> R typ (expr typ func) ->
    mrw (Progressing (expr typ func)) :=
    match n with
    | 0 => fun f e r =>
             rw_bind (f e r)
                     (fun e' =>
                        match e' with
                        | NoProgress => rw_ret (p e)
                        | Progress e' => rw_ret (Progress e')
                        end)
    | S n => fun f e r =>
               rw_bind
                 (f e r)
                 (fun e' =>
                    match e' with
                    | NoProgress => rw_ret (p e)
                    | Progress e' => repeatFunc n (@Progress _) f e' r
                    end)
    end.

  Definition pull_all_quant :=
    repeatFunc 300 (fun _ => NoProgress)
               (fun e r =>
                  bottom_up (is_reflR is_refl)
                            (is_transR is_trans)
                            (the_prewrites the_lemmas)
                            (get_respectful) e r).

  Lemma if_entails_sound : forall t X r a b c d e f g h i,
      @if_entails t X r a b c d e f g = Some (h,i) ->
      g = i /\ h = X /\ r = Inj (f_insert (ilf_entails t)).
  Proof.
    intros. revert H.
    unfold if_entails.
    eapply run_default_sound; eauto 100 with typeclass_instances.
    { intros. ptrnE.
      eapply Succeeds_ptrn_view in H2; eauto 100 with typeclass_instances.
      destruct H2 as [ ? [ ? ? ] ].
      subst. ptrnE.
      consider (t ?[ eq ] x).
      { intros. inversion H0; clear H0; subst.
        split; auto. }
      { inversion 2. } }
    { inversion 1. }
  Qed.

  Lemma acc_fold_right
    : forall t ts t',
      TransitiveClosure.leftTrans (tyAcc (typ:=typ))
                                  t (fold_right (typ2 (F:=Fun)) t (t'::ts)).
  Proof.
    induction ts.
    { simpl; intros. constructor. eapply tyAcc_typ2R; eauto. }
    { intros. specialize IHts.
      specialize (IHts a).
      simpl. eapply TransitiveClosure.leftTrans_rightTrans.
      eapply TransitiveClosure.RTStep.
      eapply TransitiveClosure.leftTrans_rightTrans. eassumption.
      eapply tyAcc_typ2R; eauto. }
  Qed.

  Lemma Rty_fold_right
    : forall y x ts,
      Rty (fold_right (typ2 (F:=Fun)) x ts) (typ2 y x) ->
      ts = y :: nil.
  Proof.
    intros. red in H.
    destruct ts; simpl in *.
    { eapply AppN.tyArr_circ_R in H; eauto. destruct H. }
    eapply typ2_inj in H; eauto.
    destruct H. destruct H.
    destruct ts.
    { reflexivity. }
    { exfalso.
      generalize (acc_fold_right x ts t0).
      assert (well_founded (TransitiveClosure.leftTrans (tyAcc (typ:=typ)))).
      { eapply Relation.wf_leftTrans.
        eapply wf_tyAcc; eauto. }
      intro. eapply Facts.wf_anti_sym in H.
      rewrite H0 in H1.
      eapply H. eassumption. }
  Qed.

  Lemma Rty_fold_right2
    : forall y x z ts,
      Rty (fold_right (typ2 (F:=Fun)) x ts) (typ2 y (typ2 z x)) ->
      ts = y :: z :: nil.
  Proof.
    intros. red in H.
    destruct ts.
    { exfalso.
      simpl in *.
      assert (well_founded (TransitiveClosure.leftTrans (tyAcc (typ:=typ)))).
      { eapply Relation.wf_leftTrans.
        eapply wf_tyAcc; eauto. }
      eapply Facts.wf_anti_sym in H0.
      eapply H0. instantiate (1 := x).
      rewrite H at 2.
      eapply TransitiveClosure.leftTrans_rightTrans.
      eapply TransitiveClosure.RTStep.
      2: eapply tyAcc_typ2R; eauto.
      constructor.
      eapply tyAcc_typ2R; eauto. }
    simpl in H.
    apply typ2_inj in H; eauto. destruct H.
    destruct H.
    eapply Rty_fold_right in H0. subst. reflexivity.
  Qed.

  Lemma RbaseD_entails'
    : forall t t' rD,
      RbaseD (Inj (f_insert (ilf_entails t'))) t = Some rD ->
      t = t' /\
      exists L,
        lops t = _Some L /\
        rD = ILogic.lentails.
  Proof.
    unfold RbaseD, exprD; simpl.
    intros. autorewrite with exprD_rw in H.
    simpl in H.
    rewrite <- (@fv_compat _ _ _ _ _ _ _ ViewFuncOk_ilogic) in H.
    unfold symAs, typeof_sym in H. simpl in H.
    rewrite castD_option in H.
    destruct (lops t') eqn:heq; try solve [ inversion H ].
    forwardy.
    inv_all. subst.
    Rty_inv. Rty_inv. split; auto.
    eexists; split; eauto.
    rewrite type_cast_refl in H by eauto.
    inv_all.
    simpl in H.
    unfold entailsR. simpl. unfold id.
    rewrite castDR. auto.
  Qed.

  Lemma RbaseD_entails
    : forall t rD,
      RbaseD (Inj (f_insert (ilf_entails t))) t = Some rD ->
      exists L,
        lops t = _Some L /\
        rD = ILogic.lentails.
  Proof.
    unfold RbaseD, exprD; simpl.
    intros. autorewrite with exprD_rw in H.
    simpl in H.
    rewrite <- (@fv_compat _ _ _ _ _ _ _ ViewFuncOk_ilogic) in H.
    unfold symAs, typeof_sym in H. simpl in H.
    rewrite castD_option in H.
    destruct (lops t); try solve [ inversion H ].
    eexists; split; eauto.
    rewrite type_cast_refl in H by eauto.
    inv_all.
    simpl in H.
    unfold entailsR in H.
    rewrite castDR in H. auto.
  Qed.

  Lemma binary_inference
  : let rs_log := @RSym_ilfunc typ _ _ _ _ lops in
    forall (X : ilfunc typ) t x ts r rD x0,
      (r = Rinj (Inj (f_insert (ilf_entails x))) \/
       r = Rflip (Rinj (Inj (f_insert (ilf_entails x))))) ->
      RD RbaseD r t = Some rD ->
      symAs X (fold_right (typ2 (F:=Fun)) t ts) = Some x0 ->
      typeof_sym X = Some (typ2 (F:=Fun) x (typ2 (F:=Fun) x x)) ->
      t = x /\ ts = t :: t :: nil.
  Proof.
    unfold symAs, RbaseD, exprD; simpl.
    destruct 1; simpl; subst; simpl; intros.
    { generalize dependent (funcD lops X).
      rewrite H1.
      intros. forwardy.
      clear H2 H0.
      autorewrite with exprD_rw in H. simpl in H.
      rewrite <- (@fv_compat _ _ _ _ _ _ _ ViewFuncOk_ilogic) in H.
      unfold symAs, typeof_sym in H; simpl in H.
      rewrite castD_option in H.
      destruct (lops x); [ inversion H | ].
      forwardy.
      inv_all. subst.
      Rty_inv. Rty_inv.
      split; auto.
      eapply Rty_fold_right2.
      eauto. }
    { generalize dependent (funcD lops X).
      rewrite H1.
      intros. forwardy.
      clear H2 H0.
      autorewrite with exprD_rw in H. simpl in H.
      rewrite <- (@fv_compat _ _ _ _ _ _ _ ViewFuncOk_ilogic) in H.
      unfold symAs, typeof_sym in H; simpl in H.
      rewrite castD_option in H.
      destruct (lops x); [ inversion H | ].
      forwardy.
      inv_all. subst.
      Rty_inv. Rty_inv.
      split; auto.
      eapply Rty_fold_right2.
      eauto. }
  Qed.

  (** It would be nice if we could prove this more quickly *)
  Theorem get_respectful_sound
  : respectful_spec RbaseD get_respectful.
  Proof.
    red. intros.
    generalize dependent e. intro.
    unfold get_respectful.
    eapply run_default_sound.
    { eauto 100 with typeclass_instances. }
    { intros.
      ptrnE.
      eapply Succeeds_ptrn_view in H3; eauto 100 with typeclass_instances.
      destruct H3 as [ ? [ ? ? ] ].
      repeat (ptrnE; try match goal with
                         | H : _ \/ _ |- _ => destruct H
                         end).
      { assert (exists X, (r = Rinj X \/ r = Rflip (Rinj X)) /\
                   if_entails t0 (Rpointwise t r :: nil) X tvs' (getUVars ctx) (getVars ctx) (length (getUVars ctx))
                              (length (getVars ctx)) cs = Some (rs, cs')).
        { destruct r; eauto; try solve [ inversion H1 ].
          destruct r; eauto; try solve [ inversion H1 ]. }
        clear H1. destruct H. destruct H.
        eapply if_entails_sound in H1.
        destruct H1 as [ ? [ ? ? ] ]. subst.
        split; auto. intros.
        forward.
        simpl.
        autorewrite with exprD_rw in H2. simpl in H2.
        forwardy. inv_all. subst.

        assert (t1 = t0 /\ ts = typ2 t t0 :: nil).
        { eapply ExprFacts.symAs_typeof_sym in H3.
          simpl in H3.
          destruct (lops t0) eqn:Heq; [ inversion H3 | ].
          inv_all.
          assert (t1 = t0).
          { destruct H; subst.
            simpl in H1.
            eapply RbaseD_entails' in H1; tauto.
            simpl in H1.
            forwardy.
            eapply RbaseD_entails' in H; tauto. }
          subst. split; auto.
          eapply Rty_fold_right. symmetry. eassumption. }
        destruct H4; subst.
        simpl.
        repeat rewrite typ2_match_iota by eauto.
        rewrite type_cast_refl by eauto.
        rewrite H1.
        autorewrite_with_eq_rw.
        split; [ reflexivity | ].
        intros.
        eapply Pure_pctxD; eauto. intros.
        unfold Morphisms.Proper.
        autorewrite_with_eq_rw.

        destruct H; subst.
        { eapply RbaseD_entails in H1.
          destruct H1 as [ ? [ ? ? ] ].
          subst.
          unfold symAs in H3.
          simpl in H3.
          rewrite H in H3.
          rewrite type_cast_refl in H3 by eauto.
          inv_all. subst.
          simpl.
          unfold respectful, existsR.
          specialize (lopsOk t0). rewrite H in lopsOk.
          clear - lopsOk.
          unfold castR. simpl.
          generalize (typ2_cast (typ2 t t0) t0).
          generalize (typ2_cast t t0).
          generalize (typD (typ2 t t0)).
          generalize (typD (typ2 (typ2 t t0) t0)).
          intros; subst. simpl in *.
          eapply ILogic.lexists_lentails_m.
          red. intros. eapply H. }
        { simpl in H1. forwardy.
          eapply RbaseD_entails in H.
          destruct H as [ ? [ ? ? ] ].
          subst.
          unfold symAs in H3.
          simpl in H3.
          rewrite H in H3.
          rewrite type_cast_refl in H3 by eauto.
          inv_all. subst.
          simpl.
          unfold respectful, existsR.
          specialize (lopsOk t0). rewrite H in lopsOk.
          clear - lopsOk.
          unfold castR. simpl.
          generalize (typ2_cast (typ2 t t0) t0).
          generalize (typ2_cast t t0).
          generalize (typD (typ2 t t0)).
          generalize (typD (typ2 (typ2 t t0) t0)).
          intros; subst. simpl in *.
          eapply ILogic.lexists_lentails_m.
          red. intros. eapply H. } }
      { (* AND *)
        assert (exists X, (r = Rinj X \/ r = Rflip (Rinj X)) /\
                   if_entails x (r :: r :: nil) X tvs' (getUVars ctx) (getVars ctx) (length (getUVars ctx))
                              (length (getVars ctx)) cs = Some (rs, cs')).
        { destruct r; eauto; try solve [ inversion H1 ].
          destruct r; eauto; try solve [ inversion H1 ]. }
        clear H1. destruct H. destruct H.
        eapply if_entails_sound in H1.
        destruct H1 as [ ? [ ? ? ] ]. subst.
        split; auto. intros.
        forward.
        simpl.
        autorewrite with exprD_rw in H2. simpl in H2.
        forwardy. inv_all. subst.
        generalize (@binary_inference (ilf_and x) _ _ _ _ _ _ H H1 H3).
        unfold symAs, typeof_sym in H3; simpl in H3.
        simpl.
        destruct (lops x) eqn:Hlops; try solve [ inversion H3 ].
        intro Hx; specialize (Hx eq_refl); destruct Hx; subst.
        simpl.
        rewrite type_cast_refl in * by eauto.
        inv_all. subst.
        repeat rewrite typ2_match_iota by eauto.
        rewrite H1.
        autorewrite_with_eq_rw.
        split; [ reflexivity | ].
        intros.
        eapply Pure_pctxD; eauto. intros.
        unfold Morphisms.Proper.
        autorewrite_with_eq_rw.

        destruct H; subst.
        { eapply RbaseD_entails in H1.
          destruct H1 as [ ? [ ? ? ] ].
          rewrite Hlops in H. inversion H; clear H; subst.
          specialize (lopsOk x).
          rewrite Hlops in lopsOk.
          clear - lopsOk.
          unfold respectful, andR, castR. simpl.
          generalize (typ2_cast x (typ2 x x)).
          generalize (typ2_cast x x).
          generalize (typD (typ2 x x)).
          generalize (typD (typ2 x (typ2 x x))).
          intros; subst; simpl.
          intros. rewrite H. rewrite H0. reflexivity. }
        { simpl in H1. forwardy.
          eapply RbaseD_entails in H.
          destruct H as [ ? [ ? ? ] ].
          inv_all; subst.
          specialize (lopsOk x).
          rewrite Hlops in lopsOk.
          rewrite Hlops in H. inversion H. subst.
          clear - lopsOk.
          unfold respectful, andR, castR. simpl.
          generalize (typ2_cast x (typ2 x x)).
          generalize (typ2_cast x x).
          generalize (typD (typ2 x x)).
          generalize (typD (typ2 x (typ2 x x))).
          intros; subst; simpl.
          intros. unfold flip in *.
          rewrite H. rewrite H0. reflexivity. } }
      { (* OR *)
        assert (exists X, (r = Rinj X \/ r = Rflip (Rinj X)) /\
                   if_entails x (r :: r :: nil) X tvs' (getUVars ctx) (getVars ctx) (length (getUVars ctx))
                              (length (getVars ctx)) cs = Some (rs, cs')).
        { destruct r; eauto; try solve [ inversion H1 ].
          destruct r; eauto; try solve [ inversion H1 ]. }
        clear H1. destruct H. destruct H.
        eapply if_entails_sound in H1.
        destruct H1 as [ ? [ ? ? ] ]. subst.
        split; auto. intros.
        forward.
        simpl.
        autorewrite with exprD_rw in H2. simpl in H2.
        forwardy. inv_all. subst.
        generalize (@binary_inference (ilf_or x) _ _ _ _ _ _ H H1 H3).
        unfold symAs, typeof_sym in H3; simpl in H3.
        simpl.
        destruct (lops x) eqn:Hlops; try solve [ inversion H3 ].
        intro Hx; specialize (Hx eq_refl); destruct Hx; subst.
        simpl.
        rewrite type_cast_refl in * by eauto.
        inv_all. subst.
        repeat rewrite typ2_match_iota by eauto.
        rewrite H1.
        autorewrite_with_eq_rw.
        split; [ reflexivity | ].
        intros.
        eapply Pure_pctxD; eauto. intros.
        unfold Morphisms.Proper.
        autorewrite_with_eq_rw.

        destruct H; subst.
        { eapply RbaseD_entails in H1.
          destruct H1 as [ ? [ ? ? ] ].
          rewrite Hlops in H. inversion H; clear H; subst.
          specialize (lopsOk x).
          rewrite Hlops in lopsOk.
          clear - lopsOk.
          unfold respectful, orR, castR. simpl.
          generalize (typ2_cast x (typ2 x x)).
          generalize (typ2_cast x x).
          generalize (typD (typ2 x x)).
          generalize (typD (typ2 x (typ2 x x))).
          intros; subst; simpl.
          intros. rewrite H. rewrite H0. reflexivity. }
        { simpl in H1. forwardy.
          eapply RbaseD_entails in H.
          destruct H as [ ? [ ? ? ] ].
          inv_all; subst.
          specialize (lopsOk x).
          rewrite Hlops in lopsOk.
          rewrite Hlops in H. inversion H. subst.
          clear - lopsOk.
          unfold respectful, orR, castR. simpl.
          generalize (typ2_cast x (typ2 x x)).
          generalize (typ2_cast x x).
          generalize (typD (typ2 x x)).
          generalize (typD (typ2 x (typ2 x x))).
          intros; subst; simpl.
          intros. unfold flip in *.
          rewrite H. rewrite H0. reflexivity. } }
      { (* Implication *)
        assert (exists X, (r = Rinj X \/ r = Rflip (Rinj X)) /\
                   if_entails x (Rflip' r :: r :: nil) X tvs' (getUVars ctx) (getVars ctx) (length (getUVars ctx))
                              (length (getVars ctx)) cs = Some (rs, cs')).
        { destruct r; eauto; try solve [ inversion H1 ].
          destruct r; eauto; try solve [ inversion H1 ]. }
        clear H1. destruct H. destruct H.
        eapply if_entails_sound in H1.
        destruct H1 as [ ? [ ? ? ] ]. subst.
        split; auto. intros.
        forward.
        simpl.
        autorewrite with exprD_rw in H2. simpl in H2.
        forwardy. inv_all. subst.
        generalize (@binary_inference (ilf_impl x) _ _ _ _ _ _ H H1 H3).
        unfold symAs, typeof_sym in H3; simpl in H3.
        simpl.
        destruct (lops x) eqn:Hlops; try solve [ inversion H3 ].
        intro Hx; specialize (Hx eq_refl); destruct Hx; subst.
        simpl.
        rewrite type_cast_refl in * by eauto.
        inv_all. subst.
        repeat rewrite typ2_match_iota by eauto.
        rewrite RD_Rflip'_Rflip. simpl.
        rewrite H1.
        autorewrite_with_eq_rw.
        split; [ reflexivity | ].
        intros.
        eapply Pure_pctxD; eauto. intros.
        unfold Morphisms.Proper.
        autorewrite_with_eq_rw.

        destruct H; subst.
        { eapply RbaseD_entails in H1.
          destruct H1 as [ ? [ ? ? ] ].
          rewrite Hlops in H. inversion H; clear H; subst.
          specialize (lopsOk x).
          rewrite Hlops in lopsOk.
          clear - lopsOk.
          unfold respectful, implR, castR. simpl.
          generalize (typ2_cast x (typ2 x x)).
          generalize (typ2_cast x x).
          generalize (typD (typ2 x x)).
          generalize (typD (typ2 x (typ2 x x))).
          intros; subst; simpl.
          unfold flip in *.
          intros. rewrite <- H. rewrite H0. reflexivity. }
        { simpl in H1. forwardy.
          eapply RbaseD_entails in H.
          destruct H as [ ? [ ? ? ] ].
          inv_all; subst.
          specialize (lopsOk x).
          rewrite Hlops in lopsOk.
          rewrite Hlops in H. inversion H. subst.
          clear - lopsOk.
          unfold respectful, implR, castR. simpl.
          generalize (typ2_cast x (typ2 x x)).
          generalize (typ2_cast x x).
          generalize (typD (typ2 x x)).
          generalize (typD (typ2 x (typ2 x x))).
          intros; subst; simpl.
          intros. unfold flip in *.
          rewrite <- H. rewrite H0. reflexivity. } } }
    { inversion 1. }
  Qed.

  Definition quant_pull (l : typ) (e : expr typ func)
  : mrw (Progressing (expr typ func)) :=
    bottom_up (is_reflR is_refl)
              (is_transR is_trans)
              (pull_all_quant)
              get_respectful
              e (Rinj (Inj (fEntails l))).

(*
  Time Eval vm_compute
    in match quant_pull (goal2 8 0) nil nil nil 0 0 (TopSubst _ nil nil) with
       | Some _ => tt
       | None => tt
       end.
*)
End parametric.
