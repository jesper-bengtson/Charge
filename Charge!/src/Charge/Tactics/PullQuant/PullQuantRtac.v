Require Import ExtLib.Core.RelDec.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.ExprD.
Require Import MirrorCore.Lambda.RedAll.
Require Import MirrorCore.Lambda.AutoSetoidRewriteRtac.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.Lambda.Ptrns.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.RTac.IdtacK.

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
  Context {Typ2_Fun : Typ2 _ RFun}.
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
  eapply Typ2_App2 with (F:=RFun); eauto with typeclass_instances.
  eapply Typ2_App2 with (F:=RFun); eauto with typeclass_instances.
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

  (* Polymorhic Lemmas are stated as functions from types
   * to lemmas. Here are two examples of them.
   *)
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

  (* This is the implementation of deciding reflexivity of a relation.
   * Note that in this approach, we only define reflexivity for Rbase,
   * i.e. expr, the rewriter contains functions to lift this to R.
   *)
  Definition is_refl : expr typ func -> bool :=
    run_default
      (inj (FuncView.ptrn_view _ (pmap (fun _ => true)
                                       (fptrnEntails ignore))))
      false.

  (* This proof is boring but unfortunately longer that in should be. *)
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

  (* This is analagous to above but for transitive relations.
   * For our purposes here, it is just entails which is also transitive,
   * so we use the same function as above.
   *)
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

  (* This function just returns Y if X is an entails, otherwise it fails. *)
  Definition if_entails {T} (t : typ) (Y : T) (X : expr typ func)
  : mrw T :=
    run_default
      (inj (ptrn_view _
                      (pmap (fun t' => if t ?[ eq ] t'
                                       then rw_ret Y else rw_fail)
                            (fptrnEntails get)))) (rw_fail) X.

  (** This function defines what terms respect what relations.
   ** The reason that it is somewhat complicated is that it handles
   ** both [entails] and [flip entails].
   **)
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
  (* We can build this from lemmas. It will be less efficient, but it is
   * painful enough to prove that it is certainly worthwhile.
   *)

  (* This was necessary for post-processing the substitution.
   *)
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


  (* This is a convenience function for performing rewrites *)
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

  (* This is a convenience function for performing rewrites for
   * polymorphic lemmas. Note that the function computes a list
   * of lemmas from an expression rather than taking a list of
   * functions from expr to lemma, i.e. a list of polymorphic
   * lemmas. This is mostly just for efficiency.
   *)
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

  (* This is just the soundness of [if_entails] *)
  Lemma if_entails_sound : forall T t X r a b c d e f g h i,
      @if_entails T t X r a b c d e f g = Some (h,i) ->
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

  (* This is just a helper lemma *)
  Lemma acc_fold_right
    : forall t ts t',
      TransitiveClosure.leftTrans (tyAcc (typ:=typ))
                                  t (fold_right (typ2 (F:=RFun)) t (t'::ts)).
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

  (* Same as above *)
  Lemma Rty_fold_right
    : forall y x ts,
      Rty (fold_right (typ2 (F:=RFun)) x ts) (typ2 y x) ->
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

  (* Same as above *)
  Lemma Rty_fold_right2
    : forall y x z ts,
      Rty (fold_right (typ2 (F:=RFun)) x ts) (typ2 y (typ2 z x)) ->
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

  (* This is essentially the view function for ilf_entails but it includes
   * type information.
   *)
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

  (* A special case of the above *)
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

  (* Here is the main annoying lemma about inverting binary operators.
   * It is generic so it should be reusable, but it is still a bit annoying.
   *)
  Lemma binary_inference
  : let rs_log := @RSym_ilfunc typ _ _ _ _ lops in
    forall (X : ilfunc typ) t x ts r rD x0,
      (r = Rinj (Inj (f_insert (ilf_entails x))) \/
       r = Rflip (Rinj (Inj (f_insert (ilf_entails x))))) ->
      RD RbaseD r t = Some rD ->
      symAs X (fold_right (typ2 (F:=RFun)) t ts) = Some x0 ->
      typeof_sym X = Some (typ2 (F:=RFun) x (typ2 (F:=RFun) x x)) ->
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

  (* It would be nice if we could prove this more quickly. Building
   * [get_respectful] out of smaller pieces would certainly help, but it
   * would not be as efficient. Perhaps we can use some combination of
   * optimization and reduction to build the efficient implementation
   * from the easy one and prove them equal.
   *)
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

  (* Here is the final quantifier puller. *)
(*
  Definition quant_pull (l : typ) (e : expr typ func)
  : mrw (Progressing (expr typ func)) :=
    bottom_up (is_reflR is_refl)
              (is_transR is_trans)
              (pull_all_quant)
              get_respectful
              e (Rinj (Inj (fEntails l))).
*)

  Definition quant_pull_tac : rtac typ (expr typ func) :=
    @auto_setoid_rewrite_bu
      typ func Rbase (Rflip (Rinj (Inj (fEntails (typ0 (F:=Prop))))))
      (is_reflR is_refl)
      (is_transR is_trans)
      (pull_all_quant)
      get_respectful.

  Lemma expr_sdec_sound
  : forall a b : expr typ func, expr_sdec a b = true -> a = b.
  Proof.
    eapply expr_eq_sdec_ok; eauto.
    unfold func_sdec.
    intros. generalize (sym_eqbOk a b); eauto with typeclass_instances.
    destruct (sym_eqb a b); intros; subst; auto.
    inversion H.
  Qed.

  Lemma RbaseD_same_type
  : forall (r : expr typ func) (t1 t2 : typ)
     (rD1 : typD t1 -> typD t1 -> Prop) (rD2 : typD t2 -> typD t2 -> Prop),
   RbaseD r t1 = Some rD1 -> RbaseD r t2 = Some rD2 -> t1 = t2.
  Proof.
    unfold RbaseD. unfold castD. intros r t1 t2 rD1 rD2.
    autorewrite_with_eq_rw.
    destruct (exprD nil nil r (typ0 (F:=typD t1 -> typD t1 -> Prop))) eqn:?; try congruence.
    destruct (exprD nil nil r (typ0 (F:=typD t2 -> typD t2 -> Prop))) eqn:?; try congruence.
    intros. inv_all. subst.
    unfold exprD in *. simpl in *.
    forwardy.
    eapply exprD_typeof_Some in H; eauto with typeclass_instances.
    inv_all. subst.
    eapply exprD_typeof_eq in H; eauto.
    inv_all. assumption.
  Qed.

  Lemma repeatFunc_sound
    : forall base rec,
      (setoid_rewrite_spec RbaseD (fun e _ => rw_ret (base e))) ->
      setoid_rewrite_spec RbaseD rec ->
      forall n,
        setoid_rewrite_spec RbaseD (repeatFunc n base rec).
  Proof.
    induction n.
    { simpl. intros.
      admit. }
    { simpl. intros.
      admit. }
  Admitted.

  Theorem quant_pull_tac_sound
  : lops (typ0 (F:=Prop)) = _Some (@castR _ _ ILogic.ILogicOps _ _ ILogic.ILogicOps_Prop) ->
    rtac_sound quant_pull_tac.
  Proof.
    unfold quant_pull_tac. intro.
    eapply auto_setoid_rewrite_bu_sound
      with (Rbase_eq := expr_sdec)
           (RbaseD := RbaseD);
      eauto using expr_sdec_sound, RbaseD_same_type,
                  is_reflROk, is_reflOk, is_transROk, is_transOk,
                  get_respectful_sound.
    { simpl. unfold RbaseD.
      unfold exprD. simpl. rewrite exprD'_Inj by eauto with typeclass_instances.
      unfold fEntails.
      erewrite <- @fv_compat with (Sym_A := RSym_ilfunc lops)
            by eauto with typeclass_instances.
      unfold symAs. simpl. unfold typeof_sym. simpl.
      rewrite H.
      rewrite type_cast_refl by eauto with typeclass_instances.
      simpl. unfold entailsR.
      rewrite castD_option.
      f_equal. rewrite castDR.
      unfold ILogic.lentails. unfold castR.
      clear.
      destruct (eq_sym (typ0_cast (F:=Prop))). reflexivity. }
    { unfold pull_all_quant.
      (** TODO(gmalecha): This isn't quite complete, something is missing here *)
      eapply repeatFunc_sound.
      { red. red. unfold rw_ret. simpl.
        inversion 1; subst.
        intros; split; auto.
        intros.
        destruct (pctxD cs') eqn:?; trivial.
        simpl.
        destruct (ExprDsimul.ExprDenote.exprD' (getUVars ctx) (tvs' ++ getVars ctx) t e).
        { split; [ reflexivity | ].
          intros.
          eapply Pure_pctxD; eauto.
          
          admit. }
        { auto. } }
      { eapply bottom_up_sound
          with (Rbase_eq := expr_sdec)
               (RbaseD := RbaseD);
        eauto using expr_sdec_sound, RbaseD_same_type,
                    is_reflROk, is_reflOk, is_transROk, is_transOk,
                    get_respectful_sound.
        admit. (** TODO(gmalecha): Not quite complete! *)
    } }
  Admitted.

(*
  Time Eval vm_compute
    in match quant_pull (goal2 8 0) nil nil nil 0 0 (TopSubst _ nil nil) with
       | Some _ => tt
       | None => tt
       end.
*)

End parametric.
