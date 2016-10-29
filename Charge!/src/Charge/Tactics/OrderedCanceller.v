(** This is a simple cancellation procedure based on
 ** an ordering of the elements on the right hand side.
 **)
Require Import ExtLib.Tactics.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.ExprSem.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprVariables.
Require Import MirrorCore.Lambda.AppN.
Require Import ChargeCore.Logics.ILogic.
Require Import ChargeCore.Logics.BILogic.
Require Import ChargeCore.Logics.Pure.
Require Import Charge.Tactics.BILNormalize.
Require Import Charge.Tactics.Iterated.
Require Import Charge.Tactics.SynSepLog.

Set Implicit Arguments.
Set Strict Implicit.

Section ordered_cancel.
  Variable typ : Set.
  Variable RType_typ : RType typ.
  Variable Typ2_Fun : Typ2 _ RFun.
  Variable func : Set.
  Variable RSym_func : RSym func.

  Let Expr_expr : ExprI.Expr _ (expr typ func) := Expr_expr.
  Local Existing Instance Expr_expr.

  Inductive Conjuncts : Set :=
  | Pure (_ : expr typ func) (c : Conjuncts)
  | Impure (f : expr typ func) (xs : list (expr typ func)) (c : Conjuncts)
  | Frame (_ : expr typ func) (xs : list (expr typ func)) (c : Conjuncts)
  | Emp
  | Tru.

  Variable subst : Type.
  Variable Subst_subst : Subst subst (expr typ func).
  Hypothesis SubstOk_subst : @SubstOk _ _ _ _ _ Subst_subst.

  Fixpoint findWithRest {T U} (f : T -> option U) (ls acc : list T) {struct ls}
  : option (T * U * list T) :=
    match ls with
      | nil => None
      | l :: ls =>
        match f l with
          | None => findWithRest f ls (l :: acc)
          | Some u => Some (l, u, rev_append acc ls)
        end
    end.

  Theorem findWithRest_spec
  : forall T U f ls acc a s b,
      @findWithRest T U f ls acc = Some (a,s,b) ->
      f a = Some s /\
      exists before after,
        b = before ++ after /\ rev_append acc ls = before ++ a :: after.
  Proof.
    clear. induction ls; simpl; intros; try congruence.
    consider (f a); intros.
    { inv_all; subst. split; auto.
      exists (rev acc). exists ls.
      repeat rewrite rev_append_rev. auto. }
    { eapply IHls in H0. intuition. }
  Qed.

  Variable doUnifySepLog : subst -> expr typ func -> expr typ func -> option subst.
  Variable eprovePure : subst -> expr typ func -> option subst.

  Variable SSL : SynSepLog typ func.

  Fixpoint cancel (rhs : Conjuncts) (lhs : conjunctives typ func)
           (rem : conjunctives typ func) (s : subst) {struct rhs}
  : conjunctives typ func * conjunctives typ func * subst :=
    match rhs with
      | Emp => (lhs, rem, s)
      | Tru => ({| spatial := lhs.(spatial)
                 ; pure := lhs.(pure)
                 ; star_true := false
                 |}, {| spatial := rem.(spatial)
                      ; pure := rem.(pure)
                      ; star_true := true
                      |}, s)
      | Frame hd xs rhs =>
        match rem.(spatial) with
          | nil =>
            (** try to get everything! **)
            let lhs_all := conjunctives_to_expr SSL lhs in
            match doUnifySepLog s lhs_all (apps hd xs) with
              | None =>
                cancel rhs lhs
                       {| spatial := rem.(spatial) ++ (hd,xs) :: nil
                        ; pure := rem.(pure)
                        ; star_true := rem.(star_true)
                        |} s
              | Some s' =>
                cancel rhs
                       {| spatial := nil
                        ; pure := lhs.(pure)
                        ; star_true := false
                        |}
                       {| spatial := nil
                        ; pure := rem.(pure)
                        ; star_true := rem.(star_true)
                        |} s'
            end
          | _ =>
            (** If there are spatial conjuncts left, we should keep this **)
            cancel rhs lhs
                   {| spatial := rem.(spatial) ++ (hd,xs) :: nil
                    ; pure := rem.(pure)
                    ; star_true := rem.(star_true)
                    |} s
        end
      | Pure p cs =>
        match eprovePure s p with
          | None =>
            cancel cs lhs {| spatial := rem.(spatial)
                           ; star_true := rem.(star_true)
                           ; pure := p :: rem.(pure)
                           |} s
          | Some s' =>
            cancel cs lhs rem s'
        end
      | Impure f xs cs =>
        let Z := apps f xs in
        let test x := doUnifySepLog s Z (apps (fst x) (snd x)) in
        match findWithRest test lhs.(spatial) nil with
          | None =>
            cancel cs lhs {| spatial := (f,xs) :: rem.(spatial)
                           ; star_true := rem.(star_true)
                           ; pure := rem.(pure)
                           |} s
          | Some (_, s', rst) =>
            cancel cs {| spatial := rst
                       ; star_true := lhs.(star_true)
                       ; pure := lhs.(pure)
                       |}
                      rem s'
        end
    end.

  Variable tySL : typ.
  Variable ILogicOps_SL : ILogicOps (typD tySL).
  Variable BILOperators_SL : BILOperators (typD tySL).
  Hypothesis ILogic_SL : @ILogic _ ILogicOps_SL.
  Hypothesis BILogic_SL : @BILogic _ ILogicOps_SL BILOperators_SL.

(*  Hypothesis eprovePureOk : eprovePure_spec.

  Variable SSLO : SynSepLogOk _ _ _ _ SSL.


  Variables tus tvs : tenv typ.
*)
(****
  (** TODO: this can be generalized to handle entailment with a remainder **)
  Definition unifySepLog_spec :=
    forall s e e' s',
      doUnifySepLog s e e' = Some s' ->
      WellTyped_expr tus tvs e tySL ->
      WellTyped_expr tus tvs e' tySL ->
      WellTyped_subst tus tvs s ->
         WellTyped_subst tus tvs s'
      /\ forall (us : HList.hlist _ tus) (vs : HList.hlist _ tvs),
           substD (join_env us) (join_env vs) s' ->
           exprD (join_env us) (join_env vs) e tySL = exprD (join_env us) (join_env vs) e' tySL /\
           substD (join_env us) (join_env vs) s.
  Hypothesis doUnifySepLogOk : unifySepLog_spec.

  (** TODO: I can't use a simple EProver here because EProvers are specialized
   **       to work with [Prop], not arbitrary ILogics.
   ** This is yet another reason to get ILogic underneath MirrorCore.
   ** - You really just need to generalize [Prover]/[EProver] with [Entails].
   **)
  Definition eprovePure_spec :=
    forall s e s',
      eprovePure s e = Some s' ->
      match exprD' tus tvs e tySL with
        | Some val =>
          WellTyped_subst tus tvs s ->
          WellTyped_subst tus tvs s'
          /\ forall (us : HList.hlist _ tus) (vs : HList.hlist _ tvs),
               substD (join_env us) (join_env vs) s' ->
               (ltrue |-- val us vs)
               /\ substD (join_env us) (join_env vs) s
        | None => True
      end.

(*
  Fixpoint ConjunctsD (ls : Conjuncts) : option (typD ts nil tySL) :=
    match ls with
      | Emp => Some empSP
      | Tru => Some ltrue
      | Pure p ls =>
        match exprD us vs p tySL , ConjunctsD ls with
          | Some a , Some b => Some (sepSP (land a empSP) b)
          | _ , _ => None
        end
      | Impure f xs ls =>
        match exprD us vs (apps f xs) tySL , ConjunctsD ls with
          | Some a , Some b => Some (sepSP a b)
          | _ , _ => None
        end
    end.
*)

  Variable PureOp_SL : @Pure.PureOp (typD ts nil tySL).
  Variable Pure_SL : Pure.Pure PureOp_SL.
  Hypothesis Pure_ltrue : Pure.pure ltrue.
  Hypothesis Pure_land : forall a b, Pure.pure a -> Pure.pure b -> Pure.pure (a //\\ b).

  Section well_formed_Conjuncts.
    Variable us' vs' : EnvI.env (typD ts).

    Fixpoint well_formed_Conjuncts (ls : Conjuncts) : Prop :=
      match ls with
        | Emp => True
        | Tru => True
        | Pure p ls =>
          match exprD us' vs' p tySL with
            | None => False
            | Some p => Pure.pure p
          end /\ well_formed_Conjuncts ls
        | Impure _ _ ls => well_formed_Conjuncts ls
      end.
  End well_formed_Conjuncts.

  Fixpoint Conjuncts_to_expr (ls : Conjuncts) : expr typ func :=
    match ls with
      | Emp => SSL.(e_emp)
      | Tru => SSL.(e_true)
      | Pure p ls =>
        SSL.(e_star) (SSL.(e_and) p SSL.(e_emp)) (Conjuncts_to_expr ls)
      | Impure f xs ls =>
        SSL.(e_star) (apps f xs) (Conjuncts_to_expr ls)
    end.

  Definition sentails : env (typD ts) -> env (typD ts) -> expr typ func -> expr typ func -> Prop :=
    @Sem_equiv typ (typD ts) (expr typ func) _ tySL lentails.

  Lemma exprD'_iterated_base_cons_Some
  : forall tus tvs a b x,
      exprD' tus tvs (iterated_base SSL.(e_emp) SSL.(e_star) (a :: b)) tySL = Some x ->
      exists aV bV,
        exprD' tus tvs a tySL = Some aV /\
        exprD' tus tvs (iterated_base SSL.(e_emp) SSL.(e_star) b) tySL = Some bV /\
        (forall us vs, ((x us vs) -|- sepSP (aV us vs) (bV us vs))).
  Proof.
    clear Pure_SL PureOp_SL Pure_ltrue Pure_land.
    unfold iterated_base. simpl.
    intros.
    destruct (iterated (e_star SSL) b).
    { go_crazy SSL SSLO; eauto. }
    { exists x.
      destruct (SSLO.(e_empOk) tus0 tvs0) as [ ? [ ? ? ] ].
      eexists. split; eauto. split; eauto. intros.
      rewrite H1. rewrite empSPR; eauto. }
  Qed.

  Lemma exprD'_iterated_base_cons_None
  : forall us tvs a b,
      exprD' us tvs (iterated_base SSL.(e_emp) SSL.(e_star) (a :: b)) tySL = None <->
      exprD' us tvs a tySL = None \/
      exprD' us tvs (iterated_base SSL.(e_emp) SSL.(e_star) b) tySL = None.
  Proof.
    clear Pure_SL PureOp_SL Pure_ltrue Pure_land.
    unfold iterated_base. simpl.
    intros.
    destruct (iterated (e_star SSL) b); auto.
    { split; intros; repeat (go_crazy SSL SSLO); auto.
      consider (exprD' us tvs0 (e_star SSL a e) tySL); intros; auto.
      exfalso. go_crazy SSL SSLO. destruct H; congruence. }
    { split; intros; repeat (go_crazy SSL SSLO); auto.
      destruct H; auto.
      exfalso.
      destruct (SSLO.(e_empOk) us tvs0). intuition. congruence. }
  Qed.

  Lemma exprD'_iterated_base_app_Some
  : forall tus tvs a b x,
      exprD' tus tvs (iterated_base SSL.(e_emp) SSL.(e_star) (a ++ b)) tySL = Some x ->
      exists aV bV,
        exprD' tus tvs (iterated_base SSL.(e_emp) SSL.(e_star) a) tySL = Some aV /\
        exprD' tus tvs (iterated_base SSL.(e_emp) SSL.(e_star) b) tySL = Some bV /\
        (forall us vs, ((x us vs) -|- sepSP (aV us vs) (bV us vs))).
  Proof.
    clear Pure_SL PureOp_SL doUnifySepLogOk Pure_ltrue Pure_land.
    induction a; simpl; intros.
    { destruct (SSLO.(e_empOk) tus0 tvs0) as [ ? [ ? ? ] ].
      exists x0. exists x.
      split; eauto. split; eauto.
      intros. rewrite H1. rewrite empSPL. reflexivity. }
    { eapply exprD'_iterated_base_cons_Some in H.
      destruct H as [ ? [ ? [ ? [ ? ? ] ] ] ].
      specialize (IHa _ _ H0).
      destruct IHa as [ ? [ ? [ ? [ ? ? ] ] ] ].
      consider (exprD' tus0 tvs0 (iterated_base (e_emp SSL) (e_star SSL) (a :: a0)) tySL); intros.
      { do 2 eexists. split; eauto. split; eauto.
        apply exprD'_iterated_base_cons_Some in H5.
        destruct H5 as [ ? [ ? [ ? [ ? ? ] ] ] ].
        intros. Cases.rewrite_all_goal.
        rewrite H in *. rewrite H6 in *.
        inv_all; subst.
        rewrite sepSPA. reflexivity. }
      { exfalso.
        eapply exprD'_iterated_base_cons_None in H5.
        destruct H5; congruence. } }
  Qed.

  Lemma exprD'_iterated_base_app_None
  : forall us tvs a b,
      exprD' us tvs (iterated_base SSL.(e_emp) SSL.(e_star) (a ++ b)) tySL = None <->
      exprD' us tvs (iterated_base SSL.(e_emp) SSL.(e_star) a) tySL = None \/
      exprD' us tvs (iterated_base SSL.(e_emp) SSL.(e_star) b) tySL = None.
  Proof.
    clear Pure_SL PureOp_SL doUnifySepLogOk Pure_ltrue Pure_land.
    induction a; simpl; intros.
    { intuition.
      unfold iterated_base in H0. simpl in *.
      destruct (SSLO.(e_empOk) us tvs0) as [ ? [ ? ? ] ].
      congruence. }
    { repeat rewrite exprD'_iterated_base_cons_None.
      rewrite IHa. split; tauto. }
  Qed.

  Lemma exprD'_WellTyped_expr
  : forall tus tvs e t val,
      exprD' tus tvs e t = Some val ->
      WellTyped_expr tus tvs e t.
  Proof.
    clear; intros.
    red. eapply ExprD3.EXPR_DENOTE_core.exprD'_typeof. eapply H.
  Qed.
  Hint Resolve exprD'_WellTyped_expr : WellTyped.

  Ltac forward_reason :=
    repeat match goal with
             | H : ?X , H' : ?X -> _ |- _ =>
               match type of X with
                 | Prop => specialize (H' H)
               end
             | vs : HList.hlist _ _ , H : forall x : HList.hlist _ _, _ |- _ =>
               specialize (H vs)
             | H : _ /\ _ |- _ => destruct H
             | H : exists x, _ |- _ => destruct H
           end.


  Lemma cancelOk_lem'
  : forall rhs lhs rem s lhs' rhs' s',
      cancel rhs lhs rem s = (lhs',rhs',s') ->
      match
          exprD' tus tvs (conjunctives_to_expr_star SSL lhs) tySL
        , exprD' tus tvs (SSL.(e_star) (conjunctives_to_expr_star SSL rem)
                                       (Conjuncts_to_expr rhs)) tySL
      with
        | Some l , Some r =>
          match
              exprD' tus tvs (conjunctives_to_expr_star SSL lhs') tySL
            , exprD' tus tvs (conjunctives_to_expr_star SSL rhs') tySL
          with
            | Some l' , Some r' =>
              WellTyped_subst tus tvs s ->
                 WellTyped_subst tus tvs s'
              /\ forall us vs,
                   well_formed _ _ _ lhs (join_env us) (join_env vs) ->
                   well_formed_Conjuncts (join_env us) (join_env vs) rhs ->
                   well_formed _ _ _ rem (join_env us) (join_env vs) ->
                      well_formed _ _ _ lhs' (join_env us) (join_env vs)
                   /\ well_formed _ _ _ rhs' (join_env us) (join_env vs)
                   /\ (substD (join_env us) (join_env vs) s' ->
                       (l' us vs |-- r' us vs) ->
                       (l us vs |-- r us vs) /\ substD (join_env us) (join_env vs) s)
            | _ , _ => False
          end
        | _ , _ => True
      end.
  Proof.
    induction rhs; intros; forward.
    { repeat go_crazy SSL SSLO.
      simpl in H.
      consider (eprovePure s e); intros;
        eapply IHrhs in H4; clear IHrhs.
      { forward. inv_all; subst.
        red in eprovePureOk.
        apply eprovePureOk in H.
        simpl in H2.
        consider (exprD' tus tvs
                         (e_star SSL (conjunctives_to_expr_star SSL rem)
                                 (Conjuncts_to_expr rhs)) tySL); intros.
        { forward.
          repeat go_crazy SSL SSLO.
          inv_all; subst.
          repeat rewrite typeof_env_join_env in *.
          forward_reason.
          split; auto. intros.
          destruct H16. unfold exprD in H16.
          repeat rewrite split_env_join_env in *.
          simpl in *.
          rewrite H2 in *.
          forward_reason.
          split; auto. split; auto. intros.
          forward_reason. split; auto.
          destruct (SSLO.(e_empOk) tus tvs) as [ ? [ ? ? ] ].
          repeat go_crazy SSL SSLO.
          inv_all; subst.
          do 6 match goal with
                 | H : _ |- _ =>
                   rewrite H; clear H
               end.
          rewrite <- empSPL with (P := x2 us vs) at 1.
          eapply scME; eauto.
          eapply scME; eauto.
          apply landR; auto.
          etransitivity; try eassumption. apply ltrueR. }
        { simpl in *.
          repeat (go_crazy SSL SSLO; try congruence). } }
      { (** eprovePure returns None **)
        forward. inv_all; subst.
        clear H.
        consider (exprD' tus tvs
           (e_star SSL
              (conjunctives_to_expr_star SSL
                 {|
                 spatial := spatial rem;
                 star_true := star_true rem;
                 pure := e :: pure rem |}) (Conjuncts_to_expr rhs)) tySL);
          intros.
        { forward.
          simpl in *. forward_reason.
          split; auto. intros.
          forward_reason.
          assert (well_formed RSym_func tySL PureOp_SL
                              {| spatial := spatial rem;
                                 star_true := star_true rem;
                                 pure := e :: pure rem |} (join_env us) (join_env vs)).
          { red. constructor; auto.
            forward. eauto. }
          forward_reason.
          split; auto. split; auto. intros.
          forward_reason.
          split; auto.
          clear H13. unfold exprD in H10.
          repeat rewrite split_env_join_env in *.
          unfold conjunctives_to_expr_star in H, H1.
          simpl in *.
          repeat go_crazy SSL SSLO.
          inv_all; subst.
          eapply exprD'_iterated_base_cons_Some in H.
          forward_reason.
          repeat go_crazy SSL SSLO.
          inv_all; subst.
          do 11 match goal with
                  | H : _ |- _ => rewrite H; clear H
                end.
          repeat rewrite <- sepSPA.
          apply scME; auto.
          repeat rewrite sepSPA.
          rewrite sepSPC. repeat rewrite <- sepSPA.
          apply scME; auto.
          rewrite landC. reflexivity. }
        { exfalso. simpl in *.
          unfold conjunctives_to_expr_star in H, H1. destruct rem; simpl in *.
          repeat (go_crazy SSL SSLO; try congruence).
          eapply exprD'_iterated_base_cons_None in H.
          destruct H;
            repeat (go_crazy SSL SSLO; try congruence). } } }
    { repeat go_crazy SSL SSLO.
      red in doUnifySepLogOk.
      simpl in H.
      consider (findWithRest
          (fun x : expr typ func * list (expr typ func) =>
           doUnifySepLog s (apps f xs) (apps (fst x) (snd x)))
          (spatial lhs) nil); intros.
      { destruct p. destruct p.
        eapply IHrhs in H4; clear IHrhs.
        consider (exprD' tus tvs
           (conjunctives_to_expr_star SSL
              {|
              spatial := l;
              star_true := star_true lhs;
              pure := pure lhs |}) tySL); intros.
        { consider (exprD' tus tvs
           (e_star SSL (conjunctives_to_expr_star SSL rem)
              (Conjuncts_to_expr rhs)) tySL); intros.
          { forward. repeat go_crazy SSL SSLO.
            inv_all; subst.
            eapply findWithRest_spec in H.
            forward_reason. simpl in *. subst.
            unfold conjunctives_to_expr_star in H4, H0.
            simpl in *. subst.
            generalize dependent (iterated_base (e_emp SSL) (e_star SSL)
               (map (e_and SSL (e_emp SSL)) (pure lhs))).
            generalize dependent (if star_true lhs then e_true SSL else e_emp SSL).
            intros.
            repeat go_crazy SSL SSLO. inv_all; subst.
            rewrite H12 in *.
            rewrite map_app in *. simpl in *.
            eapply exprD'_iterated_base_app_Some in H5.
            forward_reason.
            eapply exprD'_iterated_base_app_Some in H16.
            destruct H16 as [ ? [ ? [ ? [ ? ? ] ] ] ].
            simpl in *.
            eapply exprD'_iterated_base_cons_Some in H16.
            destruct H16 as [ ? [ ? [ ? [ ? ? ] ] ] ].
            eapply doUnifySepLogOk in H; eauto with WellTyped.
            forward_reason.
            split; auto. intros.
            forward_reason.
            split; auto. split; auto. intros.
            forward_reason.
            split; auto.
            unfold exprD in *.
            repeat rewrite split_env_join_env in *.
            simpl in *.
            repeat go_crazy SSL SSLO.
            inv_all; subst.
            rewrite H3; clear H3.
            rewrite H21; clear H21.
            rewrite H25; clear H25.
            rewrite sepSPC. rewrite sepSPA.
            rewrite (sepSPC (x2 us vs)). rewrite <- H11; clear H11.
            transitivity (x15 us vs ** t1 us vs).
            { do 7 match goal with
                     | H : _ |- _ => rewrite H; clear H
                   end.
              repeat rewrite <- sepSPA.
              do 2 (apply scME; auto).
              rewrite sepSPC.
              rewrite sepSPA. reflexivity. }
            { rewrite H31. reflexivity. } }
          { exfalso. simpl in H2.
            repeat (go_crazy SSL SSLO; try congruence). } }
        { exfalso.
          simpl in *.
          unfold conjunctives_to_expr_star in H0, H4.
          simpl in *.
          repeat (go_crazy SSL SSLO; try congruence).
          apply findWithRest_spec in H.
          forward_reason. subst.
          simpl in H13. rewrite H13 in H8.
          repeat rewrite map_app in *. simpl in *.
          eapply exprD'_iterated_base_app_Some in H8.
          forward_reason.
          eapply exprD'_iterated_base_cons_Some in H12.
          forward_reason.
          eapply exprD'_iterated_base_app_None in H4.
          destruct H4; congruence. } }
      { eapply IHrhs in H4; clear IHrhs. clear H.
        simpl in *.
        progress forward.
        inv_all; subst.
        consider (exprD' tus tvs
           (e_star SSL
              (conjunctives_to_expr_star SSL
                 {|
                 spatial := (f, xs) :: spatial rem;
                 star_true := star_true rem;
                 pure := pure rem |}) (Conjuncts_to_expr rhs)) tySL).
        { intros. forward.
          forward_reason.
          split; auto. intros.
          forward_reason.
          split; auto. split; auto. intros.
          forward_reason.
          split; auto.
          unfold conjunctives_to_expr_star in H0, H1.
          simpl in *.
          generalize dependent (iterated_base (e_emp SSL) (e_star SSL)
               (map (e_and SSL (e_emp SSL)) (pure rem))).
          generalize dependent (if star_true rem then e_true SSL else e_emp SSL).
          intros.
          repeat go_crazy SSL SSLO. inv_all; subst.
          eapply exprD'_iterated_base_cons_Some in H19.
          forward_reason.
          rewrite H23 in *. inv_all; subst.
          do 9 match goal with
                 | H : _ |- _ => rewrite H; clear H
               end.
          repeat rewrite sepSPA.
          apply scME; auto.
          repeat rewrite <- sepSPA.
          apply scME; auto.
          rewrite sepSPA.
          rewrite sepSPC.
          apply scME; auto.
          rewrite H2 in *. inv_all; subst. reflexivity. }
        { intro; exfalso.
          unfold conjunctives_to_expr_star in H0, H1.
          simpl in *.
          generalize dependent (iterated_base (e_emp SSL) (e_star SSL)
               (map (e_and SSL (e_emp SSL)) (pure rem))).
          generalize dependent (if star_true rem then e_true SSL else e_emp SSL).
          intros.
          repeat go_crazy SSL SSLO.
          eapply exprD'_iterated_base_cons_None in H0.
          destruct H0; congruence. } } }
    { simpl in H. inv_all; subst.
      simpl in *.
      destruct (SSLO.(e_empOk) tus tvs) as [ ? [ ? ? ] ].
      repeat go_crazy SSL SSLO.
      inv_all; subst.
      intros.
      split; auto. intros. split; auto. split; auto.
      intros. split; auto.
      forward_reason.
      rewrite H9; clear H9.
      do 2 match goal with
             | H : _ |- _ => rewrite H; clear H
           end.
      rewrite empSPR; eauto. }
    { simpl in H. inv_all; subst.
      simpl in *.
      destruct (SSLO.(e_empOk) tus tvs) as [ ? [ ? ? ] ].
      repeat go_crazy SSL SSLO.
      unfold conjunctives_to_expr_star. simpl.
      unfold conjunctives_to_expr_star in H1.
      generalize dependent (iterated_base (e_emp SSL) (e_star SSL)
               (map (e_and SSL (e_emp SSL)) (pure rem))).
      generalize dependent (iterated_base (e_emp SSL) (e_star SSL)
                (map
                   (fun x2 : expr typ func * list (expr typ func) =>
                    apps (fst x2) (snd x2)) (spatial rem))).
      intros.
      repeat go_crazy SSL SSLO.
      consider (exprD' tus tvs (e_star SSL e0 (e_star SSL e (e_true SSL))) tySL); intros.
      { split; auto. intros.
        forward_reason.
        split; auto. split; auto. intros.
        split; auto.
        destruct (SSLO.(e_trueOk) tus tvs) as [ ? [ ? ? ] ].
        repeat go_crazy SSL SSLO. inv_all; subst. subst.
        do 7 match goal with
               | H : _ |- _ => rewrite H; clear H
             end.
        destruct (SSLO.(e_trueOk) tus tvs) as [ ? [ ? ? ] ].
        rewrite H3 in *. inv_all; subst.
        rewrite H6. repeat rewrite sepSPA.
        apply scME; auto.
        apply scME; auto.
        destruct (star_true rem).
        { rewrite H3 in *. inv_all; subst.
          rewrite H6. rewrite ltrue_sep; eauto. }
        { rewrite H in *. inv_all; subst. rewrite H2.
          rewrite empSPL. auto. } }
      { repeat (go_crazy SSL SSLO; try congruence). } }
  Qed.
*)
  Variable order : conjunctives typ func -> Conjuncts.
(*
  Definition order_spec :=
    forall c tus tvs,
      match exprD' tus tvs (conjunctives_to_expr_star SSL c) tySL
          , exprD' tus tvs (Conjuncts_to_expr (order c)) tySL
      with
        | Some l , Some r =>
          forall us vs,
            well_formed _ _ _ c (join_env us) (join_env vs) ->
            ((l us vs -|- r us vs) /\
             well_formed_Conjuncts (join_env us) (join_env vs) (order c))
        | None , None => True
        | _ , _ => False
      end.
  Hypothesis orderOk : order_spec.
*)
  Definition ordered_cancel (lhs rhs : conjunctives typ func) (s : subst)
  : conjunctives typ func * conjunctives typ func * subst :=
    let ordered := order rhs in
    let empty := {| spatial := nil ; pure := nil ; star_true := false |} in
    cancel ordered lhs empty s.
(*
  Theorem ordered_cancelOk
  : forall lhs rhs s lhs' rhs' s',
      ordered_cancel lhs rhs s = (lhs', rhs', s') ->
      match
          exprD' tus tvs (conjunctives_to_expr SSL lhs) tySL
        , exprD' tus tvs (conjunctives_to_expr SSL rhs) tySL
      with
        | Some l , Some r =>
          match
              exprD' tus tvs (conjunctives_to_expr SSL lhs') tySL
            , exprD' tus tvs (conjunctives_to_expr SSL rhs') tySL
          with
            | Some l' , Some r' =>
              WellTyped_subst tus tvs s ->
              WellTyped_subst tus tvs s' /\
              forall (us' : HList.hlist _ tus) vs',
                let vs := join_env vs' in
                let us := join_env us' in
              well_formed _ _ _ lhs us vs ->
              well_formed _ _ _ rhs us vs ->
              substD us vs s' ->
                  well_formed _ _ _ lhs' us vs
               /\ well_formed _ _ _ rhs' us vs
               /\ ((l' us' vs' |-- r' us' vs') -> l us' vs' |-- r us' vs')
            | _ , _ => False
          end
        | _ , _ => True
      end.
  Proof.
    intros.
    unfold ordered_cancel in H.
    eapply cancelOk_lem' in H.
    generalize (@conjunctives_to_expr_conjunctives_to_expr_star_iff _ _ _ _ _ SSL _ tvs tus lhs).
    generalize (@conjunctives_to_expr_conjunctives_to_expr_star_iff _ _ _ _ _ SSL _ tvs tus rhs).
    generalize (@conjunctives_to_expr_conjunctives_to_expr_star_iff _ _ _ _ _ SSL _ tvs tus lhs').
    generalize (@conjunctives_to_expr_conjunctives_to_expr_star_iff _ _ _ _ _ SSL _ tvs tus rhs').
    intros.
    forward.
    match type of H4 with
      | match ?X with _ => _ end =>
        consider X; intros
    end.
    { forward.
      forward_reason.
      split; auto. intros. subst vs.
      forward_reason.
      repeat go_crazy SSL SSLO.
      unfold conjunctives_to_expr_star in H4. simpl in *.
      red in orderOk.
      specialize (orderOk rhs tus tvs).
      repeat go_crazy SSL SSLO.
      inv_all; subst.
      specialize (orderOk us' vs' H16).
      destruct orderOk.
      unfold iterated_base in *. simpl in *.
      assert (well_formed RSym_func tySL PureOp_SL
          {| spatial := nil; star_true := false; pure := nil |}
          (join_env us') (join_env vs')) by constructor.
      specialize (H14 H24 H25).
      destruct H14 as [ ? [ ? ? ] ].
      specialize (H27 H17).
      split; auto. split; auto. intros.
      apply H12 in H14; clear H12.
      rewrite H14 in H28; clear H14.
      apply H11 in H26; clear H11.
      rewrite H26 in H28; clear H26.
      specialize (H27 H28).
      destruct H27. clear H28.
      rewrite H7; clear H7. rewrite H20; clear H20.
      rewrite H5; clear H5. rewrite H11; clear H11.
      rewrite H19; clear H19. rewrite H21; clear H21.
      rewrite H23; clear H23.
      rewrite H22 in *. inv_all; subst.
      destruct (SSLO.(e_empOk) tus tvs) as [ ? [ ? ? ] ].
      rewrite H4 in *. inv_all; subst.
      rewrite H5.
      repeat rewrite empSPL. reflexivity. }
    { exfalso.
      unfold conjunctives_to_expr_star in H3; simpl in H3.
      unfold iterated_base in H3; simpl in H3.
      destruct (SSLO.(e_empOk) tus tvs) as [ ? [ ? ? ] ].
      destruct (SSLO.(e_trueOk) tus tvs) as [ ? [ ? ? ] ].
      unfold conjunctives_to_expr_star in H4.
      simpl in H4.
      unfold iterated_base in H4. simpl in H4.
      repeat (go_crazy SSL SSLO; try congruence).
      specialize (orderOk rhs tus tvs).
      forward. }
  Qed.
*****)
End ordered_cancel.

(** The simplest ordering heuristic just uses the order that they occur in the
 ** map without looking at unification variables.
 **)
Section simple_ordering.
  Variable typ : Set.
  Variable RType_typ : RType typ.
  Variable Typ2_Fun : Typ2 _ RFun.
  Variable func : Set.
  Variable RSym_func : RSym func.

  Variable tySL : typ.
  Variable ILogicOps_SL : ILogicOps (typD tySL).
  Variable BILOperators_SL : BILOperators (typD tySL).
  Hypothesis ILogic_SL : @ILogic _ ILogicOps_SL.
  Hypothesis BILogic_SL : @BILogic _ ILogicOps_SL BILOperators_SL.

  Definition simple_order (c : conjunctives typ func) : Conjuncts typ func :=
    List.fold_right (fun x =>
                       match fst x with
                         | UVar _ => Frame (fst x) (snd x)
                         | _ => Impure (fst x) (snd x)
                       end)
                    (List.fold_right (fun x acc => Pure x acc)
                                     (if c.(star_true) then Tru _ _ else Emp _ _)
                                     c.(pure))
                    c.(spatial).

  Variable SSL : SynSepLog typ func.
  Variable SSLO : SynSepLogOk _ _ _ _ _ SSL.

  Variable PureOp_SL : @Pure.PureOp (typD tySL).
  Variable Pure_SL : Pure.Pure PureOp_SL.
  Hypothesis Pure_ltrue : Pure.pure ltrue.
  Hypothesis Pure_land : forall a b,
                           Pure.pure a -> Pure.pure b -> Pure.pure (a //\\ b).

(*
  Theorem simple_orderOk
  : @order_spec ts func _ tySL ILogicOps_SL SSL _ simple_order.
  Proof.
    red.
    intros; destruct c; simpl.
    unfold conjunctives_to_expr_star, simple_order; simpl.
    match goal with
      | |- match ?X with _ => _ end =>
        consider X; intros
    end.
    { repeat go_crazy SSL SSLO.
      revert H0. generalize dependent x1.
      induction spatial.
      { simpl. admit. }
      { simpl. intros.
        eapply exprD'_iterated_base_cons_Some in H0; eauto.
        destruct H0 as [ ? [ ? [ ? [ ? ? ] ] ] ].
        assert (forall us vs,
                  x0 us vs -|- x4 us vs ** x2 us vs).
        { intros. rewrite H3. rewrite H5.
          specialize (fun z => IHspatial _ z H4).
          admit. }
        { admit. } } }
    { forward.
(*      repeat go_crazy SSL SSLO. *)
      admit. }
  Qed.
*)
End simple_ordering.
(** TODO: There may be a cleaner way to do this...
 **)

