(** This file implements normalization for separation lgoic formulas.
 ** The normal form is:
 **   (a /\ b /\ c) /\ (P * Q * R [* true]?)
 ** The final [* true] is optional and is likely to never occur in
 ** practice but is necessary to make the algorithm total.
 **
 ** In this format, all of [a], [b], and [c] are pure which means that
 ** the above equation is equivalent to:
 **  Inj a * Inj b * Inj c * P * Q * R [* true]?
 ** where [Inj p = p /\ emp]
 **)
Require Import Coq.Classes.Morphisms.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
From ChargeCore.Logics Require Import BILogic ILogic Pure.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.ExprSem.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.AppN.
Require Import MirrorCore.Lambda.TypedFoldApp.
Require Import Charge.Tactics.Iterated.
Require Import Charge.Tactics.SepLogFold.
Require Import Charge.Tactics.SepLogFoldWithAnd.
Require Import Charge.Tactics.SynSepLog.

Set Implicit Arguments.
Set Strict Implicit.

(** TODO: These should really be moved to Charge! **)
Section lemmas.
  Variable P : Type.
  Variable ILogicOps_P : ILogicOps P.
  Variable ILogic_P : ILogic P.
  Variable BILOperators_P : BILOperators P.
  Variable BILogic_P : BILogic P.
  Variable PureOp_P : @PureOp P.
  Variable Pure_P : Pure PureOp_P.

  Lemma ltrue_sep : pure ltrue -> ltrue ** ltrue -|- ltrue.
  Proof.
    constructor.
    { apply ltrueR. }
    { rewrite <- pureandsc by eauto with typeclass_instances.
      apply landR; reflexivity. }
  Qed.

  Lemma pure_star_and_true
  : forall a b,
      Pure.pure a ->
      a ** b -|- a //\\ b ** ltrue.
  Proof.
    intros.
    rewrite <- (landtrueR a) at 1.
    rewrite pureandscD by eauto with typeclass_instances.
    rewrite sepSPC. reflexivity.
  Qed.

  Lemma lequiv_sep_cancel : forall a b c,
                              a -|- b -> a ** c -|- b ** c.
  Proof.
    split; apply bilsep; eapply H.
  Qed.

  Lemma land_cancel : forall a b c, b -|- c -> a //\\ b -|- a //\\ c.
  Proof.
    intros. rewrite H. reflexivity.
  Qed.
End lemmas.

Section conjunctives.
  Variable typ : Type.
  Variable RType_typ : RType typ.
  Variable Typ2_Fun : Typ2 _ Fun.
  Variable sym : Type.
  Variable RSym_sym : RSym sym.

  Let Expr_expr : Expr _ (expr typ sym) := Expr_expr _ _ _ _.
  Local Existing Instance Expr_expr.

  Record conjunctives : Type :=
  { spatial : list (expr typ sym * list (expr typ sym))
  ; star_true : bool
  ; pure : list (expr typ sym)
  }.

  Definition mkEmpty : conjunctives :=
  {| spatial := nil
   ; star_true := false
   ; pure := nil
   |}.

  Definition mkPure e : conjunctives :=
  {| spatial := nil
   ; star_true := true
   ; pure := e :: nil
   |}.

  Definition mkSpatial e es : conjunctives :=
  {| spatial := (e,es) :: nil
   ; star_true := false
   ; pure := nil
   |}.

  Definition mkStar (l r : conjunctives) : conjunctives :=
  {| spatial := l.(spatial) ++ r.(spatial)
   ; star_true := orb l.(star_true) r.(star_true)
   ; pure := l.(pure) ++ r.(pure)
   |}.

  Definition SepLogArgs_normalize : SepLogArgs typ sym conjunctives :=
  {| SepLogFold.do_emp := mkEmpty
   ; SepLogFold.do_star := mkStar
   ; SepLogFold.do_other := fun f xs => mkSpatial f (List.map fst xs)
   ; SepLogFold.do_pure := mkPure
   |}.

  Variable SL : typ.

  Section conjunctivesD.
    Variable ILO : ILogicOps (typD SL).
    Variable BILO : BILOperators (typD SL).
    Variable IL : @ILogic _ ILO.
    Variable BIL : @BILogic _ ILO BILO.

    Definition well_formed (PO : PureOp)
               (c : conjunctives) (us vs : env) : Prop :=
      List.Forall (fun e =>
                     exists val, exprD us vs e SL  = Some val
                              /\ @Pure.pure _ PO val) c.(pure).

    Variable SSL : SynSepLog typ sym.
    Variable SSLO : @SynSepLogOk typ _ _ sym _ SL _ _ SSL.

    Definition conjunctives_to_expr (c : conjunctives) : expr typ sym :=
      let spa := iterated_base SSL.(e_emp) SSL.(e_star) (map (fun x => apps (fst x) (snd x)) c.(spatial)) in
      let pur := iterated_base SSL.(e_true) SSL.(e_and) c.(pure) in
      SSL.(e_and) pur (SSL.(e_star) spa (if c.(star_true) then SSL.(e_true) else SSL.(e_emp))).

    Definition conjunctives_to_expr_star (c : conjunctives) : expr typ sym :=
      let spa := iterated_base SSL.(e_emp) SSL.(e_star) (map (fun x => apps (fst x) (snd x)) c.(spatial)) in
      let pur := iterated_base SSL.(e_emp) SSL.(e_star) (map (SSL.(e_and) SSL.(e_emp)) c.(pure)) in
      SSL.(e_star) pur (SSL.(e_star) spa (if c.(star_true) then SSL.(e_true) else SSL.(e_emp))).

    Section with_pure.

    Variable PureOp_it : @PureOp (typD SL).
    Variable Pure_it : @Pure _ _ _ PureOp_it.
    Hypothesis pure_ltrue : Pure.pure ltrue.
    Hypothesis pure_land : forall p q, Pure.pure p -> Pure.pure q -> Pure.pure (land p q).

    Lemma iterated_base_true_and_pure
    : forall us vs ps x1,
        exprD us vs (iterated_base (e_true SSL) (e_and SSL) ps) SL = Some x1 ->
        List.Forall
          (fun e : expr typ sym =>
             exists val : typD SL,
               exprD us vs e SL = Some val /\ Pure.pure val) ps -> Pure.pure x1.
    Proof.
(*
      intros.
      generalize dependent x1.
      induction H0; simpl.
      { unfold iterated_base. simpl. intros.
        destruct (exprD_e_trueOk SSLO us vs) as [ ? [ ? ? ] ].
        go_crazy SSL SSLO.
        inv_all; subst.
        eapply pure_proper; eauto. }
      { intros.
        generalize (@iterated_base_cons _ SSL.(e_true) SSL.(e_and)
                      (Sem_equiv _ SL lequiv us vs)
                      (@Reflexive_Sem_equiv _ _ _ _ SL lequiv _ us vs)
                      (@Transitive_Sem_equiv _ _ _ _ SL lequiv _ us vs)
                      (@Sem_equiv_e_and_assoc _ _ _ SL _ _ _ SSL SSLO us vs)
                      (@Sem_equiv_Proper_e_and _ _ _ SL _ _ _ _ SSLO us vs)
                      (@Sem_equiv_e_true_e_and_unitLL _ _ _ SL _ _ _ _ SSLO us vs)
                      (@Sem_equiv_e_true_e_and_unitLR _ _ _ SL _ _ _ _ SSLO us vs)
                      (@Sem_equiv_e_true_e_and_unitRL _ _ _ SL _ _ _ _ SSLO us vs)
                      (@Sem_equiv_e_true_e_and_unitRR _ _ _ SL _ _ _ _ SSLO us vs)
                      x l).
        unfold Sem_equiv. rewrite H1.
        intros; forward.
        repeat go_crazy SSL SSLO.
        destruct H as [ ? [ ? ? ] ].
        inv_all; subst.
        specialize (IHForall _ eq_refl).
        eapply pure_proper. rewrite H5 in H3. apply H3.
        eapply pure_land; eauto. }
    Qed.
*)
    Admitted.

(*
    Lemma iterated_base_true_and_star_emp'
    : forall tus tvs ps,
        match
            exprD' tus tvs (iterated_base SSL.(e_true) SSL.(e_and) ps) SL
          , exprD' tus tvs (iterated_base SSL.(e_emp) SSL.(e_star) (map (SSL.(e_and) SSL.(e_emp)) ps)) SL
        with
          | Some x , Some x' =>
            forall Q us vs,
              List.Forall
                (fun e : expr sym =>
                   exists val : typD nil SL,
                        exprD (join_env us) (join_env vs) e SL = Some val
                     /\ Pure.pure val)
                ps ->
              (x us vs //\\ Q -|- x' us vs ** Q)
          | None , None => True
          | _ , _ => False
        end.
    Proof.
      induction ps; simpl; intros.
      { unfold iterated_base in *; simpl in *.
        destruct (SSLO.(e_empOk) tus tvs) as [ ? [ ? ? ] ].
        destruct (e_trueOk SSLO tus tvs) as [ ? [ ? ? ] ].
        Cases.rewrite_all_goal; intros.
        rewrite H0. rewrite H2.
        rewrite empSPL. rewrite ltrue_unitL; eauto. }
      { (*
generalize (@iterated_base_cons _ SSL.(e_true) SSL.(e_and)
                      (Sem_equiv' _ SL lequiv us vs)
                      (@Reflexive_Sem_equiv' _ _ _ SL lequiv _ us tvs)
                      (@Transitive_Sem_equiv' _ _ _ SL lequiv _ us tvs)
                      (@Sem_equiv'_e_and_assoc _ _ _ SL _ _ _ SSL SSLO us tvs)
                      (@Sem_equiv'_Proper_e_and _ _ _ SL _ _ _ _ SSLO us tvs)
                      (@Sem_equiv'_e_true_e_and_unitLL _ _ _ SL _ _ _ _ SSLO us tvs)
                      (@Sem_equiv'_e_true_e_and_unitLR _ _ _ SL _ _ _ _ SSLO us tvs)
                      (@Sem_equiv'_e_true_e_and_unitRL _ _ _ SL _ _ _ _ SSLO us tvs)
                      (@Sem_equiv'_e_true_e_and_unitRR _ _ _ SL _ _ _ _ SSLO us tvs)
                   a ps).
        generalize (@iterated_base_cons _ SSL.(e_emp) SSL.(e_star)
                      (Sem_equiv _ SL lequiv us vs)
                      (@Reflexive_Sem_equiv _ _ _ SL lequiv _ us vs)
                      (@Transitive_Sem_equiv _ _ _ SL lequiv _ us vs)
                      (@Sem_equiv_e_star_assoc _ _ _ SL _ _ _ _ SSL SSLO us vs)
                      (@Sem_equiv_Proper_e_star _ _ _ SL _ _ _ _ _ SSLO us vs)
                      (@Sem_equiv_e_emp_e_star_unitLL _ _ _ SL _ _ _ _ _ SSLO us vs)
                      (@Sem_equiv_e_emp_e_star_unitLR _ _ _ SL _ _ _ _ _ SSLO us vs)
                      (@Sem_equiv_e_emp_e_star_unitRL _ _ _ SL _ _ _ _ _ SSLO us vs)
                      (@Sem_equiv_e_emp_e_star_unitRR _ _ _ SL _ _ _ _ _ SSLO us vs)
                   (e_and SSL (e_emp SSL) a) (map (e_and SSL (e_emp SSL)) ps)).
        unfold Sem_equiv.
        intros.
        repeat match goal with
                 | |- match ?X with _ => _ end =>
                   consider X; intros
               end; forward; repeat go_crazy SSL SSLO.
        { inv_all; subst.
          rewrite H5; clear H5.
          rewrite H4; clear H4.
          rewrite H9; clear H9.
          rewrite H7; clear H7.
          rewrite H11; clear H11.
          inversion H3; subst.
          specialize (IHps Q H7).
          destruct (exprD_e_empOk SSLO us vs) as [ ? [ ? ? ] ].
          rewrite H1 in *. inv_all; subst.
          rewrite H4.
          destruct H5. rewrite H10 in *. destruct H2.
          inv_all; subst.
          rewrite (landC empSP).
          rewrite sepSPA.
          rewrite pureandscD by eauto with typeclass_instances.
          rewrite empSPL.
          rewrite landA. rewrite IHps. reflexivity. 
        { destruct (exprD_e_empOk SSLO us vs) as [ ? [ ? ? ] ].
          congruence. } }
*) admit. }
    Qed.
    Lemma iterated_base_true_and_star_emp
    : forall us vs ps,
        match
            exprD us vs (iterated_base SSL.(e_true) SSL.(e_and) ps) SL
          , exprD us vs (iterated_base SSL.(e_emp) SSL.(e_star) (map (SSL.(e_and) SSL.(e_emp)) ps)) SL
        with
          | Some x , Some x' =>
            forall Q,
              List.Forall
                (fun e : expr sym =>
                   exists val : typD ts nil SL, exprD us vs e SL = Some val /\ Pure.pure val)
                ps ->
              x //\\ Q -|- x' ** Q
          | None , None => True
          | _ , _ => False
        end.
    Proof.
      induction ps; simpl; intros.
      { unfold iterated_base in *; simpl in *.
        destruct (exprD_e_empOk SSLO us vs) as [ ? [ ? ? ] ].
        destruct (exprD_e_trueOk SSLO us vs) as [ ? [ ? ? ] ].
        Cases.rewrite_all_goal; intros.
        rewrite H0. rewrite H2.
        rewrite empSPL. rewrite ltrue_unitL; eauto. }
      { generalize (@iterated_base_cons _ SSL.(e_true) SSL.(e_and)
                      (Sem_equiv _ SL lequiv us vs)
                      (@Reflexive_Sem_equiv _ _ _ _ SL lequiv _ us vs)
                      (@Transitive_Sem_equiv _ _ _ _ SL lequiv _ us vs)
                      (@Sem_equiv_e_and_assoc _ _ _ SL _ _ _ SSL SSLO us vs)
                      (@Sem_equiv_Proper_e_and _ _ _ SL _ _ _ _ SSLO us vs)
                      (@Sem_equiv_e_true_e_and_unitLL _ _ _ SL _ _ _ _ SSLO us vs)
                      (@Sem_equiv_e_true_e_and_unitLR _ _ _ SL _ _ _ _ SSLO us vs)
                      (@Sem_equiv_e_true_e_and_unitRL _ _ _ SL _ _ _ _ SSLO us vs)
                      (@Sem_equiv_e_true_e_and_unitRR _ _ _ SL _ _ _ _ SSLO us vs)
                   a ps).
        generalize (@iterated_base_cons _ SSL.(e_emp) SSL.(e_star)
                      (Sem_equiv _ SL lequiv us vs)
                      (@Reflexive_Sem_equiv _ _ _ _ SL lequiv _ us vs)
                      (@Transitive_Sem_equiv _ _ _ _ SL lequiv _ us vs)
                      (@Sem_equiv_e_star_assoc _ _ _ SL _ _ _ _ SSL SSLO us vs)
                      (@Sem_equiv_Proper_e_star _ _ _ SL _ _ _ _ _ SSLO us vs)
                      (@Sem_equiv_e_emp_e_star_unitLL _ _ _ SL _ _ _ _ _ SSLO us vs)
                      (@Sem_equiv_e_emp_e_star_unitLR _ _ _ SL _ _ _ _ _ SSLO us vs)
                      (@Sem_equiv_e_emp_e_star_unitRL _ _ _ SL _ _ _ _ _ SSLO us vs)
                      (@Sem_equiv_e_emp_e_star_unitRR _ _ _ SL _ _ _ _ _ SSLO us vs)
                   (e_and SSL (e_emp SSL) a) (map (e_and SSL (e_emp SSL)) ps)).
        unfold Sem_equiv.
        intros.
        repeat match goal with
                 | |- match ?X with _ => _ end =>
                   consider X; intros
               end; forward; repeat go_crazy SSL SSLO.
        { inv_all; subst.
          rewrite H5; clear H5.
          rewrite H4; clear H4.
          rewrite H9; clear H9.
          rewrite H7; clear H7.
          rewrite H11; clear H11.
          inversion H3; subst.
          specialize (IHps Q H7).
          destruct (exprD_e_empOk SSLO us vs) as [ ? [ ? ? ] ].
          rewrite H1 in *. inv_all; subst.
          rewrite H4.
          destruct H5. rewrite H10 in *. destruct H2.
          inv_all; subst.
          rewrite (landC empSP).
          rewrite sepSPA.
          rewrite pureandscD by eauto with typeclass_instances.
          rewrite empSPL.
          rewrite landA. rewrite IHps. reflexivity. }
        { destruct (exprD_e_empOk SSLO us vs) as [ ? [ ? ? ] ].
          congruence. } }
    Qed.
*)

(*
    Lemma iterated_base_true_and_star_emp
    : forall us vs ps x,
        exprD us vs (iterated_base SSL.(e_true) SSL.(e_and) ps) SL = Some x ->
        exists x',
          exprD us vs (iterated_base SSL.(e_emp) SSL.(e_star) (map (SSL.(e_and) SSL.(e_emp)) ps)) SL = Some x' /\
          forall Q,
            List.Forall
              (fun e : expr sym =>
                 exists val : typD ts nil SL, exprD us vs e SL = Some val /\ Pure.pure val)
              ps ->
            x //\\ Q -|- x' ** Q.
    Proof.
      
      induction ps; simpl; intros.
      { unfold iterated_base in *; simpl in *.
        destruct (exprD_e_empOk SSLO us vs) as [ ? [ ? ? ] ].
        destruct (exprD_e_trueOk SSLO us vs) as [ ? [ ? ? ] ].
        eexists; split; eauto. intros.
        rewrite H1. rewrite H in *. inv_all; subst.
        rewrite H3. rewrite empSPL. rewrite ltrue_unitL; eauto. }
      { generalize (@iterated_base_cons _ SSL.(e_true) SSL.(e_and)
                      (Sem_equiv _ SL lequiv us vs)
                      (@Reflexive_Sem_equiv _ _ _ SL lequiv _ us vs)
                      (@Transitive_Sem_equiv _ _ _ SL lequiv _ us vs)
                      (@Sem_equiv_e_and_assoc _ _ _ SL _ _ _ SSL SSLO us vs)
                      (@Sem_equiv_Proper_e_and _ _ _ SL _ _ _ _ SSLO us vs)
                      (@Sem_equiv_e_true_e_and_unitLL _ _ _ SL _ _ _ _ SSLO us vs)
                      (@Sem_equiv_e_true_e_and_unitLR _ _ _ SL _ _ _ _ SSLO us vs)
                      (@Sem_equiv_e_true_e_and_unitRL _ _ _ SL _ _ _ _ SSLO us vs)
                      (@Sem_equiv_e_true_e_and_unitRR _ _ _ SL _ _ _ _ SSLO us vs)
                   a ps).
        generalize (@iterated_base_cons _ SSL.(e_emp) SSL.(e_star)
                      (Sem_equiv _ SL lequiv us vs)
                      (@Reflexive_Sem_equiv _ _ _ SL lequiv _ us vs)
                      (@Transitive_Sem_equiv _ _ _ SL lequiv _ us vs)
                      (@Sem_equiv_e_star_assoc _ _ _ SL _ _ _ _ SSL SSLO us vs)
                      (@Sem_equiv_Proper_e_star _ _ _ SL _ _ _ _ _ SSLO us vs)
                      (@Sem_equiv_e_emp_e_star_unitLL _ _ _ SL _ _ _ _ _ SSLO us vs)
                      (@Sem_equiv_e_emp_e_star_unitLR _ _ _ SL _ _ _ _ _ SSLO us vs)
                      (@Sem_equiv_e_emp_e_star_unitRL _ _ _ SL _ _ _ _ _ SSLO us vs)
                      (@Sem_equiv_e_emp_e_star_unitRR _ _ _ SL _ _ _ _ _ SSLO us vs)
                   (e_and SSL (e_emp SSL) a) (map (e_and SSL (e_emp SSL)) ps)).
        unfold Sem_equiv.
        rewrite H. intros; forward.
        go_crazy SSL SSLO.
        generalize (iterated_base_true_and_pure _ _ H3); intro.
        eapply IHps in H3; clear IHps H.
        destruct H3 as [ ? [ ? ? ] ].
        consider (exprD us vs
               (e_star SSL (e_and SSL (e_emp SSL) a)
                  (iterated_base (e_emp SSL) (e_star SSL)
                     (map (e_and SSL (e_emp SSL)) ps))) SL).
        { intros.
          forward. eexists; split; eauto.
          intros. specialize (H3 Q).
          inversion H8. subst.
          destruct (exprD_e_empOk SSLO us vs) as [ ? [ ? ? ] ].
          repeat go_crazy SSL SSLO.
          inv_all; subst.
          specialize (H5 H12).
          destruct H11 as [ ? [ ? ? ] ]; inv_all; subst.
          specialize (H3 H12); clear H6 H12.
          subst.
          rewrite H2. rewrite H4. rewrite H7. rewrite H14. rewrite H16. rewrite H10.
          rewrite (landC empSP).
          rewrite sepSPA.
          rewrite pureandscD by eauto with typeclass_instances.
          rewrite empSPL.
          rewrite landA. rewrite H3. reflexivity. }
        { intros. forward.
          exfalso. repeat go_crazy SSL SSLO.
          destruct (exprD_e_empOk SSLO us vs) as [ ? [ ? ? ] ].
          congruence. } }
    Qed.
    Theorem conjunctives_to_expr_conjunctives_to_expr_star
    : forall tvs us c cE,
        exprD' us tvs (conjunctives_to_expr c) SL = Some cE ->
        exists cE',
          exprD' us tvs (conjunctives_to_expr_star c) SL = Some cE' /\
          forall (vs : hlist (typD ts nil) tvs),
            well_formed _ c us (join_env vs) ->
            cE vs -|- cE' vs.
    Proof.
      intros.
      consider (exprD' us tvs (conjunctives_to_expr_star c) SL); intros.
      { eexists; split; eauto; intros.
        destruct c.
        unfold well_formed, conjunctives_to_expr, conjunctives_to_expr_star in *.
        simpl in *.
        generalize dependent (e_star SSL
               (iterated_base (e_emp SSL) (e_star SSL)
                  (map
                     (fun x : expr sym * list (expr sym) =>
                      apps (fst x) (snd x)) spatial0))
               (if star_true0 then e_true SSL else e_emp SSL)).
        intros.
        repeat go_crazy SSL SSLO.
        generalize (@iterated_base_true_and_star_emp us (join_env vs) pure0).
        unfold exprD. rewrite split_env_join_env.
        rewrite H.
        intro. specialize (H6 _ eq_refl).
        destruct H6. destruct H6.
        forward. inv_all; subst.
        rewrite H3; clear H3.
        rewrite H5; clear H5.
        eapply H7; eauto.
        clear - H1.
        unfold exprD in H1.
        rewrite split_env_join_env in H1. assumption. }
      { exfalso.
        destruct c.
        unfold well_formed, conjunctives_to_expr, conjunctives_to_expr_star in *.
        simpl in *.
        generalize dependent (e_star SSL
               (iterated_base (e_emp SSL) (e_star SSL)
                  (map
                     (fun x : expr sym * list (expr sym) =>
                      apps (fst x) (snd x)) spatial0))
               (if star_true0 then e_true SSL else e_emp SSL)).
        intros.
        repeat go_crazy SSL SSLO.
        clear H2.
        generalize dependent x.
        generalize dependent pure0.
        induction pure0; intros.
        { unfold iterated_base in *. simpl in *.
          destruct (SSLO.(e_empOk) us tvs) as [ ? [ ? ? ] ].
          congruence. }
        { unfold iterated_base in *.
          simpl in *.
          consider ( iterated (e_and SSL) pure0); intros.
          { consider (iterated (e_star SSL) (map (e_and SSL (e_emp SSL)) pure0)); intros.
            { repeat go_crazy SSL SSLO.
              destruct (SSLO.(e_empOk) us tvs) as [ ? [ ? ? ] ].
              congruence.
              eapply IHpure0; reflexivity. }
            { repeat go_crazy SSL SSLO.
              destruct (SSLO.(e_empOk) us tvs) as [ ? [ ? ? ] ].
              congruence. } }
          { consider (iterated (e_star SSL) (map (e_and SSL (e_emp SSL)) pure0)); intros.
            { repeat go_crazy SSL SSLO.
              destruct (SSLO.(e_empOk) us tvs) as [ ? [ ? ? ] ].
              congruence.
              destruct (SSLO.(e_trueOk) us tvs) as [ ? [ ? ? ] ].
              eapply H4; eauto. }
            { repeat go_crazy SSL SSLO.
              destruct (SSLO.(e_empOk) us tvs) as [ ? [ ? ? ] ].
              congruence. } } } }
    Qed.
*)

    Theorem conjunctives_to_expr_conjunctives_to_expr_star_iff
    : forall tvs tus c,
        match
            exprD' tus tvs SL (conjunctives_to_expr c)
          , exprD' tus tvs SL (conjunctives_to_expr_star c)
        with
          | Some cE , Some cE' =>
            forall us (vs : hlist typD tvs),
            well_formed _ c (join_env us) (join_env vs) ->
            cE us vs -|- cE' us vs
          | None , None => True
          | _ , _ => False
        end.
    Proof.
(*
      intros.
      unfold conjunctives_to_expr, conjunctives_to_expr_star.
      generalize (e_star SSL
                 (iterated_base (e_emp SSL) (e_star SSL)
                    (map
                       (fun x : expr sym * list (expr sym) =>
                        apps (fst x) (snd x)) (spatial c)))
                 (if star_true c then e_true SSL else e_emp SSL)); intros.
(*
      consider (exprD' us tvs (conjunctives_to_expr_star c) SL); intros; forward.
      { consider (exprD' us tvs (conjunctives_to_expr c) SL); intros.
        { admit. }
        { unfold conjunctives_to_expr, conjunctives_to_expr_star in *.
          generalize dependent ((e_star SSL
              (iterated_base (e_emp SSL) (e_star SSL)
                 (map
                    (fun x : expr sym * list (expr sym) =>
                     apps (fst x) (snd x)) (spatial c)))
              (if star_true c then e_true SSL else e_emp SSL))).
          intros.
          repeat go_crazy SSL SSLO.
          destruct c; simpl in *.
          clear - H H0.
          generalize dependent x.
      
      { eexists; split; eauto; intros.
        destruct c.
        unfold well_formed, conjunctives_to_expr, conjunctives_to_expr_star in *.
        simpl in *.
        generalize dependent (e_star SSL
               (iterated_base (e_emp SSL) (e_star SSL)
                  (map
                     (fun x : expr sym * list (expr sym) =>
                      apps (fst x) (snd x)) spatial0))
               (if star_true0 then e_true SSL else e_emp SSL)).
        intros.
        repeat go_crazy SSL SSLO.
        generalize (@iterated_base_true_and_star_emp us (join_env vs) pure0).
        unfold exprD. rewrite split_env_join_env.
        rewrite H.
        intro. specialize (H6 _ eq_refl).
        destruct H6. destruct H6.
        forward. inv_all; subst.
        rewrite H3; clear H3.
        rewrite H5; clear H5.
        eapply H7; eauto.
        clear - H1.
        unfold exprD in H1.
        rewrite split_env_join_env in H1. assumption. }
      { exfalso.
        destruct c.
        unfold well_formed, conjunctives_to_expr, conjunctives_to_expr_star in *.
        simpl in *.
        generalize dependent (e_star SSL
               (iterated_base (e_emp SSL) (e_star SSL)
                  (map
                     (fun x : expr sym * list (expr sym) =>
                      apps (fst x) (snd x)) spatial0))
               (if star_true0 then e_true SSL else e_emp SSL)).
        intros.
        repeat go_crazy SSL SSLO.
        clear H2.
        generalize dependent x.
        generalize dependent pure0.
        induction pure0; intros.
        { unfold iterated_base in *. simpl in *.
          destruct (SSLO.(e_empOk) us tvs) as [ ? [ ? ? ] ].
          congruence. }
        { unfold iterated_base in *.
          simpl in *.
          consider ( iterated (e_and SSL) pure0); intros.
          { consider (iterated (e_star SSL) (map (e_and SSL (e_emp SSL)) pure0)); intros.
            { repeat go_crazy SSL SSLO.
              destruct (SSLO.(e_empOk) us tvs) as [ ? [ ? ? ] ].
              congruence.
              eapply IHpure0; reflexivity. }
            { repeat go_crazy SSL SSLO.
              destruct (SSLO.(e_empOk) us tvs) as [ ? [ ? ? ] ].
              congruence. } }
          { consider (iterated (e_star SSL) (map (e_and SSL (e_emp SSL)) pure0)); intros.
            { repeat go_crazy SSL SSLO.
              destruct (SSLO.(e_empOk) us tvs) as [ ? [ ? ? ] ].
              congruence.
              destruct (SSLO.(e_trueOk) us tvs) as [ ? [ ? ? ] ].
              eapply H4; eauto. }
            { repeat go_crazy SSL SSLO.
              destruct (SSLO.(e_empOk) us tvs) as [ ? [ ? ? ] ].
              congruence. } } } }
*)
*)
    Admitted.

(*
    Definition conjunctives_to_expr (c : conjunctives) : expr sym :=
      let ps := iterated e_and c.(pure) in
      let sp := iterated e_star (map (fun x => apps (fst x) (snd x)) c.(spatial)) in
      match ps , sp with
        | None , None => if c.(star_true) then e_true else e_emp
        | None , Some sp => if c.(star_true) then e_star sp e_true else sp
        | Some p , None => if c.(star_true) then p else e_and p e_emp
        | Some p , Some sp =>
          e_and p (if c.(star_true) then
                     e_star sp e_true
                   else
                     sp)
      end.
*)

(*
    Definition R_conjunctives
               (e : expr typ sym) (c : conjunctives) (tus tvs : tenv typ) : Prop :=
      forall val,
        exprD' (ts := ts) tus tvs e SL = Some val ->
        exists val',
             exprD' tus tvs (conjunctives_to_expr c) SL = Some val'
          /\ (forall us vs,
                (val us vs -|- val' us vs) /\ well_formed _ c (join_env us) (join_env vs)).

    Ltac forward_ex_and :=
      repeat match goal with
               | H : exists x, _ |- _ => destruct H
               | H : _ /\ _ |- _ => destruct H
             end.

    Local Instance Reflexive_lentails : Reflexive lentails.
    Proof.
      destruct IL. destruct lentailsPre. auto.
    Qed.

    Lemma something_smart
    : forall a b c d,
        Pure.pure a -> Pure.pure b ->
        (a //\\ b) //\\ c ** d -|- (a //\\ c) ** b //\\ d.
    Proof.
      clear - BIL IL Pure_it. intros.
      symmetry.
      rewrite pureandscD by eauto with typeclass_instances.
      rewrite sepSPC.
      rewrite pureandscD by eauto with typeclass_instances.
      rewrite <- landA.
      rewrite sepSPC. reflexivity.
    Qed.

    Lemma well_formed_pure
    : forall x us vs,
        well_formed _ x us vs ->
        forall x7,
          exprD us vs (iterated_base SSL.(e_true) SSL.(e_and) (pure x)) SL = Some x7 ->
          Pure.pure x7.
    Proof.
      unfold well_formed. destruct x; simpl.
      induction 1; simpl; intros.
(*
      { unfold iterated_base in H. simpl in *.
        destruct (SSLO.(e_trueOk) us tvs).
        rewrite H in *. destruct H0.
        inv_all; subst. eapply Pure.pure_proper. eapply H1.
        eapply pure_ltrue; eauto with typeclass_instances. }
      { unfold iterated_base in *. simpl in *.
        destruct (iterated SSL.(e_and) l); intros.
        { go_crazy SSL SSLO.
          eapply Pure.pure_proper. eapply H3.
          destruct H. destruct H.
          eapply pure_land; eauto with typeclass_instances.
          unfold exprD in *. rewrite split_env_join_env in *.
          rewrite H1 in *. inv_all. rewrite H. auto. }
        { destruct H. destruct H.
          unfold exprD in H. rewrite split_env_join_env in *.
          rewrite H1 in *. inv_all; subst.
          auto. } }
    Qed. *)
    Admitted.

    Lemma Forall_app
    : forall T (P : T -> Prop) xs ys,
        List.Forall P (xs ++ ys) <-> (List.Forall P xs /\ List.Forall P ys).
    Proof.
      clear. induction xs; simpl; intros.
      { intuition. }
      { split; intros.
        { inversion H; subst. rewrite IHxs in H3. intuition. }
        { intuition. inversion H0; subst. constructor; eauto. eapply IHxs. auto. } }
    Qed.

    Lemma something_smart'
    : forall a b c d e f g,
        Pure.pure a -> Pure.pure b ->
        e -|- f ** g ->
        (a //\\ b) //\\ (c ** d) ** e -|-
                   (a //\\ c ** f) ** b //\\ d ** g.
    Proof.
      clear - BIL pure_land pure_ltrue. intros. rewrite H1. clear H1.
      transitivity ((a //\\ b) //\\ (c ** f) ** d ** g).
      { apply land_cancel; eauto with typeclass_instances.
        repeat rewrite sepSPA.
        rewrite (sepSPC c).
        rewrite (sepSPC c).
        apply lequiv_sep_cancel; eauto with typeclass_instances.
        repeat rewrite <- sepSPA.
        rewrite (sepSPC d f). reflexivity. }
      { rewrite something_smart by eauto. reflexivity. }
    Qed.

    Lemma cte_mkStar
    : forall tus tvs r_res l_res rval lval,
        exprD' tus tvs (conjunctives_to_expr r_res) SL = Some rval ->
        exprD' tus tvs (conjunctives_to_expr l_res) SL = Some lval ->
        exists val,
          exprD' tus tvs (conjunctives_to_expr (mkStar l_res r_res)) SL = Some val /\
          forall us vs,
            well_formed _ l_res (join_env us) (join_env vs) ->
            well_formed _ r_res (join_env us) (join_env vs) ->
            (val us vs -|- lval us vs ** rval us vs) /\
            well_formed _ (mkStar l_res r_res) (join_env us) (join_env vs).
    Proof.
(*
      intros.
      consider (exprD' us tvs (conjunctives_to_expr (mkStar l_res r_res)) SL);
        intros; unfold conjunctives_to_expr, mkStar in *; simpl in *.
      { eexists; split; eauto. intros.
        split.
        { destruct (SSLO.(e_empOk) us tvs).
          destruct (SSLO.(e_trueOk) us tvs).
          rewrite map_app in *.
          forward_ex_and.
          generalize (@iterated_base_app _ SSL.(e_true) SSL.(e_and)
                        (Sem_equiv _ SL lequiv us (join_env vs))
                 (@Reflexive_Sem_equiv _ _ _ SL lequiv _ us (join_env vs))
                 (@Transitive_Sem_equiv _ _ _ SL lequiv _ us (join_env vs))
                 (Sem_equiv_e_and_assoc _ SSLO) Sem_equiv_Proper_e_and
                 Sem_equiv_e_true_e_and_unitLL
                 Sem_equiv_e_true_e_and_unitLR
                 Sem_equiv_e_true_e_and_unitRL
                 Sem_equiv_e_true_e_and_unitRR r_res.(pure) l_res.(pure) us tvs).
          generalize (@iterated_base_app _ e_emp e_star (Sem_equiv _ SL lequiv)
                (@Reflexive_Sem_equiv _ _ _ SL lequiv _)
                (@Transitive_Sem_equiv _ _ _ SL lequiv _)
                Sem_equiv_e_star_assoc Sem_equiv_Proper_e_star
                Sem_equiv_e_emp_e_star_unitLL
                Sem_equiv_e_emp_e_star_unitLR
                Sem_equiv_e_emp_e_star_unitRL
                Sem_equiv_e_emp_e_star_unitRR
                (map (fun x : expr sym * list (expr sym) => apps (fst x) (snd x)) r_res.(spatial))
                (map (fun x : expr sym * list (expr sym) => apps (fst x) (snd x)) l_res.(spatial))
                us tvs).
          repeat go_crazy.
          intros; forward.
          inv_all; subst.
          repeat match goal with
                   | H : forall x, _ -|- _ |- _ => rewrite H
                 end.
          assert (Pure.pure (x8 vs)).
          { eapply well_formed_pure; [ | eauto ]; eauto. }
          assert (Pure.pure (x9 vs)).
          { eapply well_formed_pure; [ | eauto ]; eauto. }
          destruct l_res.(star_true); destruct r_res.(star_true);
          intros; simpl in *; repeat go_crazy; inv_all; subst;
          repeat match goal with
                   | H : forall x, _ -|- _ |- _ => rewrite H
                 end; eapply something_smart'; auto.
          { rewrite ltrue_sep. reflexivity. }
          { rewrite empSPR. reflexivity. }
          { rewrite empSPL. reflexivity. }
          { rewrite empSPL. reflexivity. } }
        { red. simpl.
          apply Forall_app. split; assumption. } }
      { exfalso.
        generalize (@iterated_base_app _ e_true e_and (Sem_equiv _ SL lequiv)
                                     (@Reflexive_Sem_equiv _ _ _ SL lequiv _)
                                     (@Transitive_Sem_equiv _ _ _ SL lequiv _)
                                     Sem_equiv_e_and_assoc Sem_equiv_Proper_e_and
                 Sem_equiv_e_true_e_and_unitLL
                 Sem_equiv_e_true_e_and_unitLR
                 Sem_equiv_e_true_e_and_unitRL
                 Sem_equiv_e_true_e_and_unitRR r_res.(pure) l_res.(pure) us tvs).
        generalize (@iterated_base_app _ e_emp e_star (Sem_equiv _ SL lequiv)
           (@Reflexive_Sem_equiv _ _ _ SL lequiv _)
           (@Transitive_Sem_equiv _ _ _ SL lequiv _)
           Sem_equiv_e_star_assoc Sem_equiv_Proper_e_star
           Sem_equiv_e_emp_e_star_unitLL
           Sem_equiv_e_emp_e_star_unitLR
           Sem_equiv_e_emp_e_star_unitRL
           Sem_equiv_e_emp_e_star_unitRR
           (map (fun x : expr sym * list (expr sym) => apps (fst x) (snd x)) r_res.(spatial))
           (map (fun x : expr sym * list (expr sym) => apps (fst x) (snd x)) l_res.(spatial))
           us tvs).
        rewrite map_app in *.
        repeat go_crazy.
        inv_all; subst. intros; forward.
        destruct l_res.(star_true); destruct r_res.(star_true); simpl in *;
        repeat go_crazy; congruence. }
    Qed.
*) Admitted.
*)
    End with_pure.
(*
    Variable SLS : SepLogSpec sym.
    Variable slsok : SepLogSpecOk RSym_sym SL SLS ILO BILO.
(*
    Theorem SepLogArgsOk_conjunctives
    : SepLogArgsOk RSym_sym SL SepLogArgs_normalize SLS R_conjunctives.
    Proof.
      constructor; unfold R_conjunctives; simpl; intros.
      { unfold mkSpatial, conjunctives_to_expr. simpl.
        unfold iterated_base. simpl.
        consider (exprD' (join_env us) tvs (SSL.(e_and) SSL.(e_true) (SSL.(e_star) (apps e (map fst es)) SSL.(e_emp))) SL); intros;
        repeat (go_crazy SSL SSLO); inv_all; subst.
        { eexists; split; eauto.
          intros.
          destruct (SSLO.(e_empOk) (join_env us) tvs).
          destruct (SSLO.(e_trueOk) (join_env us) tvs).
          forward_ex_and.
          repeat (go_crazy SSL SSLO).
          inv_all; subst.
          repeat match goal with
                   | H : forall x, _ -|- _ |- _ =>
                     rewrite H
                 end.
          rewrite empSPR; eauto with typeclass_instances.
          rewrite landtrueL. split.
          reflexivity. constructor. }
        { destruct (SSLO.(e_trueOk) (join_env us) tvs) as [ ? [ ? ? ] ]. congruence. }
        { destruct (SSLO.(e_empOk) (join_env us) tvs) as [ ? [ ? ? ] ]. congruence. } }
      { unfold conjunctives_to_expr, mkPure; simpl.
        unfold iterated_base. simpl.
        destruct (SSLO.(e_empOk) (join_env us) tvs).
        destruct (SSLO.(e_trueOk) (join_env us) tvs).
        forward_ex_and.
        consider (exprD' (join_env us) tvs (SSL.(e_and) e (SSL.(e_star) SSL.(e_emp) SSL.(e_true))) SL);
          intros; do 5 (go_crazy SSL SSLO); try congruence.
        { eexists; split; eauto.
          intros. inv_all; subst.
          rewrite H8. rewrite H10. rewrite H4. rewrite H5.
          rewrite empSPL. rewrite landtrueR. split.
          { reflexivity. }
          { red. constructor. 2: constructor.
            unfold exprD. rewrite split_env_join_env. rewrite H1.
            eexists; split; eauto.
            eapply His_pure. eassumption.
            instantiate (1 := join_env vs).
            instantiate (1 := join_env us).
            unfold exprD. rewrite split_env_join_env. rewrite H1. reflexivity. } } }
      { unfold conjunctives_to_expr, mkEmpty; simpl.
        destruct (SSLO.(e_empOk) (join_env us) tvs).
        destruct (SSLO.(e_trueOk) (join_env us) tvs).
        forward_ex_and. unfold iterated_base. simpl.
        consider (exprD' (join_env us) tvs (SSL.(e_and) SSL.(e_true) (SSL.(e_star) SSL.(e_emp) SSL.(e_emp))) SL); 
          intros; repeat (go_crazy SSL SSLO); try congruence.
        { eexists; split; eauto.
          inv_all; subst. intros.
          split; try solve [ constructor ].
          eapply His_emp  with (us := join_env us) (vs := join_env vs) in H0; eauto.
          unfold exprD in *. rewrite split_env_join_env in *.
          rewrite H1 in *. inv_all; subst. rewrite H0.
          rewrite H8. rewrite H10. rewrite H4. rewrite H5.
          rewrite empSPL. rewrite landtrueL. reflexivity. } }
      { red_exprD.
        generalize (slsok.(His_star) _ H2 (join_env us)).
        rewrite H in *.
        unfold type_of_apply in *.
        forward.
        inv_all. subst t. subst t4. subst p. subst val.
        red_exprD. rewrite H in H8.
        forward. inv_all.
        subst p t2.
        specialize (H3 _ _ H8).
        subst t0 t1.
        specialize (H4 _ _ H9).
        forward_ex_and.
        specialize (@cte_mkStar (join_env us) tvs _ _ _ _ H4 H3); intros.
        forward_ex_and.
        eexists; split; eauto.
        intros.
        uip_all'.
        specialize (H7 (join_env vs)).
        unfold exprD in *.
        rewrite split_env_join_env in *.
        rewrite H5 in *. inv_all; subst.
        rewrite H7.
        specialize (H10 vs). specialize (H11 vs).
        forward_ex_and.
        specialize (H13 _ H16 H14).
        forward_ex_and. split; auto.
        symmetry. rewrite H11. rewrite H10. auto. }
    Qed.
*)
*)

    Definition mkAnd (l r : conjunctives) : conjunctives :=
      match l.(spatial) with
        | nil => {| spatial := r.(spatial)
                    ; pure := r.(pure) ++ l.(pure)
                    ; star_true := r.(star_true)
                 |}
        | _ :: _ =>
          match r.(spatial) with
            | nil => {| spatial := l.(spatial)
                        ; pure := l.(pure) ++ r.(pure)
                        ; star_true := l.(star_true)
                     |}
            | _ :: _ =>
              (** This is sub-optimal on several levels *)
              mkSpatial (SSL.(e_and) (conjunctives_to_expr l) (conjunctives_to_expr r)) nil
          end
      end.

    Definition SepLogAndArgs_normalize : SepLogAndArgs typ sym conjunctives :=
    {| do_emp := mkEmpty
     ; do_star := mkStar
     ; do_other := fun f xs => mkSpatial f (List.map fst xs)
     ; do_pure := mkPure
     ; do_and := mkAnd
     |}.

  End conjunctivesD.

  Definition normalize (sls : SepLogSpec typ sym) :=
    lazy_typed_mfold _ _ (AppFullFoldArgs_SepLogArgs SepLogArgs_normalize sls).

  Definition normalize_and (ssl : SynSepLog typ sym) (sls : SepLogAndSpec typ sym) :=
    lazy_typed_mfold _ _ (AppFullFoldArgs_SepLogAndArgs (SepLogAndArgs_normalize ssl) sls).


(*
  Theorem normalizeOk
          (ILO : ILogicOps (typD nil SL))
          (BILO : BILOperators (typD nil SL))
          (IL : @ILogic _ ILO)
          (BIL : @BILogic _ ILO BILO)
          (sls : SepLogSpec _ sym) (slsOk : SepLogSpecOk _ _ _ sls _ _)
          (ssl : SynSepLog _ sym) (sslo : SynSepLogOk _ _ _ _ _ ssl)
  : forall (e : expr typ sym) tus tvs,
      match exprD' nil tus tvs SL e
          , exprD' nil tus tvs SL (conjunctives_to_expr ssl (normalize sls nil tus tvs e))
      with
        | Some l , Some r =>
          forall us vs,
            (l us vs -|- r us vs) /\
            well_formed (slsOk.(_PureOp)) (normalize sls e tus tvs) (join_env us) (join_env vs)
        | None , None => True
        | _ , _ => False
      end.
  Proof.
  Admitted.
*)

End conjunctives.

(*
Module demo.
  Definition is_emp (i : ilfunc) : bool :=
    match i with
      | ilf_true _ => true
      | _ => false
    end.
  Definition is_star (e : ilfunc) : bool :=
    match e with
      | fref 1%positive => true
      | _ => false
    end.
  Definition SepLogSpec_demo : SepLogSpec ilfunc :=
    Build_SepLogSpec (fun _ => false) is_emp is_star.
  Definition inj_emp := Inj (ilf_true (tyType 1)).
  Definition inj_star a b :=
    Eval compute in apps (Inj (fref 1%positive)) (a :: b :: nil).
  Definition inj_and a b :=
    Eval compute in apps (Inj (fref 2%positive)) (a :: b :: nil).
  Definition test := fun x => normalize SepLogSpec_demo x nil nil.
  Eval compute in  test inj_emp.
  Eval compute in  test (inj_star inj_emp inj_emp).
  Eval compute in  test (inj_star (Var 0) (inj_star inj_emp (inj_and (Var 1) (Var 3)))).
End demo.
*)