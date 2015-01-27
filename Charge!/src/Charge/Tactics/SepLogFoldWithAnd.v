(** This file implements an interface to [expr] that
 ** makes star, emp, and pure assertions apparent.
 **)
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Tactics.
Require Import Charge.Logics.BILogic Charge.Logics.Pure.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.AppN.
Require Import MirrorCore.Lambda.TypedFoldApp.

Set Implicit Arguments.
Set Strict Implicit.

(** NOTE: This could work on arbitrary expr's **)
Section seplog_fold.
  Variable typ : Type.
  Variable RType_typ : RType typ.
  Variable Typ2_Fun : Typ2 _ Fun.
  Variable sym : Type.
  Variable RSym_sym : RSym sym.

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.

  Let Expr_expr := @Expr_expr typ sym _ _ _.
  Local Existing Instance Expr_expr.

  Variable T : Type.
  Variable SL : typ.

  Record SepLogAndArgs : Type :=
  { do_other : expr typ sym -> list (expr typ sym * T) -> T
  ; do_pure : expr typ sym -> T
  ; do_emp : T
  ; do_star : T -> T -> T
  ; do_and : T -> T -> T
  }.

  Record SepLogAndSpec : Type :=
  { is_pure : expr typ sym -> bool
  ; is_emp : expr typ sym -> bool
  ; is_star : expr typ sym -> bool
  ; is_and : expr typ sym -> bool
  }.

  Variable sla : SepLogAndArgs.
  Variable sls : SepLogAndSpec.

  Record SepLogAndSpecOk (sls : SepLogAndSpec)
         (OPS : ILogic.ILogicOps (typD SL))
         (BI : BILOperators (typD SL)) : Type :=
  { _PureOp : @PureOp (typD SL)
  ; _Pure : @Pure _ OPS BI _PureOp
  ; His_pure : forall e,
                 sls.(is_pure) e = true ->
                 forall us vs val,
                   exprD us vs e SL = Some val ->
                   pure val
  ; His_emp : forall e,
                sls.(is_emp) e = true ->
                forall us vs,
                  exprD us vs e SL = Some empSP
  ; His_star : forall e,
                 sls.(is_star) e = true ->
                 forall us vs,
                   exprD us vs e (tyArr SL (tyArr SL SL)) =
                   Some match eq_sym (typ2_cast SL (tyArr SL SL)) in _ = t
                              return t
                        with
                          | eq_refl =>
                            match eq_sym (typ2_cast SL SL) in _ = t
                                  return _ -> t
                            with
                              | eq_refl => sepSP
                            end
                        end
  ; His_and : forall e,
                 sls.(is_and) e = true ->
                 forall us vs,
                   exprD us vs e (tyArr SL (tyArr SL SL)) =
                   Some match eq_sym (typ2_cast SL (tyArr SL SL)) in _ = t
                              return t
                        with
                          | eq_refl =>
                            match eq_sym (typ2_cast SL SL) in _ = t
                                  return _ -> t
                            with
                              | eq_refl => ILogic.land
                            end
                        end
  }.

  Record SepLogAndArgsOk (R_t : expr typ sym -> T -> tenv typ -> tenv typ -> Prop) :=
  { otherOk
    : forall e es tus tvs,
        @typeof_apps typ sym _ _ _ tus tvs e (List.map fst es) = Some SL ->
        (forall x y,
           In (x,y) es ->
           typeof_expr tus tvs x = Some SL ->
           R_t x y tus tvs) ->
        R_t (apps e (List.map fst es)) (sla.(do_other) e es) tus tvs
  ; pureOk
    : forall e tus tvs,
        typeof_expr tus tvs e = Some SL ->
        sls.(is_pure) e = true ->
        R_t e (sla.(do_pure) e) tus tvs
  ; empOk
    : forall e tus tvs,
        typeof_sym e = Some SL ->
        sls.(is_emp) (Inj e) = true ->
        R_t (Inj e) sla.(do_emp) tus tvs
  ; starOk
    : forall e l r l_res r_res tus tvs,
        typeof_sym e = Some (tyArr SL (tyArr SL SL)) ->
        typeof_expr tus tvs l = Some SL ->
        typeof_expr tus tvs r = Some SL ->
        sls.(is_star) (Inj e) = true ->
        R_t l l_res tus tvs ->
        R_t r r_res tus tvs ->
        R_t (apps (Inj e) (l :: r :: nil)) (sla.(do_star) l_res r_res) tus tvs
  ; andOk
    : forall e l r l_res r_res tus tvs,
        typeof_sym e = Some (tyArr SL (tyArr SL SL)) ->
        typeof_expr tus tvs l = Some SL ->
        typeof_expr tus tvs r = Some SL ->
        sls.(is_and) (Inj e) = true ->
        R_t l l_res tus tvs ->
        R_t r r_res tus tvs ->
        R_t (apps (Inj e) (l :: r :: nil)) (sla.(do_and) l_res r_res) tus tvs
  }.

  Instance Applicative_Lazy : Applicative Lazy :=
  { ap := fun _ _ f x z =>
            match f z , x z with
              | Some f , Some x => Some (f x)
              | _ , _ => None
            end
  ; pure := fun _ x => fun _ => Some x }.

  (** NOTE: This does not need to be typed! **)
  Definition AppFullFoldArgs_SepLogAndArgs
  : AppFullFoldArgs typ sym T.
  refine
    match sla , sls with
      | {| do_other := do_other'
         ; do_pure := do_pure'
         ; do_star := do_star'
         ; do_emp := do_emp'
         ; do_and := do_and' |}
      , {| is_pure := is_pure'
         ; is_star := is_star'
         ; is_emp := is_emp'
         ; is_and := is_and' |} =>
        @Build_AppFullFoldArgs
          typ sym T
          (fun v _ _ =>
             if is_pure' (Var v) then
               Some (do_pure' (Var v))
             else
               if is_emp' (Var v) then
                 Some do_emp'
               else
                 Some (do_other' (Var v) nil))
          (fun u _ _ =>
             if is_pure' (UVar u) then
               Some (do_pure' (UVar u))
             else
               if is_emp' (UVar u) then
                 Some do_emp'
               else
                 Some (do_other' (UVar u) nil))
          (fun i _ _ =>
             if is_emp' (Inj i) then
               Some do_emp'
             else
               if is_pure' (Inj i) then
                 Some (do_pure' (Inj i))
               else
                 Some (do_other' (Inj i) nil))
          (fun tus tvs t f fres args z =>
             if is_star' f then
               match args with
                 | (_,_,l) :: (_,_,r) :: nil =>
                   match l z , r z with
                     | Some l , Some r =>
                       Some (do_star' l r)
                     | _ , _ => None
                   end
                 | _ => Some do_emp'
               end
             else
               if is_and' f then
                 match args with
                   | (_,_,l) :: (_,_,r) :: nil =>
                     match l z , r z with
                       | Some l , Some r =>
                         Some (do_and' l r)
                       | _ , _ => None
                     end
                   | _ => Some do_emp'
                 end
               else
                 let original := apps f (map (fun x => snd (fst x)) args) in
                 if is_pure' original then
                   Some (do_pure' original)
                 else
                   ap (Applicative.pure (do_other' f))
                      (mapT (fun tev => let '(t,e,v) := tev in
                                        match v tt with
                                          | None => None
                                          | Some v => Some (e,v)
                                        end) args))
          (fun tus tvs t _ e eres _ =>
             if is_pure' (Abs t e) then
               Some (do_pure' (Abs t e))
             else
               if is_emp' (Abs t e) then
                 Some do_emp'
               else
                 Some (do_other' (Abs t e) nil))
    end.
  Defined.

(* TODO(gmalecha): Port the proof!
  Section sound.
    Hypothesis BILOps : BILOperators (typD nil SL).
    Context R_t `{slaok : SepLogArgsOk R_t}.

    Lemma atomic_ok
    : forall ts (tus tvs : tenv typ) e (t : typ),
        typeof_expr ts tus tvs e = Some t ->
        t = SL ->
        R_t e (sla.(do_other) e nil) tus tvs.
    Proof.
      destruct slaok. simpl; intros. subst.
      change e with (apps e nil) at 1.
      eapply (otherOk0 ts e nil tus tvs); simpl.
      { unfold typeof_apps. simpl. rewrite H. reflexivity. }
      { intuition. }
    Qed.

    Hypothesis is_starOk
    : forall i,
        sls.(is_star) (Inj i) = true ->
        typeof_sym i = Some (tyArr SL (tyArr SL SL)).

    Lemma lem_other
    : forall ts0 t rs tus tvs l_res do_atomic_app0,
        Forall2
          (fun (t0 : typ) (x : expr sym * (tenv typ -> tenv typ -> T)) =>
             typeof_expr tus tvs (fst x) = Some t0 /\
             (t0 = SL -> R_t (fst x) (snd x tus tvs) tus tvs)) ts0 rs ->
        forall e : expr sym,
          typeof_expr tus tvs (apps e (map fst rs)) = Some t ->
          (fold_right tyArr t ts0 = SL -> R_t e (l_res tus tvs) tus tvs) ->
          typeof_apps RSym_sym tus tvs e (map fst rs) = Some SL ->
          (forall (e0 : expr sym) (es : list (expr sym * T)) (tus0 tvs0 : tenv typ),
             typeof_apps RSym_sym tus0 tvs0 e0 (map fst es) = Some SL ->
             (forall (x : expr sym) (y : T),
                In (x, y) es -> typeof_expr tus0 tvs0 x = Some SL -> R_t x y tus0 tvs0) ->
             R_t (apps e0 (map fst es)) (do_atomic_app0 e0 es) tus0 tvs0) ->
          R_t (apps e (map fst rs))
              (do_atomic_app0 e
                              (map
                                 (fun x : expr sym * (tenv typ -> tenv typ -> T) =>
                                    (fst x, snd x tus tvs)) rs)) tus tvs.
    Proof.
      intros.
      specialize (H3 e (map
                          (fun x : expr sym * (tenv typ -> tenv typ -> T) =>
                             (fst x, snd x tus tvs)) rs) tus tvs).
      rewrite map_map in *. simpl in *.
      eapply H3; eauto.
      clear - H. induction H; simpl; intuition.
      inv_all. subst. rewrite H1 in *. inv_all; subst.
      eauto.
    Qed.

    Definition AppFullFoldArgsOk_SepLogsOk
    : AppFullFoldArgsOk _ (AppFullFoldArgs_SepLogArgs sla)
                        (fun t e res tus tvs =>
                           t = SL ->
                           R_t e res tus tvs).
    Proof.
      remember sla as s; destruct s; simpl; remember sls as s; destruct s.
      constructor.
      { simpl; intros.
        replace do_other0 with (sla.(do_other)).
        eapply atomic_ok; eauto. rewrite <- Heqs; reflexivity. }
      { simpl; intros.
        replace do_other0 with (sla.(do_other)).
        eapply atomic_ok; eauto. rewrite <- Heqs; reflexivity. }
      { simpl; intros.
        consider (is_emp0 v); intros.
        { replace do_emp0 with (sla.(do_emp)).
          eapply (@empOk _ slaok); eauto.
          Cases.rewrite_all_goal. auto.
          rewrite <- Heqs0. simpl. auto.
          rewrite <- Heqs. reflexivity. }
        { replace do_other0 with (sla.(do_other)).
          eapply atomic_ok; eauto. rewrite <- Heqs; reflexivity. } }
      { simpl; intros.
        replace do_other0 with (sla.(do_other)).
        eapply atomic_ok; eauto. rewrite <- Heqs; reflexivity. }
      { intros. subst ft. simpl.
        assert (typeof_apps RSym_sym tus tvs l (map fst rs) = Some SL).
        { rewrite <- typeof_expr_apps. congruence. }
        generalize (otherOk slaok). rewrite <- Heqs. simpl.
        destruct l; eauto using lem_other.
        consider (is_star0 s); eauto using lem_other; intros.
        { generalize H4. eapply is_starOk in H4.
          unfold typeof_apps in H3.
          simpl in H3. rewrite H4 in *.
          inversion H1; clear H1; try subst.
          { subst rs ts0; intros.
            simpl in *. clear - H3. inv_all.
            symmetry in H3. eapply tyArr_circ_L in H3. intuition. }
          { subst rs ts0. inversion H7; clear H7.
            { subst l l'; intros; simpl in *.
              rewrite H4 in *. forward.
              intuition. inv_all. subst y t0.
              clear - H8. symmetry in H8.
              eapply tyArr_circ_L in H8. intuition. }
            { subst l l'. inversion H8; clear H8.
              { subst l0 l'0. intuition. subst t.
                destruct y, y0; simpl in *.
                rewrite H8 in *. rewrite H6 in *. rewrite H4 in *.
                unfold type_of_apply in *. forward.
                inv_all.
                subst x0 x t1 t2 t3 p0 p.
                replace do_star0 with (sla.(do_star));
                  [ | rewrite <- Heqs; reflexivity ].
                eapply (starOk slaok); eauto.
                rewrite <- Heqs0. auto. }
              { exfalso. clear Heqs Heqs0. subst.
                simpl in H3. intuition.
                rewrite H2 in *. rewrite H6 in *. rewrite H1 in *.
                forward. inv_all; try subst.
                clear H15 H13. subst x x0 x1.
                clear - H14.
                eapply type_of_applys_circle_False in H14. auto. } } } } }
    Qed.

    Definition seplog_fold (sla : SepLogArgs) : expr sym -> tenv typ -> tenv typ -> T :=
      app_fold_args (AppFullFoldArgs_SepLogArgs sla).

    Theorem seplog_fold_sound
    : forall e tus tvs result,
        seplog_fold sla e tus tvs = result ->
        typeof_expr tus tvs e = Some SL ->
        R_t e result tus tvs.
    Proof.
      intros.
      eapply (app_fold_args_sound AppFullFoldArgsOk_SepLogsOk) in H; eauto.
    Qed.
  End sound.
*)


(*
  Variable OPS : ILogic.ILogicOps (typD ts nil SL).
  Variable BI : BILOperators (typD ts nil SL).
  Variable slsok : SepLogSpecOk sls OPS BI.

  Require Import Relations.
  Require Import ExtLib.Data.HList.

  Record SepLogArgsSemOk
         (TD : T -> forall tus tvs, tenv typ -> tenv typ -> option (typD ts nil SL))
         (R : forall tus tvs,
                relation (hlist (typD ts nil) tus ->
                          hlist (typD ts nil) tvs ->
                          typD ts nil SL)) :=
  { atomic_appOk
    : forall e es tus tvs val,
        exprD' tus tvs (apps e es) SL = Some val ->
        R tus tvs val (TD (sla.(do_other) e es))
  ; pureOk
    : forall e tus tvs,
        typeof_expr tus tvs e = Some SL ->
        sls.(is_pure) e = true ->
        R_t e (sla.(do_pure) e) tus tvs
  ; empOk
    : forall e tus tvs,
        typeof_sym e = Some SL ->
        sls.(is_emp) e = true ->
        R_t (Inj e) sla.(do_emp) tus tvs
  ; starOk
    : forall e l r l_res r_res tus tvs,
        typeof_sym e = Some (tyArr SL (tyArr SL SL)) ->
        typeof_expr tus tvs l = Some SL ->
        typeof_expr tus tvs r = Some SL ->
        sls.(is_star) e = true ->
        R_t l l_res tus tvs ->
        R_t r r_res tus tvs ->
        R_t (apps (Inj e) (l :: r :: nil)) (sla.(do_star) l_res r_res) tus tvs
  }.
*)

End seplog_fold.