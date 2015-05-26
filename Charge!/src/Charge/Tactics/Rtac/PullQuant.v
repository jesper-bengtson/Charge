Require Import ExtLib.Core.RelDec.

Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.Subst.FMapSubst.
Require Import MirrorCore.Lambda.ExprSubst.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require MirrorCore.syms.SymEnv.
Require MirrorCore.syms.SymSum.

Require Import Charge.ModularFunc.BaseFunc.
Require Import Charge.ModularFunc.ILogicFunc.
Require Import Charge.ModularFunc.BILogicFunc.
Require Import Charge.ModularFunc.EmbedFunc.
Require Import Charge.SetoidRewrite.AutoSetoidRewrite.
Require Import Charge.SetoidRewrite.Base.
Require Import Charge.SetoidRewrite.ILSetoidRewrite.
Require Import Charge.SetoidRewrite.BILSetoidRewrite.
Require Import Charge.SetoidRewrite.EmbedSetoidRewrite.
Require Import Charge.Tactics.PullQuant.ILPullQuant.
Require Import Charge.Tactics.PullQuant.BILPullQuant.
Require Import Charge.Tactics.PullQuant.EmbedPullQuant.
Require Import Charge.Logics.ILogic.

Set Implicit Arguments.
Set Strict Implicit.

Section PullQuant.
  Context (typ func : Type) {RType_typ : RType typ}.
  Context {HIL : ILogicFunc typ func} {HB : BaseFunc typ func}.
  Context {HBIL : BILogicFunc typ func} {HE : EmbedFunc typ func}.
  Context {RelDec_func : RelDec (@eq (expr typ func))}.
  Context {target : expr typ func -> bool}.
  Context {Typ2_typ : Typ2 RType_typ Fun}.
  Context {Typ0_typ : Typ0 RType_typ Prop}.
  Context {RSym_func : RSym func}.
  Context {Expr_expr : Expr RType_typ (expr typ func)}.
  Context {ilogic : forall t : typ, option (ILogicOps (typD t))}.

  Definition pull_quant vars :=
  setoid_rewrite vars _ (fEntails : typ -> expr typ func) rw_fail
    (sr_combine il_respects
               (sr_combine (@il_respects_reflexive typ func _ _ _ ilogic _ _)
                                        (sr_combine bil_respects (sr_combine embed_respects
                                                    (sr_combine eq_respects refl)))))
    (sr_combineK  (il_match_plus (fun _ => true) fEq)
                  (sr_combineK (bil_match_plus fEq) (eil_match_plus fEq))).

  Definition PULL_EXISTSR_AUX (pq : list typ -> typ -> expr typ func -> option (expr typ func * rsubst (expr typ func))) : 
    rtac typ (expr typ func) :=
    fun tus tvs lus lvs c s e =>
    match e with
      | App (App f p) q =>
        match ilogicS f with
          | Some (ilf_entails t) => 
            match pq (getVars c) t q with
              | Some (q', _) => More s (GGoal (App (App f p) q'))
              | _ => More s (GGoal e)
            end
          | _ => More s (GGoal e)
        end
      | _ => More s (GGoal e)
    end.

  Definition PULL_EXISTSL_AUX (pq : list typ -> typ -> expr typ func -> option (expr typ func * rsubst (expr typ func))) : 
    rtac typ (expr typ func) :=
    fun tus tvs lus lvs c s e =>
    match e with
      | App (App f p) q =>
        match ilogicS f with
          | Some (ilf_entails t) => 
            match pq (getVars c) t p with
              | Some (p', _) => More s (GGoal (App (App f p') q))
              | _ => More s (GGoal e)
            end
          | _ => More s (GGoal e)
        end
      | _ => More s (GGoal e)
    end.

Definition PULL_EXISTSR := PULL_EXISTSR_AUX pull_quant.
Definition PULL_EXISTSL := PULL_EXISTSL_AUX pull_quant.

Lemma PULL_EXISTSR_sound : rtac_sound PULL_EXISTSR.
Proof.
  admit.
Admitted.

Lemma PULL_EXISTSL_sound : rtac_sound PULL_EXISTSL.
Proof.
  admit.
Admitted.

End PullQuant.

Implicit Arguments PULL_EXISTSR [[HIL] [HBIL] [HE] [HB] [RelDec_func] [RType_typ] [Typ2_typ] [Typ0_typ] [RSym_func]].
Implicit Arguments PULL_EXISTSL [[HIL] [HBIL] [HE] [HB] [RelDec_func] [RType_typ] [Typ2_typ] [Typ0_typ] [RSym_func]].