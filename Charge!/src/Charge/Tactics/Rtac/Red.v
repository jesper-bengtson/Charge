Require Import Charge.Views.ILogicView.
Require Import Charge.Patterns.ILogicPattern.
Require Import Charge.Views.BILogicView.
Require Import Charge.Patterns.BILogicPattern.
Require Import Charge.Views.EmbedView.
Require Import Charge.Patterns.EmbedPattern.

Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.CTypes.CoreTypes.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.Lib.ApplicativeView.
Require Import MirrorCore.RTac.RTac.

Section Red.
  Context {typ' : nat -> Set} {func : Set}.
  Context {TSym_typ' : TSym typ'}.
  Let typ := ctyp typ'.
  Local Instance RType_typ : RType typ := RType_ctyp typ' _.
  Local Instance Typ2_typ : Typ2 RType_typ RFun := Typ2_Fun.
  Local Instance Typ0_Prop : Typ0 RType_typ Prop := Typ0_Prop _ _.
  Context {FVIL : PartialView func (ilfunc typ)}.
  Context {FVBIL : PartialView func (bilfunc typ)}.
  Context {FVEmbed : PartialView func (embed_func typ)}.
  Context {FVAp : PartialView func (ap_func typ)}.
  Context {Expr_expr : Expr typ (expr typ func)}.

  Definition pointwise_redF (f : typ -> expr typ func -> expr typ func) : 
    ptrn (expr typ func) (expr typ func)  :=
    Eval compute in 
      por (bil_pointwise_red f (fun x => x)) 
          (por (embed_pointwise_red f (fun x => x)) 
               (por (red_ap_ptrn f)
                    (il_pointwise_red f (fun x => x)))).

  Fixpoint pointwise_red_aux (s : expr typ func) (t : typ) (e : expr typ func) {struct e} : expr typ func :=
    run_ptrn (pointwise_redF (pointwise_red_aux s)) (App e s) e.

  Definition pointwise_red (s e : expr typ func) := pointwise_red_aux s tyProp e.

  Definition red_entails_lhs :=
    pmap (fun t' => let '(t, (p, s), r) := t' in 
    		 mkEntails t (pointwise_red s p) r)
         (ptrnEntails get (Ptrns.app get get) get).

  Definition RED_ENTAILS : rtac typ (expr typ func) :=
    fun c s e =>
      run_ptrn (pmap (fun e => More s (GGoal e)) red_entails_lhs) Fail e.
      
  Lemma RED_ENTAILS_sound : rtac_sound RED_ENTAILS.
  Proof.
    admit.
  Admitted.

End Red.