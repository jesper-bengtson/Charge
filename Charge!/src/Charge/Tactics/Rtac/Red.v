Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Core.RelDec.

Require Import Charge.Views.ILogicView.
Require Import Charge.Patterns.ILogicPattern.
Require Import Charge.Views.BILogicView.
Require Import Charge.Patterns.BILogicPattern.
Require Import Charge.Views.EmbedView.
Require Import Charge.Patterns.EmbedPattern.

Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.Lambda.Ptrns.
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
  Context {RSym_func : RSym func}.
  Context {T : Type -> Type} {Applicative_T : Applicative T}.

  Context {Typ1_T : Typ1 _ T}.
  Let g := @typ1 _ _ T _.


  Definition pointwise_redF (tus tvs : tenv typ)
    (f : tenv typ -> tenv typ -> typ -> expr typ func -> typ * expr typ func) :
    ptrn (expr typ func) (typ * expr typ func)  :=
    Eval compute in 
      por (bil_pointwise_red (f tus tvs) g) 
          (por (embed_pointwise_red (f tus tvs) g) 
               (por (red_ap_ptrn (f tus tvs))
                    (il_pointwise_red tus tvs f g))).
          
  Fixpoint pointwise_red_aux 
      (s : expr typ func) 
      (tus tvs : tenv typ) (t : typ) (e : expr typ func) {struct e} : 
        typ * expr typ func :=
    let f := pointwise_red_aux s in
    run_ptrn (pointwise_redF tus tvs f)
             (t, App e (lift 0 (length tvs) s)) e.

  Definition pointwise_red (t : typ) (s e : expr typ func) := 
    pointwise_red_aux s nil nil t e.

  Definition red_entails_lhs (g : typ -> typ) :=
    pmap (fun t' => let '(t, (p, s), r) := t' in 
    		 mkEntails t (snd (pointwise_red t s p)) r)
         (ptrnEntails get (Ptrns.app get get) get).

  Definition RED_ENTAILS (g : typ -> typ) : rtac typ (expr typ func) :=
    fun c s e =>
      run_ptrn (pmap (fun e' => More s (GGoal e')) (red_entails_lhs g)) Fail e.
      
  Lemma RED_ENTAILS_sound : rtac_sound (RED_ENTAILS g).
  Proof.
    admit.
  Admitted.

  Definition pointwise_restoreF (tus tvs : tenv typ) (s : expr typ func) (t : typ) 
    (f : tenv typ -> tenv typ -> typ -> expr typ func -> typ * expr typ func) : 
    ptrn (expr typ func) (typ * expr typ func)  :=
    Eval compute in 
      por (bil_pointwise_red (f tus tvs) g) 
          (por (embed_pointwise_red (f tus tvs) g)                
               (il_pointwise_red tus tvs f g)).
SearchAbout RelDec ctyp.                         

  Fixpoint pointwise_restore_aux 
      (s : expr typ func) 
      (g : typ -> typ) 
      (tus tvs : tenv typ) (t : typ) (e : expr typ func) {struct e} : 
        typ * expr typ func :=
    let f := pointwise_restore_aux s g in
    let default := run_ptrn (por (restore_ap_ptrn tus tvs s (f tus tvs t)) (restore_pure_ptrn tus tvs)) (t, e) e in
    run_ptrn (pointwise_restoreF tus tvs s t f)
             default e.

  Definition pointwise_restore (t : typ) (s e : expr typ func) := 
    pointwise_restore_aux s g nil nil t e.

  Definition restore_entails_lhs (s : expr typ func) :=
    pmap (fun t' => let '(t, p, r) := t' in 
    		 mkEntails t (snd (pointwise_restore t s p)) r)
         (ptrnEntails get get get).

  Definition RESTORE_ENTAILS (s : expr typ func) : rtac typ (expr typ func) :=
    fun c s' e =>
      run_ptrn (pmap (fun e' => More s' (GGoal e')) (restore_entails_lhs s)) Fail e.
  
  Lemma RESTORE_ENTAILS_sound (s : expr typ func) : rtac_sound (RESTORE_ENTAILS s). 
  Proof.
    admit.
  Admitted.


End Red.