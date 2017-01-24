Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.POption.

Require Import MirrorCore.Lambda.Ptrns.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.TCLemma.
Require Import MirrorCore.PLemma.
Require Import MirrorCore.Polymorphic.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.Reify.Reify.
Require Import MirrorCore.Reify.ReifyView.
Require Import MirrorCore.RTac.RTac.

Require Import MirrorCore.Lambda.RewriteRelations.
Require Import MirrorCore.Lambda.Rewrite.Respectful.
Require Import MirrorCore.Lambda.Rewrite.Core.
Require Import MirrorCore.Lambda.Rewrite.HintDbs.
Require Import MirrorCore.Lambda.Rewrite.Repeat.
Require Import MirrorCore.Lambda.Rewrite.BottomUp.
Require Import MirrorCore.Lambda.Rewrite.Reduce.
Require Import MirrorCore.Lambda.Rewrite.Rewrite.
Require Import MirrorCore.Lambda.Rewrite.Tactic.
Require Import MirrorCore.Lambda.PolyInst.

Require Import MirrorCore.CTypes.CTypeUnify.
Require Import MirrorCore.CTypes.CoreTypes.
Require Import MirrorCore.CTypes.BaseType.

Require Import ChargeCore.Logics.ILogic.
Require Import ChargeCore.Logics.BILogic.

Require Import Charge.Views.ILogicView.
Require Import Charge.Patterns.ILogicPattern.
Require Import Charge.Reify.ILogicReify.
Require Import Charge.Views.BILogicView.
Require Import Charge.Patterns.BILogicPattern.
Require Import Charge.Reify.BILogicReify.
Require Import Charge.Rewriter.ILogicRewrite.
Require Import Charge.Tactics.Rtac.PApply.

Section RewriteBILogic.
  Context {typ' : nat -> Set} {func : Set}.

  Notation typ := (ctyp typ').   
  
  Context {RType_typ : RType typ}.
  Context {RSym_func : RSym func}.
  Context {RelDec_eq_typ : RelDec (@eq typ)}.
  Context {Expr_expr : Expr typ (expr typ func)}.
  Context {Typ2_tyArr : Typ2 _ RFun}.
  Context {Typ2Ok_tyArr : Typ2Ok Typ2_tyArr}.
  Context {Typ0_tyProp : Typ0 _ Prop}.
  Context {FVIL : PartialView func (ilfunc typ)}.
  Context {FVBIL : PartialView func (bilfunc typ)}.
  Context {FV_typ : PartialView typ (base_typ 0)}.
  
  Context {bilops : @bilogic_ops typ RType_typ}.
                        
  Let tyProp : typ := @typ0 _ _ _ Typ0_tyProp.
  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ Typ2_tyArr.

  Existing Instance Reify_typ.
              
  Local Instance Reify_expr : Reify (expr typ func) :=
    Reify_func_no_table typ func 
      (reify_plogic typ func :: 
       reify_ilogic typ func :: 
       reify_bilogic typ func :: nil).

  Definition bil_ignore := 
    RApp (RExact (@BILogicOps)) RIgnore :: 
    RApp (RApp (RApp (RExact (@BILogic)) RIgnore) RIgnore) RIgnore :: 
    il_ignore.
    
  Definition lem_typ x := ptc_lem_typ typ (expr typ func) (expr typ func) x bil_ignore.
  Definition rel_lem_typ x := ptc_rel_lem_typ typ func (expr typ func) x bil_ignore.
  Definition proper_rel_lem_typ x := ptc_proper_rel_lem_typ typ func (expr typ func) x bil_ignore.
    
  Definition lem_bilexistsscL1 : rel_lem_typ 2 :=
    Eval unfold Lemma.add_var, Lemma.add_prem, Lemma.vars, Lemma.concl, 
                Lemma.premises, List.app in
      <:: @bilexistsscL1 ::>.
              
  Definition lem_bilexistsscR1 : rel_lem_typ 2 :=
    Eval unfold Lemma.add_var, Lemma.add_prem, Lemma.vars, Lemma.concl, 
                Lemma.premises, List.app in
      <:: @bilexistsscR1 ::>.
              
  Definition lem_bilexistsscL2 : rel_lem_typ 2 :=
    Eval unfold Lemma.add_var, Lemma.add_prem, Lemma.vars, Lemma.concl, 
                Lemma.premises, List.app in
      <:: @bilexistsscL2 ::>.
              
  Definition lem_bilexistsscR2 : rel_lem_typ 2 :=
    Eval unfold Lemma.add_var, Lemma.add_prem, Lemma.vars, Lemma.concl, 
                Lemma.premises, List.app in
      <:: @bilexistsscR2 ::>.
              
  Definition lem_Proper_sc : proper_rel_lem_typ 1 :=
    Eval unfold Lemma.add_var, Lemma.add_prem, Lemma.vars, Lemma.concl, 
                Lemma.premises in
    <:: @sepSP_lentails_m ::>.
  
  Definition is_bilogic1 : polymorphic typ 1 bool := 
  	fun t => 
   	  match bilops t with
      | pSome _ => true
      | _ => false
      end.
      
  Definition is_bilogic2 : polymorphic typ 2 bool := 
  	fun t _ => 
   	  match bilops t with
      | pSome _ => true
      | _ => false
      end.
      
  Definition pull_exists_lemmasL : RewriteHintDb (expr typ func) :=
    @PRw_tc _ _ _ 2 lem_bilexistsscL1 is_bilogic2 (runOnGoals IDTAC) ::
    @PRw_tc _ _ _ 2 lem_bilexistsscL2 is_bilogic2 (runOnGoals IDTAC) :: nil.

  Definition pull_exists_lemmasR : RewriteHintDb (expr typ func) :=
    @PRw_tc _ _ _ 2 lem_bilexistsscR1 is_bilogic2 (runOnGoals IDTAC) :: 
    @PRw_tc _ _ _ 2 lem_bilexistsscR1 is_bilogic2 (runOnGoals IDTAC) :: nil.

  Definition bil_proper : ProperDb (expr typ func) :=
    (@PPr_tc typ func (expr typ func) 1 (pconcl lem_Proper_sc) is_bilogic1 :: 
     @PPr_tc typ func (expr typ func) 1 (pconcl (flip_proper_rel_lem lem_Proper_sc)) is_bilogic1 ::
     nil).

End RewriteBILogic.