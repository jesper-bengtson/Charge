Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.POption.

Require Import MirrorCore.Lambda.Ptrns.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.PLemma.
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

Require Import Charge.Views.ILogicView.
Require Import Charge.Patterns.ILogicPattern.
Require Import Charge.Reify.ILogicReify.
Require Import Charge.Tactics.Rtac.PApply.

Section RewriteILogic.
  Context {typ' : nat -> Set} {func : Set}.

  Notation typ := (ctyp typ').   
  
  Context {RType_typ : RType typ}.
  Context {RSym_func : RSym func}.
  Context {RelDec_eq_typ : RelDec (@eq typ)}.
  Context {Expr_expr : Expr typ (expr typ func)}.
  Context {Typ2_tyArr : Typ2 _ RFun}.
  Context {Typ2Ok_tyArr : Typ2Ok Typ2_tyArr}.
  Context {Typ0_tyProp : Typ0 _ Prop}.
  Context {FV : PartialView func (ilfunc typ)}.
  Context {FV_typ : PartialView typ (base_typ 0)}.
  
  Context {ilops : @logic_ops typ RType_typ}.
  Context (unify_func : PolyInst.sym_unifier (typ := typ) (sym := func)).
                        
  Let tyProp : typ := @typ0 _ _ _ Typ0_tyProp.
  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ Typ2_tyArr.

  Definition is_refl : refl_dec (expr typ func) :=
   	run_ptrn
      (pmap (fun _ => true) 
        (inj (por (ptrn_view _ (fptrnEntails ignore))
                  (ptrn_view _ (fptrnImpl ignore)))))
      false.
    
  Definition is_trans : trans_dec (expr typ func) :=
   	run_ptrn 
      (pmap (fun _ => true) 
        (inj (por (ptrn_view _ (fptrnEntails ignore))
                  (ptrn_view _ (fptrnImpl ignore)))))
      false.
    
  Local Instance Reify_typ : Reify typ :=
    Reify_typ typ (reify_base_typ typ :: nil).

  Local Instance Reify_expr : Reify (expr typ func) :=
    Reify_func_no_table typ func (reify_plogic typ func :: reify_ilogic typ func :: nil).
                
  Definition il_ignore := 
    RApp (RExact (@ILogicOps)) RIgnore :: 
    RApp (RApp (RExact (@ILogic)) RIgnore) RIgnore :: 
    nil.
    
  Definition lem_typ x := ptc_lem_typ typ (expr typ func) (expr typ func) x il_ignore.
  Definition rel_lem_typ x := ptc_rel_lem_typ typ func (expr typ func) x il_ignore.
  Definition proper_rel_lem_typ x := ptc_proper_rel_lem_typ typ func (expr typ func) x il_ignore.
  
  Definition flip_rw_concl (c : rw_concl typ func (expr typ func)) :=
    Build_rw_concl (lhs c) (Rflip'' (rel c)) (rhs c). 
                  
  Definition flip_Proper_concl (c : Proper_concl typ func (expr typ func)) :=
    mkProper (Rflip'' (relation c)) (term c). 
                  
  Definition flip_rel_lem {x : nat} (l : rel_lem_typ x) : rel_lem_typ x :=
    fmap_polymorphic (fun x => mkLemma (vars x) (premises x) (flip_rw_concl (concl x))) l.
  
  Definition flip_proper_rel_lem {x : nat} (l : proper_rel_lem_typ x) : proper_rel_lem_typ x :=
    fmap_polymorphic (fun x => mkLemma (vars x) (premises x) (flip_Proper_concl (concl x))) l.
  
  Definition lem_landexistsDL1 : rel_lem_typ 2 :=
    Eval unfold Lemma.add_var, Lemma.add_prem, Lemma.vars, Lemma.concl, 
                Lemma.premises, List.app in
      <:: @landexistsDL1 ::>.
              
  Definition lem_landexistsDR1 : rel_lem_typ 2 :=
    Eval unfold Lemma.add_var, Lemma.add_prem, Lemma.vars, Lemma.concl, 
                Lemma.premises, List.app in
      <:: @landexistsDR1 ::>.
                            
  Definition lem_landexistsDL2 : rel_lem_typ 2 :=
    Eval unfold Lemma.add_var, Lemma.add_prem, Lemma.vars, Lemma.concl, 
                Lemma.premises, List.app in
      <:: @landexistsDL2 ::>.
              
  Definition lem_landexistsDR2 : rel_lem_typ 2 :=
    Eval unfold Lemma.add_var, Lemma.add_prem, Lemma.vars, Lemma.concl, 
                Lemma.premises, List.app in
      <:: @landexistsDR2 ::>.
                            
  Definition lem_lorexistsDR : rel_lem_typ 2 :=
    Eval unfold Lemma.add_var, Lemma.add_prem, Lemma.vars, Lemma.concl, 
                Lemma.premises, List.app in
      <:: @lorexistsDR ::>.
              
  Definition lem_Proper_exists : proper_rel_lem_typ 2 :=
    Eval unfold Lemma.add_var, Lemma.add_prem, Lemma.vars, Lemma.concl, 
                Lemma.premises, function in
    <:: @lexists_lentails_m ::>.

  Definition lem_Proper_forall : proper_rel_lem_typ 2 :=
    Eval unfold Lemma.add_var, Lemma.add_prem , Lemma.vars , Lemma.concl , 
                Lemma.premises, function in
    <:: @lforall_lentails_m ::>.

  Definition lem_Proper_and : proper_rel_lem_typ 1 :=
    Eval unfold Lemma.add_var, Lemma.add_prem, Lemma.vars, Lemma.concl, 
                Lemma.premises in
    <:: @land_lentails_m ::>.

  Definition lem_Proper_or : proper_rel_lem_typ 1 :=
    Eval unfold Lemma.add_var, Lemma.add_prem, Lemma.vars, Lemma.concl, 
                Lemma.premises in
    <:: @lor_lentails_m ::>.

  Definition lem_Proper_impl : proper_rel_lem_typ 1 :=
    Eval unfold Lemma.add_var, Lemma.add_prem, Lemma.vars, Lemma.concl, 
                Lemma.premises in
    <:: @limpl_lentails_m ::>.

  Definition lem_Proper_entails : proper_rel_lem_typ 1 :=
    Eval unfold Lemma.add_var, Lemma.add_prem, Lemma.vars, Lemma.concl, 
                Lemma.premises, function in
    <:: @lentails_lentails_m ::>.
  
  Definition lem_entails_refl : lem_typ 1 :=
    Eval unfold Lemma.add_var, Lemma.add_prem, Lemma.vars, Lemma.concl, 
         Lemma.premises, List.app, function in
      <:: @lentails_refl ::>.

  Definition is_ilogic1 : polymorphic typ 1 bool := 
  	fun t => 
   	  match ilops t with
      | pSome _ => true
      | _ => false
      end.
      
  Definition is_ilogic2 : polymorphic typ 2 bool := 
  	fun t _ => 
   	  match ilops t with
      | pSome _ => true
      | _ => false
      end.
      
  Definition plem_entails_refl : PolyLemma typ (expr typ func) (expr typ func) :=
    {| p_n := 1;
       p_lem := lem_entails_refl;
       p_tc := is_ilogic1 |}.

  Definition DO_REFL :=
    (runOnGoals (THEN (TRY INSTANTIATE) (runOnGoals (TRY (PAPPLY unify_func plem_entails_refl))))).

  Definition pull_exists_lemmasL : RewriteHintDb (expr typ func) :=
    @PRw_tc _ _ _ 2 lem_landexistsDL1 is_ilogic2 (runOnGoals IDTAC) ::
    @PRw_tc _ _ _ 2 lem_landexistsDL2 is_ilogic2 (runOnGoals IDTAC) :: nil.

  Definition pull_exists_lemmasR : RewriteHintDb (expr typ func) :=
    @PRw_tc _ _ _ 2 lem_landexistsDR1 is_ilogic2 (runOnGoals IDTAC) :: 
    @PRw_tc _ _ _ 2 lem_landexistsDR2 is_ilogic2 (runOnGoals IDTAC) :: 
    @PRw_tc _ _ _ 2 lem_lorexistsDR is_ilogic2 (runOnGoals IDTAC) :: nil.

  Definition get_respectful (pdb : ProperDb (expr typ func)) : 
    ResolveProper typ func (expr typ func) :=
    do_prespectful expr_eqb tyVar unify_func
      (@PPr_tc typ func (expr typ func) 2 (pconcl lem_Proper_exists) is_ilogic2 ::
       @PPr_tc typ func (expr typ func) 2 (pconcl (flip_proper_rel_lem lem_Proper_exists)) is_ilogic2 ::
       @PPr_tc typ func (expr typ func) 1 (pconcl lem_Proper_entails) is_ilogic1 :: 
       @PPr_tc typ func (expr typ func) 1 (pconcl (flip_proper_rel_lem lem_Proper_entails)) is_ilogic1 :: 
       @PPr_tc typ func (expr typ func) 1 (pconcl lem_Proper_or) is_ilogic1 :: 
       @PPr_tc typ func (expr typ func) 1 (pconcl (flip_proper_rel_lem lem_Proper_or)) is_ilogic1 :: 
       @PPr_tc typ func (expr typ func) 1 (pconcl lem_Proper_impl) is_ilogic1 :: 
       @PPr_tc typ func (expr typ func) 1 (pconcl (flip_proper_rel_lem lem_Proper_impl)) is_ilogic1 :: 
       @PPr_tc typ func (expr typ func) 1 (pconcl lem_Proper_and) is_ilogic1 ::
       @PPr_tc typ func (expr typ func) 1 (pconcl (flip_proper_rel_lem lem_Proper_and)) is_ilogic1 :: pdb).

  Definition simple_reduce (e : expr typ func) : expr typ func :=
    run_ptrn
      (pmap (fun abcd => let '(a,(b,(c,d),e)) := abcd in
                         App a (Abs c (App (App b d) e)))
            (app get (abs get (fun t =>
                                 app (app get
                                          (pmap (fun x => (t,Red.beta x)) get))
                                     (pmap Red.beta get)))))
    e e.
    
  Definition rw_lemmas (lems : RewriteHintDb (expr typ func)) : 
    RwAction typ func (expr typ func) :=
    rw_post_simplify simple_reduce (rw_simplify Red.beta (using_prewrite_db expr_eqb (CompileHints unify_func lems))).
  
  Definition rw_action
  	(rdb : RewriteHintDb (expr typ func)) 
  	(rp : ResolveProper typ func (expr typ func)) : RwAction typ func (expr typ func) :=
    repeat_rewrite (fun e r =>
                      bottom_up (is_reflR is_refl) (is_transR is_trans) (rw_lemmas rdb) 
                                 rp e r)
                   (is_reflR is_refl) (is_transR is_trans) false 300.

  Definition REWRITE 
  	(rdb : RewriteHintDb (expr typ func)) 
  	(pdb : ProperDb (expr typ func)) : rtac typ (expr typ func) :=
    let rp := get_respectful pdb in
    let rw := rw_action rdb rp in
        @auto_setoid_rewrite_bu typ func (expr typ func)
                            (Rflip (Rinj (Inj (fImpl tyProp))))
                            (is_reflR is_refl) (is_transR is_trans) rw rp.

End RewriteILogic.