Require Import ExtLib.Core.RelDec.

Require Import MirrorCore.Lambda.Ptrns.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.TCLemma.
Require Import MirrorCore.PLemma.
Require Import MirrorCore.Polymorphic.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.Reify.Reify.
Require Import MirrorCore.Reify.ReifyView.

Require Import MirrorCore.Lambda.RewriteRelations.
Require Import MirrorCore.Lambda.Rewrite.Respectful.
Require Import MirrorCore.Lambda.Rewrite.Core.
Require Import MirrorCore.Lambda.Rewrite.HintDbs.
Require Import MirrorCore.Lambda.PolyInst.

Require Import MirrorCore.CTypes.CTypeUnify.
Require Import MirrorCore.CTypes.CoreTypes.
Require Import MirrorCore.CTypes.BaseType.

Require Import ChargeCore.Logics.ILogic.

Require Import Charge.Views.ILogicView.
Require Import Charge.Patterns.ILogicPattern.
Require Import Charge.Reify.ILogicReify.

Section IgnoreILogic.

  Definition reify_ILogicOps : RPattern :=
    RApp (RExact (@ILogicOps)) RIgnore.
  
  Definition reify_ILogic : RPattern  :=
    RApp (RApp (RExact (@ILogic)) RIgnore) RIgnore.
 
End IgnoreILogic.

Section RewriteILogic.
  Context {typ' : nat -> Set} {func : Set}.

  Notation typ := (ctyp typ').   
  
  Context {RType_typ : RType typ}.
  Context {RSym_func : RSym func}.
  Context {RelDec_eq_typ : RelDec (@eq typ)}.
  Context {RelDec_eq_func : RelDec (@eq func)}.
  Context {Expr_expr : Expr typ (expr typ func)}.
  Context {Typ2_tyArr : Typ2 _ RFun}.
  Context {Typ2Ok_tyArr : Typ2Ok Typ2_tyArr}.
  Context {Typ0_tyProp : Typ0 _ Prop}.
  Context {FV : PartialView func (ilfunc typ)}.
  Context {FV_typ : PartialView typ (base_typ 0)}.
      
  Let tyProp : typ := @typ0 _ _ _ Typ0_tyProp.
  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ Typ2_tyArr.
(* 
  Definition RbaseD (e : expr typ func) (t : typ) : option (TypesI.typD t -> TypesI.typD t -> Prop) :=
    castD option (RFun (typD t) (RFun (typD t) Prop)) (env_exprD nil nil (tyArr t (tyArr t tyProp)) e).


  Theorem RbaseD_single_type
  : forall (r : expr typ func) (t1 t2 : typ)
           (rD1 : TypesI.typD t1 -> TypesI.typD t1 -> Prop)
           (rD2 : TypesI.typD t2 -> TypesI.typD t2 -> Prop),
      RbaseD r t1 = Some rD1 -> RbaseD r t2 = Some rD2 -> t1 = t2.
  Proof.
    unfold RbaseD, env_exprD, castD. simpl; intros.
    unfold eq_sym in *. simpl in *.
    
    generalize (lambda_exprD_deterministic _ _ _ H0 H). unfold Rty.
    intros. inversion H3. reflexivity.
  Qed.  
 
 
  Fixpoint from_terms (rs : list (expr typ func) : refl_dec Rbase :=
    match rs with
    | nil => fun _ => false
    | r :: rs => fun r' =>
      if expr_eq_dec _ _ r r' then true else from_terms rs r'
    end.
*)
 
  Definition is_refl : refl_dec (expr typ func) :=
   	run_ptrn
      (pmap (fun _ => true) (inj (ptrn_view _ (fptrnEntails ignore))))
      false.
    
  Definition is_trans : trans_dec (expr typ func) :=
   	run_ptrn 
      (pmap (fun _ => true) (inj (ptrn_view _ (fptrnEntails ignore))))
      false.
    
  Local Instance Reify_typ : Reify typ :=
    Reify_typ typ (reify_base_typ typ :: nil).

  Local Instance Reify_expr : Reify (expr typ func) :=
    Reify_func_no_table typ func (reify_plogic typ func :: reify_ilogic typ func :: nil).

  Definition lem_typ x := 
    polymorphic typ x 
      (tc_lemma typ (expr typ func) 
         (rw_concl typ func (expr typ func))
         (RApp (RExact (@ILogicOps)) RIgnore :: 
          RApp (RApp (RExact (@ILogic)) RIgnore) RIgnore :: 
          nil)).  

  Definition proper_lem_typ x := 
    polymorphic typ x
      (tc_lemma typ (expr typ func)
        (Proper_concl typ func (expr typ func))
         (RApp (RExact (@ILogicOps)) RIgnore :: 
          RApp (RApp (RExact (@ILogic)) RIgnore) RIgnore :: 
          nil)).  
                      
  Definition lem_landexistsDL : lem_typ 2 :=
    Eval unfold Lemma.add_var, Lemma.add_prem , Lemma.vars , Lemma.concl , Lemma.premises, List.app in
      <:: @landexistsDL ::>.
              
  Definition lem_landexistsDR : lem_typ 2 :=
    Eval unfold Lemma.add_var, Lemma.add_prem , Lemma.vars , Lemma.concl , Lemma.premises, List.app in
      <:: @landexistsDR ::>.
                            
  Definition lem_lorexistsDR : lem_typ 2 :=
    Eval unfold Lemma.add_var, Lemma.add_prem , Lemma.vars , Lemma.concl , Lemma.premises, List.app in
      <:: @landexistsDR ::>.
              
  Definition lem_Proper_exists : proper_lem_typ 2 :=
    Eval unfold Lemma.add_var, Lemma.add_prem , Lemma.vars , Lemma.concl , Lemma.premises in
    <:: @lexists_lentails_m ::>.

  Definition lem_Proper_forall : proper_lem_typ 2 :=
    Eval unfold Lemma.add_var, Lemma.add_prem , Lemma.vars , Lemma.concl , Lemma.premises in
    <:: @lforall_lentails_m ::>.

  Definition lem_Proper_and : proper_lem_typ 1 :=
    Eval unfold Lemma.add_var, Lemma.add_prem , Lemma.vars , Lemma.concl , Lemma.premises in
    <:: @land_lentails_m ::>.

  Definition lem_Proper_or : proper_lem_typ 1 :=
    Eval unfold Lemma.add_var, Lemma.add_prem , Lemma.vars , Lemma.concl , Lemma.premises in
    <:: @lor_lentails_m ::>.

  Definition lem_Proper_impl : proper_lem_typ 1 :=
    Eval unfold Lemma.add_var, Lemma.add_prem , Lemma.vars , Lemma.concl , Lemma.premises in
    <:: @limpl_lentails_m ::>.

  Fixpoint polymorphic_map {A B : Set} {x : nat} (f : A -> B) : polymorphic typ x A -> polymorphic typ x B :=
    match x with
    | 0 => fun a => f a
    | S x => fun a x => polymorphic_map f (a x)
    end.

Arguments concl {_ _ _} _.

  Definition lentails_respectful : ResolveProper typ func (expr typ func) :=
    do_prespectful (Rbase := expr typ func) rel_dec tyVar (type_sym_unifier (CTypeUnify.ctype_unify_slow _))
      (@PPr typ func (expr typ func) 2 (polymorphic_map concl lem_Proper_exists) ::
       @PPr typ func (expr typ func) 2 (polymorphic_map concl lem_Proper_forall) ::
       @PPr typ func (expr typ func) 1 (polymorphic_map concl lem_Proper_and) ::
       @PPr typ func (expr typ func) 1 (polymorphic_map concl lem_Proper_or) ::
       @PPr typ func (expr typ func) 1 (polymorphic_map concl lem_Proper_impl) ::
       nil).

  Definition lem_entails_refl : lem_typ 1 :=
    Eval unfold Lemma.add_var, Lemma.add_prem, Lemma.vars, Lemma.concl, Lemma.premises, List.app in
      <:: @lentails_refl ::>.

  Definition the_lemmas : RewriteHintDb (expr typ func) :=
    @PRw _ _ _ 1 lem_pull_ex_and_left DO_REFL ::
    @PRw _ _ _ 1 lem_pull_ex_and_right DO_REFL ::

Check (or_respectful lentails_respectful lentails_respectful).
End RewriteILogic.