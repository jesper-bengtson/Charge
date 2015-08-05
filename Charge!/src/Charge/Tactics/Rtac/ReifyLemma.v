Require Import ExtLib.Core.RelDec.

Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.Ptrns.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.Reify.Reify.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.Views.FuncView.

Require Import Charge.Tactics.Views.ILogicView.

Section ReifyLemma.
  Context {typ func : Type} {HIL : FuncView func (ilfunc typ)}.
  Context {RType_typ : RType typ}.
  Context {Typ0_tyProp : Typ0 RType_typ Prop}.
  Context {Heq : RelDec (@eq typ)}.
  
  Let tyProp : typ := @typ0 _ _ _ _.

  Fixpoint get_alls (e : expr typ func) : list typ * expr typ func :=
    run_tptrn
      (pdefault
         (pmap (fun t_t'_p =>
               let '(t, t', p) := t_t'_p in 
               if t' ?[ eq ] tyProp then 
                 let (alls, e) := get_alls p in (t::alls, e) 
               else
                 (nil, e))
               (ptrnForall get (abs get (fun _ => get))))
         (nil, e)) e.

  Fixpoint get_impls (e : expr typ func) : list (expr typ func) * expr typ func :=
    run_tptrn
      (pdefault
         (pmap (fun t_p_q =>
               let '(t, p, q) := t_p_q in 
               if t ?[ eq ] tyProp then 
                 let (impls, e) := get_impls q in (p::impls, e) 
               else
                 (nil, e))
               (ptrnImpl get get get))
         (nil, e)) e.

  Definition convert_to_lemma (e : expr typ func)
    : lemma typ (expr typ func) (expr typ func) :=
    let (alls, e) := get_alls e in
    let (impls, e) := get_impls e in
	  {| vars := rev alls
	     ; premises := impls
	     ; concl := e |}.
  
End ReifyLemma.

Ltac reify_lemma_aux reify T :=
  let k e := 
    let e := constr:(convert_to_lemma e) in
    let e := eval unfold convert_to_lemma in e in 
  let e := eval simpl in e in
                          refine e
                        in
                          reify_expr reify k [ True ] [ T ].

Ltac reify_lemma reify e :=
  let T := type of e in reify_lemma_aux reify T.
