Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.ExprD.
Require Import MirrorCore.Lambda.Red.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.ExprI.

Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Tactics.
Require Import MirrorCore.syms.SymSum.

Require Import Charge.SetoidRewrite.AutoSetoidRewrite.
Require Import Charge.ModularFunc.BaseFunc.

Set Implicit Arguments.
Set Strict Implicit.

Section SetoidRewrite.
  Context {typ func : Type} {RType_typ : RType typ}.
  Context {HB : BaseFunc typ func}.

  Context {RelDec_typ_eq : RelDec (@eq typ)}
          {RelDecCorrect_typ_eq : RelDec_Correct RelDec_typ_eq}.

  Context {RelDec_func_eq : RelDec (@eq (expr typ func))}.

  Let Rbase := expr typ func.

  Definition m (T : Type) : Type :=
    rsubst Rbase -> option (T * rsubst Rbase).

  Definition rewriter :=
    expr typ func ->
    list (AutoSetoidRewrite.RG Rbase) ->
    AutoSetoidRewrite.RG Rbase -> m (expr typ func).
    
  Definition rw_type :=
    expr typ func -> list (RG Rbase) -> RG Rbase -> m (expr typ func).

  Definition rw_under (r : RG Rbase) (rw : rw_type) : rw_type :=
    fun e rvars => rw e (r :: rvars).

  Definition rg_bind {T U} (a : m T) (b : T -> m U) : m U :=
    fun s => match a s with
               | None => None
               | Some (val,s') => b val s'
             end.
             
  Definition rg_fail {T} : m T := fun _ => None.
  Definition rg_ret {T} (v : T) : m T := fun s => Some (v, s).
  Definition rg_plus {T} (l r : m T) : m T :=
    fun s =>
      let v := l s in
      match v with
        | None => r s
        | Some _ => v
      end.
  Definition rg_fmap {T U} (f : T -> U) (l : m T) : m U :=
    fun s =>
      match l s with
        | None => None
        | Some (x,y) => Some (f x, y)
      end.

  Section do_several.
    Variable (rw : rewriter).

    Fixpoint do_several (n : nat) a b c {struct n} :=
      match n with
        | 0 => rg_ret a
        | S n => fun d => match rw a b c d with
                            | None => rg_ret a d
                            | Some (a',d') => do_several n a' b c d'
                          end
      end.
  End do_several.

  Section do_severalK.
    Variable (rw : rewriter -> rewriter).

    Fixpoint do_severalK  (n : nat) (rw' : rewriter)
             (a : expr typ func) (b : list (AutoSetoidRewrite.RG Rbase))
             (c :  AutoSetoidRewrite.RG Rbase) {struct n} :=
      match n with
        | 0 => rg_ret a
        | S n => fun d =>
                   AutoSetoidRewrite.tryRewrite
                     (rw (fun a b c d => do_severalK n rw' a b c d))
                     a b c d
      end.
  End do_severalK.

  Definition rw_fail : rewriter := fun _ _ _ => rg_fail.

  Definition sr_combine (f g : expr typ func -> list (RG (expr typ func)) -> RG (expr typ func) -> m (expr typ func))
    (e : (expr typ func)) (rvars : list (RG (expr typ func))) (rg : RG (expr typ func)) :
  	m (expr typ func) :=
    rg_plus (f e rvars rg) (g e rvars rg).

  Definition sr_combineK (f g : rw_type -> rw_type)
             (k : rw_type)
             (e : (expr typ func)) (rvars : list (AutoSetoidRewrite.RG (expr typ func))) (rg : AutoSetoidRewrite.RG (expr typ func)) :
    m (expr typ func) :=
    rg_plus (f k e rvars rg) (g k e rvars rg).

  Definition setoid_rewrite vars := 
  fun (RelDec_func_eq : RelDec.RelDec eq) =>
  let Rbase := expr typ func in
  fun (rel : typ -> Rbase)
    (rewrite_start : rewriter)
    (rewrite_respects : rewriter)
    (rewrite_exs : rewriter -> rewriter)
    (l : typ) (e : expr typ func) =>
    (AutoSetoidRewrite.setoid_rewrite
       RelDec.rel_dec
       rewrite_start
       rewrite_respects
       (do_severalK rewrite_exs 1024 (fun a _ _ => rg_ret a)))
      e (map (fun t => RGinj (Inj (fEq t))) vars) (AutoSetoidRewrite.RGinj (rel l))
      (AutoSetoidRewrite.rsubst_empty Rbase).

End SetoidRewrite.