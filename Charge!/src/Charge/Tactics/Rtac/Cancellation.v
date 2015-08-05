Require Import ExtLib.Core.RelDec.

Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.Lambda.ExprSubst.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require Import MirrorCore.Lambda.ExprVariables.
Require MirrorCore.syms.SymEnv.
Require MirrorCore.syms.SymSum.
Require Import MirrorCore.VariablesI.
Require Import Charge.Tactics.OrderedCanceller.
Require Import Charge.Tactics.BILNormalize.
Require Import Charge.Tactics.SynSepLog.
Require Import Charge.Tactics.SepLogFoldWithAnd.
Require Import Charge.Tactics.Views.ILogicView.
Require Import Charge.Tactics.Views.BILogicView.

Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.Lambda.Ptrns.

Set Implicit Arguments.
Set Strict Implicit.

Section Canceller.
  Context (typ func subst : Type) (tyLogic : typ).
  Context {FVIL : FuncView func (ilfunc typ)}.
  Context {FVBIL : FuncView func (bilfunc typ)}.
  Context {RType_typ : RType typ} {RelDec_typ : RelDec (@eq typ)}.
  Context {Typ2_typ : Typ2 RType_typ Fun}.
  Context {RSym_func : @RSym _ RType_typ func}.
  Existing Instance Expr_expr.
  Context {SS : Subst subst (expr typ func)}.
  Context {SU : SubstUpdate subst (expr typ func)}.
  Context {SO : SubstOk SS}.

  Context {uis_pure : expr typ func -> bool}.

  Definition sls : SepLogAndSpec typ func :=
  {| is_pure e := run_default
                    (pmap (fun _ => true)
                          (inj (ptrn_view _ (por (fptrnTrue ignore) (fptrnFalse ignore)))))
                    (uis_pure e) e
   ; is_emp := fun e =>
                 run_default (pmap (fun _ => true)
                                   (inj (ptrn_view _ (fptrnEmp ignore)))) false e
   ; is_star := run_default
                  (pmap (fun _ => true) (inj (ptrn_view _ (fptrnStar ignore))))
                  false
   ; is_and := run_default
                 (pmap (fun _ => true) (inj (ptrn_view _ (fptrnAnd ignore))))
                 false
   |}.

  Let doUnifySepLog c (tus tvs : EnvI.tenv typ)
      (s : ctx_subst (typ := typ) (expr := expr typ func) c)
      (e1 e2 : expr typ func)
  : option (ctx_subst c) :=
    @exprUnify (ctx_subst c) typ func RType_typ RSym_func Typ2_typ _ _ 10 tus tvs 0 e1 e2 tyLogic s.

  Let ssl : SynSepLog typ func :=
  {| e_star := fun l r =>
                 let lt := sls.(is_emp) l in
                 let rt := sls.(is_emp) r in
                 match lt, rt with
                 | true, true => mkEmp tyLogic
                 | true, false => r
                 | false, true => l
                 | false, false => mkStar tyLogic l r
                 end
   ; e_emp := mkEmp tyLogic
   ; e_and := fun l r =>
                let lt := run_tptrn 
                            (pdefault 
                               (inj (ptrn_view _ (pmap (fun _ => true) (fptrnTrue ignore))))
                               false) l in
                let rt := run_tptrn
                            (pdefault 
                               (inj (ptrn_view _ (pmap (fun _ => true) (fptrnTrue ignore))))
                               false) r in
                match lt, rt with
                | true, true => mkTrue tyLogic
                | true, false => r
                | false, true => l
                | false, false => mkAnd tyLogic l r
                end
   ; e_true := mkTrue tyLogic
   |}.

  Definition eproveTrue c (s : ctx_subst (typ := typ) (expr := expr typ func) c) : 
    expr typ func -> option (ctx_subst c) :=
    run_tptrn
      (pdefault
         (inj (ptrn_view _ (pmap (fun _ => Some s) (fptrnTrue ignore))))
         None).

  Definition is_solved (e1 e2 : conjunctives typ func) : bool :=
    match e1 , e2 with
      | {| spatial := e1s ; star_true := t ; pure := _ |}
        , {| spatial := nil ; star_true := t' ; pure := nil |} =>
        if t' then
          (** ... |- true **)
          true
        else
          (** ... |- emp **)
          if t then false else match e1s with
                                 | nil => true
                                 | _ => false
                               end
      | _ , _ => false
    end.

  Definition the_canceller tus tvs (lhs rhs : expr typ func) c
             (s : ctx_subst c)
  : (expr typ func * expr typ func * (ctx_subst c)) + (ctx_subst c) :=
    match @normalize_and typ _ _ func _ ssl sls tus tvs tyLogic lhs
        , @normalize_and typ _ _ func _ ssl sls tus tvs tyLogic rhs
    with
      | Some lhs_norm , Some rhs_norm =>
        match lhs_norm tt , rhs_norm tt with
          | Some lhs_norm , Some rhs_norm =>
            let '(lhs',rhs',s') :=
                OrderedCanceller.ordered_cancel (subst := ctx_subst c)
                  (doUnifySepLog (c := c) tus tvs) (eproveTrue (c := c))
                  ssl
                  (simple_order (func:=func)) lhs_norm rhs_norm s
            in
            if is_solved lhs' rhs' then
              inr s'
            else
              inl (conjunctives_to_expr ssl lhs',
                   conjunctives_to_expr ssl rhs',
                   s')
          | _ , _ => inl (lhs, rhs, s)
        end
      | _ , _ => inl (lhs, rhs, s)
    end.

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.

  Definition CANCELLATION : rtac typ (expr typ func) :=
    fun tus tvs nus nvs c s e =>
      run_tptrn
        (pdefault
           (pmap (fun t_a_b => 
                    let '(t, a, b) := t_a_b in
                    match t ?[ eq ] tyLogic with
                    | true =>
                      match the_canceller tus tvs a b s with
                      | inl (l, r, s') => 
                        run_tptrn
                          (pdefault
                             (pmap (fun _ => Solved s') (ptrnEmp get))
                             (More s' (GGoal (mkEntails tyLogic l r)))) r
                      | inr s' => Solved s'
                      end
                    | false => More s (GGoal e)
                    end)
                 (ptrnEntails get get get))
           (More s (GGoal e))) e.
(*      
      
Definition the_canceller2 tus tvs (lhs rhs : expr typ func) :=
    match @normalize_and typ _ _ func _ ssl sls tus tvs tyLogic lhs
        , @normalize_and typ _ _ func _ ssl sls tus tvs tyLogic rhs
    with
      | Some lhs_norm , Some rhs_norm =>
        match lhs_norm tt , rhs_norm tt with
          | Some lhs_norm , Some rhs_norm =>
            Some (simple_order (func := func) lhs_norm,
                  simple_order (func := func) rhs_norm)
          | _ , _ => None
        end
      | _ , _ => None
    end.

  Definition CANCELLATION2 tus tvs e :=
      match e with
        | App (App f L) R =>
          match ilogicS f with
	    | Some (ilf_entails t) =>
	      match t ?[ eq ] tyLogic with
	     	| true => the_canceller2 tus tvs L R
		    | false => None
	      end
	    | _ => None
	  end
        | _ => None
      end.
*)
End Canceller.

Implicit Arguments CANCELLATION [[FVIL] [FVBIL] [RType_typ] [RelDec_typ]
                                [Typ2_typ] [RSym_func]].
