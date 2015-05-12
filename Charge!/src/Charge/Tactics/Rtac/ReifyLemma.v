Require Import ExtLib.Core.RelDec.

Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.TypesI.
(*
Require Import MirrorCore.Reify.Reify.
*)
Require Import Charge.ModularFunc.ILogicFunc.

Section ReifyLemma.
	Context {typ func : Type} {HIL : ILogicFunc typ func}.
	Context {RType_typ : RType typ}.
    Context {Typ0_tyProp : Typ0 RType_typ Prop}.
    Context {Heq : RelDec (@eq typ)}.

    Let tyProp : typ := @typ0 _ _ _ _.

	Fixpoint get_alls (e : expr typ func) : list typ * expr typ func :=
	  match e with
	    | App f (Abs _ e) =>
	      match ilogicS f with
	      	| Some (ilf_forall t t') => 
	      		if t' ?[ eq ] tyProp then
	      			 let (alls, e) := get_alls e in (t :: alls, e)
	      		else
	      			 (nil, e)
	      	| _ => (nil, e)
	      end
	    | _ => (nil, e)
	  end.

	Fixpoint get_impls (e : expr typ func) : list (expr typ func) * expr typ func :=
	  match e with
	    | App (App f P) Q =>
	      match ilogicS f with
	        | Some (ilf_impl t) => 
	        	if t ?[ eq ] tyProp then
	        		let (impls,e) := get_impls Q in (P :: impls,e)
	        	else
	        		(nil, e)
	        | _ => (nil, e)
	      end
	    | _ => (nil, e)
	  end.
	
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
