Require Import Setoid Morphisms RelationClasses Program.Basics Omega.
Require Import BILogic BaseTactics.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Section BIEnv.
	Context {A : Type} `{ILA : BILogic A}.
	
	Definition bi_env : env A := env_add_binop (env_empty A) 1 sepSP.
	
End BIEnv.

Ltac quote_term P :=
	match P with
		| ?P ** ?Q => let t1 := quote_term P in 
		              let t2 := quote_term Q in
		               	constr:(t_binop 1 t1 t2)
		| _        => BaseTactics.quote_term_aux quote_term P
	end.
