Require Import Setoid Morphisms RelationClasses Program.Basics Omega.
Require Import Later BaseTactics.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Section LaterEnv.
	Context {A : Type} `{ILA : ILLater A}.
	
	Definition later_env : env A := env_add_unop (env_empty A) 0 illater.
	
End LaterEnv.

Ltac quote_term P :=
	match P with
		| |>?P => let t := quote_term P in constr:(t_unop 0 t)
		| _    => BaseTactics.quote_term_aux quote_term P
	end.
