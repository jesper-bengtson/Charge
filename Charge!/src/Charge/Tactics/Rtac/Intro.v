Require Import ExtLib.Core.RelDec.

Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.Red.
Require Import MirrorCore.TypesI.

Require Import Charge.ModularFunc.ILogicFunc.

Section IntroTac.
	Context {typ func subst : Type}.
	Context {HIL : ILogicFunc typ func}.
	Context {RType_typ : RType typ}.
    Context {Typ0_tyProp : Typ0 RType_typ Prop}.
    Context {Heq : RelDec (@eq typ)}.
    Context {EV : ExprVar (expr typ func)}.
    Context {EU : ExprUVar (expr typ func)}.

    Let tyProp : typ := @typ0 _ _ _ _.

	Definition fintro e : option (@OpenAs typ (expr typ func)) :=
		match e with
			| App (Inj f) P =>
				match ilogicS f with
				  | Some (ilf_forall t t') => 
				  	if t' ?[ eq ] tyProp then 
				  		Some (AsAl t (fun x => beta (App P x)))
				  	else
				  		None
				  | Some (ilf_exists t t') => 
				  	if t' ?[ eq ] tyProp then 
				  		Some (AsEx t (fun x => beta (App P x)))
				  	else
				  		None
				  | _ => None
				end
			| App (App (Inj f) P) Q =>
				match ilogicS f with
				  | Some (ilf_impl t') => 
				  	if t' ?[ eq ] tyProp then 
				  		Some (AsHy P Q)
				  	else
				  		None
(*				  | Some (ilf_entails t) =>
				    match Q with
				      | App (Inj g) Q' =>
				        match ilogicS g with
				          | Some (ilf_exists t' t'') => 
				            Some (AsEx t' (fun x => mkEntails t (lift 0 1 P) (beta (App Q' x))))
				          | _ => None
				        end
				      | _ => None
				    end*)
				  | _ => None
				end
			| _ => None
		end.

	Definition INTRO := @INTRO typ (expr typ func) EV EU fintro.

End IntroTac.

Implicit Arguments INTRO [[HIL] [RType_typ] [Typ0_tyProp] [Heq] [EU] [EV]].