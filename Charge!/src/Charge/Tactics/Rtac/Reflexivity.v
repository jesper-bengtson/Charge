Require Import MirrorCore.SymI.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.RTac.Core.

Require Import ExtLib.Tactics.
Require Import ExtLib.Data.HList.

Section Reflexivity.
(*
  Context {typ func : Set} {RType_typ : RType typ} {RSym_func : RSym (expr typ func)}.
  Context {BF : BaseFunc typ func}.
  
  Context {Expr_func : Expr RType_typ (expr typ func)}.
  Context {EU : ExprUVar (expr typ func)}.
  
  Context {edt : eq_dec_typ typ}.

  Context {Typ0_Prop : Typ0 RType_typ Prop}.

  Let tyProp : typ := @typ0 _ _ _ _.

  Definition REFLEXIVITY : rtac typ (expr typ func) :=
    fun tus tvs nus nvs c s e =>
      match e with
        | App (App f e1) e2 =>
          match baseS f with
            | Some (pEq t) =>
              match sym_eqb e1 e2 with
                | Some true => Solved s
                | _ =>
                  match exprD' nil nil e1 t, exprD' nil nil e2 t with
                    | Some e1D, Some e2D =>
                      match edt t (e1D Hnil Hnil) (e2D Hnil Hnil) with
                        | Some true => Solved s
                        | _ => Fail
                      end
                    | _, _ => Fail
                  end
              end
            | _ => Fail
          end 
		| _ => Fail
      end.

  Lemma REFLEXIVITY_sound : rtac_sound REFLEXIVITY.
  Proof.
    intros ctx s g res.
  	unfold REFLEXIVITY.
    destruct g; intros; subst; try apply I.
    destruct g1; try apply I.
    destruct g1_1; try apply I.
    remember (baseS (Inj f)).
	destruct o; [|apply I].
    destruct b; try apply I.
    remember (sym_eqb g1_2 g2).
    
	
   admit.
Qed.
*)
End Reflexivity.
