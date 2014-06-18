Require Import ILogic ILEmbed ILInsts Rel.
Require Import Open Stack String.

Local Existing Instance ILFun_Ops.
Local Existing Instance ILFun_ILogic.

Section VLogic.
  Context {V : ValNull}.

  Definition vlogic := @open V Prop.

  Definition open_eq {T} (a b : open T) : vlogic :=
    fun s => a s = b s.
    
  Global Instance ILOpsVLogic : ILogicOps vlogic := _.
  Global Instance ILogicVLogic : ILogic vlogic := _.
  
  Local Transparent ILFun_Ops.
 
  Lemma open_eq_reflexive {T : Type} (a b : open T) (H : forall s, a s = b s) : 
  	ltrue |-- open_eq a b.
  Proof.
  	intros s _; apply H.
  Qed.

End VLogic.

Section Existentialise.
  Context {A : Type} {Heq : DecidableEq A}.
  Context {V : ValNull}.
  Context {B : Type} `{ILB : ILogic B} {EmbOp : EmbedOp Prop B} {Emb : Embed Prop B}.
  
  Local Transparent ILFun_Ops.
  Local Transparent EmbedILFunOp.
  
  Local Existing Instance EmbedILFunOp.
  Local Existing Instance EmbedILFun.

  Lemma existentialise_var (x : string) (P : open B) : 
  	P |-- @lexists (open B) _ _ (fun v : val => @lembedand vlogic (open B) _ _ (open_eq (x/V) `v) P).
  Proof.
  	intro s; unfold liftn, lift, var_expr, open_eq; simpl. apply lexistsR with (s x). 	
  	apply landR; [apply embedPropR|]; reflexivity.
  Qed.
End Existentialise.
