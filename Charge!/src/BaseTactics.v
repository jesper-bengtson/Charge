Require Import ILogic ILEmbed.
Require Import Maps MapInterface MapFacts.
	 
Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Inductive Tlist : Type := 
| Tnil  : Tlist 
| Tcons : Type -> Tlist -> Tlist.

Fixpoint Tappend (Ts Us : Tlist) :=
  match Ts with
    | Tnil       => Us
    | Tcons T Ts => Tcons T (Tappend Ts Us)
  end.

Fixpoint Tappend_assoc (Ts Us Rs : Tlist) :
  Tappend (Tappend Ts Us) Rs = Tappend Ts (Tappend Us Rs) :=
  match Ts with
    | Tnil => eq_refl
    | Tcons T Ts => f_equal (Tcons T) (Tappend_assoc Ts Us Rs)
  end.

Fixpoint arrows (Ts : Tlist) (R : Type) :=
  match Ts with
    | Tnil => R
    | Tcons T Ts => T -> (arrows Ts R)
  end.

Definition arrows_assoc {Ts Us Rs : Tlist} {R : Type} :
           arrows (Tappend (Tappend Ts Us) Rs) R = arrows (Tappend Ts (Tappend Us Rs)) R :=
  eq_ind_r
    (fun t : Tlist => arrows t R = arrows (Tappend Ts (Tappend Us Rs)) R)
  eq_refl (Tappend_assoc Ts Us Rs).

Fixpoint arrows_const {R : Type} (Ts : Tlist) (r : R) : arrows Ts R :=
  match Ts with
    | Tnil       => r
    | Tcons T Ts => fun x => arrows_const Ts r
  end.
 
Fixpoint arrows_append_r {Ts R} (Us : Tlist) : arrows Ts R -> arrows (Tappend Ts Us) R :=
  match Ts with
    | Tnil       => fun f   => arrows_const Us f
    | Tcons T Ts => fun f x => arrows_append_r Us (f x)
  end.

Fixpoint arrows_append_l {Us R} (Ts : Tlist) (a : arrows Us R) : arrows (Tappend Ts Us) R :=
  match Ts with
    | Tnil       => a
    | Tcons T Ts => fun _ => arrows_append_l Ts a
  end.

Fixpoint arrows_splice_r {Ts Rs C} Us :
  arrows (Tappend Ts Rs) C -> arrows (Tappend (Tappend Ts Us) Rs) C :=
  match Ts with
    | Tnil       => fun f => arrows_append_l Us f
    | Tcons T Ts => fun f x => arrows_splice_r Us (f x)
  end. 

Fixpoint arrows_cons_splice {Ts Rs C} R :
  arrows (Tappend Ts Rs) C -> arrows (Tappend Ts (Tcons R Rs)) C :=
  match Ts with
    | Tnil       => fun f x => f
    | Tcons T Ts => fun f x => arrows_cons_splice R (f x)
  end.

Fixpoint arrows_splice_l {Us Rs C} Ts :
  arrows (Tappend Us Rs) C -> arrows (Tappend (Tappend Ts Us) Rs) C :=
  match Ts with
    | Tnil       => fun h => h
    | Tcons T Ts => fun h x => arrows_splice_l Ts h
  end.

Fixpoint arrows_unop {A B} {Ts : Tlist} (op : A -> B) :
  arrows Ts A -> arrows Ts B :=
  match Ts with
    | Tnil       => fun f => op f
    | Tcons T Ts => fun f x => arrows_unop op (f x)
  end.

Fixpoint arrows_binop {A B C} (op : A -> B -> C) (Ts : Tlist) :
  arrows Ts A -> arrows Ts B -> arrows Ts C :=
  match Ts with
    | Tnil       => fun f g => op f g
    | Tcons T Ts => fun f g x => arrows_binop op (f x) (g x)
  end.
  
Fixpoint arrows_unop_merge {A B} {Ts Us : Tlist} (op : arrows Us A -> arrows Us B) :
  arrows (Tappend Ts Us) A -> arrows (Tappend Ts Us) B :=
  match Ts with
    | Tnil       => fun f => op f
    | Tcons T Ts => fun f x => arrows_unop_merge op (f x) 
  end.

Fixpoint arrows_binop_merge {A B C} (op : A -> B -> C) (Ts Us : Tlist) :
	arrows Ts A -> arrows Us B -> arrows (Tappend Ts Us) C :=
	match Ts with
		| Tnil       => fun f g => arrows_unop (op f) g
		| Tcons T Ts => fun f g x => arrows_binop_merge op (f x) g
	end.

Implicit Arguments arrows_binop [[A] [B] [C]].

Fixpoint arrows_rel_close {A Ts} (R : relation A) : relation (arrows Ts A) :=
  match Ts with
    | Tnil       => fun a b => R a b
    | Tcons T Ts => fun a b => forall t, arrows_rel_close R (a t) (b t)
  end.

Fixpoint arrows_quant {T : Type} {f : nat -> Type} {x : nat} (Ts : Tlist) 
           (quant : (T -> f x) -> f x) : 
  arrows (Tcons T Ts) (f x) -> arrows Ts (f x) :=
  match Ts with
    | Tnil       => fun f => quant f
    | Tcons U Ts => fun f u => arrows_quant quant (fun t => f t u)
  end.

Fixpoint Tcast {T : Type} (f : T -> Type) (Ts : list T) :=
  match Ts with
    | nil     => Tnil
    | T :: Ts => Tcons (f T) (Tcast f Ts)
  end.

Inductive deep_op {A : Type} {ILA : ILogicOps A} :=
| t_atom     : A -> deep_op
| t_true     : deep_op
| t_false    : deep_op
| t_and      : deep_op -> deep_op -> deep_op
| t_or       : deep_op -> deep_op -> deep_op
| t_impl     : deep_op -> deep_op -> deep_op
| t_unop     : nat -> deep_op -> deep_op
| t_binop    : nat -> deep_op -> deep_op -> deep_op
| t_exists T : (T -> A) -> deep_op
| t_forall T : (T -> A) -> deep_op
| t_and_inj (B : Type) `(ILB : ILogic B) (EmbBOp : EmbedOp B A) (EmbB : Embed B A) 
			(EmbOp : EmbedOp Prop B) (Emb : Embed Prop B) :
    @deep_op B _ -> deep_op -> deep_op
| t_impl_inj (B : Type) `(ILB : ILogic B) (EmbBOp : EmbedOp B A) (EmbB : Embed B A)
	 		 (EmbOp : EmbedOp Prop B) (Emb : Embed Prop B) :
    @deep_op B _-> deep_op -> deep_op
| t_and_prop (EmbOp : EmbedOp Prop A) (Emb : Embed Prop A) : 
	@deep_op Prop _ -> deep_op -> deep_op
| t_impl_prop (EmbOp : EmbedOp Prop A) (Emb : Embed Prop A) : 
	@deep_op Prop _ -> deep_op -> deep_op.

Definition unop_option {A B} (f : A -> B) (a : option A) :=
	match a with	
		| Some p => Some (f p)
		| None => None
	end.

Definition binop_option {A B C} (f : A -> B -> C) (a : option A) (b : option B) :=
  match a, b with
    | Some p, Some q => Some (f p q)
    | _, _ => None
  end.

Definition env_unops (A : Type)   := Map [nat, A -> A]. 
Definition env_binops  (A : Type) := Map [nat, A -> A -> A].
Definition env (A : Type) := ((env_unops A) * (env_binops A))%type.

Definition env_empty (A : Type) : env A := 
	(@empty nat _ _ (A -> A), @empty nat _ _ (A -> A -> A)).
	
Definition env_add_unop {A : Type} (e : env A) (n : nat) (f : A -> A) : env A := 
	((fst e) [n <- f], snd e).
	
Definition env_add_binop {A : Type} (e : env A) (n : nat) (f : A -> A -> A) : env A := 
	(fst e, (snd e) [n <- f]).
	
Fixpoint deep_op_eval (A : Type) {ILA : ILogicOps A} (env : env A) (e : deep_op) : option A := 
  match e with
    | t_atom p => Some p
    | t_true => Some ltrue
    | t_false => Some lfalse
    | t_and p q => binop_option land (deep_op_eval env p) (deep_op_eval env q)
    | t_or p q => binop_option lor (deep_op_eval env p) (deep_op_eval env q)
    | t_impl p q => binop_option limpl (deep_op_eval env p) (deep_op_eval env q)
    | t_exists T f => Some (lexists f)
    | t_forall T f => Some (lforall f)
    | t_and_inj B _ _ _ _ _ _ p q => binop_option lembedand (deep_op_eval (env_empty B) p) (deep_op_eval env q)
    | t_impl_inj B _ _ _ _ _ _ p q => binop_option lembedimpl (deep_op_eval (env_empty B) p) (deep_op_eval env q)
    | t_and_prop _ _ p q => binop_option lembedand (deep_op_eval (env_empty Prop) p) (deep_op_eval env q)
    | t_impl_prop _ _ p q => binop_option lembedimpl (deep_op_eval (env_empty Prop) p) (deep_op_eval env q)
    | t_unop n p => match (fst env) [n] with
    				  | Some f => unop_option f (deep_op_eval env p)
    				  | None => None
    				end
    | t_binop n p q => match (snd env) [n] with
    				     | Some f => binop_option f (deep_op_eval env p) (deep_op_eval env q)
    				     | None => None
    				   end
  end.

Ltac quote_term P :=
  match P with
    | ltrue => constr:(t_true)
    | lfalse => constr:(t_false)
    | ?P1 //\\ ?P2 =>
      let t1 := quote_term P1 in
      let t2 := quote_term P2 in
      constr:(t_and t1 t2)
    | ?P1 \\// ?P2 =>
      let t1 := quote_term P1 in
      let t2 := quote_term P2 in
      constr:(t_or t1 t2)
    | ?P1 -->> ?P2 => 
      let t1 := quote_term P1 in
      let t2 := quote_term P2 in
      constr:(t_impl t1 t2)
    | lexists ?f => constr:(t_exists f)
    | lforall ?f => constr:(t_forall f)
    | ?P1 /\\ ?P2 => 
      let t1 := quote_term P1 in
      let t2 := quote_term P2 in
      constr:(t_and_prop _ t1 t2)
    | ?P1 ->> ?P2 => 
      let t1 := quote_term P1 in
      let t2 := quote_term P2 in
      constr:(t_impl_prop _ t1 t2)
    | ?P1 /\\ ?P2 => 
      let t1 := quote_term P1 in
      let t2 := quote_term P2 in
      constr:(t_and_inj _ _ _ t1 t2)
    | ?P1 ->> ?P2 => 
      let t1 := quote_term P1 in
      let t2 := quote_term P2 in
      constr:(t_impl_inj _ _ _ t1 t2)
    | _ => constr:(t_atom P)
  end. 


Definition unop_sound_lr (A B : Type) {ILA : ILogicOps A} (de_env : env A) (tac_env : env B) 
       (tac_eval : B -> A) := forall f n, (fst tac_env) [n] = Some f ->
       exists g, (fst de_env) [n] = Some g /\ Proper (lentails ==> lentails) g /\
	             forall a, tac_eval (f a) |-- g (tac_eval a).
  
Definition binop_sound_lr (A B : Type) {ILA : ILogicOps A} (de_env : env A) (tac_env : env B) 
       (tac_eval : B -> A) := forall f n, (snd tac_env) [n] = Some f -> 
       exists g, (snd de_env) [n] = Some g /\ Proper (lentails ==> lentails ==> lentails) g /\
	             forall a b, tac_eval (f a b) |-- g (tac_eval a) (tac_eval b).
	             
Definition env_sound_lr (A B : Type) {ILA : ILogicOps A} (de_env : env A) (tac_env : env B)
                        (tac_eval : B -> A) :=
	(unop_sound_lr de_env tac_env tac_eval) /\
	(binop_sound_lr de_env tac_env tac_eval).
	
	
Lemma env_sound_lr_empty {A B : Type} {ILA : ILogicOps A} (de_env : env A) (tac_eval : B -> A) :
	env_sound_lr de_env (env_empty B) tac_eval.
Proof.
	split; intros n f H; simpl in H; rewrite empty_o in H; inversion H.
Qed.		

Lemma env_sound_lr_add_unop_tac {A B : Type} {ILA : ILogicOps A} (e1 : env A) (e2 : env B) (n : nat) (eval : B -> A) (f : B -> B) 
	(H : env_sound_lr e1 e2 eval) (Hg : exists g : A -> A, (fst e1) [n] = Some g /\ (forall a, eval (f a) |-- g (eval a)) /\
	Proper (lentails ==> lentails) g) : env_sound_lr e1 (env_add_unop e2 n f) eval.
Proof.
	destruct Hg as [g [Hn [Heval Hprop]]].
	split; [|apply H].
	intros h m Hm; unfold env_add_unop in Hm; simpl in Hm.
	rewrite add_o in Hm; destruct (eq_dec n m).
	+ inversion Hm; subst.
	  exists g. intuition. rewrite <- H0. assumption.
	+ apply H. apply Hm.
Qed.

Lemma env_sound_lr_add_unop {A B : Type} {ILA : ILogicOps A} (e1 : env A) (e2 : env B) (n : nat) (eval : B -> A) (f : A -> A) 
	    				    (H : env_sound_lr e1 e2 eval) (Hn : (fst e2) [n] = None) :
env_sound_lr (env_add_unop e1 n f) e2 eval. 
Proof.
	split; [|apply H].
	intros g m Hm.
	destruct (eq_dec n m).
	+ rewrite H0 in Hn. rewrite Hn in Hm. inversion Hm.
	+ destruct H as [H _]. specialize (H g m Hm).
	  destruct H as [h [H1 [H2 H3]]].
	  exists h; intuition.
	  unfold env_add_unop. simpl. rewrite add_neq_o; assumption.
Qed.
		
Lemma env_sound_lr_add_binop_tac {A B : Type} {ILA : ILogicOps A} (e1 : env A) (e2 : env B) (n : nat) (eval : B -> A) (f : B -> B -> B) 
	(H : env_sound_lr e1 e2 eval) (Hg : exists g : A -> A -> A, (snd e1) [n] = Some g /\ (forall a b, eval (f a b) |-- g (eval a) (eval b)) /\
	Proper (lentails ==> lentails ==> lentails) g) : env_sound_lr e1 (env_add_binop e2 n f) eval.
Proof.
	destruct Hg as [g [Hn [Heval Hprop]]].
	split; [apply H|].
	intros h m Hm; unfold env_add_unop in Hm; simpl in Hm.
	rewrite add_o in Hm; destruct (eq_dec n m).
	+ inversion Hm; subst.
	  exists g. intuition. rewrite <- H0. assumption.
	+ apply H. apply Hm.
Qed.

Lemma env_sound_lr_add_binop {A B : Type} {ILA : ILogicOps A} (e1 : env A) (e2 : env B) (n : nat) (eval : B -> A) (f : A -> A -> A) 
	    				    (H : env_sound_lr e1 e2 eval) (Hn : (snd e2) [n] = None) :
env_sound_lr (env_add_binop e1 n f) e2 eval. 
Proof.
	split; [apply H|].
	intros g m Hm.
	destruct (eq_dec n m).
	+ rewrite H0 in Hn. rewrite Hn in Hm. inversion Hm.
	+ destruct H as [_ H]. specialize (H g m Hm).
	  destruct H as [h [H1 [H2 H3]]].
	  exists h; intuition.
	  unfold env_add_unop. simpl. rewrite add_neq_o; assumption.
Qed.
		

		
Definition unop_sound_rl (A B : Type) {ILA : ILogicOps A} (de_env : env A) (tac_env : env B) 
       (tac_eval : B -> A) := forall f n, (fst tac_env) [n] = Some f ->
       exists g, (fst de_env) [n] = Some g /\ Proper (lentails ==> lentails) g /\ 
	             forall a, g (tac_eval a) |-- tac_eval (f a).
  
Definition binop_sound_rl (A B : Type) {ILA : ILogicOps A} (de_env : env A) (tac_env : env B) 
       (tac_eval : B -> A) := forall f n, (snd tac_env) [n] = Some f -> 
       exists g, (snd de_env) [n] = Some g /\ Proper (lentails ==> lentails ==> lentails) g /\
	             forall a b, g (tac_eval a) (tac_eval b) |-- tac_eval (f a b).
	             
Definition env_sound_rl (A B : Type) {ILA : ILogicOps A} (de_env : env A) (tac_env : env B)
                        (tac_eval : B -> A) :=
	(unop_sound_rl de_env tac_env tac_eval) /\
	(binop_sound_rl de_env tac_env tac_eval).
	
Lemma env_sound_rl_empty {A B : Type} {ILA : ILogicOps A} (de_env : env A) (tac_eval : B -> A) :
	env_sound_rl de_env (env_empty B) tac_eval.
Proof.
	split; intros n f H; simpl in H; rewrite empty_o in H; inversion H.
Qed.		
	
Lemma env_sound_rl_add_unop_tac {A B : Type} {ILA : ILogicOps A} (e1 : env A) (e2 : env B) (n : nat) (eval : B -> A) (f : B -> B) 
	(H : env_sound_rl e1 e2 eval) (Hg : exists g : A -> A, (fst e1) [n] = Some g /\ (forall a,  g (eval a) |-- eval (f a)) /\
	Proper (lentails ==> lentails) g) : env_sound_rl e1 (env_add_unop e2 n f) eval.
Proof.
	destruct Hg as [g [Hn [Heval Hprop]]].
	split; [|apply H].
	intros h m Hm; unfold env_add_unop in Hm; simpl in Hm.
	rewrite add_o in Hm; destruct (eq_dec n m).
	+ inversion Hm; subst.
	  exists g. intuition. rewrite <- H0. assumption.
	+ apply H. apply Hm.
Qed.

Lemma env_sound_rl_add_unop {A B : Type} {ILA : ILogicOps A} (e1 : env A) (e2 : env B) (n : nat) (eval : B -> A) (f : A -> A) 
	    				    (H : env_sound_rl e1 e2 eval) (Hn : (fst e2) [n] = None) :
env_sound_rl (env_add_unop e1 n f) e2 eval. 
Proof.
	split; [|apply H].
	intros g m Hm.
	destruct (eq_dec n m).
	+ rewrite H0 in Hn. rewrite Hn in Hm. inversion Hm.
	+ destruct H as [H _]. specialize (H g m Hm).
	  destruct H as [h [H1 [H2 H3]]].
	  exists h; intuition.
	  unfold env_add_unop. simpl. rewrite add_neq_o; assumption.
Qed.
		
Lemma env_sound_rl_add_binop_tac {A B : Type} {ILA : ILogicOps A} (e1 : env A) (e2 : env B) (n : nat) (eval : B -> A) (f : B -> B -> B) 
	(H : env_sound_rl e1 e2 eval) (Hg : exists g : A -> A -> A, (snd e1) [n] = Some g /\ (forall a b, g (eval a) (eval b) |-- eval (f a b)) /\
	Proper (lentails ==> lentails ==> lentails) g) : env_sound_rl e1 (env_add_binop e2 n f) eval.
Proof.
	destruct Hg as [g [Hn [Heval Hprop]]].
	split; [apply H|].
	intros h m Hm; unfold env_add_unop in Hm; simpl in Hm.
	rewrite add_o in Hm; destruct (eq_dec n m).
	+ inversion Hm; subst.
	  exists g. intuition. rewrite <- H0. assumption.
	+ apply H. apply Hm.
Qed.

Lemma env_sound_rl_add_binop {A B : Type} {ILA : ILogicOps A} (e1 : env A) (e2 : env B) (n : nat) (eval : B -> A) (f : A -> A -> A) 
	    				    (H : env_sound_rl e1 e2 eval) (Hn : (snd e2) [n] = None) :
env_sound_rl (env_add_binop e1 n f) e2 eval. 
Proof.
	split; [apply H|].
	intros g m Hm.
	destruct (eq_dec n m).
	+ rewrite H0 in Hn. rewrite Hn in Hm. inversion Hm.
	+ destruct H as [_ H]. specialize (H g m Hm).
	  destruct H as [h [H1 [H2 H3]]].
	  exists h; intuition.
	  unfold env_add_unop. simpl. rewrite add_neq_o; assumption.
Qed.