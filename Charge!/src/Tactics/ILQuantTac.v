Add Rec LoadPath "/Users/jebe/coq/user-contrib".
Add Rec LoadPath "/Users/jebe/git/Charge/Charge!/bin".

Require Import Maps MapInterface MapFacts.
Require Import BaseTactics ILogic ILEmbed.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.
  
  Record find_res (A : Type) := mkf {
    find_types : Tlist;
    find_closure : arrows find_types A
  }.
		
	Definition find_res_unop {A B : Type} (op : A -> B) (a : option (find_res A)) :
  	option (find_res B) :=
  	match a with
  		| Some a => Some (mkf (arrows_unop op (find_closure a)))
  		| None => None
  	end.
  
  Definition find_res_binop {A B C : Type} (op : A -> B -> C) (a : option (find_res A)) 
  	(b: option (find_res B)) : option (find_res C) :=
  	match a, b with
  	  | Some a, Some b => Some (mkf (arrows_binop_merge op (find_closure a) (find_closure b)))
  	  | _,      _      => None
  	end.
  	
  	Definition find_res_create {A : Type} (a : option A) : option (find_res A) :=
  	match a with
  		| Some a => Some (@mkf A Tnil a)
  		| None   => None
  	end.
  	
	Definition find_res_bind {A T : Type} {H : Inhabited T} (f : T -> A) :=
	@mkf A (Tcons T Tnil) f.
 
 
 	Fixpoint find_res_eval_exists_aux {A : Type} {ILA : ILogicOps A} (Ts : Tlist) 
		: arrows Ts A -> A :=
		match Ts with
		  | Tnil => fun p => p
		  | Tcons T Ts => fun p => Exists x : T, find_res_eval_exists_aux (p x)
	    end.
	
	Polymorphic Definition find_res_eval_exists {A : Type} {ILA : ILogicOps A} (p : find_res A) :=
		find_res_eval_exists_aux (find_closure p).
 
Polymorphic Fixpoint pull_exists_r {A : Type} {ILA : ILogicOps A}
(t : @deep_op A ILA) (de_env : env A) (tac_env : env (find_res A)) : option (find_res A) :=
match t with
	| t_and t1 t2   => find_res_binop land (pull_exists_r t1 de_env tac_env) (pull_exists_r t2 de_env tac_env)
	| t_or  t1 t2   => find_res_binop lor (pull_exists_r t1 de_env tac_env) (pull_exists_r t2 de_env tac_env)
	| t_exists T f  => Some (@mkf A (Tcons T Tnil) f)
	| t_and_inj B _ _ _ _ _ _ a b => find_res_binop lembedand (pull_exists_r a (env_empty B) (env_empty (find_res B)))
	                         (pull_exists_r b de_env tac_env)
	| t_and_prop _ _ a b => find_res_binop lembedand (pull_exists_r a (env_empty Prop) (env_empty (find_res Prop)))
	                         (pull_exists_r b de_env tac_env)
    | t_unop n p => 
    	match ((fst tac_env) [n]) with
    		| Some f => unop_option f (pull_exists_r p de_env tac_env)
    		| None => None
    	end
	| t_binop n p q =>
		match ((snd tac_env) [n]) with
			| Some f => binop_option f (pull_exists_r p de_env tac_env) (pull_exists_r q de_env tac_env)
			| None => None
		end
    | _ => match deep_op_eval de_env t with
    	     | Some t => Some (@mkf A Tnil t)
    	     | None   => None
    	   end
end.

Section PullExistsRight.  
   
	Lemma find_res_unop_sound_er {Ts : Tlist} {A B : Type} {ILA : ILogicOps A} `{ILB : ILogic B} 
	        (f : arrows Ts A) (op : A -> B) 
	        (Hop : forall T (f : T -> A), Exists x, op (f x) |-- op (Exists x, f x)) :
	      find_res_eval_exists_aux(arrows_unop op f) |-- op (find_res_eval_exists_aux f).
	Proof.
		induction Ts.
		simpl. reflexivity.
		simpl in *. rewrite <- Hop. 
		apply lexistsL; intro x. apply lexistsR with x.
		rewrite IHTs; firstorder. 
	Qed.
  	
 
 Lemma find_res_binop_sound_er {Ts Us : Tlist} {A B C : Type} {ILA : ILogicOps A} {ILB : ILogicOps B} `{ILC : ILogic C}
        (f : arrows Ts A) (g : arrows Us B) (op : A -> B -> C) 
        (Hop1 : forall T (f : T -> A) g, Exists x, op (f x) g |-- op (Exists x, f x) g)
        (Hop2 : forall T f (g : T -> B), Exists x, op f (g x) |-- op f (Exists x, g x)) :
      find_res_eval_exists_aux (arrows_binop_merge op f g) |-- op (find_res_eval_exists_aux f) (find_res_eval_exists_aux g).
Proof.
	induction Ts; simpl in *.
	+ apply find_res_unop_sound_er. 
	  intros. apply Hop2.
	+ rewrite <- Hop1. 
      apply lexistsL; intro x; apply lexistsR with x.
	  rewrite <- IHTs; try tauto; reflexivity. 
Qed.
 
  Lemma binop_sound_er {A B C : Type} {ILA : ILogicOps A} {ILB : ILogicOps B} `{ILC : ILogic C} 
                        (de_env1 : env A) (tac_env1 : env (find_res A))
                       (de_env2 : env B) (tac_env2 : env (find_res B))
                       (p : @deep_op A ILA) (q : @deep_op B ILB) (op : A -> B -> C) 
                       {H : Proper (lentails ==> lentails ==> lentails) op} 
      (Hp : match deep_op_eval de_env1 p, pull_exists_r p de_env1 tac_env1 with
	    | None, None => True
	    | Some p, Some q => @lentails A ILA (find_res_eval_exists q) p
	    | _, _ => True
	  end) 
(*      (Hq : match deep_op_eval de_env2 q, pull_exists_r q de_env2 tac_env2 with
	    | None, None => True
	    | Some p, Some q => find_res_eval_exists q |-- p
	    | _, _ => True
	  end) *)
        (Hop1 : forall T (f : T -> A) g, Exists x, op (f x) g |-- op (Exists x, f x) g)
        (Hop2 : forall T f (g : T -> B), Exists x, op f (g x) |-- op f (Exists x, g x)) :
match binop_option op (deep_op_eval de_env1 p) (deep_op_eval de_env2 q), 
      find_res_binop op (pull_exists_r p de_env1 tac_env1) (pull_exists_r q de_env2 tac_env2) with
  | None, None     => True
  | Some p, Some q => find_res_eval_exists q |-- p
  | _, _           => True
end.
Proof.
	remember (deep_op_eval de_env1 p) as o1.
	remember (deep_op_eval de_env2 q) as o2.
	remember (pull_exists_r p de_env1 tac_env1) as o3.
	remember (pull_exists_r q de_env2 tac_env2) as o4.
	destruct o1, o2, o3, o4; simpl in *; try intuition congruence.
	etransitivity; [|apply H; [apply Hp | apply Hq]].
	destruct f; destruct f0.
	apply find_res_binop_sound_er; assumption.
Qed.


  	Lemma env_sound_aux_er {A : Type} `{ILA : ILogic A}
  	(de_env : env A) (tac_env : env (find_res A))
    (t : @deep_op A _) (H : env_sound_lr de_env tac_env find_res_eval_exists) :
    match deep_op_eval de_env t, pull_exists_r t de_env tac_env with
      | None, None     => True
      | Some p, Some q => find_res_eval_exists q |-- p
      | _, _           => True
    end.
    Proof.
    	induction t.
    	+ simpl; reflexivity.
    	+ simpl; reflexivity.
    	+ simpl; reflexivity.   
        + apply binop_sound_er; [apply IHt1; assumption | apply IHt2; assumption | |]. 
          intros. apply landexistsDR.
          intros. rewrite landC, <- landexistsDR. setoid_rewrite landC at 1. reflexivity.
        + apply binop_sound_er; [apply IHt1; assumption | apply IHt2; assumption | |].
          intros. apply lorexistsDR. 
          intros. rewrite lorC, <- lorexistsDR. setoid_rewrite lorC at 1; reflexivity.
        + simpl; remember (deep_op_eval de_env t1) as o1.
	      remember (deep_op_eval de_env t2) as o2.
	      destruct o1, o2; simpl; (try intuition congruence); reflexivity.
        + simpl.
          specialize (IHt ILA de_env tac_env H).
          remember (fst de_env) [n] as o1.
          remember (fst tac_env) [n] as o2.
          remember (deep_op_eval de_env t) as o3.
          remember (pull_exists_r t de_env tac_env) as o4.
          destruct o1, o2, o3, o4; simpl in *; try intuition congruence.
          symmetry in Heqo2;
          destruct H as [H _]; specialize (H f n Heqo2); destruct H as [g [H3 [H4 H5]]];
          rewrite <- Heqo1 in H3; inversion H3; subst.
          rewrite H5. apply H4. apply IHt.
        + simpl. 
          specialize (IHt1 ILA de_env tac_env H); specialize (IHt2 ILA de_env tac_env H).
          remember (snd de_env) [n] as o1.
          remember (snd tac_env) [n] as o2.
          remember (deep_op_eval de_env t1) as o3.
          remember (deep_op_eval de_env t2) as o4.
          remember (pull_exists_r t1 de_env tac_env) as o5.
          remember (pull_exists_r t2 de_env tac_env) as o6.
          destruct o1, o2, o3, o4, o5, o6; simpl in *; try intuition congruence.
          symmetry in Heqo2;
          destruct H as [_ H]; specialize (H f n Heqo2); destruct H as [g [H3 [H4 H5]]];
          rewrite <- Heqo1 in H3; inversion H3; subst.
          rewrite H5. apply H4; [apply IHt1 | apply IHt2].
	    + simpl. reflexivity.
        + simpl. reflexivity.
        + apply binop_sound_er.
          apply IHt1. assumption. apply env_sound_lr_empty.
          apply IHt2. assumption. assumption.
          intros. unfold lembedand. rewrite <- embedlexists, landexistsDR. reflexivity.
          intros. unfold lembedand. rewrite landC, <- landexistsDR. setoid_rewrite landC at 1. reflexivity.
        + simpl. remember (deep_op_eval (env_empty B) t1) as o1.
          remember (deep_op_eval de_env t2) as o2.
          destruct o1, o2; simpl; (try intuition congruence); reflexivity.
        + apply binop_sound_er.
          apply IHt1. apply _. apply env_sound_lr_empty.
          apply IHt2; assumption.
          intros. unfold lembedand. rewrite <- embedlexists, landexistsDR. reflexivity.
          intros. unfold lembedand. rewrite landC, <- landexistsDR. setoid_rewrite landC at 1. reflexivity.
        + simpl. remember (deep_op_eval (env_empty Prop) t1) as o1.
          remember (deep_op_eval de_env t2) as o2.
          destruct o1, o2; simpl; (try intuition congruence); reflexivity.
    Qed.

    Implicit Arguments env_sound_aux_er [[A] [ILOps] [ILA]].
    
  	Lemma env_sound_er {A : Type} `{ILA : ILogic A}
  		               (de_env : env A) (tac_env : env (find_res A))
    (t : @deep_op A _) (H : env_sound_lr de_env tac_env find_res_eval_exists) (P : A) :
    match deep_op_eval de_env t, pull_exists_r t de_env tac_env with
      | None, None     => True
      | Some p, Some q => P |-- find_res_eval_exists q -> P |-- p
      | _, _           => True
    end.
    Proof.
    	pose proof (env_sound_aux_er de_env tac_env t H).
    	remember (deep_op_eval de_env t) as o1.
    	remember (pull_exists_r t de_env tac_env) as o2.
    	destruct o1, o2; simpl in *; try intuition congruence.
    	intros. rewrite <- H0; assumption.
    Qed.

End PullExistsRight.

Implicit Arguments env_sound_er [[A] [ILOps] [ILA]].
  
Ltac lexistsR_aux :=
  match goal with
    | |- ?P |-- ?Q =>
      let A := type of Q in 
      let t := quote_term Q in 
       apply (env_sound_er (env_empty A) (env_empty (find_res A)) t (env_sound_lr_empty (env_empty A) find_res_eval_exists) P);
        simpl; cbv [find_res_eval_exists find_res_eval_exists_aux]; simpl
    | |- _ => fail 1 "Goal is not an entailment"
  end.
  
Ltac lexistsR2 := 
	repeat (
		repeat (
			let x := fresh "x" in 
			simple eapply lexistsR
		); 
  		lexistsR_aux
  	).
 
Tactic Notation "lexistsR" := lexistsR2.
Tactic Notation "lexistsR" constr(x1) :=
	first [simple apply lexistsR with x1 | lexistsR_aux; simple apply lexistsR with x1].
Tactic Notation "lexistsR" constr(x1) constr(x2) :=
	first [simple apply lexistsR with x1 | lexistsR_aux; simple apply lexistsR with x1]; lexistsR x2.
Tactic Notation "lexistsR" constr(x1) constr(x2) constr(x3) :=
	first [simple apply lexistsR with x1 | lexistsR_aux; simple apply lexistsR with x1]; lexistsR x2 x3.
Tactic Notation "lexistsR" constr(x1) constr(x2) constr(x3) constr(x4) :=
	first [simple apply lexistsR with x1 | lexistsR_aux; simple apply lexistsR with x1]; lexistsR x2 x3 x4.

Local Existing Instance EmbedOpId.		   
Local Existing Instance EmbedId.

Lemma test_er {A B : Type} `{H : Embed B A} {HBPO: EmbedOp Prop B} {HPB : Embed Prop B} {HO : EmbedOp Prop A} {HE: Embed Prop A} {HA : ILogic A} {HB : ILogic B} 
    (P Q R : A) (S : B) (T : Prop) (f : nat -> A) (g : nat -> B) (h : nat -> Prop) :
  lfalse |-- (S //\\ Exists y, g y) /\\ (P //\\ (Exists y, f y) \\// R //\\ (T //\\ Exists y, h y) /\\ Exists x, f x).
Proof.
	lexistsR 3 4 5 6.
	apply lfalseL.
Qed.

Section PullExistsLeft.  

Fixpoint pull_exists_l {A : Type} {ILA : ILogicOps A}
(t : @deep_op A ILA) (de_env : env A) (tac_env : env (find_res A)) : option (find_res A) :=
match t with
	| t_and t1 t2   => find_res_binop land (pull_exists_l t1 de_env tac_env) (pull_exists_l t2 de_env tac_env)
	| t_exists T f  => Some (@mkf A (Tcons T Tnil) f)
	| t_and_inj B _ _ _ _ _ _ a b => find_res_binop lembedand (pull_exists_l a (env_empty B) (env_empty (find_res B)))
	                         (pull_exists_l b de_env tac_env)
	| t_and_prop _ _ a b => find_res_binop lembedand (pull_exists_l a (env_empty Prop) (env_empty (find_res Prop)))
	                         (pull_exists_l b de_env tac_env)
    | t_unop n p => 
    	match ((fst tac_env) [n]) with
    		| Some f => unop_option f (pull_exists_l p de_env tac_env)
    		| None => None
    	end
	| t_binop n p q =>
		match ((snd tac_env) [n]) with
			| Some f => binop_option f (pull_exists_l p de_env tac_env) (pull_exists_l q de_env tac_env)
			| None => None
		end
    | _ => match deep_op_eval de_env t with
    	     | Some t => Some (@mkf A Tnil t)
    	     | None   => None
    	   end
end.

   
	Lemma find_res_unop_sound_el {Ts : Tlist} {A B : Type} {ILA : ILogicOps A} `{ILB : ILogic B} 
	         (f : arrows Ts A) (op : A -> B) 
	        (Hop : forall T (f : T -> A) , op (Exists x, f x) |-- Exists x, op (f x)) :
	      op (find_res_eval_exists_aux f) |-- 
	      find_res_eval_exists_aux(arrows_unop op f).
	Proof.
		induction Ts.
		simpl. reflexivity.
		simpl in *. rewrite Hop.
		apply lexistsL; intro x; apply lexistsR with x.
		apply IHTs; tauto.
	Qed.
  	
 
 Lemma find_res_binop_sound_el {Ts Us : Tlist} {A B C : Type} {ILA : ILogicOps A} {ILB : ILogicOps B} `{ILC : ILogic C}
        (f : arrows Ts A) (g : arrows Us B) (op : A -> B -> C) 
        (Hop1 : forall T (f : T -> A) g, op (Exists x, f x) g |-- Exists x, (op (f x) g))
        (Hop2 : forall T f (g : T -> B), op f (Exists x, g x) |-- Exists x, (op f (g x))) :
      op (find_res_eval_exists_aux f) (find_res_eval_exists_aux g) |-- 
      find_res_eval_exists_aux (arrows_binop_merge op f g).
Proof.
	induction Ts; simpl in *.
	+ apply find_res_unop_sound_el.
	  intros. apply Hop2.
	+ rewrite Hop1. 
      apply lexistsL; intro x; apply lexistsR with x.
	  rewrite <- IHTs; try tauto; reflexivity. 
Qed.
 
  Lemma binop_sound_el {A B C : Type} {ILA : ILogicOps A} {ILB : ILogicOps B} `{ILC : ILogic C} 
                    (de_env1 : env A) (tac_env1 : env (find_res A))
                    (de_env2 : env B) (tac_env2 : env (find_res B))
                    (p : @deep_op A _) (q : @deep_op B _) (op : A -> B -> C) 
                  {H : Proper (lentails ==> lentails ==> lentails) op} 
      (Hp : match deep_op_eval de_env1 p, pull_exists_l p de_env1 tac_env1 with
	    | None, None => True
	    | Some p, Some q => p |-- find_res_eval_exists q
	    | _, _ => True
	  end)
      (Hq : match deep_op_eval de_env2 q, pull_exists_l q de_env2 tac_env2 with
	    | None, None => True
	    | Some p, Some q => p |-- find_res_eval_exists q
	    | _, _ => True
	  end) 
        (Hop1 : forall T (f : T -> A) g, op (Exists x, f x) g |-- Exists x, (op (f x) g))
        (Hop2 : forall T f (g : T -> B), op f (Exists x, g x) |-- Exists x, (op f (g x))) :
match binop_option op (deep_op_eval de_env1 p) (deep_op_eval de_env2 q), 
      find_res_binop op (pull_exists_l p de_env1 tac_env1) (pull_exists_l q de_env2 tac_env2) with
  | None, None     => True
  | Some p, Some q => p |-- find_res_eval_exists q
  | _, _           => True
end.
Proof.
	remember (deep_op_eval de_env1 p) as o1.
	remember (deep_op_eval de_env2 q) as o2.
	remember (pull_exists_l p de_env1 tac_env1) as o3.
	remember (pull_exists_l q de_env2 tac_env2) as o4.
	destruct o1, o2, o3, o4; simpl in *; try intuition congruence.
	etransitivity.
	apply H.
	apply Hp.
	apply Hq.
	destruct f; destruct f0.
	apply find_res_binop_sound_el; assumption.
Qed.
 

  	Lemma env_sound_aux_el {A : Type} `{ILA : ILogic A} 
  	                       (de_env : env A) (tac_env : env (find_res A))
    (t : @deep_op A _) (H : env_sound_rl de_env tac_env find_res_eval_exists) :
    match deep_op_eval de_env t, pull_exists_l t de_env tac_env with
      | None, None     => True
      | Some p, Some q => p |-- find_res_eval_exists q
      | _, _           => True
    end.
    Proof.
    	induction t.
    	+ simpl; reflexivity.
    	+ simpl; reflexivity.
    	+ simpl; reflexivity.   
        + apply binop_sound_el; [apply IHt1; assumption | apply IHt2; assumption | |]. 
          intros. apply landexistsDL.
          intros. rewrite landC, landexistsDL. setoid_rewrite landC at 1. reflexivity.
        + simpl; remember (deep_op_eval de_env t1) as o1.
	      remember (deep_op_eval de_env t2) as o2.
	      destruct o1, o2; simpl; (try intuition congruence); reflexivity.
        + simpl; remember (deep_op_eval de_env t1) as o1.
	      remember (deep_op_eval de_env t2) as o2.
	      destruct o1, o2; simpl; (try intuition congruence); reflexivity.
        + simpl.
          specialize (IHt ILA de_env tac_env H).
          remember (fst de_env) [n] as o1.
          remember (fst tac_env) [n] as o2.
          remember (deep_op_eval de_env t) as o3.
          remember (pull_exists_l t de_env tac_env) as o4.
          destruct o1, o2, o3, o4; simpl in *; try intuition congruence.
          symmetry in Heqo2;
          destruct H as [H _]; specialize (H f n Heqo2); destruct H as [g [H3 [H4 H5]]];
          rewrite <- Heqo1 in H3; inversion H3; subst.
          rewrite <- H5. apply H4. apply IHt.
        + simpl. 
          specialize (IHt1 ILA de_env tac_env H); specialize (IHt2 ILA de_env tac_env H).
          remember (snd de_env) [n] as o1.
          remember (snd tac_env) [n] as o2.
          remember (deep_op_eval de_env t1) as o3.
          remember (deep_op_eval de_env t2) as o4.
          remember (pull_exists_l t1 de_env tac_env) as o5.
          remember (pull_exists_l t2 de_env tac_env) as o6.
          destruct o1, o2, o3, o4, o5, o6; simpl in *; try intuition congruence.
          symmetry in Heqo2;
          destruct H as [_ H]; specialize (H f n Heqo2); destruct H as [g [H3 [H4 H5]]];
          rewrite <- Heqo1 in H3; inversion H3; subst.
          rewrite <- H5. apply H4; [apply IHt1 | apply IHt2].
        + simpl. reflexivity.
        + simpl. reflexivity.
        + apply binop_sound_el.
          apply IHt1. assumption. apply env_sound_rl_empty.
          apply IHt2; assumption.
          intros. unfold lembedand. rewrite <- embedlexists, landexistsDL. reflexivity.
          intros. unfold lembedand. rewrite landC, landexistsDL. setoid_rewrite landC at 1. reflexivity.
        + simpl. remember (deep_op_eval (env_empty B) t1) as o1.
          remember (deep_op_eval de_env t2) as o2.
          destruct o1, o2; simpl; (try intuition congruence); reflexivity.
        + apply binop_sound_el.
          apply IHt1. apply _. apply (env_sound_rl_empty).
          apply IHt2; assumption.
          intros. unfold lembedand. rewrite <- embedlexists, landexistsDL. reflexivity.
          intros. unfold lembedand. rewrite landC, landexistsDL. setoid_rewrite landC at 1. reflexivity.
        + simpl. remember (deep_op_eval (env_empty Prop) t1) as o1.
          remember (deep_op_eval de_env t2) as o2.
          destruct o1, o2; simpl; (try intuition congruence); reflexivity.
    Qed.

    Implicit Arguments env_sound_aux_el [[A] [ILOps] [ILA]].
    
  	Lemma env_sound_el {A : Type} `{ILA : ILogic A} (de_env : env A) (tac_env : env (find_res A))
    (t : @deep_op A _) (H : env_sound_rl de_env tac_env find_res_eval_exists) (P : A) :
    match deep_op_eval de_env t, pull_exists_l t de_env tac_env with
      | None, None     => True
      | Some p, Some q => find_res_eval_exists q |-- P -> p |-- P
      | _, _           => True
    end.
    Proof.
    	pose proof (env_sound_aux_el de_env tac_env t H).
    	remember (deep_op_eval de_env t) as o1.
    	remember (pull_exists_l t de_env tac_env) as o2.
    	destruct o1, o2; simpl in *; try intuition congruence.
    	intros. rewrite H0; assumption.
    Qed. 

End PullExistsLeft.

Implicit Arguments env_sound_el [[A] [ILOps] [ILA]].
  
Ltac lexistsL_aux :=
  match goal with
    | |- ?P |-- ?Q =>
      let A := type of P in 
      let t := quote_term P in
       apply (env_sound_el (env_empty A) (env_empty (find_res A)) t (env_sound_rl_empty (env_empty A) find_res_eval_exists) Q);
        simpl; cbv [find_res_eval_exists find_res_eval_exists_aux]; simpl
    | |- _ => fail 1 "Goal is not an entailment"
  end.
  
Ltac lexistsL2 := 
	repeat (
		repeat (
			let x := fresh "x" in 
			simple apply lexistsL; intro x
		); 
  		lexistsL_aux
  	).

Tactic Notation "lexistsL" := lexistsL2.
Tactic Notation "lexistsL" simple_intropattern(x1) :=
	first [simple apply lexistsL; intro x1 | lexistsL_aux; simple apply lexistsL; intro x1].
Tactic Notation "lexistsL" simple_intropattern(x1) simple_intropattern(x2) :=
	first [simple apply lexistsL; intro x1 | lexistsL_aux; simple apply lexistsL; intro x1]; lexistsL x2.
Tactic Notation "lexistsL" simple_intropattern(x1) simple_intropattern(x2) simple_intropattern(x3) :=
	first [simple apply lexistsL; intro x1 | lexistsL_aux; simple apply lexistsL; intro x1]; lexistsL x2 x3.
Tactic Notation "lexistsL" simple_intropattern(x1) simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) :=
	first [simple apply lexistsL; intro x1 | lexistsL_aux; simple apply lexistsL; intro x1]; lexistsL x2 x3 x4.

Lemma test_el {A B : Type} `{H : Embed B A} {HBPO: EmbedOp Prop B} {HPB : Embed Prop B} {HO : EmbedOp Prop A} {HE: Embed Prop A} {HA : ILogic A} {HB : ILogic B} 
    (P Q R : A) (S : B) (T : Prop) (f : nat -> A) (g : nat -> B) (h : nat -> Prop) :
  (S //\\ Exists y, g y) /\\ (P //\\ (Exists y, f y) //\\ R //\\ (T //\\ Exists y, h y) /\\ Exists x, f x) |-- ltrue.
Proof.
  lexistsL a b c d.
  lexistsL. apply ltrueR.
Qed.

 	Fixpoint find_res_eval_forall_aux {A : Type} {ILA : ILogicOps A} (Ts : Tlist) 
		: arrows Ts A -> A :=
		match Ts with
		  | Tnil => fun p => p
		  | Tcons T Ts => fun p => Forall x : T, find_res_eval_forall_aux (p x)
	    end.
	
	Definition find_res_eval_forall {A : Type} {ILA : ILogicOps A} (p : find_res A) :=
		find_res_eval_forall_aux (find_closure p).
 
(* Extracting universal quantifiers of the right of an entailment is currently next to useless.
   Forall does not propagate over any connective, especially not conjunction unless the type
   that is being quantified over is inhabitted. Until we fix a Gallina function that checks
   for wether types are inhabitted or not, this method is not useful. *) 
 
Fixpoint pull_forall_r {A : Type} {ILA : ILogicOps A}
(t : @deep_op A _) (de_env : env A) (tac_env : env (find_res A)) : option (find_res A) :=
match t with
	| t_forall T f  => Some (@mkf A (Tcons T Tnil) f)
    | t_unop n p => 
    	match ((fst tac_env) [n]) with
    		| Some f => unop_option f (pull_forall_r p de_env tac_env)
    		| None => None
    	end
	| t_binop n p q =>
		match ((snd tac_env) [n]) with
			| Some f => binop_option f (pull_forall_r p de_env tac_env) (pull_forall_r q de_env tac_env)
			| None => None
		end
    | _ => match deep_op_eval de_env t with
    	     | Some t => Some (@mkf A Tnil t)
    	     | None   => None
    	   end
end.

Section PullForallRight.  
   
	Lemma find_res_unop_sound_ar {Ts : Tlist} {A B : Type} {ILA : ILogicOps A} `{ILB : ILogic B} 
	        (f : arrows Ts A) (op : A -> B) 
	        (Hop : forall T (f : T -> A), Forall x, op (f x) |-- op (Forall x, f x)) :
	      find_res_eval_forall_aux(arrows_unop op f) |-- op (find_res_eval_forall_aux f).
	Proof.
		induction Ts.
		simpl. reflexivity.
		simpl in *. rewrite <- Hop.
		apply lforallR; intro x. apply lforallL with x.
		rewrite IHTs; firstorder. 
	Qed.
  	
 
 Lemma find_res_binop_sound_ar {Ts Us : Tlist} {A B C : Type} {ILA : ILogicOps A} {ILB : ILogicOps B} `{ILC : ILogic C}
        (f : arrows Ts A) (g : arrows Us B) (op : A -> B -> C) 
        (Hop1 : forall T (f : T -> A) g, Forall x, op (f x) g |-- op (Forall x, f x) g)
        (Hop2 : forall T f (g : T -> B), Forall x, op f (g x) |-- op f (Forall x, g x)) :
      find_res_eval_forall_aux (arrows_binop_merge op f g) |-- op (find_res_eval_forall_aux f) (find_res_eval_forall_aux g).
Proof.
	induction Ts; simpl in *.
	+ apply find_res_unop_sound_ar.
	  intros. apply Hop2.
	+ rewrite <- Hop1. 
      apply lforallR; intro x; apply lforallL with x.
	  rewrite <- IHTs; try tauto; reflexivity. 
Qed.
 
  Lemma binop_sound_ar {A B C : Type} {ILA : ILogicOps A} {ILB : ILogicOps B} `{ILC : ILogic C} 
                       (de_env1 : env A) (tac_env1 : env (find_res A))
                       (de_env2 : env B) (tac_env2 : env (find_res B))
                       (p : @deep_op A _) (q : @deep_op B _) (op : A -> B -> C) 
                       {H : Proper (lentails ==> lentails ==> lentails) op} 
      (Hp : match deep_op_eval de_env1 p, pull_forall_r p de_env1 tac_env1 with
	    | None, None => True
	    | Some p, Some q => find_res_eval_forall q |-- p
	    | _, _ => True
	  end)
      (Hq : match deep_op_eval de_env2 q, pull_forall_r q de_env2 tac_env2 with
	    | None, None => True
	    | Some p, Some q => find_res_eval_forall q |-- p
	    | _, _ => True
	  end) 
        (Hop1 : forall T (f : T -> A) g, Forall x, op (f x) g |-- op (Forall x, f x) g)
        (Hop2 : forall T f (g : T -> B), Forall x, op f (g x) |-- op f (Forall x, g x)) :
match binop_option op (deep_op_eval de_env1 p) (deep_op_eval de_env2 q), 
      find_res_binop op (pull_forall_r p de_env1 tac_env1) (pull_forall_r q de_env2 tac_env2) with
  | None, None     => True
  | Some p, Some q => find_res_eval_forall q |-- p
  | _, _           => True
end.
Proof.
	remember (deep_op_eval de_env1 p) as o1.
	remember (deep_op_eval de_env2 q) as o2.
	remember (pull_forall_r p de_env1 tac_env1) as o3.
	remember (pull_forall_r q de_env2 tac_env2) as o4.
	destruct o1, o2, o3, o4; simpl in *; try intuition congruence.
	etransitivity; [|apply H; [apply Hp | apply Hq]].
	destruct f; destruct f0.
	apply find_res_binop_sound_ar; assumption.
Qed.


  	Lemma env_sound_aux_ar {A : Type} `{ILA : ILogic A}
  	(de_env : env A) (tac_env : env (find_res A))
    (t : @deep_op A _) (H : env_sound_lr de_env tac_env find_res_eval_forall) :
    match deep_op_eval de_env t, pull_forall_r t de_env tac_env with
      | None, None     => True
      | Some p, Some q => find_res_eval_forall q |-- p
      | _, _           => True
    end.
    Proof.
    	induction t.
    	+ simpl; reflexivity.
    	+ simpl; reflexivity.
    	+ simpl; reflexivity.   
        + simpl; remember (deep_op_eval de_env t1) as o1.
	      remember (deep_op_eval de_env t2) as o2.
	      destruct o1, o2; simpl; (try intuition congruence); reflexivity.
        + simpl; remember (deep_op_eval de_env t1) as o1.
	      remember (deep_op_eval de_env t2) as o2.
	      destruct o1, o2; simpl; (try intuition congruence); reflexivity.
        + simpl; remember (deep_op_eval de_env t1) as o1.
	      remember (deep_op_eval de_env t2) as o2.
	      destruct o1, o2; simpl; (try intuition congruence); reflexivity.
        + simpl.
          specialize (IHt ILA de_env tac_env H).
          remember (fst de_env) [n] as o1.
          remember (fst tac_env) [n] as o2.
          remember (deep_op_eval de_env t) as o3.
          remember (pull_forall_r t de_env tac_env) as o4.
          destruct o1, o2, o3, o4; simpl in *; try intuition congruence.
          symmetry in Heqo2;
          destruct H as [H _]; specialize (H f n Heqo2); destruct H as [g [H3 [H4 H5]]];
          rewrite <- Heqo1 in H3; inversion H3; subst.
          rewrite H5. apply H4. apply IHt.
        + simpl. 
          specialize (IHt1 ILA de_env tac_env H); specialize (IHt2 ILA de_env tac_env H).
          remember (snd de_env) [n] as o1.
          remember (snd tac_env) [n] as o2.
          remember (deep_op_eval de_env t1) as o3.
          remember (deep_op_eval de_env t2) as o4.
          remember (pull_forall_r t1 de_env tac_env) as o5.
          remember (pull_forall_r t2 de_env tac_env) as o6.
          destruct o1, o2, o3, o4, o5, o6; simpl in *; try intuition congruence.
          symmetry in Heqo2;
          destruct H as [_ H]; specialize (H f n Heqo2); destruct H as [g [H3 [H4 H5]]];
          rewrite <- Heqo1 in H3; inversion H3; subst.
          rewrite H5. apply H4; [apply IHt1 | apply IHt2].
        + simpl. reflexivity.
        + simpl. reflexivity.
        + simpl. remember (deep_op_eval (env_empty B) t1) as o1.
          remember (deep_op_eval de_env t2) as o2.
          destruct o1, o2; simpl; (try intuition congruence); reflexivity.
        + simpl. remember (deep_op_eval (env_empty B) t1) as o1.
          remember (deep_op_eval de_env t2) as o2.
          destruct o1, o2; simpl; (try intuition congruence); reflexivity.
        + simpl. remember (deep_op_eval (env_empty Prop) t1) as o1.
          remember (deep_op_eval de_env t2) as o2.
          destruct o1, o2; simpl; (try intuition congruence); reflexivity.
        + simpl. remember (deep_op_eval (env_empty Prop) t1) as o1.
          remember (deep_op_eval de_env t2) as o2.
          destruct o1, o2; simpl; (try intuition congruence); reflexivity.
    Qed.
    
    Implicit Arguments env_sound_aux_ar [[A] [ILOps] [ILA]].
    
    
  	Lemma env_sound_ar {A : Type} `{ILA : ILogic A}
  	 (de_env : env A) (tac_env : env (find_res A))
    (t : @deep_op A _) (H : env_sound_lr de_env tac_env find_res_eval_forall) (P : A) :
    match deep_op_eval de_env t, pull_forall_r t de_env tac_env with
      | None, None     => True
      | Some p, Some q => P |-- find_res_eval_forall q -> P |-- p
      | _, _           => True
    end.
    Proof.
    	pose proof (env_sound_aux_ar de_env tac_env t).
    	remember (deep_op_eval de_env t) as o1.
    	remember (pull_forall_r t de_env tac_env) as o2.
    	destruct o1, o2; simpl in *; try intuition congruence.
    	intros. rewrite <- H0; assumption.
    Qed. 
    
    Implicit Arguments env_sound_ar [[A] [ILOps] [ILA]].
    
End PullForallRight.
  
Ltac lforallR_aux :=
  match goal with
    | |- ?P |-- ?Q =>
      let A := type of Q in 
      let t := quote_term Q in
       apply (env_sound_ar (env_empty A) (env_empty (find_res A)) t 
              (env_sound_lr_empty (env_empty A) find_res_eval_forall) P);
        simpl; cbv [find_res_eval_forall find_res_eval_forall_aux]; simpl
    | |- _ => fail 1 "Goal is not an entailment"
  end.
  
Ltac lforallR2 := 
	repeat (
		repeat (
			let x := fresh "x" in 
			simple apply lforallR; intro x
		); 
  		lforallR_aux
  	).

Tactic Notation "lforallR" := lforallR2.
Tactic Notation "lforallR" simple_intropattern(x1) :=
	first [simple apply lforallR; intro x1 | lforallR_aux; simple apply lforallR; intro x1].
Tactic Notation "lforallR" simple_intropattern(x1) simple_intropattern(x2) :=
	first [simple apply lforallR; intro x1 | lforallR_aux; simple apply lforallR; intro x1]; lforallR x2.
Tactic Notation "lforallR" simple_intropattern(x1) simple_intropattern(x2) simple_intropattern(x3) :=
	first [simple apply lforallR; intro x1 | lforallR_aux; simple apply lforallR; intro x1]; lforallR x2 x3.
Tactic Notation "lforallR" simple_intropattern(x1) simple_intropattern(x2) simple_intropattern(x3)  simple_intropattern(x4) :=
	first [simple apply lforallR; intro x1 | lforallR_aux; simple apply lforallR; intro x1]; lforallR x2 x3 x4.
   
(* This example wont work until we have a means for hanlding type inhabitation. *)  
 
(*
Lemma test_ar {A B : Type} `{H : Embed B A} {HBPO: EmbedOp Prop B} {HPB : Embed Prop B} {HO : EmbedOp Prop A} {HE: Embed Prop A} {HA : ILogic A} {HB : ILogic B} 
    (P Q R : A) (S : B) (T : Prop) (f : nat -> A) (g : nat -> B) (h : nat -> Prop) :
  lfalse |-- (S //\\ Forall y, g y) /\\ (P //\\ (Forall y, f y) //\\ R //\\ (T //\\ Forall y, h y) /\\ Forall x, f x).
Proof.
	lforallR a b c d.
	apply lfalseL.
Qed.
*)

Section PullForallLeft.  

Fixpoint pull_forall_l {A : Type} {ILA : ILogicOps A}
(t : @deep_op A _) (de_env : env A) (tac_env : env (find_res A)) : option (find_res A) :=
match t with
	| t_and t1 t2   => find_res_binop land (pull_forall_l t1 de_env tac_env) (pull_forall_l t2 de_env tac_env)
	| t_or  t1 t2   => find_res_binop lor (pull_forall_l t1 de_env tac_env) (pull_forall_l t2 de_env tac_env)
	| t_forall T f  => Some (@mkf A (Tcons T Tnil) f)
	| t_and_inj B _ _ _ _ _ _ a b => find_res_binop lembedand (pull_forall_l a (env_empty B) (env_empty (find_res B)))
	                         (pull_forall_l b de_env tac_env)
	| t_and_prop _ _ a b => find_res_binop lembedand (pull_forall_l a (env_empty Prop) (env_empty (find_res Prop)))
	                         (pull_forall_l b de_env tac_env)
    | t_unop n p => 
    	match ((fst tac_env) [n]) with
    		| Some f => unop_option f (pull_forall_l p de_env tac_env)
    		| None => None
    	end
	| t_binop n p q =>
		match ((snd tac_env) [n]) with
			| Some f => binop_option f (pull_forall_l p de_env tac_env) (pull_forall_l q de_env tac_env)
			| None => None
		end
    | _ => match deep_op_eval de_env t with
    	     | Some t => Some (@mkf A Tnil t)
    	     | None   => None
    	   end
end.   



	Lemma find_res_unop_sound_al {Ts : Tlist} {A B : Type} {ILA : ILogicOps A} `{ILB : ILogic B} 
	        (f : arrows Ts A) (op : A -> B) 
	        (Hop : forall T (f : T -> A) , op (Forall x, f x) |-- Forall x, op (f x)) :
	      op (find_res_eval_forall_aux f) |-- 
	      find_res_eval_forall_aux(arrows_unop op f).
	Proof.
		induction Ts.
		simpl. reflexivity.
		simpl in *. rewrite Hop.
		apply lforallR; intro x; apply lforallL with x.
		apply IHTs; tauto.
	Qed.
 
 Lemma find_res_binop_sound_al {Ts Us : Tlist} {A B C : Type} {ILA : ILogicOps A} {ILB : ILogicOps B} `{ILC : ILogic C}
        (f : arrows Ts A) (g : arrows Us B) (op : A -> B -> C) 
        (Hop1 : forall T (f : T -> A) g, op (Forall x, f x) g |-- Forall x, (op (f x) g))
        (Hop2 : forall T f (g : T -> B), op f (Forall x, g x) |-- Forall x, (op f (g x))) :
      op (find_res_eval_forall_aux f) (find_res_eval_forall_aux g) |-- 
      find_res_eval_forall_aux (arrows_binop_merge op f g).
Proof.
	induction Ts; simpl in *.
	+ apply find_res_unop_sound_al.
	  intros. apply Hop2.
	+ rewrite Hop1. 
      apply lforallR; intro x; apply lforallL with x.
	  rewrite <- IHTs; try tauto; reflexivity. 
Qed.
 
  Lemma binop_sound_al {A B C : Type} {ILA : ILogicOps A} {ILB : ILogicOps B} `{ILC : ILogic C} 
                   (de_env1 : env A) (tac_env1 : env (find_res A))
                    (de_env2 : env B) (tac_env2 : env (find_res B))
                    (p : @deep_op A _) (q : @deep_op B _) (op : A -> B -> C) 
                  {H : Proper (lentails ==> lentails ==> lentails) op} 
      (Hp : match deep_op_eval de_env1 p, pull_forall_l p de_env1 tac_env1 with
	    | None, None => True
	    | Some p, Some q => p |-- find_res_eval_forall q
	    | _, _ => True
	  end)
      (Hq : match deep_op_eval de_env2 q, pull_forall_l q de_env2 tac_env2 with
	    | None, None => True
	    | Some p, Some q => p |-- find_res_eval_forall q
	    | _, _ => True
	  end) 
        (Hop1 : forall T (f : T -> A) g, op (Forall x, f x) g |-- Forall x, (op (f x) g))
        (Hop2 : forall T f (g : T -> B), op f (Forall x, g x) |-- Forall x, (op f (g x))) :
match binop_option op (deep_op_eval de_env1 p) (deep_op_eval de_env2 q), 
      find_res_binop op (pull_forall_l p de_env1 tac_env1) (pull_forall_l q de_env2 tac_env2) with
  | None, None     => True
  | Some p, Some q => p |-- find_res_eval_forall q
  | _, _           => True
end.
Proof.
	remember (deep_op_eval de_env1 p) as o1.
	remember (deep_op_eval de_env2 q) as o2.
	remember (pull_forall_l p de_env1 tac_env1) as o3.
	remember (pull_forall_l q de_env2 tac_env2) as o4.
	destruct o1, o2, o3, o4; simpl in *; try intuition congruence.
	etransitivity.
	apply H.
	apply Hp.
	apply Hq.
	destruct f; destruct f0.
	apply find_res_binop_sound_al; assumption.
Qed.

  	Lemma env_sound_aux_al {A : Type} `{ILA : ILogic A}
  		 (de_env : env A) (tac_env : env (find_res A))
    (t : @deep_op A _) (H : env_sound_rl de_env tac_env find_res_eval_forall) :
    match deep_op_eval de_env t, pull_forall_l t de_env tac_env with
      | None, None     => True
      | Some p, Some q => p |-- find_res_eval_forall q
      | _, _           => True
    end.
    Proof.
    	induction t.
    	+ simpl; reflexivity.
    	+ simpl; reflexivity.
    	+ simpl; reflexivity.   
        + apply binop_sound_al; [apply IHt1; assumption | apply IHt2; assumption | |]. 
          intros. apply landforallDL.
          intros. rewrite landC, landforallDL. setoid_rewrite landC at 1. reflexivity.
        + apply binop_sound_al; [apply IHt1; assumption | apply IHt2; assumption | |]. 
          intros. apply lorforallDL.
          intros. rewrite lorC, lorforallDL. setoid_rewrite lorC at 1. reflexivity.
        + simpl; remember (deep_op_eval de_env t1) as o1.
	      remember (deep_op_eval de_env t2) as o2.
	      destruct o1, o2; simpl; (try intuition congruence); reflexivity.
        + simpl.
          specialize (IHt ILA de_env tac_env H).
          remember (fst de_env) [n] as o1.
          remember (fst tac_env) [n] as o2.
          remember (deep_op_eval de_env t) as o3.
          remember (pull_forall_l t de_env tac_env) as o4.
          destruct o1, o2, o3, o4; simpl in *; try intuition congruence.
          symmetry in Heqo2;
          destruct H as [H _]; specialize (H f n Heqo2); destruct H as [g [H3 [H4 H5]]];
          rewrite <- Heqo1 in H3; inversion H3; subst.
          rewrite <- H5. apply H4. apply IHt.
        + simpl. 
          specialize (IHt1 ILA de_env tac_env H); specialize (IHt2 ILA de_env tac_env H).
          remember (snd de_env) [n] as o1.
          remember (snd tac_env) [n] as o2.
          remember (deep_op_eval de_env t1) as o3.
          remember (deep_op_eval de_env t2) as o4.
          remember (pull_forall_l t1 de_env tac_env) as o5.
          remember (pull_forall_l t2 de_env tac_env) as o6.
          destruct o1, o2, o3, o4, o5, o6; simpl in *; try intuition congruence.
          symmetry in Heqo2;
          destruct H as [_ H]; specialize (H f n Heqo2); destruct H as [g [H3 [H4 H5]]];
          rewrite <- Heqo1 in H3; inversion H3; subst.
          rewrite <- H5. apply H4; [apply IHt1 | apply IHt2].
        + simpl. reflexivity.
        + simpl. reflexivity.
        + apply binop_sound_al.
          apply IHt1. assumption. apply env_sound_rl_empty.
          apply IHt2; assumption.
          intros. unfold lembedand. rewrite <- embedlforall, landforallDL. reflexivity.
          intros. unfold lembedand. rewrite landC, landforallDL. setoid_rewrite landC at 1. reflexivity.
        + simpl. remember (deep_op_eval (env_empty B) t1) as o1.
          remember (deep_op_eval de_env t2) as o2.
          destruct o1, o2; simpl; (try intuition congruence); reflexivity.
        + apply binop_sound_al.
          apply IHt1. apply _. apply env_sound_rl_empty.
          apply IHt2; assumption.
          intros. unfold lembedand. rewrite <- embedlforall, landforallDL. reflexivity.
          intros. unfold lembedand. rewrite landC, landforallDL. setoid_rewrite landC at 1. reflexivity.
        + simpl. remember (deep_op_eval (env_empty Prop) t1) as o1.
          remember (deep_op_eval de_env t2) as o2.
          destruct o1, o2; simpl; (try intuition congruence); reflexivity.
    Qed.

    Implicit Arguments env_sound_aux_al [[A] [ILOps] [ILA]].
    
  	Lemma env_sound_al' {A : Type} `{ILA : ILogic A}
  	(de_env : env A) (tac_env : env (find_res A))
    (t : @deep_op A _) (H : env_sound_rl de_env tac_env find_res_eval_forall) (P : A) :
    match deep_op_eval de_env t, pull_forall_l t de_env tac_env with
      | None, None     => True
      | Some p, Some q => find_res_eval_forall q |-- P -> p |-- P
      | _, _           => True
    end.
    Proof.
    	pose proof (env_sound_aux_al de_env tac_env t).
    	remember (deep_op_eval de_env t) as o1.
    	remember (pull_forall_l t de_env tac_env) as o2.
    	destruct o1, o2; simpl in *; try intuition congruence.
    	intros. rewrite H0; assumption.
    Qed. 

  	Lemma env_sound_al {A : Type} `{ILA : ILogic A}
  	(de_env : env A) (tac_env : env (find_res A))
    (t : @deep_op A _) (H : env_sound_rl de_env tac_env find_res_eval_forall) (P : A) (Q : find_res A) 
    (H1 : deep_op_eval de_env t = Some P) (H2 :  pull_forall_l t de_env tac_env = Some Q) :
    P |-- find_res_eval_forall Q.
    Proof.
    	pose proof (@env_sound_al' A _ _ de_env tac_env t H (find_res_eval_forall Q)).
    	rewrite H1, H2 in H0. apply H0. reflexivity.
    Qed.
	

End PullForallLeft.

Implicit Arguments env_sound_al [[A] [ILOps] [ILA]].

Ltac lforallL_aux :=
  match goal with
    | |- ?P |-- ?Q =>
      let A := type of P in 
      let t := quote_term P in
      etransitivity; [eapply (env_sound_al (env_empty A) (env_empty (find_res A)) t 
      	(env_sound_rl_empty (env_empty A) find_res_eval_forall)); [reflexivity | simpl; reflexivity] |
      	cbv [find_res_eval_forall find_res_eval_forall_aux]; simpl]
    | |- _ => fail 1 "Goal is not an entailment"
  end.
  
Ltac lforallL2 := 
	repeat (
		repeat (
			let x := fresh "x" in 
			simple eapply lforallL
		); 
  		lforallL_aux
  	).
 
Tactic Notation "lforallL" := lforallL2.
Tactic Notation "lforallL" constr(x1) :=
	first [simple apply lforallL with x1 | lforallL_aux; simple apply lforallL with x1].
Tactic Notation "lforallL" constr(x1) constr(x2) :=
	first [simple apply lforallL with x1 | lforallL_aux; simple apply lforallL with x1]; lforallL x2.
Tactic Notation "lforallL" constr(x1) constr(x2) constr(x3) :=
	first [simple apply lforallL with x1 | lforallL_aux; simple apply lforallL with x1]; lforallL x2 x3.
Tactic Notation "lforallL" constr(x1) constr(x2) constr(x3) constr(x4) :=
	first [simple apply lforallL with x1 | lforallL_aux; simple apply lforallL with x1]; lforallL x2 x3 x4.

 
Lemma test_al {A B : Type} `{H : Embed B A} {HBPO: EmbedOp Prop B} {HPB : Embed Prop B} {HO : EmbedOp Prop A} {HE: Embed Prop A} {HA : ILogic A} {HB : ILogic B} 
    (P Q R : A) (S : B) (T : Prop) (f : nat -> A) (g : nat -> B) (h : nat -> Prop) :
  (S //\\ Forall y, g y) /\\ (P //\\ (Forall y, f y) //\\ R //\\ (T //\\ Forall y, h y) /\\ Forall x, f x) |-- ltrue.
Proof.
	Check deep_op_eval (env_empty A).
  lforallL 2 3 4 5.
  apply ltrueR.
Qed.