Require Import BaseTactics.
Require Import ILogic ILEmbed.
Require Import List.
Require Import Maps MapInterface MapFacts.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.
 
Definition find_prop (A : Type) := (list Prop * A)%type.
		
Definition find_prop_unop {A B : Type} (op : A -> B) (a : option (find_prop A)) :
option (find_prop B) :=
match a with
	| Some a => Some (fst a, op (snd a))
	| None => None
end.
  
  Definition find_prop_binop {A B C : Type} (op : A -> B -> C) (a : option (find_prop A)) 
  	(b: option (find_prop B)) : option (find_prop C) :=
  	match a, b with
  	  | Some a, Some b => Some (fst a ++ fst b, op (snd a) (snd b))
  	  | _,      _      => None
  	end.
  	
  	Definition find_prop_create {A : Type} (a : option A) : option (find_prop A) :=
  	match a with
  		| Some a => Some (nil, a)
  		| None   => None
  	end.
  	 
 	Fixpoint find_prop_eval_and_aux {A : Type} {ILA : ILogicOps A} {H: EmbedOp Prop A} (Ps : list Prop) (a : A) : A :=
 		match Ps with
 			| nil     => a
 			| P :: Ps => P /\\ (find_prop_eval_and_aux Ps a)
 		end.
	
	Definition find_prop_eval_and {A : Type} {ILA : ILogicOps A} {H: EmbedOp Prop A} (p : find_prop A) :=
		find_prop_eval_and_aux (fst p) (snd p).
 
Fixpoint pull_and {A : Type} {ILA : ILogicOps A}
                  (t : @deep_op A _) (de_env : env A) (tac_env : env (find_prop A)) : option (find_prop A) :=
match t with
	| t_and t1 t2   => find_prop_binop land (pull_and t1 de_env tac_env) (pull_and t2 de_env tac_env)
	| t_and_inj B _ _ _ _ _ _ a b => find_prop_binop lembedand (pull_and a (env_empty B) (env_empty (find_prop B)))
	                         (pull_and b de_env tac_env)
	| t_and_prop _ _ a b => 
		match deep_op_eval (env_empty Prop) a, pull_and b de_env tac_env with
			| Some a, Some b => Some (a::(fst b), snd b)
			| _, _           => None
		end
    | t_unop n p => 
    	match ((fst tac_env) [n]) with
    		| Some f => unop_option f (pull_and p de_env tac_env)
    		| None => None
    	end
	| t_binop n p q =>
		match ((snd tac_env) [n]) with
			| Some f => binop_option f (pull_and p de_env tac_env) (pull_and q de_env tac_env)
			| None => None
		end
    | _ => match deep_op_eval de_env t with
    	     | Some t => Some (nil, t)
    	     | None   => None
    	   end
end.

Section PullAndRight.

	Lemma find_prop_unop_sound_ar {A B : Type} {ILA : ILogicOps A} `{ILB : ILogic B} 
						{HA : EmbedOp Prop A} {HB : EmbedOp Prop B} 
						{HEA : Embed Prop A} {HEB : Embed Prop B}
	        (Ps : list Prop) (f : A) (op : A -> B) 
        (Hop : forall (P : Prop) p, P /\\ op p |-- op (P /\\ p)) :
	      find_prop_eval_and_aux Ps (op f) |-- op (find_prop_eval_and_aux Ps f).
	Proof.
		induction Ps.
		simpl. reflexivity.
		simpl in *. rewrite <- Hop.
		apply lpropandL; intro H. apply lpropandR; [apply H|].
		rewrite IHPs. reflexivity.
	Qed.
  	
 
 Lemma find_prop_binop_sound_ar {A B C : Type} {ILA : ILogicOps A} {ILB : ILogicOps B} `{ILC : ILogic C}
						{HA : EmbedOp Prop A} {HB : EmbedOp Prop B} {HC : EmbedOp Prop C}
						{HAE : Embed Prop A} {HBE : Embed Prop B} {HCE : Embed Prop C}
         (Ps Qs : list Prop) (f : A) (g : B) (op : A -> B -> C) 
        (Hop1 : forall (P : Prop) p q, P /\\ op p q |-- op (P /\\ p) q)
        (Hop2 : forall (P : Prop) p q, P /\\ op p q |-- op p (P /\\ q)) :
      find_prop_eval_and_aux (Ps ++ Qs) (op f g) |-- op (find_prop_eval_and_aux Ps f) (find_prop_eval_and_aux Qs g).
Proof.
	induction Ps; simpl in *.
	+ apply find_prop_unop_sound_ar.
	  intros. apply Hop2.
	+ rewrite <- Hop1. 
	  apply lpropandL; intro H. apply lpropandR; [apply H|].
	  rewrite <- IHPs; reflexivity.
Qed.
 
  Lemma binop_sound_ar {A B C : Type} {ILA : ILogicOps A} {ILB : ILogicOps B} `{ILC : ILogic C} 
						{HA : EmbedOp Prop A} {HB : EmbedOp Prop B} {HC : EmbedOp Prop C}
 						{HAE : Embed Prop A} {HBE : Embed Prop B} {HCE : Embed Prop C}
                       (de_env1 : env A) (tac_env1 : env (find_prop A))
                       (de_env2 : env B) (tac_env2 : env (find_prop B))
                       (p : @deep_op A _) (q : @deep_op B _) (op : A -> B -> C) 
                       {H : Proper (lentails ==> lentails ==> lentails) op} 
      (Hp : match deep_op_eval de_env1 p, pull_and p de_env1 tac_env1 with
	    | None, None => True
	    | Some p, Some q => find_prop_eval_and q |-- p
	    | _, _ => False
	  end)
      (Hq : match deep_op_eval de_env2 q, pull_and q de_env2 tac_env2 with
	    | None, None => True
	    | Some p, Some q => find_prop_eval_and q |-- p
	    | _, _ => False
	  end) 
        (Hop1 : forall (P : Prop) p q, P /\\ op p q |-- op (P /\\ p) q)
        (Hop2 : forall (P : Prop) p q, P /\\ op p q |-- op p (P /\\ q)) :
match binop_option op (deep_op_eval de_env1 p) (deep_op_eval de_env2 q), 
      find_prop_binop op (pull_and p de_env1 tac_env1) (pull_and q de_env2 tac_env2) with
  | None, None     => True
  | Some p, Some q => find_prop_eval_and q |-- p
  | _, _           => False
end.
Proof.
	remember (deep_op_eval de_env1 p) as o1.
	remember (deep_op_eval de_env2 q) as o2.
	remember (pull_and p de_env1 tac_env1) as o3.
	remember (pull_and q de_env2 tac_env2) as o4.
	destruct o1, o2, o3, o4; simpl in *; try intuition congruence.
	etransitivity; [|apply H; [apply Hp | apply Hq]].
	destruct f; destruct f0. simpl. 
	unfold find_prop_eval_and. simpl. apply find_prop_binop_sound_ar.
	apply Hop1. apply Hop2.
Qed.

  	Lemma env_sound_aux_ar {A : Type} `{ILA : ILogic A} {HA : EmbedOp Prop A} {HAE : Embed Prop A} (de_env : env A) (tac_env : env (find_prop A))
    (t : @deep_op A _) :
    match deep_op_eval de_env t, pull_and t de_env tac_env with
      | None, None     => True
      | Some p, Some q => find_prop_eval_and q |-- p
      | _, _           => False
    end.
    Proof.
    	induction t.
    	+ simpl; reflexivity.
    	+ simpl; reflexivity.
    	+ simpl; reflexivity.   
        + simpl. apply binop_sound_ar; [apply IHt1; apply _ | apply IHt2; apply _ | |]. 
          intros. unfold lembedand. rewrite <- landA. reflexivity. 
          intros. unfold lembedand. rewrite <- landA, (landC (embed P)), landA. reflexivity.
        + simpl; remember (deep_op_eval de_env t1) as o1.
	      remember (deep_op_eval de_env t2) as o2.
	      destruct o1, o2; simpl; (try intuition congruence); reflexivity.
        + simpl; remember (deep_op_eval de_env t1) as o1.
	      remember (deep_op_eval de_env t2) as o2.
	      destruct o1, o2; simpl; (try intuition congruence); reflexivity.
        + admit.
        + admit.
        + simpl. reflexivity.
        + simpl. reflexivity.
        + apply binop_sound_ar.
          apply IHt1. assumption. assumption.
          apply IHt2. assumption. assumption.
          intros. apply lpropandAL.
          intros. apply lpropandAC. 
        + simpl. remember (deep_op_eval (env_empty B) t1) as o1.
          remember (deep_op_eval de_env t2) as o2.
          destruct o1, o2; simpl; (try intuition congruence); reflexivity.
        + simpl in *.    
          specialize (IHt2 _ HA HAE de_env tac_env).
          remember (deep_op_eval (env_empty Prop) t1) as o1.
          remember (deep_op_eval de_env t2) as o2.
          remember (pull_and t2 de_env tac_env) as o3.
          destruct o1, o2, o3; try (simpl; intuition congruence).
          simpl. rewrite <- IHt2. destruct f; simpl.
          unfold find_prop_eval_and. simpl. 
          unfold lembedand; rewrite emb_prop_eq; reflexivity.
        + simpl. remember (deep_op_eval (env_empty Prop) t1) as o1.
          remember (deep_op_eval de_env t2) as o2.
          destruct o1, o2; simpl; (try intuition congruence); reflexivity.
    Qed.
    
  	Lemma env_sound_ar {A : Type} `{ILA : ILogic A} {EmbOp : EmbedOp Prop A} {Emb : Embed Prop A}
  	(de_env : env A) (tac_env : env (find_prop A))
    (t : @deep_op A _) (P : A) :
    match deep_op_eval de_env t, pull_and t de_env tac_env with
      | None, None     => True
      | Some p, Some q => P |-- find_prop_eval_and q -> P |-- p
      | _, _           => False
    end.
    Proof.
    	pose proof (env_sound_aux_ar de_env tac_env t).
    	remember (deep_op_eval de_env t) as o1.
    	remember (pull_and t de_env tac_env) as o2.
    	destruct o1, o2; simpl in *; try intuition congruence.
    	intros. rewrite <- H; assumption.
    Qed. 

End PullAndRight.
  
Ltac lpropandR_aux :=
  match goal with
    | |- ?P |-- ?Q =>
      let A := type of Q in 
      let t := quote_term Q in 
       apply (env_sound_ar (env_empty A) (env_empty (find_prop A)) t P);
        simpl; cbv [find_prop_eval_and find_prop_eval_and_aux]; simpl
    | |- _ => fail 1 "Goal is not an entailment"
  end.
 
Ltac lpropandR := lpropandR_aux; repeat apply lpropandR.
   
Local Existing Instance EmbedOpId.
Local Existing Instance EmbedId.   
   
Lemma test_ar {A B : Type} `{H : Embed B A} {HBPO: EmbedOp Prop B} {HPB : Embed Prop B} {HO : EmbedOp Prop A} {HE: Embed Prop A} {HA : ILogic A} {HB : ILogic B} 
    (P Q R : A) (S : B) (a b c d : Prop) (f : nat -> A) (g : nat -> B) (h : nat -> Prop) (HF : False):
  lfalse |-- (a /\\ P) //\\ b /\\ (c /\\ S) /\\ Q //\\ (d /\\ R).
Proof.
	lpropandR; intuition.
Qed.


 	Fixpoint find_prop_eval_impl_aux {A : Type} {ILA : ILogicOps A} {H: EmbedOp Prop A} (Ps : list Prop) (a : A) : A :=
 		match Ps with
 			| nil     => a
 			| P :: Ps => P ->> (find_prop_eval_impl_aux Ps a)
 		end.
	
	Definition find_prop_eval_impl {A : Type} {ILA : ILogicOps A} {H: EmbedOp Prop A} (p : find_prop A) :=
		find_prop_eval_impl_aux (fst p) (snd p).
 
Fixpoint pull_impl {A : Type} {ILA : ILogicOps A} {EmbOp : EmbedOp Prop A} {Emb : Embed Prop A}
                  (t : @deep_op A _) (de_env : env A) (tac_env : env (find_prop A)) : option (find_prop A) :=
match t with
	| t_and t1 t2   => find_prop_binop land (pull_impl t1 de_env tac_env) (pull_impl t2 de_env tac_env)
	| t_and_inj B _ _ _ _ _ _ a b => find_prop_binop lembedand (pull_impl a (env_empty B) (env_empty (find_prop B)))
	                         (pull_impl b de_env tac_env)
	| t_and_prop _ _ a b => find_prop_binop lembedand (pull_impl a (env_empty Prop) (env_empty (find_prop Prop)))
	                         (pull_impl b de_env tac_env)
	| t_impl_prop _ _ a b => 
		match deep_op_eval (env_empty Prop) a, pull_impl b de_env tac_env with
			| Some a, Some b => Some (a::(fst b), snd b)
			| _, _           => None
		end
    | t_unop n p => 
    	match ((fst tac_env) [n]) with
    		| Some f => unop_option f (pull_impl p de_env tac_env)
    		| None => None
    	end
	| t_binop n p q =>
		match ((snd tac_env) [n]) with
			| Some f => binop_option f (pull_impl p de_env tac_env) (pull_impl q de_env tac_env)
			| None => None
		end
    | _ => match deep_op_eval de_env t with
    	     | Some t => Some (nil, t)
    	     | None   => None
    	   end
end.

Section PullImplLeft.

	Lemma find_prop_unop_sound_il {A B : Type} {ILA : ILogicOps A} `{ILB : ILogic B} 
						{HA : EmbedOp Prop A} {HB : EmbedOp Prop B} 
						{HEA : Embed Prop A} {HEB : Embed Prop B}
	        (Ps : list Prop) (f : A) (op : A -> B) 
        (Hop : forall (P : Prop) p, op (P ->> p) |-- P ->> op p) :
	      op (find_prop_eval_impl_aux Ps f) |-- find_prop_eval_impl_aux Ps (op f).
	Proof.
		induction Ps.
		simpl. reflexivity.
		simpl in *. rewrite Hop.
		apply lpropimplR; intro H. apply lpropimplL; [apply H|].
		rewrite IHPs. reflexivity.
	Qed.
  	
 
 Lemma find_prop_binop_sound_il {A B C : Type} {ILA : ILogicOps A} {ILB : ILogicOps B} `{ILC : ILogic C}
						{HA : EmbedOp Prop A} {HB : EmbedOp Prop B} {HC : EmbedOp Prop C}
						{HAE : Embed Prop A} {HBE : Embed Prop B} {HCE : Embed Prop C}
         (Ps Qs : list Prop) (f : A) (g : B) (op : A -> B -> C) 
        (Hop1 : forall (P : Prop) p q, op (P ->> p) q |-- P ->> op p q)
        (Hop2 : forall (P : Prop) p q, op p (P ->> q) |-- P ->> op p q) :
      op (find_prop_eval_impl_aux Ps f) (find_prop_eval_impl_aux Qs g) |-- find_prop_eval_impl_aux (Ps ++ Qs) (op f g).
Proof.
	induction Ps; simpl in *.
	+ apply find_prop_unop_sound_il.
	  intros. apply Hop2.
	+ rewrite Hop1. 
	  apply lpropimplR; intro H. apply lpropimplL; [apply H|].
	  rewrite <- IHPs; reflexivity.
Qed.
 
  Lemma binop_sound_il {A B C : Type} {ILA : ILogicOps A} {ILB : ILogicOps B} `{ILC : ILogic C} 
						{HA : EmbedOp Prop A} {HB : EmbedOp Prop B} {HC : EmbedOp Prop C}
 						{HAE : Embed Prop A} {HBE : Embed Prop B} {HCE : Embed Prop C}
                       (de_env1 : env A) (tac_env1 : env (find_prop A))
                       (de_env2 : env B) (tac_env2 : env (find_prop B))
                       (p : @deep_op A _) (q : @deep_op B _) (op : A -> B -> C) 
                       {H : Proper (lentails ==> lentails ==> lentails) op} 
      (Hp : match deep_op_eval de_env1 p, pull_impl p de_env1 tac_env1 with
	    | None, None => True
	    | Some p, Some q => p |-- find_prop_eval_impl q
	    | _, _ => False
	  end)
      (Hq : match deep_op_eval de_env2 q, pull_impl q de_env2 tac_env2 with
	    | None, None => True
	    | Some p, Some q => p |-- find_prop_eval_impl q
	    | _, _ => False
	  end) 
        (Hop1 : forall (P : Prop) p q, op (P ->> p) q |-- P ->> op p q)
        (Hop2 : forall (P : Prop) p q, op p (P ->> q) |-- P ->> op p q) :
match binop_option op (deep_op_eval de_env1 p) (deep_op_eval de_env2 q), 
      find_prop_binop op (pull_impl p de_env1 tac_env1) (pull_impl q de_env2 tac_env2) with
  | None, None     => True
  | Some p, Some q => p |-- find_prop_eval_impl q
  | _, _           => False
end.
Proof.
	remember (deep_op_eval de_env1 p) as o1.
	remember (deep_op_eval de_env2 q) as o2.
	remember (pull_impl p de_env1 tac_env1) as o3.
	remember (pull_impl q de_env2 tac_env2) as o4.
	destruct o1, o2, o3, o4; simpl in *; try intuition congruence.
	etransitivity; [apply H; [apply Hp | apply Hq]|].
	destruct f; destruct f0. simpl. 
	unfold find_prop_eval_impl. simpl. apply find_prop_binop_sound_il.
	apply Hop1. apply Hop2.
Qed.

  	Lemma env_sound_aux_il {A : Type} `{ILA : ILogic A} {HA : EmbedOp Prop A} {HAE : Embed Prop A} (de_env : env A) (tac_env : env (find_prop A))
    (t : @deep_op A _) :
    match deep_op_eval de_env t, pull_impl t de_env tac_env with
      | None, None     => True
      | Some p, Some q => p |-- find_prop_eval_impl q
      | _, _           => False
    end.
    Proof.
    	induction t.
    	+ simpl; reflexivity.
    	+ simpl; reflexivity.
    	+ simpl; reflexivity.   
        + simpl. apply binop_sound_il; [apply IHt1; apply _ | apply IHt2; apply _ | |]. 
          intros. unfold lembedimpl. apply limplAdj. apply landR.
          * rewrite landA. apply limplL. apply landL2. reflexivity.
            apply landL1. reflexivity.
          * apply landL1. apply landL2. reflexivity.
          * intros. rewrite landC. apply limplAdj. rewrite landA. apply limplL.
            apply landL2. reflexivity.
            apply landR. apply landL2. apply landL1. reflexivity.
            apply landL1. reflexivity.
        + simpl; remember (deep_op_eval de_env t1) as o1.
	      remember (deep_op_eval de_env t2) as o2.
	      destruct o1, o2; simpl; (try intuition congruence); reflexivity.
        + simpl; remember (deep_op_eval de_env t1) as o1.
	      remember (deep_op_eval de_env t2) as o2.
	      destruct o1, o2; simpl; (try intuition congruence); reflexivity.
        + admit.
        + admit.
        + simpl. reflexivity.
        + simpl. reflexivity.
        + apply binop_sound_il.
          apply IHt1. assumption.
          apply IHt2. assumption.
          intros. apply lpropimplAL. 
          intros; apply lpropimplAR.
        + simpl. remember (deep_op_eval (env_empty B) t1) as o1.
          remember (deep_op_eval de_env t2) as o2.
          destruct o1, o2; simpl; (try intuition congruence); reflexivity.
        + simpl in *.   
          apply binop_sound_il.
          apply IHt1. apply _.
          apply IHt2. apply _.
          intros; apply lpropimplAL.
          intros. unfold lembedand, lembedimpl. 
          etransitivity; [apply lpropimplAR|].
          rewrite emb_prop_eq. reflexivity.
        + simpl in *. 
          specialize (IHt2  ILA EmbOp Emb de_env tac_env).
          remember (deep_op_eval (env_empty Prop) t1) as o1.
          remember (deep_op_eval de_env t2) as o2.
          remember (@pull_impl A ILA0 EmbOp Emb t2 de_env tac_env) as o3.
          destruct o1, o2, o3; try (simpl; intuition congruence).
          simpl. destruct f; simpl.
          unfold find_prop_eval_impl. simpl.
          apply lpropimplR. intros HP.
          apply lpropimplL. apply HP.
          rewrite IHt2. unfold find_prop_eval_impl; simpl.
          admit. (* Proof by induction on find_pro_eval_impl_aux *)
    Qed.
    
  	Lemma env_sound_il {A : Type} `{ILA : ILogic A} {EmbOp : EmbedOp Prop A} {Emb : Embed Prop A}
  	(de_env : env A) (tac_env : env (find_prop A))
    (t : @deep_op A _) (P : A) :
    match deep_op_eval de_env t, pull_impl t de_env tac_env with
      | None, None     => True
      | Some p, Some q => find_prop_eval_impl q |-- P -> p |-- P
      | _, _           => False
    end.
    Proof.
    	pose proof (env_sound_aux_il de_env tac_env t).
    	remember (deep_op_eval de_env t) as o1.
    	remember (pull_impl t de_env tac_env) as o2.
    	destruct o1, o2; simpl in *; try intuition congruence.
    	intros. rewrite <- H0. assumption.
    Qed. 

End PullImplLeft.
  
Ltac lpropimplL_aux :=
  match goal with
    | |- ?P |-- ?Q =>
      let A := type of P in 
      let t := quote_term P in 
       apply (env_sound_il (env_empty A) (env_empty (find_prop A)) t Q);
        simpl; cbv [find_prop_eval_impl find_prop_eval_impl_aux]; simpl
    | |- _ => fail 1 "Goal is not an entailment"
  end.
  
Ltac lpropimplL := lpropimplL_aux; repeat apply lpropimplL.
 
   Lemma test_il {A B : Type} `{H : Embed B A} {HBPO: EmbedOp Prop B} {HPB : Embed Prop B} {HO : EmbedOp Prop A} {HE: Embed Prop A} {HA : ILogic A} {HB : ILogic B} 
    (P Q R : A) (S : B) (a b c d : Prop) (f : nat -> A) (g : nat -> B) (h : nat -> Prop) (HF : False):
  (a ->> P) //\\ (b ->> (c ->> S)) /\\ Q //\\ (d ->> R) |-- ltrue.
Proof.
	lpropimplL; destruct HF.
Qed.