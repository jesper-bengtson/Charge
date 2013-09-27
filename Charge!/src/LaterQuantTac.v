Require Import Maps MapInterface MapFacts.
Require Import ILogic ILEmbed BaseTactics ILQuantTac Later.

Set Implicit Arguments.
Unset Strict Implicit.

Section PullForallLeft.

	Context {A : Type} `{ILA : ILLater A}.

	Definition later_op (p : find_res A) : find_res A :=
		mkf (arrows_unop illater (find_closure p)).

	Definition later_env_tac : env (find_res A) :=
		env_add_unop (env_empty (find_res A)) 0 later_op.
		
	Lemma later_env_sound : env_sound_rl later_env later_env_tac find_res_eval_forall.
	Proof.
		unfold later_env_tac, later_env.
		apply env_sound_rl_add_unop_tac. 
		apply env_sound_rl_add_unop. apply env_sound_rl_empty. reflexivity.

		exists illater. simpl. split. intuition.
		split; [|apply _].
		intros. destruct a.
		simpl. induction find_types. simpl. reflexivity.
		simpl in *. unfold find_res_eval_forall in *. simpl in *. 
		rewrite spec_later_forall. lforallR x; lforallL x. apply IHfind_types.
	Qed.

End PullForallLeft.

Local Transparent MapInterface.find MapInterface.empty MapInterface.add OrderedType.compare.

Ltac lforallL_aux :=
  match goal with
    | |- ?P |-- ?Q =>
      let A := type of P in 
      let t := quote_term P in idtac t (*
       apply (env_sound_al later_env later_env_tac t 
              later_env_sound Q);
        simpl; cbv [find_res_eval_forall find_res_eval_forall_aux]; simpl*)
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

 
Lemma test_al {A B : Type} `{H : Embed B A} {HBPO: EmbedOp Prop B} {HPB : Embed Prop B} {HO : EmbedOp Prop A} {HE: Embed Prop A} 
	{HAL : ILLOperators A} {HA : ILLater A} {HBL : ILLOperators B} {HB : ILLater B} 
    (P Q R : A) (S : B) (T : Prop) (f : nat -> A) (g : nat -> B) (h : nat -> Prop) :
  (S //\\ Forall y, g y) /\\ (P //\\ (Forall y, f y) //\\ R //\\ (T //\\ Forall y, h y) /\\ Forall x, f x) |-- ltrue.
Proof.
	apply (env_sound_al later_env later_env_tac (t_and_inj illogic H HPB (t_and (t_atom S) (t_forall (fun y : nat => g y)))
   (t_and (t_atom P)
      (t_and (t_forall (fun y : nat => f y))
         (t_and (t_atom R)
            (t_and_prop HE (t_and (t_atom T) (t_forall (fun y : nat => h y)))
               (t_forall (fun x : nat => f x))))))) later_env_sound ltrue).
  lforallL 2 3 4 5.
  apply ltrueR.
Qed.