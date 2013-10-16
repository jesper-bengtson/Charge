Require Import Maps MapInterface MapFacts.
Require Import ILogic ILEmbed BaseTactics ILEmbedTac Later LaterBaseTactics.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Section PullEmbedLeft.

	Context {A : Type} `{ILA : ILLater A}.
	Context {HE : EmbedOp Prop A}.

	Definition later_op (p : find_prop A) : find_prop A :=
		(fst p, illater (snd p)).

	Definition later_env_tac : env (find_prop A) :=
		env_add_unop (env_empty (find_prop A)) 0 later_op.
		
	Lemma later_env_sound : env_sound_rl later_env later_env_tac find_prop_eval_and.
	Proof.
		unfold later_env_tac, later_env.
		apply env_sound_rl_add_unop_tac. 
		apply env_sound_rl_add_unop. apply env_sound_rl_empty. reflexivity.

		exists illater. simpl. split. intuition.
		split; [|apply _].
		intros. destruct a.
		induction l. simpl. reflexivity.
		simpl in *. unfold find_prop_eval_and in *. simpl in *. 
		rewrite spec_later_forall. lforallR x; lforallL x. apply IHfind_types.
	Qed.

End PullForallLeft.

Ltac lforallL_aux :=
  match goal with
    | |- ?P |-- ?Q =>
      let A := type of P in 
      let t := quote_term P in
      etransitivity; [eapply (env_sound_al later_env later_env_tac t 
      	later_env_sound); [reflexivity | simpl; reflexivity] |
      	cbv [find_res_eval_forall find_res_eval_forall_aux]; simpl]
    | |- _ => ILQuantTac.lforallL_aux
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
  (S //\\ Forall y, g y) /\\ |>(P //\\ (|>Forall y, |>f y) //\\ |>(R //\\ (T //\\ Forall y, h y) /\\ Forall x, f x)) |-- ltrue.
Proof.
	lforallL 2 3 4 5.
  apply ltrueR.
Qed.