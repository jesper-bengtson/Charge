Require Import Maps MapInterface MapFacts.
Require Import ILogic ILEmbed BaseTactics ILQuantTac BILogic BIBaseTactics.

Set Implicit Arguments.
Unset Strict Implicit.

Section PullForallLeft.

	Context {A : Type} `{ILA : BILogic A}.

	Definition sep_op (p q : find_res A) : find_res A :=
		mkf (arrows_binop_merge sepSP (find_closure p) (find_closure q)).

	Definition bi_env_tac : env (find_res A) :=
		env_add_binop (env_empty (find_res A)) 1 sep_op.
		
	Lemma bi_env_sound : env_sound_rl bi_env bi_env_tac find_res_eval_forall.
	Proof.
		unfold bi_env_tac, bi_env.
		apply env_sound_rl_add_binop_tac. 
		apply env_sound_rl_add_binop. apply env_sound_rl_empty. reflexivity.

		exists sepSP. simpl. split. intuition.
		split; [|apply _].
		intros. destruct a, b.
		simpl. unfold find_res_eval_forall; simpl. 
		induction find_types; simpl in *. 
		+ induction find_types0; simpl in *.
		  * reflexivity.
		  * rewrite bilforallscR. setoid_rewrite IHfind_types0. reflexivity.
		+ rewrite sepSPC1, bilforallscR. setoid_rewrite sepSPC1; setoid_rewrite IHfind_types.
		  reflexivity.
	Qed.

End PullForallLeft.

Ltac lforallL_aux :=
  match goal with
    | |- ?P |-- ?Q =>
      let A := type of P in 
      let t := quote_term P in
      etransitivity; [eapply (env_sound_al bi_env bi_env_tac t 
      	bi_env_sound); [reflexivity | simpl; reflexivity] |
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
	{HAL : BILOperators A} {HA : BILogic A} {HBL : BILOperators B} {HB : BILogic B} 
    (P Q R : A) (S : B) (T : Prop) (f : nat -> A) (g : nat -> B) (h : nat -> Prop) :
  (S //\\ Forall y, g y) /\\ (P ** (Forall y, f y) ** (R //\\ (T //\\ Forall y, h y) /\\ Forall x, f x)) |-- ltrue.
Proof.
	lforallL 2 3 4 5.
  apply ltrueR.
Qed.