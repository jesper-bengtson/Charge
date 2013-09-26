Require Import Maps MapInterface MapFacts.
Require Import ILogic Later BaseTactics ILQuantTac.

Set Implicit Arguments.
Unset Strict Implicit.

Section PullForallLeft.

	Context {A : Type} `{ILA : ILLater A}.

	Definition later_op (p : find_res A) : find_res A :=
		mkf (arrows_unop illater (find_closure p)).

	Definition later_env_tac : env (find_res A) :=
		env_add_unop (env_empty (find_res A)) 0 later_op.
		
	Lemma later_env_sound : env_sound_lr later_env later_env_tac find_res_eval_forall.
	Proof.
		unfold later_env_tac, later_env.
		apply env_sound_lr_add_unop_tac. 
		apply env_sound_lr_add_unop. apply env_sound_lr_empty. reflexivity.

		exists illater. simpl. split. intuition.
		split; [|apply _].
		intros. destruct a.
		simpl. induction find_types. simpl. reflexivity.
		simpl in *. unfold find_res_eval_forall in *. simpl in *. setoid_rewrite IHfind_types.
		apply spec_later_forall.
	Qed.
