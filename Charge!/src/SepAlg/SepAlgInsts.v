
Add Rec LoadPath "/Users/jebe/git/Charge/Charge!/bin".

Require Import UUSepAlg SepAlg Rel.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Section SAProd.
  Context A B `{HA: SepAlg A} `{HB: SepAlg B}.

  Instance SepAlgOps_prod: SepAlgOps (A * B) := {|
    sa_unit ab := sa_unit (fst ab) /\ sa_unit (snd ab);
    sa_mul a b c :=
      sa_mul (fst a) (fst b) (fst c) /\
      sa_mul (snd a) (snd b) (snd c)
   |}.

  Definition SepAlg_prod: SepAlg (A * B).
  Proof.
    esplit.
    - intros * [Hab Hab']. split; apply sa_mulC; assumption.
    - intros * [Habc Habc'] [Hbc Hbc'].
      destruct (sa_mulA Habc Hbc) as [exA []].
      destruct (sa_mulA Habc' Hbc') as [exB []].
      exists (exA, exB). split; split; assumption.
    - intros [a b].
      destruct (sa_unit_ex a) as [ea [Hea Hmulea]].
      destruct (sa_unit_ex b) as [eb [Heb Hmuleb]].
      exists (ea,eb). split; split; assumption.
    - intros * [Hunita Hunitb] [Hmula Hmulb].
      split; eapply sa_unit_eq; eassumption.
    - intros ab ab' [Hab Hab']. simpl. rewrite Hab, Hab'. reflexivity.
    - intros [a1 a2] [b1 b2] [c1 c2] [d1 d2] Heq [H1 H2].
      unfold Equivalence.equiv in Heq; destruct Heq; simpl in *.
      rewrite <- H, <- H0; intuition.
  Qed.
  
  Lemma subheap_prod (a a' : A) (b b' : B) : subheap (a, b) (a', b') <-> subheap a a' /\ subheap b b'.
  Proof.
  	split; [intros [c [H1 H2]]| intros [[c H1] [d H2]]]; simpl in *.
  	+ destruct c as [c d]; simpl in *; split.
  	  * exists c. apply H1.
  	  * exists d. apply H2.
  	+ exists (c, d); simpl; split.
  	  * apply H1.
  	  * apply H2.
  Qed.

  Lemma sa_mul_split (a b c : A) (a' b' c' : B) : sa_mul (a, a') (b, b') (c, c') <-> sa_mul a b c /\ sa_mul a' b' c'.
  Proof.
    split; intros; simpl in *; auto.
  Qed.
  
End SAProd.

Section UUSAProd.
	Context A B `{HA : UUSepAlg A} `{HB: UUSepAlg B}.
	
	Local Existing Instance SepAlgOps_prod.
	Local Existing Instance SepAlg_prod.
	
	Instance UUSepAlg_prod : UUSepAlg (A * B).
	Proof.
		split.
		+ apply _.
		+ intros. destruct H as [H1 H2]. destruct u; simpl in *.
		  split; apply uusa_unit; assumption.
	Qed.
	
End UUSAProd.