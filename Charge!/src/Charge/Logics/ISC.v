Require Import ILogic BILogic.
Require Import SetInterface SetFacts SetProperties.
Require Import Compare_dec.
Require Import Omega.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.


Section IteratedSeparatingConjunction.
	Context {A : Type} {HO : OrderedType A} {HF : FSet} {HS : FSetSpecs HF}. 
	Context {B : Type} `{HBI : BILogic B}.

	Definition isc (f : A -> B) (s : set A) := fold (fun b acc => f b ** acc) s empSP.
	

	Lemma isc_add (f : A -> B) (s : set A) (a : A) {H : Proper (_eq ==> lentails) f} 
	              (Ha : ~(In a s)) : 
	              isc f (add a s) -|- f a ** isc f s.
	Proof.
		unfold isc; rewrite fold_add; [reflexivity | apply _ | | | assumption].
		+ intros b c Hbc p q Hpq; rewrite Hpq. 
		  split; apply bilsep; apply H; [|symmetry]; assumption.
		+ intros b c p. repeat rewrite <- sepSPA; rewrite sepSPC with (P := f b).
		  reflexivity.
    Qed.

    Lemma isc_union (f : A -> B) (s1 s2 : set A) {H : Proper (_eq ==> lentails) f}
                    (Hs1s2 : forall x, ~(In x s1 /\ In x s2)) :
                    isc f (union s1 s2) -|- isc f s1 ** isc f s2.
    Proof.
        unfold isc; rewrite fold_union; [ | apply _ | | |].
        + revert Hs1s2. apply set_induction with (s := s1); clear s1.
		  * intros s1 Hs1 Hs1s2.
		    do 2 (rewrite fold_1 with (s := s1); [| apply _ | assumption]).
		    rewrite sepSPC, empSPR; reflexivity.
		  * intros s1 s3 IH x Hx Hadd Hs3s2.
		    rewrite fold_2 with (s' := s3); [| apply _ | | | eassumption | assumption].
		    - rewrite fold_2 with (s' := s3); [| apply _ | | | eassumption | assumption].
		      rewrite sepSPA. rewrite <- IH. reflexivity. 
		      intros y [Hs1 Hs2]. specialize (Hs3s2 y). apply Hs3s2.
		      split; [|apply Hs2]. 
		      SearchAbout add Add.
		      pose proof (Add_Equal x s1 s3) as H1; destruct H1 as [H1 _].
		      specialize (H1 Hadd). rewrite H1.
		      rewrite add_iff. right; assumption.
		      intros a b Hab p q Hpq; rewrite Hpq.
   		 	  split; apply bilsep; apply H; [|symmetry]; assumption.
   		 	  intros a b p; repeat rewrite <- sepSPA; rewrite sepSPC with (P := f a);
       		  reflexivity.
       		- intros a b Hab p q Hpq; rewrite Hpq.
   		 	  split; apply bilsep; apply H; [|symmetry]; assumption.
   		 	- intros a b p; repeat rewrite <- sepSPA; rewrite sepSPC with (P := f a);
       		  reflexivity.
    	+ intros a b Hab p q Hpq; rewrite Hpq.
    	  split; apply bilsep; apply H; [|symmetry]; assumption.
        + intros a b p; repeat rewrite <- sepSPA; rewrite sepSPC with (P := f a);
          reflexivity.
        +  intros x [Hs1 Hs2]. specialize (Hs1s2 x).
           apply Hs1s2; split; assumption.
	Qed.

	Global Instance isc_m (f : A -> B) {H : Proper (_eq ==> lentails) f} : 
		Proper (Equal ==> lequiv) (isc f).
	Proof.
		intros a b Hab.
		unfold isc. apply fold_equal.
		+ apply _.
   	    + intros c d Hcd p q Hpq; rewrite Hpq.
    	  split; apply bilsep; apply H; [|symmetry]; assumption.
        + intros c d p; repeat rewrite <- sepSPA; rewrite sepSPC with (P := f c);
          reflexivity.
        + assumption.
	Qed.
	
End IteratedSeparatingConjunction.

Section NatSet.
	Context {HF : @FSet nat _} {HS : FSetSpecs HF}.
	Context {A : Type} `{HBI: BILogic A}.

	Fixpoint nat_set_aux (count start : nat) : set nat :=
		match count with
			| O => add start empty
			| S x => add (start + count) (nat_set_aux x start)
		end.

	Definition nat_set (from to : nat) := 
		if le_dec from to then
			nat_set_aux (to - from) from
		else
			empty.

	Lemma nat_set_empty (from to : nat) (H : to > from) : Equal (nat_set to from) empty.
	Proof.
		unfold nat_set.
		destruct (le_dec to from); [omega|reflexivity].
	Qed.
	
	Lemma nat_set_singleton (from to : nat) (H : from = to) : Equal (nat_set to from) {from; empty}.
	Proof.
		unfold nat_set.
		destruct (le_dec to from); [|omega].
		assert (from - to = 0) as H1 by omega.
		rewrite H1. simpl. rewrite H. reflexivity.
	Qed.

    Lemma nat_set_in (a b x : nat) (Hax : a <= x) (Hbx : b >= x) : In x (nat_set a b).
    Proof.
    	unfold nat_set. destruct (le_dec a b); [|omega].
    	remember (b - a) as c. generalize dependent b. induction c; intros.
    	+ simpl. assert (a = b) by omega; subst. rewrite add_iff.
    	  left; unfold Equivalence.equiv; simpl; omega.
    	+ simpl. rewrite add_iff. destruct (eq_dec (a + S c) x).
          - left; assumption.
          - right. unfold Equivalence.equiv in H; simpl in H. 
            apply IHc with (b := b - 1); try omega.
    Qed.
    
    Lemma nat_set_in_from (a b x : nat) (Hin : In x (nat_set a b)) : x >= a.
    Proof.
    	unfold nat_set in Hin.
    	destruct (le_dec a b).
    	- remember (b - a) as c. generalize dependent b; induction c; intros. 
    	  + simpl in Hin. rewrite add_iff in Hin. destruct Hin as [Hax | Hin].
    	    * rewrite Hax. reflexivity.
    	    * rewrite empty_iff in Hin; destruct Hin.
    	  + simpl in Hin. rewrite add_iff in Hin; destruct Hin as [Hax | Hin].
            * rewrite <- Hax. omega.
            * apply IHc with (b := b - 1); try omega. assumption.
        - rewrite empty_iff in Hin; destruct Hin.
    Qed.
    
    Lemma nat_set_in_to (a b x : nat) (Hin : In x (nat_set a b)) : x <= b.
    Proof.
    	unfold nat_set in Hin.
    	destruct (le_dec a b).
    	- remember (b - a) as c; generalize dependent a; 
    	  generalize dependent x; induction c; intros.
    	  + simpl in Hin. rewrite add_iff in Hin. destruct Hin as [Hax | Hin].
    	    * rewrite <- Hax. assumption.
    	    * rewrite empty_iff in Hin; destruct Hin.
    	  + simpl in Hin.
    	    rewrite add_iff in Hin; destruct Hin as [Hax | Hin];
    	    unfold Equivalence.equiv in *; simpl in *; try omega.
    	    assert (S x <= b); [|omega].
    	    apply IHc with (a := S a); try omega.
    	    clear IHc Heqc l. induction c; simpl in *.
    	    * rewrite add_iff in Hin. destruct Hin as [Hax | Hin].
    	      rewrite Hax, add_iff; left; reflexivity.
    	      rewrite empty_iff in Hin; destruct Hin.
    	    * rewrite add_iff in Hin. destruct Hin as [Hacx | Hin].
    	      rewrite add_iff; left; rewrite Hacx; reflexivity.
    	      rewrite add_iff; right; apply IHc; assumption.
        - rewrite empty_iff in Hin; destruct Hin.
    Qed.
    
    Lemma nat_set_inter (a b c d : nat) (Hbc : b < c) :
    	Equal (inter (nat_set a b) (nat_set c d)) empty.
    Proof.
    	intros x; split; intros H.
    	+ rewrite inter_iff in H. destruct H as [H1 H2].
		  assert (x >= c) by (eapply nat_set_in_from; eassumption).
		  assert (x <= b) by (eapply nat_set_in_to; eassumption).
		  omega.
		+ rewrite empty_iff in H. destruct H.
	Qed.
		  
	Lemma nat_set_split (a b c : nat) (Hab : a <= b) (Hbc : b <= c) : 
		Equal (nat_set a c) (nat_set a b ++ nat_set (b + 1) c).
	Proof.
		intros x; split; intros H.
		* assert (x >= a) by (eapply nat_set_in_from; eassumption).
		  assert (x <= c) by (eapply nat_set_in_to; eassumption).
	  	  rewrite union_iff. destruct (le_gt_dec x b).
		  + left. apply nat_set_in; assumption.
		  + right. apply nat_set_in; [omega|assumption].
		* rewrite union_iff in H. destruct H as [H | H].
		  + assert (x >= a) by (eapply nat_set_in_from; eassumption).
	  	    assert (x <= b) by (eapply nat_set_in_to; eassumption).
	  	    apply nat_set_in; [assumption | omega].
		  + assert (x >= b + 1) by (eapply nat_set_in_from; eassumption).
	  	    assert (x <= c) by (eapply nat_set_in_to; eassumption).
	  	    apply nat_set_in; [omega | assumption].
	Qed.

	Definition isc_nat (f : nat -> A) (from to : nat) := isc f (nat_set from to).

	Lemma isc_nat_split (f : nat -> A) (a b c : nat) (Hab : a < b) (Hbc : b < c) :
		  isc_nat f a c -|- isc_nat f a b ** isc_nat f (b + 1) c.
	Proof.	
		unfold isc_nat.		
		rewrite <- isc_union.
		rewrite <- nat_set_split. reflexivity.
		omega. omega.
		intros x [H1 H2].
		pose proof (@nat_set_inter a b (b + 1) c).
		assert (b < b + 1) by omega.
		specialize (H H0 x). destruct H. rewrite empty_iff in H. apply H.
		rewrite inter_iff; split; assumption.
	Qed.
End NatSet.	    