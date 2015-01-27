Require Import ExtLib.Core.RelDec.
Require Import MirrorCore.TypesI.
Require Import Charge.Logics.ILogic.

Set Implicit Arguments.
Set Strict Implicit.

Section RTypeSum.

	Context {t1 t2 : Type} {Tt1 : RType t1} {Tt2 : RType t2}.

	Definition typ_sum := (t1 + t2)%type.

    Definition typD  (t : typ_sum) : Type :=
    match t with
    	| inl t => typD t
    	| inr t => typD t
    end.
    
    Inductive tyAcc_typ : typ_sum -> typ_sum -> Prop :=
      | tyAcc_sum_l (a b : t1) : tyAcc a b -> tyAcc_typ (inl a) (inl b)
      | tyAcc_sum_r (a b : t2) : tyAcc a b -> tyAcc_typ (inr a) (inr b).

	Definition type_cast_typ (a b : typ_sum) : option (a = b) :=
		match a, b with
			| inl t1, inl t2 =>
			  match type_cast t1 t2 with
			  	| Some pf => Some (match pf in _ = t1' return inl t1 = inl t1' with
			  	                   | eq_refl => eq_refl
			  	                   end)
			  	| None => None
			  end
			| inr t1, inr t2 =>
			  match type_cast t1 t2 with
			  	| Some pf => Some (match pf in _ = t1' return inr t1 = inr t1' with
			  	                   | eq_refl => eq_refl
			  	                   end)
			  	| None => None
			  end
			| _, _ => None
		end.

	Global Instance RTypeSum : RType typ_sum :=
	{ typD := typD
	; tyAcc := tyAcc_typ
	; type_cast := type_cast_typ
	}.

End RTypeSum.

Section WFSum.

	Context {t1 t2 : Type} {Tt1 : RType t1} {Tt2 : RType t2}.
	
	Hypothesis WFt1 : well_founded (@tyAcc _ Tt1).
	Hypothesis WFt2 : well_founded (@tyAcc _ Tt2).
	
	Lemma well_founded_tyAcc_sum : well_founded (@tyAcc _ (@RTypeSum t1 t2 _ _)).
	Proof.
	  red; intro a; destruct a; simpl in *.
	  + apply (well_founded_ind WFt1 (fun t => Acc tyAcc_typ (inl t))).
	    intros; constructor. intros. inversion H0; subst.
	    apply H. apply H3.
	  + apply (well_founded_ind WFt2 (fun t => Acc tyAcc_typ (inr t))).
	    do 2 intros. constructor. intros. inversion H0; subst.
	    apply H. apply H3.
	Defined.

End WFSum.

Section RTypeOk_Sum.

	Context {t1 t2 : Type} {Rt1 : RType t1} {Rt2 : RType t2}.
	Context {Tt1 : @RTypeOk t1 _} {Tt2 : @RTypeOk t2 _}.
	
	Global Instance RTypeSumOk : (@RTypeOk _ (@RTypeSum t1 t2 _ _)).
	Proof.
	  split; intros.
	  + reflexivity.
	  + apply well_founded_tyAcc_sum.
	  	apply wf_tyAcc; apply _.
	  	apply wf_tyAcc; apply _.
	  + destruct pf; reflexivity.
	  + destruct pf1, pf2; reflexivity.
	  + destruct x; simpl.
	  	* remember (type_cast t t); destruct o.
	  	  - rewrite type_cast_refl in Heqo; [| apply _].
	  	    assert (r = Rrefl t) by congruence.
	  	    rewrite H. reflexivity.
	  	  - rewrite type_cast_refl in Heqo; [congruence | apply _].
	  	* remember (type_cast t t); destruct o.
	  	  - rewrite type_cast_refl in Heqo; [| apply _].
	  	    assert (r = Rrefl t) by congruence.
	  	    rewrite H. reflexivity.
	  	  - rewrite type_cast_refl in Heqo; [congruence | apply _].
	  + intro Hxy; destruct x, y; simpl in *; [| congruence | congruence |].
	  	* remember (type_cast t t0); destruct o; [congruence|].
	  	  symmetry in Heqo. apply type_cast_total in Heqo; [| apply _]. 
	  	  inversion Hxy; subst. apply Heqo. reflexivity.
	  	* remember (type_cast t t0); destruct o; [congruence|].
	  	  symmetry in Heqo. apply type_cast_total in Heqo; [| apply _]. 
	  	  inversion Hxy; subst. apply Heqo. reflexivity.
	  + intros x y; destruct x, y.
	    - destruct (@EquivDec_typ t1 Rt1 Tt1 t t0); [
	        left; rewrite e; reflexivity |
	        right; intros H; apply c; inversion H; subst; reflexivity
	      ].
	    - right; intros H; inversion H.
	    - right; intros H; inversion H.
	    - destruct (@EquivDec_typ t2 Rt2 Tt2 t t0); [
	        left; rewrite e; reflexivity |
	        right; intros H; apply c; inversion H; subst; reflexivity
	      ].
	Qed.
	      
	Global Instance RelDec_typ_sum_eq : RelDec (@eq typ_sum) :=
	{ rel_dec t1 t2 := match type_cast_typ t1 t2 with
	                   | None => false
	                   | Some _ => true
	                   end
	}.

	Global Instance RelDecCorrect_typ_sum_eq : RelDec_Correct RelDec_typ_sum_eq.
	Proof.
	  split; intros x y; destruct x, y; simpl in *.
	  + remember (type_cast t t0) as o; destruct o; intros; split;
	  	[intros _ | reflexivity | intro H | intro H].
	  	* inversion r. reflexivity.
	  	* inversion H.
	  	* inversion H; subst.
	  	  rewrite type_cast_refl in Heqo; [|apply _].
	  	  inversion Heqo.
	  + split; intros; inversion H.
	  + split; intros; inversion H.
	  + split; intros; [inversion H|]; 
	    remember (type_cast t t0) as o; destruct o; 
	    	[ | inversion H | reflexivity | ].
	    * inversion r. reflexivity.
	    * inversion H; subst.
	      rewrite type_cast_refl in Heqo; [|apply _].
	      inversion Heqo.
   Qed.

End RTypeOk_Sum.