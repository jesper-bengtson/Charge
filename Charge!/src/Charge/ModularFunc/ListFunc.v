Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.syms.SymEnv.
Require Import MirrorCore.syms.SymSum.
Require Import MirrorCore.Lambda.Expr.

Require Import Charge.Logics.ILogic.
Require Import Charge.ModularFunc.ListType.
Require Import Charge.ModularFunc.BaseType.
Require Import Charge.ModularFunc.BaseFunc.
Require Import Charge.ModularFunc.Denotation.
Require Import Charge.ModularFunc.SemiEqDecTyp.

Require Import Charge.Tactics.Base.MirrorCoreTacs.

Require Import Coq.Strings.String.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Inductive list_func (typ : Type) :=
  | pNil : typ -> list_func typ
  | pCons : typ -> list_func typ
  | pLength : typ -> list_func typ
  | pNoDup : typ -> list_func typ
  | pIn : typ -> list_func typ
  | pMap : typ -> typ -> list_func typ
  | pFold : typ -> typ -> list_func typ
  | pZip : typ -> typ -> list_func typ.

Class ListFunc (typ func : Type) := {
  fNil  : typ -> func;
  fCons : typ -> func;
  fLength : typ -> func;
  fNoDup : typ -> func;
  fIn : typ -> func;
  fMap : typ -> typ -> func;
  fFold : typ -> typ -> func;
  fZip : typ -> typ -> func;
  
  listS : func -> option (list_func typ)
}.

Section ListFuncSum.
	Context {typ func : Type} {H : ListFunc typ func}.

	Global Instance ListFuncSumL (A : Type) : 
		ListFunc typ (func + A) := {
		  fNil t := inl (fNil t);
	      fCons t := inl (fCons t);
	      fLength t := inl (fLength t);
	      fNoDup t := inl (fNoDup t);
	      fIn t := inl (fIn t);
          fMap t1 t2 := inl (fMap t1 t2);
          fFold t1 t2 := inl (fFold t1 t2);
          fZip t1 t2 := inl (fZip t1 t2);
          
          listS f := match f with
          			   | inl f => listS f
          			   | inr _ => None
          			 end
        }.

	Global Instance ListFuncSumR (A : Type) : 
		ListFunc typ (A + func) := {
		  fNil t := inr (fNil t);
	      fCons t := inr (fCons t);
	      fLength t := inr (fLength t);
	      fNoDup t := inr (fNoDup t);
	      fIn t := inr (fIn t);
          fMap t1 t2 := inr (fMap t1 t2);
          fFold t1 t2 := inr (fFold t1 t2);
          fZip t1 t2 := inr (fZip t1 t2);
         
          listS f := match f with
          			   | inr f => listS f
          			   | inl _ => None
          			 end
        }.

    Global Instance ListFuncExpr :
    	ListFunc typ (expr typ func) := {
    	  fNil t := Inj (fNil t);
    	  fCons t := Inj (fCons t);
    	  fLength t := Inj (fLength t);
    	  fNoDup t := Inj (fNoDup t);
    	  fIn t := Inj (fIn t);
    	  fMap t1 t2 := Inj (fMap t1 t2);
    	  fFold t1 t2 := Inj (fFold t1 t2);
    	  fZip t1 t2 := Inj (fZip t1 t2);
         
          listS f := match f with
          			   | Inj f => listS f
          			   | _ => None
          			 end
     }.
        
End ListFuncSum.

Section ListFuncInst.
	Context {typ : Type} {RType_typ : RType typ} 
	        {BT : BaseType typ} {HTBD : BaseTypeD BT}
	        {LT : ListType typ} {HTD: ListTypeD LT}.
	Context {func : Type} {H : ListFunc typ func}.
	Context {Heq : RelDec (@eq typ)} {HC : RelDec_Correct Heq}.

    Context {Typ2_tyArr : Typ2 _ Fun}.
    Context {Typ0_tyProp : Typ0 _ Prop}.
    
    Context {Typ0_tyPropOk : Typ0Ok Typ0_tyProp}.

    Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.
    Let tyProp : typ := @typ0 _ _ _ _.

	Global Instance ListFuncInst : ListFunc typ (list_func typ) := {
	  fNil := pNil;
	  fCons := pCons;
	  fLength := pLength;
	  fNoDup := pNoDup;
	  fIn := pIn;
	  fMap := pMap;
	  fFold := pFold;
	  fZip := pZip;
	  
	  listS f := Some f
	}.

	Definition typeof_list_func lf :=
		match lf with
		  | pNil t => Some (tyList t)
		  | pCons t => Some (tyArr t (tyArr (tyList t) (tyList t)))
		  | pLength t => Some (tyArr (tyList t) tyNat)
		  | pNoDup t => Some (tyArr (tyList t) tyProp)
		  | pIn t => Some (tyArr t (tyArr (tyList t) tyProp))
		  | pMap t1 t2 => Some (tyArr (tyArr t1 t2) (tyArr (tyList t1) (tyList t2)))
		  | pFold t1 t2 => Some (tyArr (tyArr t2 (tyArr t1 t1)) (tyArr t1 (tyArr (tyList t2) t1))) 
		  | pZip t1 t2 => Some (tyArr (tyList t1) (tyArr (tyList t2) (tyList (tyProd t1 t2))))
		end.

	Definition list_func_eq (a b : list_func typ) : option bool :=
	  match a , b with
	    | pNil t1, pNil t2 => Some (t1 ?[ eq ] t2)
	    | pCons t1, pCons t2 => Some (t1 ?[ eq ] t2)
	    | pLength t1, pLength t2 => Some (t1 ?[ eq ] t2)
	    | pNoDup t1, pNoDup t2 => Some (t1 ?[ eq ] t2)
	    | pIn t1, pIn t2 => Some (t1 ?[ eq ] t2)
	    | pMap t1 t2, pMap t3 t4 => Some (t1 ?[ eq ] t3 &&
	      								    t2 ?[ eq ] t4)%bool
	    | pFold t1 t2, pFold t3 t4 => Some (t1 ?[ eq ] t3 &&
	      								    t2 ?[ eq ] t4)%bool
	    | pZip t1 t2, pZip t3 t4 => Some (t1 ?[ eq ] t3 &&
	      								    t2 ?[ eq ] t4)%bool
	    | _, _ => None
	  end.

    Global Instance RelDec_list_func : RelDec (@eq (list_func typ)) := {
      rel_dec a b := match list_func_eq a b with 
    	  		       | Some b => b 
    		 	       | None => false 
    			     end
    }.

  Definition nilD t : typD (tyList t) := listR nil.
  Definition consD t : typD (tyArr t (tyArr (tyList t) (tyList t))) :=
    tyArrR2 (fun (x : typD t) (xs : typD (tyList t)) =>
      listR (cons x (trmD xs (listE eq_refl)))).
  
  Definition lengthD t := tyArrR (fun (xs : typD (tyList t)) => 
    natR (List.length (listD xs))).

  Definition NoDupD t := 
     tyArrR (fun (xs : typD (tyList t)) => PropR (NoDup (listD xs))).
     
  Definition InD t := 
    tyArrR2 (fun (x : typD t) (xs : typD (tyList t)) => 
      PropR (In x (listD xs))).

  Definition mapD t u :=
    tyArrR2 (fun (f : typD (tyArr t u)) (xs : typD (tyList t)) => 
      (listR (map (tyArrD f) (listD xs)))).

  Definition foldD t u :=
    tyArrR3 (fun (f : typD (tyArr u (tyArr t t))) (acc : typD t) (lst : typD (tyList u)) =>
      fold_right (tyArrD2 f) acc (listD lst)).

  Definition zipD t u :=
    tyArrR2 (fun (xs : typD (tyList t)) (ys : typD (tyList u)) =>
      trmR (combine (listD xs) (listD ys)) (listE (pairE (t := t) (u := u) eq_refl eq_refl))).

  Lemma listD_nil t : listD (nilD t) = nil.
  Proof.
    unfold listD, nilD, listR. rewrite trmDR. reflexivity.
  Qed.

  Lemma listR_nil t : listR nil = nilD t.
  Proof.
    reflexivity.
  Qed.

	 Definition list_func_symD lf :=
		match lf as lf return match typeof_list_func lf return Type with
								| Some t => typD t
								| None => unit
							  end with
	    | pNil t => nilD t
	    | pCons t => consD t
	    | pLength t => lengthD t
	    | pNoDup t => NoDupD t
	    | pIn t => InD t
	    | pMap t1 t2 => mapD t1 t2
	    | pFold t1 t2 => foldD t1 t2
	    | pZip t1 t2 => zipD t1 t2
	 end.

	Global Instance RSym_ListFunc : SymI.RSym (list_func typ) := {
	  typeof_sym := typeof_list_func;
	  symD := list_func_symD;
	  sym_eqb := list_func_eq
	}.

	Global Instance RSymOk_ListFunc : SymI.RSymOk RSym_ListFunc.
	Proof.
		split; intros.
		destruct a, b; simpl; try apply I.
		+ consider (t ?[ eq ] t0); intuition congruence.
		+ consider (t ?[ eq ] t0); intuition congruence.
		+ consider (t ?[ eq ] t0); intuition congruence.
		+ consider (t ?[ eq ] t0); intuition congruence.
		+ consider (t ?[ eq ] t0); intuition congruence.
		+ consider (t ?[ eq ] t1 && t0 ?[ eq ] t2)%bool; intuition congruence. 
		+ consider (t ?[ eq ] t1 && t0 ?[ eq ] t2)%bool; intuition congruence. 
		+ consider (t ?[ eq ] t1 && t0 ?[ eq ] t2)%bool; intuition congruence. 
	Qed.

End ListFuncInst.

Section MakeList.
	Context {typ func : Type} {H : ListFunc typ func}.

	Definition mkNil t : expr typ func := Inj (fNil t).
	Definition mkCons (t : typ) (x xs : expr typ func) := App (App (fCons t) x) xs.
	Definition mkLength (t : typ) (lst : expr typ func) := App (fLength t) lst.
	Definition mkNoDup (t : typ) (lst : expr typ func) := App (fNoDup t) lst.
	Definition mkIn (t : typ) (x lst : expr typ func) := App (App (fIn t) x) lst.
	Definition mkMap (t u : typ) (f lst : expr typ func) :=  App (App (fMap t u) f) lst.
	Definition mkFold (t u : typ) (f acc lst : expr typ func) :=  App (App (App (fFold t u) f) acc) lst.
	Definition mkZip (t u : typ) (xs ys : expr typ func) := App (App (fZip t u) xs) ys.
	
End MakeList.

Section ListOps.
  Context {typ func : Type} {RType_typ : RType typ}.
  Context {BF: BaseFunc typ func} {LF : ListFunc typ func}.
  Context {RSym_func : RSym func}.
  Context {LT : ListType typ}.
 
  Context {Typ2_tyArr : Typ2 _ Fun}.

  Definition list_to_expr (t : typ) (lst : list (typD t)) :=
    fold_right (fun x acc => mkCons t (mkConst t x) acc) (mkNil t) lst.
 
  Fixpoint expr_to_list (e : expr typ func) : (list (expr typ func) * expr typ func) :=
    match e with
      | App (App f x) xs =>
        match listS f with
          | Some (pCons t) =>
            let p := expr_to_list xs in (x::fst p, snd p)
          | _ => (nil, e)
        end
      | _ => (nil, e)
    end.
  
  Lemma expr_to_list_nil (e1 e2 : expr typ func) (H : expr_to_list e1 = (nil, e2)) : e1 = e2.
  Proof.
    destruct e1; simpl in *; try (solve [inversion H; reflexivity]).
    destruct e1_1; simpl in *; try (solve [inversion H; reflexivity]).
    destruct e1_1_1; simpl in *; try (solve [inversion H; reflexivity]).
    destruct (listS f); simpl in *; try (solve [inversion H; reflexivity]).
    destruct l; simpl in *; try (solve [inversion H; reflexivity]).
  Qed.

  Lemma expr_to_list_cons tus tvs t (e1 e2 : expr typ func) x xs (H : expr_to_list e1 = (x::xs, e2))
    (Htype : typeof_expr tus tvs e1 = Some (tyList t)) :
    exists e3, expr_to_list e3 = (xs, e2) /\ e1 = mkCons t x e3.
  Proof.
    destruct e1; simpl in *; try (solve [inversion H; reflexivity]).
    destruct e1_1; simpl in *; try (solve [inversion H; reflexivity]).
    destruct e1_1_1; simpl in *; try (solve [inversion H; reflexivity]).
    remember (listS f); destruct o; simpl in *; try (solve [inversion H; reflexivity]).
    destruct l; simpl in *; try (solve [inversion H; reflexivity]).
    inversion H; subst.
    exists e1_2.
    split.
    destruct (expr_to_list e1_2). reflexivity.
    unfold mkCons.
    symmetry in Heqo.
    forward.
	admit.
  Admitted.
  
End ListOps.

Section ListFuncOk.
  Context {typ func : Type} {RType_typ : RType typ}.
  Context {LF: ListFunc typ func} {RSym_func : RSym func}.
  Context {RelDec_eq : RelDec (@eq typ)}.
  Context {BT : BaseType typ} {BTD : BaseTypeD BT}.
  Context {LT : ListType typ} {LTD : ListTypeD LT}.
  Context {Typ2_tyArr : Typ2 _ Fun}.
  Context {Typ0_Prop : Typ0 _ Prop}.

  Class ListFuncOk := {
    lf_funcAsOk (f : func) (e : list_func typ) : listS f = Some e -> 
      forall t, 
        funcAs f t = 
        funcAs (RSym_func := RSym_ListFunc) e t;
    lf_fNilOk t : listS (fNil t) = Some (pNil t);
    lf_fConsOk t : listS (fCons t) = Some (pCons t);
    lf_fLengthOk t : listS (fLength t) = Some (pLength t);
    lf_fNoDupOk t : listS (fNoDup t) = Some (pNoDup t);
    lf_fInOk t : listS (fIn t) = Some (pIn t);
    lf_fMapOk t u : listS (fMap t u) = Some (pMap t u);
    lf_fFoldOk t u : listS (fFold t u) = Some (pFold t u);
    lf_fZipOk t u : listS (fZip t u) = Some (pZip t u)
  }.

End ListFuncOk.

Implicit Arguments ListFuncOk [[LF] [RType_typ] [RSym_func] [RelDec_eq] [LT] [LTD]
                               [Typ2_tyArr] [Typ0_Prop] [BT] [BTD]].
                               
Section ListFuncBaseOk.
  Context {typ func : Type} {RType_typ : RType typ}.
  Context {LF: ListFunc typ func} {RSym_func : RSym func}.
  Context {RelDec_eq : RelDec (@eq typ)}.
  Context {RelDec_eqOk : RelDec_Correct RelDec_eq}.
  Context {BT : BaseType typ} {BTD : BaseTypeD BT}.
  Context {LT : ListType typ} {LTD : ListTypeD LT}.

  Context {Typ2_tyArr : Typ2 _ Fun}.
  Context {Typ0_Prop : Typ0 _ Prop}.

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.
  
  Global Program Instance ListFuncBaseOk : 
  	ListFuncOk typ (RSym_func := RSym_ListFunc) (list_func typ) := {
    lf_funcAsOk := fun _ _ _ _ => eq_refl;
    lf_fNilOk t := eq_refl;
    lf_fConsOk t := eq_refl;
    lf_fLengthOk t := eq_refl;
    lf_fNoDupOk t := eq_refl;
    lf_fInOk t := eq_refl;
    lf_fMapOk t u := eq_refl;
    lf_fFoldOk t u := eq_refl;
    lf_fZipOk t u := eq_refl
  }.

End ListFuncBaseOk.

Section ListFuncExprOk.
  Context {typ func : Type} `{HOK : ListFuncOk typ func}.
  Context {HROk : RTypeOk}.
  Context {A : Type} {RSymA : RSym A}.
  Context {Typ2Ok_tyArr : Typ2Ok Typ2_tyArr}.
  Context {RSym_funcOk : RSymOk RSym_func0}.
  

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.
  Let tyProp : typ := @typ0 _ _ _ _.

  Lemma ListFunc_typeOk (f : func) (e : list_func typ) (H : listS f = Some e) :
    typeof_sym f = typeof_list_func e.
  Proof.
    destruct HOK as [H1 H2 _ _ _ _ _ _ _].
    specialize (H1 _ _ H).
    destruct e; simpl in *;
    match goal with 
      | |- typeof_sym ?f = Some ?t => 
	 	specialize (H1 t);
	 	simpl in H1;
	 	unfold funcAs in H1; simpl in H1 ; rewrite type_cast_refl in H1; [|apply _];
	    generalize dependent (symD f);
	 	destruct (typeof_sym f); simpl; intros; [forward|]; inversion H1
 	end.
  Qed.
  
  Lemma lf_nil_func_type_eq (f : func) t t' df
    (H1 : listS f = Some (pNil t)) (H2 : funcAs f t' = Some df) :
    t' = tyList t.
  Proof.
    rewrite (lf_funcAsOk _ H1) in H2.
    unfold funcAs in H2; simpl in *.
    forward.
  Qed.

  Lemma lf_nil_type_eq tus tvs (e : expr typ func) t t' df
    (H1 : listS e = Some (pNil t)) (H2 : exprD' tus tvs t' e = Some df) :
    t' = tyList t.
  Proof.
    destruct e; simpl in *; try congruence.
    autorewrite with exprD_rw in H2; simpl in H2; forward; inv_all; subst.
    eapply lf_nil_func_type_eq; eassumption.
  Qed.

  Lemma lf_cons_func_type_eq (f : func) t t' df
    (H1 : listS f = Some (pCons t)) (H2 : funcAs f t' = Some df) :
    t' = tyArr t (tyArr (tyList t) (tyList t)).
  Proof.
    rewrite (lf_funcAsOk _ H1) in H2.
    unfold funcAs in H2; simpl in *.
    forward.
    rewrite <- r. reflexivity.
  Qed.

  Lemma lf_cons_type_eq tus tvs (e : expr typ func) t t' df
    (H1 : listS e = Some (pCons t)) (H2 : exprD' tus tvs t' e = Some df) :
    t' = tyArr t (tyArr (tyList t) (tyList t)).
  Proof.
    destruct e; simpl in *; try congruence.
    autorewrite with exprD_rw in H2; simpl in H2; forward; inv_all; subst.
    eapply lf_cons_func_type_eq; eassumption.
  Qed.

  Lemma lf_length_func_type_eq (f : func) t t' df
    (H1 : listS f = Some (pLength t)) (H2 : funcAs f t' = Some df) :
    t' = tyArr (tyList t) tyNat.
  Proof.
    rewrite (lf_funcAsOk _ H1) in H2.
    unfold funcAs in H2; simpl in *.
    forward.
    rewrite <- r. reflexivity.
  Qed.

  Lemma lf_length_type_eq tus tvs (e : expr typ func) t t' df
    (H1 : listS e = Some (pLength t)) (H2 : exprD' tus tvs t' e = Some df) :
    t' = tyArr (tyList t) tyNat.
  Proof.
    destruct e; simpl in *; try congruence.
    autorewrite with exprD_rw in H2; simpl in H2; forward; inv_all; subst.
    eapply lf_length_func_type_eq; eassumption.
  Qed.

  Lemma lf_NoDup_func_type_eq (f : func) t t' df
    (H1 : listS f = Some (pNoDup t)) (H2 : funcAs f t' = Some df) :
    t' = tyArr (tyList t) tyProp.
  Proof.
    rewrite (lf_funcAsOk _ H1) in H2.
    unfold funcAs in H2; simpl in *.
    forward.
    rewrite <- r. reflexivity.
  Qed.

  Lemma lf_NoDup_type_eq tus tvs (e : expr typ func) t t' df
    (H1 : listS e = Some (pNoDup t)) (H2 : exprD' tus tvs t' e = Some df) :
    t' = tyArr (tyList t) tyProp.
  Proof.
    destruct e; simpl in *; try congruence.
    autorewrite with exprD_rw in H2; simpl in H2; forward; inv_all; subst.
    eapply lf_NoDup_func_type_eq; eassumption.
  Qed.

  Lemma lf_In_func_type_eq (f : func) t t' df
    (H1 : listS f = Some (pIn t)) (H2 : funcAs f t' = Some df) :
    t' = tyArr t (tyArr (tyList t) tyProp).
  Proof.
    rewrite (lf_funcAsOk _ H1) in H2.
    unfold funcAs in H2; simpl in *.
    forward.
    rewrite <- r. reflexivity.
  Qed.

  Lemma lf_In_type_eq tus tvs (e : expr typ func) t t' df
    (H1 : listS e = Some (pIn t)) (H2 : exprD' tus tvs t' e = Some df) :
    t' = tyArr t (tyArr (tyList t) tyProp).
  Proof.
    destruct e; simpl in *; try congruence.
    autorewrite with exprD_rw in H2; simpl in H2; forward; inv_all; subst.
    eapply lf_In_func_type_eq; eassumption.
  Qed.

  Lemma lf_map_func_type_eq (f : func) t u t' df
    (H1 : listS f = Some (pMap t u)) (H2 : funcAs f t' = Some df) :
    t' = tyArr (tyArr t u) (tyArr (tyList t) (tyList u)).
  Proof.
    rewrite (lf_funcAsOk _ H1) in H2.
    unfold funcAs in H2; simpl in *.
    forward.
    rewrite <- r. reflexivity.
  Qed.

  Lemma lf_map_type_eq tus tvs (e : expr typ func) t u t' df
    (H1 : listS e = Some (pMap t u)) (H2 : exprD' tus tvs t' e = Some df) :
    t' = tyArr (tyArr t u) (tyArr (tyList t) (tyList u)).
  Proof.
    destruct e; simpl in *; try congruence.
    autorewrite with exprD_rw in H2; simpl in H2; forward; inv_all; subst.
    eapply lf_map_func_type_eq; eassumption.
  Qed.

  Lemma lf_fold_func_type_eq (f : func) t u t' df
    (H1 : listS f = Some (pFold t u)) (H2 : funcAs f t' = Some df) :
    t' = tyArr (tyArr u (tyArr t t)) (tyArr t (tyArr (tyList u) t)).
  Proof.
    rewrite (lf_funcAsOk _ H1) in H2.
    unfold funcAs in H2; simpl in *.
    forward.
    rewrite <- r. reflexivity.
  Qed.

  Lemma lf_fold_type_eq (e : expr typ func) tus tvs t u t' df
    (H1 : listS e = Some (pFold t u)) (H2 : exprD' tus tvs t' e = Some df) :
    t' = tyArr (tyArr u (tyArr t t)) (tyArr t (tyArr (tyList u) t)).
  Proof.
    destruct e; simpl in *; try congruence.
    autorewrite with exprD_rw in H2; simpl in H2; forward; inv_all; subst.
    eapply lf_fold_func_type_eq; eassumption.
  Qed.

  Lemma lf_zip_func_type_eq (f : func) t u t' df
    (H1 : listS f = Some (pZip t u)) (H2 : funcAs f t' = Some df) :
    t' = tyArr (tyList t) (tyArr (tyList u) (tyList (tyProd t u))).
  Proof.
    rewrite (lf_funcAsOk _ H1) in H2.
    unfold funcAs in H2; simpl in *.
    forward.
    rewrite <- r. reflexivity.
  Qed.

  Lemma lf_zip_type_eq tus tvs (e : expr typ func) t u t' df
    (H1 : listS e = Some (pZip t u)) (H2 : exprD' tus tvs t' e = Some df) :
    t' = tyArr (tyList t) (tyArr (tyList u) (tyList (tyProd t u))).
  Proof.
    destruct e; simpl in *; try congruence.
    autorewrite with exprD_rw in H2; simpl in H2; forward; inv_all; subst.
    eapply lf_zip_func_type_eq; eassumption.
  Qed.

  Existing Instance RSym_sum.

  Global Program Instance ListFuncOkSumR : ListFuncOk typ ((A + func)%type) := {
    lf_funcAsOk := 
      fun a f H t => 
        match a with
          | inl b => _
          | inr b => _
        end;
    lf_fNilOk t := lf_fNilOk (func := func) t;
    lf_fConsOk t := lf_fConsOk (func := func) t;
    lf_fLengthOk t := lf_fLengthOk (func := func) t;
    lf_fNoDupOk t := lf_fNoDupOk (func := func) t;
    lf_fInOk t := lf_fInOk (func := func) t;
    lf_fMapOk t u := lf_fMapOk (func := func) t u;
    lf_fFoldOk t u := lf_fFoldOk (func := func) t u;
    lf_fZipOk t u := lf_fZipOk (func := func) t u
  }.
  Next Obligation.
    apply (lf_funcAsOk (func := func)).
    apply H.
  Qed.

  Global Program Instance ListFuncOkSumL : ListFuncOk typ ((func + A)%type) := {
    lf_funcAsOk := 
      fun a f H t => 
        match a with
          | inl b => _
          | inr b => _
        end;
    lf_fNilOk t := lf_fNilOk (func := func) t;
    lf_fConsOk t := lf_fConsOk (func := func) t;
    lf_fLengthOk t := lf_fLengthOk (func := func) t;
    lf_fNoDupOk t := lf_fNoDupOk (func := func) t;
    lf_fInOk t := lf_fInOk (func := func) t;
    lf_fMapOk t u := lf_fMapOk (func := func) t u;
    lf_fFoldOk t u := lf_fFoldOk (func := func) t u;
    lf_fZipOk t u := lf_fZipOk (func := func) t u
  }.
  Next Obligation.
    apply (lf_funcAsOk (func := func)).
    apply H.
  Qed.

End ListFuncExprOk.

Section MakeListFuncSound.
  Context {typ func : Type} `{HOK : ListFuncOk typ func}.
  Context {HROk : RTypeOk} {Typ2_tyArrOk : Typ2Ok Typ2_tyArr}
          {RSym_funcOk : RSymOk RSym_func0}.

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.
  Let tyProp : typ := @typ0 _ _ _ _.
  
  Lemma lf_nil_func_eq (t : typ) (f : func) (df : typD (tyList t))
    (Ho : listS f = Some (pNil t))
    (Hf : funcAs f (tyList t) = Some df) :
    df = nilD t.
  Proof.
   rewrite (lf_funcAsOk _ Ho) in Hf.
   unfold funcAs in Hf; simpl in *.
   rewrite type_cast_refl in Hf; [|apply HROk].
   unfold Rcast, Relim_refl in Hf.
   inversion Hf. reflexivity.
  Qed.

  Lemma lf_nil_eq tus tvs (t : typ) (e : expr typ func) (df : ExprI.exprT tus tvs (typD (tyList t)))
    (Ho : listS e = Some (pNil t))
    (Hf : exprD' tus tvs (tyList t) e = Some df) :
    df = fun us vs => nilD t.
  Proof.
   destruct e; simpl in *; try congruence.
   autorewrite with exprD_rw in Hf; simpl in Hf; forward; inv_all; subst.
   erewrite <- lf_nil_func_eq; try eassumption; reflexivity.
  Qed.

  Lemma lf_cons_func_eq (t : typ) (f : func) (df : typD (tyArr t (tyArr (tyList t) (tyList t))))
    (Ho : listS f = Some (pCons t))
    (Hf : funcAs f (tyArr t (tyArr (tyList t) (tyList t))) = Some df) :
    df = consD t.
  Proof.
   rewrite (lf_funcAsOk _ Ho) in Hf.
   unfold funcAs in Hf; simpl in *.
   rewrite type_cast_refl in Hf; [|apply HROk].
   unfold Rcast, Relim_refl in Hf.
   inversion Hf. reflexivity.
  Qed.

  Lemma lf_cons_eq tus tvs (t : typ) (e : expr typ func) 
    (df : ExprI.exprT tus tvs (typD (tyArr t (tyArr (tyList t) (tyList t)))))
    (Ho : listS e = Some (pCons t))
    (Hf : exprD' tus tvs (tyArr t (tyArr (tyList t) (tyList t))) e = Some df) :
    df = fun us vs => consD t.
  Proof.
   destruct e; simpl in *; try congruence.
   autorewrite with exprD_rw in Hf; simpl in Hf; forward; inv_all; subst.
   erewrite <- lf_cons_func_eq; try eassumption; reflexivity.
  Qed.

  Lemma lf_length_func_eq (t : typ) (f : func) (df : typD (tyArr (tyList t) tyNat))
    (Ho : listS f = Some (pLength t))
    (Hf : funcAs f (tyArr (tyList t) tyNat) = Some df) :
    df = lengthD t.
  Proof.
   rewrite (lf_funcAsOk _ Ho) in Hf.
   unfold funcAs in Hf; simpl in *.
   rewrite type_cast_refl in Hf; [|apply HROk].
   unfold Rcast, Relim_refl in Hf.
   inversion Hf. reflexivity.
  Qed.

  Lemma lf_length_eq tus tvs (t : typ) (e : expr typ func) (df : ExprI.exprT tus tvs (typD (tyArr (tyList t) tyNat)))
    (Ho : listS e = Some (pLength t))
    (Hf : exprD' tus tvs (tyArr (tyList t) tyNat) e = Some df) :
    df = fun us vs => lengthD t.
  Proof.
   destruct e; simpl in *; try congruence.
   autorewrite with exprD_rw in Hf; simpl in Hf; forward; inv_all; subst.
   erewrite <- lf_length_func_eq; try eassumption; reflexivity.
  Qed.

  Lemma lf_NoDup_func_eq (t : typ) (f : func) (df : typD (tyArr (tyList t) tyProp))
    (Ho : listS f = Some (pNoDup t))
    (Hf : funcAs f (tyArr (tyList t) tyProp) = Some df) :
    df = NoDupD t.
  Proof.
   rewrite (lf_funcAsOk _ Ho) in Hf.
   unfold funcAs in Hf; simpl in *.
   rewrite type_cast_refl in Hf; [|apply HROk].
   unfold Rcast, Relim_refl in Hf.
   inversion Hf. reflexivity.
  Qed.

  Lemma lf_NoDup_eq tus tvs (t : typ) (e : expr typ func) (df : ExprI.exprT tus tvs (typD (tyArr (tyList t) tyProp)))
    (Ho : listS e = Some (pNoDup t))
    (Hf : exprD' tus tvs (tyArr (tyList t) tyProp) e = Some df) :
    df = fun us vs => NoDupD t.
  Proof.
   destruct e; simpl in *; try congruence.
   autorewrite with exprD_rw in Hf; simpl in Hf; forward; inv_all; subst.
   erewrite <- lf_NoDup_func_eq; try eassumption; reflexivity.
  Qed.

  Lemma lf_In_func_eq (t : typ) (f : func) (df : typD (tyArr t (tyArr (tyList t) tyProp)))
    (Ho : listS f = Some (pIn t))
    (Hf : funcAs f (tyArr t (tyArr (tyList t) tyProp)) = Some df) :
    df = InD t.
  Proof.
   rewrite (lf_funcAsOk _ Ho) in Hf.
   unfold funcAs in Hf; simpl in *.
   rewrite type_cast_refl in Hf; [|apply HROk].
   unfold Rcast, Relim_refl in Hf.
   inversion Hf. reflexivity.
  Qed.

  Lemma lf_In_eq tus tvs (t : typ) (e : expr typ func) (df : ExprI.exprT tus tvs (typD (tyArr t (tyArr (tyList t) tyProp))))
    (Ho : listS e = Some (pIn t))
    (Hf : exprD' tus tvs (tyArr t (tyArr (tyList t) tyProp)) e = Some df) :
    df = fun us vs => InD t.
  Proof.
   destruct e; simpl in *; try congruence.
   autorewrite with exprD_rw in Hf; simpl in Hf; forward; inv_all; subst.
   erewrite <- lf_In_func_eq; try eassumption; reflexivity.
  Qed.

  Lemma lf_map_func_eq (t u : typ) (f : func) (df : typD (tyArr (tyArr t u) (tyArr (tyList t) (tyList u))))
    (Ho : listS f = Some (pMap t u))
    (Hf : funcAs f (tyArr (tyArr t u) (tyArr (tyList t) (tyList u))) = Some df) :
    df = mapD t u.
  Proof.
   rewrite (lf_funcAsOk _ Ho) in Hf.
   unfold funcAs in Hf; simpl in *.
   rewrite type_cast_refl in Hf; [|apply HROk].
   unfold Rcast, Relim_refl in Hf.
   inversion Hf. reflexivity.
  Qed.

  Lemma lf_map_eq tus tvs (t u : typ) (e : expr typ func) (df : ExprI.exprT tus tvs (typD (tyArr (tyArr t u) (tyArr (tyList t) (tyList u)))))
    (Ho : listS e = Some (pMap t u))
    (Hf : exprD' tus tvs (tyArr (tyArr t u) (tyArr (tyList t) (tyList u))) e = Some df) :
    df = fun us vs => mapD t u.
  Proof.
   destruct e; simpl in *; try congruence.
   autorewrite with exprD_rw in Hf; simpl in Hf; forward; inv_all; subst.
   erewrite <- lf_map_func_eq; try eassumption; reflexivity.
  Qed.

  Lemma lf_fold_func_eq (t u : typ) (f : func) (df : typD (tyArr (tyArr u (tyArr t t)) (tyArr t (tyArr (tyList u) t))))
    (Ho : listS f = Some (pFold t u))
    (Hf : funcAs f (tyArr (tyArr u (tyArr t t)) (tyArr t (tyArr (tyList u) t))) = Some df) :
    df = foldD t u.
  Proof.
   rewrite (lf_funcAsOk _ Ho) in Hf.
   unfold funcAs in Hf; simpl in *.
   rewrite type_cast_refl in Hf; [|apply HROk].
   unfold Rcast, Relim_refl in Hf.
   inversion Hf. reflexivity.
  Qed.

  Lemma lf_fold_eq (t u : typ) tus tvs (e : expr typ func) 
    (df : ExprI.exprT tus tvs (typD (tyArr (tyArr u (tyArr t t)) (tyArr t (tyArr (tyList u) t)))))
    (Ho : listS e = Some (pFold t u))
    (Hf : exprD' tus tvs (tyArr (tyArr u (tyArr t t)) (tyArr t (tyArr (tyList u) t))) e = Some df) :
    df = fun us vs => foldD t u.
  Proof.
   destruct e; simpl in *; try congruence.
   autorewrite with exprD_rw in Hf; simpl in Hf; forward; inv_all; subst.
   erewrite <- lf_fold_func_eq; try eassumption; reflexivity.
  Qed.

  Lemma lf_zip_func_eq (t u : typ) (f : func) (df : typD (tyArr (tyList t) (tyArr (tyList u) (tyList (tyProd t u)))))
    (Ho : listS f = Some (pZip t u))
    (Hf : funcAs f (tyArr (tyList t) (tyArr (tyList u) (tyList (tyProd t u)))) = Some df) :
    df = zipD t u.
  Proof.
   rewrite (lf_funcAsOk _ Ho) in Hf.
   unfold funcAs in Hf; simpl in *.
   rewrite type_cast_refl in Hf; [|apply HROk].
   unfold Rcast, Relim_refl in Hf.
   inversion Hf. reflexivity.
  Qed.

  Lemma lf_zip_eq tus tvs (t u : typ) (e : expr typ func) (df : ExprI.exprT tus tvs (typD (tyArr (tyList t) (tyArr (tyList u) (tyList (tyProd t u))))))
    (Ho : listS e = Some (pZip t u))
    (Hf : exprD' tus tvs (tyArr (tyList t) (tyArr (tyList u) (tyList (tyProd t u)))) e = Some df) :
    df = fun us vs => zipD t u.
  Proof.
   destruct e; simpl in *; try congruence.
   autorewrite with exprD_rw in Hf; simpl in Hf; forward; inv_all; subst.
   erewrite <- lf_zip_func_eq; try eassumption; reflexivity.
  Qed.

  Lemma mkNil_sound (t : typ) tus tvs :
    exprD' tus tvs (tyList t) (mkNil t) = Some (fun _ _ => nilD t).
  Proof.
    unfold mkNil; simpl.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    pose proof (lf_fNilOk t) as H1.
    pose proof (lf_funcAsOk _ H1) as H2; rewrite H2. 
    unfold funcAs; simpl; rewrite type_cast_refl; [|apply HROk].
    reflexivity.
  Qed.

  Lemma mkCons_sound (t : typ) (tus tvs : tenv typ) x xs
    (dx : ExprI.exprT tus tvs (typD t)) (dxs : ExprI.exprT tus tvs (typD (tyList t)))
    (Hx : exprD' tus tvs t x = Some dx) (Hxs : exprD' tus tvs (tyList t) xs = Some dxs) :
    exprD' tus tvs (tyList t) (mkCons t x xs) = Some (exprT_App (exprT_App (fun _ _ => consD t) dx) dxs).
  Proof.
    unfold mkCons; simpl.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ xs _ Hxs).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ x _ Hx).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    pose proof (lf_fConsOk t) as Ho.
    pose proof (lf_funcAsOk _ Ho) as H1.
    rewrite H1. unfold funcAs; simpl.
    rewrite type_cast_refl; [reflexivity | apply _].
  Qed.

  Lemma mkConsD (t : typ) (tus tvs : tenv typ) x xs (lstD : ExprI.exprT tus tvs (typD (tyList t)))
    (H : exprD' tus tvs (tyList t) (mkCons t x xs) = Some lstD) : 
    match exprD' tus tvs t x with
      | Some xD => 
        match exprD' tus tvs (tyList t) xs with
          | Some xsD => lstD = exprT_App (exprT_App (fun _ _ => consD t) xD) xsD
          | None => False
        end
      | None => False
    end.
  Proof.
    unfold mkCons in H.
    autorewrite with exprD_rw in H; simpl in H; forward; inv_all; subst.
    autorewrite with exprD_rw in H0; simpl in H0; forward; inv_all; subst.
    autorewrite with exprD_rw in H2; simpl in H2; forward; inv_all; subst.
    pose proof (lf_cons_func_type_eq _ _ (lf_fConsOk t) H2).
    r_inj H4.
    forward; inv_all; subst. 
    pose proof (lf_cons_func_eq _ (lf_fConsOk t) H2); subst.
    reflexivity.
  Qed.

  Lemma mkZipD (t u : typ) (tus tvs : tenv typ) xs ys (lstD : ExprI.exprT tus tvs (typD (tyList (tyProd t u))))
    (H : exprD' tus tvs (tyList (tyProd t u)) (mkZip t u xs ys) = Some lstD) : 
    match exprD' tus tvs (tyList t) xs with
      | Some xsD => 
        match exprD' tus tvs (tyList u) ys with
          | Some ysD => lstD = exprT_App (exprT_App (fun _ _ => zipD t u) xsD) ysD
          | None => False
        end
      | None => False
    end.
  Proof.
    unfold mkZip in H.
    autorewrite with exprD_rw in H; simpl in H; forward; inv_all; subst.
    autorewrite with exprD_rw in H0; simpl in H0; forward; inv_all; subst.
    autorewrite with exprD_rw in H2; simpl in H2; forward; inv_all; subst.
    pose proof (lf_zip_func_type_eq _ _ (lf_fZipOk t u) H2).
    r_inj H4.
    forward; inv_all; subst. 
    pose proof (lf_zip_func_eq _ (lf_fZipOk t u) H2); subst.
    reflexivity.
  Qed.

  Lemma mkLength_sound (t : typ) (tus tvs : tenv typ) lst
    (lstD : ExprI.exprT tus tvs (typD (tyList t))) 
    (Hlst : exprD' tus tvs (tyList t) lst = Some lstD)  :
    exprD' tus tvs tyNat (mkLength t lst) = Some (exprT_App (fun _ _ => lengthD t) lstD).
  Proof.
    unfold mkLength; simpl.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ lst _ Hlst).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    pose proof (lf_fLengthOk t) as Ho.
    pose proof (lf_funcAsOk _ Ho) as H1.
    rewrite H1. unfold funcAs; simpl.
    rewrite type_cast_refl; [reflexivity | apply _].
  Qed.

  Lemma mkNoDup_sound (t : typ) (tus tvs : tenv typ) lst
    (lstD : ExprI.exprT tus tvs (typD (tyList t))) 
    (Hlst : exprD' tus tvs (tyList t) lst = Some lstD)  :
    exprD' tus tvs tyProp (mkNoDup t lst) = Some (exprT_App (fun _ _ => NoDupD t) lstD).
  Proof.
    unfold mkNoDup; simpl.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ lst _ Hlst).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    pose proof (lf_fNoDupOk t) as Ho.
    pose proof (lf_funcAsOk _ Ho) as H1.
    rewrite H1. unfold funcAs; simpl.
    rewrite type_cast_refl; [reflexivity | apply _].
  Qed.

  Lemma mkIn_sound (t : typ) (tus tvs : tenv typ) x lst
    (xD : ExprI.exprT tus tvs (typD t)) 
    (lstD : ExprI.exprT tus tvs (typD (tyList t))) 
    (Hx : exprD' tus tvs t x = Some xD) 
    (Hlst : exprD' tus tvs (tyList t) lst = Some lstD)  :
    exprD' tus tvs tyProp (mkIn t x lst) = Some (exprT_App (exprT_App (fun _ _ => InD t) xD) lstD).
  Proof.
    unfold mkIn; simpl.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ lst _ Hlst).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ x _ Hx).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    pose proof (lf_fInOk t) as Ho.
    pose proof (lf_funcAsOk _ Ho) as H1.
    rewrite H1. unfold funcAs; simpl.
    rewrite type_cast_refl; [reflexivity | apply _].
  Qed.

  Lemma mkMap_sound (t u : typ) (tus tvs : tenv typ) f lst
    (fD : ExprI.exprT tus tvs (typD (tyArr t u)))
    (lstD : ExprI.exprT tus tvs (typD (tyList t))) 
    (Hf : exprD' tus tvs (tyArr t u) f = Some fD) 
    (Hlst : exprD' tus tvs (tyList t) lst = Some lstD)  :
    exprD' tus tvs (tyList u) (mkMap t u f lst) = Some (exprT_App (exprT_App (fun _ _ => mapD t u) fD) lstD).
  Proof.
    unfold mkMap; simpl.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ lst _ Hlst).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ f _ Hf).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    pose proof (lf_fMapOk t u) as Ho.
    pose proof (lf_funcAsOk _ Ho) as H1.
    rewrite H1. unfold funcAs; simpl.
    rewrite type_cast_refl; [reflexivity | apply _].
  Qed.

  Lemma mkFold_sound (t u : typ) (tus tvs : tenv typ) f acc lst
    (fD : ExprI.exprT tus tvs (typD (tyArr u (tyArr t t))))
    (accD : ExprI.exprT tus tvs (typD t))
    (lstD : ExprI.exprT tus tvs (typD (tyList u))) 
    (Hf : exprD' tus tvs (tyArr u (tyArr t t)) f = Some fD) 
    (Hacc : exprD' tus tvs t acc = Some accD)
    (Hlst : exprD' tus tvs (tyList u) lst = Some lstD)  :
    exprD' tus tvs t (mkFold t u f acc lst) = Some (exprT_App (exprT_App (exprT_App (fun _ _ => foldD t u) fD) accD) lstD).
  Proof.
    unfold mkFold; simpl.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ lst _ Hlst).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ acc _ Hacc).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ f _ Hf).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    pose proof (lf_fFoldOk t u) as Ho.
    pose proof (lf_funcAsOk _ Ho) as H2.
    rewrite H2. unfold funcAs; simpl.
    rewrite type_cast_refl; [reflexivity | apply _].
  Qed.

  Lemma mkZip_sound (t u : typ) (tus tvs : tenv typ) xs ys
    (xsD : ExprI.exprT tus tvs (typD (tyList t))) 
    (ysD : ExprI.exprT tus tvs (typD (tyList u))) 
    (Hxs : exprD' tus tvs (tyList t) xs = Some xsD) 
    (Hys : exprD' tus tvs (tyList u) ys = Some ysD) :
    exprD' tus tvs (tyList (tyProd t u)) (mkZip t u xs ys) = 
      Some (exprT_App (exprT_App (fun _ _ => zipD t u) xsD) ysD).
  Proof.
    unfold mkZip; simpl.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ ys _ Hys).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ xs _ Hxs).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    pose proof (lf_fZipOk t u) as Ho.
    pose proof (lf_funcAsOk _ Ho) as H1.
    rewrite H1. unfold funcAs; simpl.
    rewrite type_cast_refl; [reflexivity | apply _].
  Qed.

End MakeListFuncSound.

