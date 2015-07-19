Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Map.FMapPositive.
Require Import ExtLib.Data.SumN.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.syms.SymEnv.
Require Import MirrorCore.syms.SymSum.
Require Import MirrorCore.Lambda.Expr.

Require Import Charge.Logics.ILogic.
Require Import Charge.ModularFunc.NatFunc.
Require Import Charge.ModularFunc.Prop.
Require Import Charge.ModularFunc.Denotation.

Require Import Charge.Tactics.Base.MirrorCoreTacs.

Require Import Coq.Strings.String.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Inductive list_func (typ : Type) :=
  | pNil : typ -> list_func typ
  | pCons : typ -> list_func typ.

Class ListFunc (typ func : Type) := {
  fNil  : typ -> func;
  fCons : typ -> func;
  
  listS : func -> option (list_func typ)
}.

Section ListFuncSum.
	Context {typ func : Type} {H : ListFunc typ func}.

	Global Instance ListFuncPMap (p : positive) (m : pmap Type) 
	  (pf : Some func = pmap_lookup' m p) :
	  ListFunc typ (OneOf m) := {
	    fNil t := Into (fNil t) p pf;
	    fCons t := Into (fCons t) p pf;
	    
	    listS f :=
	      match f with
	        | Build_OneOf _ p' pf1 =>
	          match Pos.eq_dec p p' with
	            | left Heq => 
	              listS (eq_rect_r (fun o => match o with | Some T => T | None => Empty_set end) pf1 
	                (eq_rect _ (fun p =>  Some func = pmap_lookup' m p) pf _ Heq))
	            | right _ => None
	          end
	      end
	}.
         
    Global Instance ListFuncExpr :
    	ListFunc typ (expr typ func) := {
    	  fNil t := Inj (fNil t);
    	  fCons t := Inj (fCons t);
         
          listS f := match f with
          			   | Inj f => listS f
          			   | _ => None
          			 end
     }.
        
End ListFuncSum.

Section ListFuncInst.
  Context {typ : Type} {RType_typ : RType typ}.
  Context {func : Type} {H : ListFunc typ func}.
  Context {Heq : RelDec (@eq typ)} {HC : RelDec_Correct Heq}.
  
  Context {Typ2_tyArr : Typ2 _ Fun}.
  Context {Typ1_tyList : Typ1 _ list}.
  
  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ Typ2_tyArr.
  Let tyList : typ -> typ := @typ1 _ _ _ _.

  Global Instance ListFuncInst : ListFunc typ (list_func typ) := 
    {
      fNil := pNil;
      fCons := pCons;
      
      listS f := Some f
    }.

  Definition typeof_list_func lf :=
    match lf with
      | pNil t => Some (tyList t)
      | pCons t => Some (tyArr t (tyArr (tyList t) (tyList t)))
    end.

  Definition list_func_eq (a b : list_func typ) : option bool :=
    match a , b with
      | pNil t1, pNil t2 => Some (t1 ?[ eq ] t2)
      | pCons t1, pCons t2 => Some (t1 ?[ eq ] t2)
      | _, _ => None
    end.

  Global Instance RelDec_list_func : RelDec (@eq (list_func typ)) := 
    {
      rel_dec a b := match list_func_eq a b with 
    	  	       | Some b => b 
    		       | None => false 
    		     end
    }.

  Definition listE {A : Type} {t : typ} (e : typD t = A) : typD (tyList t) = list A :=
    eq_ind (typD t) (fun B : Type => typD (tyList t) = list B) (typ1_cast t) A e.

  Definition listD {t : typ} (lst : typD (tyList t)) : list (typD t) :=
    trmD lst (listE eq_refl).

  Definition listR {t : typ} (lst : list (typD t)) : typD (tyList t) :=
    trmR lst (listE eq_refl).

  Lemma trmDR_cons (t : typ) A B (x : A) (xs : list A) (e1 : typD t = A) (e2 : typD t = B) :
    (trmD (trmR (x :: xs) (listE e1)) (listE e2)) =
      trmD (trmR x e1) e2 :: trmD (trmR xs (listE e1)) (listE e2). 
  Proof.
    admit.
(*
    unfold trmD, trmR, listE, eq_ind, eq_rect_r, eq_rect, eq_sym, id.
    clear.
    pose proof (@typ1_cast typ RType_typ list _ t).
    unfold tyList.
    rewrite H in *.
    revert e1 e2.
    generalize (typ1_cast t).
    generalize dependent (typD t).
    intros; subst.
    destruct e2.
    revert e.
    rewrite H in *.
    SearchAbout typ1.
    unfold typ1.
    generalize dependent (typD (typ1 t)).
    generalize dependent (tyList t).
    
    generalize dependent (typD (tyList t)).
    generalize dependent (typD t); intros; repeat subst. reflexivity.
*)
  Admitted.

  Definition nilD t : typD (tyList t) := listR nil.
  Definition consD t : typD (tyArr t (tyArr (tyList t) (tyList t))) :=
    tyArrR2 (fun (x : typD t) (xs : typD (tyList t)) =>
               listR (cons x (trmD xs (listE eq_refl)))).

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
    end.

  Global Instance RSym_ListFunc : SymI.RSym (list_func typ) := 
    {
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
  Qed.

End ListFuncInst.

Section MakeList.
  Context {typ func : Type} {H : ListFunc typ func}.
  
  Definition mkNil t : expr typ func := Inj (fNil t).
  Definition mkCons (t : typ) (x xs : expr typ func) := App (App (fCons t) x) xs.
  
End MakeList.

Section ListFuncOk.
  Context {typ func : Type} {RType_typ : RType typ}.
  Context {LF: ListFunc typ func} {RSym_func : RSym func}.
  Context {RelDec_eq : RelDec (@eq typ)}.
  Context {Typ2_tyArr : Typ2 _ Fun}.
  Context {Typ1_tyList : Typ1 _ list}.

  Class ListFuncOk := {
    lf_funcAsOk (f : func) (e : list_func typ) : listS f = Some e -> 
      forall t, 
        funcAs f t = 
        funcAs (RSym_func := RSym_ListFunc) e t;
    lf_fNilOk t : listS (fNil t) = Some (pNil t);
    lf_fConsOk t : listS (fCons t) = Some (pCons t)
  }.

End ListFuncOk.

Implicit Arguments ListFuncOk [[LF] [RType_typ] [RSym_func] [RelDec_eq]
                               [Typ2_tyArr] [Typ1_tyList]].
                               
Section ListFuncBaseOk.
  Context {typ func : Type} {RType_typ : RType typ}.
  Context {LF: ListFunc typ func} {RSym_func : RSym func}.
  Context {RelDec_eq : RelDec (@eq typ)}.
  Context {RelDec_eqOk : RelDec_Correct RelDec_eq}.

  Context {Typ2_tyArr : Typ2 _ Fun}.
  Context {Typ1_tyList : Typ1 _ list}.
  
  Global Program Instance ListFuncBaseOk : 
  	ListFuncOk typ (RSym_func := RSym_ListFunc) (list_func typ) := {
    lf_funcAsOk := fun _ _ _ _ => eq_refl;
    lf_fNilOk t := eq_refl
  }.

End ListFuncBaseOk.

Section ListFuncExprOk.
  Context {typ func : Type} `{HOK : ListFuncOk typ func}.
  Context {HROk : RTypeOk}.
  Context {A : Type} {RSymA : RSym A}.
  Context {Typ2Ok_tyArr : Typ2Ok Typ2_tyArr}.
  Context {Typ1Ok_tyList : Typ1Ok Typ1_tyList}.
  Context {RSym_funcOk : RSymOk RSym_func0}.
  

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.
  Let tyList : typ -> typ  := @typ1 _ _ _ _.

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
    forward. rewrite <- r. reflexivity.
  Qed.

  Lemma lf_nil_type_eq tus tvs (e : expr typ func) t t' df
    (H1 : listS e = Some (pNil t)) (H2 : exprD' tus tvs t' e = Some df) :
    t' = tyList t.
  Proof.
    destruct e; simpl in *; try congruence.
    autorewrite with exprD_rw in H2; simpl in H2; forward; inv_all; subst.
    eapply lf_nil_func_type_eq; eassumption.
  Qed.

  Lemma list_nil_type_eq (f : func) (t u : typ) 
        (H1 : listS f = Some (pNil t)) (H2 : typeof_sym f = Some u) :
    u = tyList t.
  Proof.
    destruct (ExprFacts.typeof_expr_exprD' _ _ _ nil nil (Inj f) H2) as [x H].
    autorewrite with exprD_rw in H.
    simpl in H. forward.
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

  Lemma list_cons_type_eq (f : func) (t u : typ) 
        (H1 : listS f = Some (pCons t)) (H2 : typeof_sym f = Some u) :
    u = tyArr t (tyArr (tyList t) (tyList t)).
  Proof.
    destruct (ExprFacts.typeof_expr_exprD' _ _ _ nil nil (Inj f) H2) as [x H].
    autorewrite with exprD_rw in H.
    simpl in H. forward.
    eapply lf_cons_func_type_eq; eassumption.
  Qed.

End ListFuncExprOk.

Section MakeListFuncSound.
  Context {typ func : Type} `{HOK : ListFuncOk typ func}.
  Context {HROk : RTypeOk} {Typ2_tyArrOk : Typ2Ok Typ2_tyArr}
          {RSym_funcOk : RSymOk RSym_func0}.

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.
  Let tyList : typ -> typ := @typ1 _ _ _ _.
  
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

End MakeListFuncSound.

Section ListCases.
  Context {typ func : Type} {LF : ListFunc typ func}.

  Definition list_cases (e : expr typ func) (P : Type)
    (f_nil : P)
    (f_cons : expr typ func -> expr typ func -> P)
    (f_default : P) : P := 
    match e as e' return e = e' -> P with
      | Inj f => 
        match listS f as e'' return listS f = e'' -> e = Inj f -> P with
          | Some p => 
            match p as p' return listS (ListFunc := LF) (typ := typ) f = Some p' -> e = Inj f -> P with
              | pNil t => fun _ _ => f_nil
              | _ => fun _ _ => f_default
            end
          | _ => fun _ _ => f_default
        end eq_refl
      | App (App (Inj f) x) xs =>
        match listS f as e'' return listS f = e'' -> e = App (App (Inj f) x) xs -> P with
          | Some p => 
            match p as p' return listS (ListFunc := LF) (typ := typ) f = Some p' -> e = App (App (Inj f) x) xs -> P with
              | pCons t => fun _ _ => f_cons x xs
              | _ => fun _ _ => f_default
            end
          | _ => fun _ _ => f_default
        end eq_refl
      | _ => fun _ => f_default
    end eq_refl.
    
  Fixpoint list_length (e : expr typ func) : nat :=
    @list_cases e _
      0
      (fun _ xs => S (list_length xs))
      0.
    
End ListCases.      

Section ListCasesRules.
  Context {typ func : Type} {LF : ListFunc typ func}.
  Context {RType_typ : RType typ} {RTypeOk_typ : RTypeOk} {RSym_func : RSym func}.
  
  Context {HEq : RelDec (@eq typ)}.
    
  Context {Typ2_tyArr : Typ2 _ Fun}.
  Context {Typ1_tyList : Typ1 _ list}.
 
  Context {LFOk : ListFuncOk typ func}.

  Context {Typ2Ok_tyArr : Typ2Ok Typ2_tyArr}.
  Context {Typ1Ok_tyList : Typ1Ok Typ1_tyList}.
  Context {RSym_funcOk : RSymOk RSym_func}.

  Let tyList : typ -> typ  := @typ1 _ _ _ _.

  Lemma list_case tus tvs (t : typ) (e : expr typ func) (P : Type) (Q : P -> Prop)
    (f_nil : P) 
    (f_cons : expr typ func -> expr typ func -> P)
    (f_default : P) 
    (HType : typeof_expr tus tvs e = Some (tyList t))
    (Hdefault : Q f_default)
    (Hnil : forall f, listS f = Some (pNil t) -> e = Inj f -> Q f_nil)
    (Hcons : forall f x xs, 
               listS f = Some (pCons t) -> e = App (App (Inj f) x) xs ->
               typeof_expr tus tvs x = Some t -> typeof_expr tus tvs xs = Some (tyList t) ->
               TransitiveClosure.leftTrans (expr_acc (func := func)) x e ->
               TransitiveClosure.leftTrans (expr_acc (func := func)) xs e ->
               Q (f_cons x xs)) : 
    (Q (@list_cases typ func LF e P f_nil f_cons f_default)).
  Proof.
    destruct e; simpl; try apply Hdefault.
    { 
      destruct (listS f) eqn:Heq1; try apply Hdefault.
      destruct l eqn:Heq2; try apply Hdefault.
      simpl in HType.
      pose proof (list_nil_type_eq f Heq1 HType).
      apply typ1_inj in H; [|apply _]; unfold Rty in H; subst.
      eapply Hnil; [eassumption | reflexivity].
    } {
      destruct e1; simpl; try apply Hdefault.
      destruct e1_1; simpl; try apply Hdefault.
      destruct (listS f) eqn:Heq1; try apply Hdefault.
      destruct l eqn:Heq2; try apply Hdefault. subst.
      simpl in HType.
      forward.
      pose proof (list_cons_type_eq f Heq1 H); subst.
      
      apply ExprFacts.type_of_apply_Some in H2.
      apply typ2_inj in H2; [|apply _]; unfold Rty in H2; destruct H2; subst.
      apply ExprFacts.type_of_apply_Some in HType.
      apply typ2_inj in HType; [|apply _]; unfold Rty in HType; destruct HType; subst.
      apply typ1_inj in H3; [|apply _]; unfold Rty in H3; subst.
      
      eapply Hcons; try eassumption. 
      { reflexivity. }
      { apply TransitiveClosure.LTStep with (App (Inj f) e1_2); repeat constructor. }
      { repeat constructor. }
    }
  Qed.
 
End ListCasesRules.