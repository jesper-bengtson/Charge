Add Rec LoadPath "/Users/jebe/git/coq-ext-lib/theories" as ExtLib.
Add Rec LoadPath "/Users/jebe/git/mirror-core/theories" as MirrorCore.
Add Rec LoadPath "/Users/jebe/git/Charge/Charge!/bin/Charge" as Charge.

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
Require Import Charge.ModularFunc.Denotation.

Require Import Coq.Strings.String.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Inductive pair_func {typ : Type} :=
  | pPair : typ -> typ -> pair_func.

Implicit Arguments pair_func [].

Class PairFunc (typ func : Type) := {
  fPair : typ -> typ -> func;
  
  pairS : func -> option (pair_func typ)
}.

Section PairFuncSum.
  Context {typ func : Type} {H : PairFunc typ func}.
	
  Global Instance PairFuncPMap (p : positive) (m : pmap Type) 
	 (pf : Some func = pmap_lookup' m p) :
    PairFunc typ (OneOf m) := 
    {
      fPair t u := Into (fPair t u) p pf;
      
      pairS f :=
	match f with
	  | Build_OneOf _ p' pf1 =>
	    match Pos.eq_dec p p' with
	      | left Heq => 
	        pairS (eq_rect_r (fun o => match o with | Some T => T | None => Empty_set end) pf1 
	                         (eq_rect _ (fun p =>  Some func = pmap_lookup' m p) pf _ Heq))
	      | right _ => None
	    end
	end
    }.

  Global Instance PairFuncExpr :
    PairFunc typ (expr typ func) := 
    {
      fPair t1 t2 := Inj (fPair t1 t2);
      pairS f := match f with
    	  	   | Inj f => pairS f
    	  	   | _     => None
    	  	 end
    }.

End PairFuncSum.

Section PairFuncInst.
  Context {typ : Type} {HR : RType typ}.
  Context {func : Type} {H : PairFunc typ func}.
  Context {RelDec_typ : RelDec (@eq typ)}.
  Context {RelDecCorrect_typ : RelDec_Correct RelDec_typ}.
  
  Context {Typ2_tyArr : Typ2 _ Fun}.
  Context {Typ2_tyProd : Typ2 _ prod}.
  
  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ Typ2_tyArr.
  Let tyProd : typ -> typ -> typ := @typ2 _ _ _ Typ2_tyProd.

  Global Instance PairFuncInst : PairFunc typ (pair_func typ) := 
    {
      fPair := pPair;
      pairS f := Some f 
    }.

  Definition typeof_pair_func pf :=
    match pf with
      | pPair t1 t2 => Some (tyArr t1 (tyArr t2 (tyProd t1 t2)))
    end.
  
  Definition pair_func_eq (a b : pair_func typ) : option bool :=
    match a , b with
      | pPair t1 t2, pPair t3 t4 => Some (t1 ?[ eq ] t3 &&
	      				     t2 ?[ eq ] t4)%bool
    end.

  Definition pairE {A B : Type} {t u : typ} (e1 : typD t = A) (e2 : typD u = B) : 
    typD (tyProd t u) = (A * B)%type :=
    eq_ind (typD t) (fun X : Type => typD (tyProd t u) = (X * B)%type)
      (eq_ind (typD u) (fun Y : Type => typD (tyProd t u) = (typD t * Y)%type)
              (typ2_cast t u) B e2) A e1.
  
  
  Definition prodD t u (p : typD (tyProd t u)) : typD t * typD u :=
    trmD p (pairE (t := t) (u := u) eq_refl eq_refl).
  
  Definition prodR t u (p : typD t * typD u) : typD (tyProd t u) :=
    trmR p (pairE (t := t) (u := u) eq_refl eq_refl).
  
  Lemma prodDR (t u : typ) A B C D (x : A) (y : B) (e1 : typD t = A) 
        (e2 : typD u = B) (e3 : typD t = C) (e4 : typD u = D) :
    trmD (trmR (x, y) (pairE e1 e2)) (pairE e3 e4) = 
    (trmD (trmR x e1) e3, trmD (trmR y e2) e4).
  Proof.
    unfold trmD, trmR, pairE, eq_ind, eq_rect_r, eq_rect, eq_sym, id.
    clear.
    revert e1 e2 e3 e4.
    generalize (typ2_cast t u).
    unfold tyProd.
    generalize dependent (typ2 t u).
    generalize dependent (typD t).
    generalize dependent (typD u).
    do 3 intros.
    generalize dependent (typD t0).
    intros; repeat subst. reflexivity.
  Qed.

  Definition pairD (t u : typ) : typD (tyArr t (tyArr u (tyProd t u))) :=
    (tyArrR2 (fun a b => prodR t u (a, b))).
  
  Definition pair_func_symD bf :=
    match bf as bf return match typeof_pair_func bf return Type with
			    | Some t => typD t
			    | None => unit
			  end with
      | pPair t u => pairD t u
    end.

  Global Instance RSym_PairFunc
  : SymI.RSym (pair_func typ) := 
    {
      typeof_sym := typeof_pair_func;
      symD := pair_func_symD ;
      sym_eqb := pair_func_eq
    }.
  
  Global Instance RSymOk_PairFunc : SymI.RSymOk RSym_PairFunc.
  Proof.
    split; intros.
    destruct a, b; simpl; try apply I.
    + consider (t ?[ eq ] t1 && t0 ?[ eq ] t2)%bool;
      intuition congruence.
  Qed.
  
End PairFuncInst.

Section MakePair.
  Context {typ func : Type} {RType_typ : RType typ}.
  Context {HF : PairFunc typ func}.
  
  Definition mkPair t u a b := App (App (fPair t u) a) b.
  
End MakePair.

Section PairFuncOk.
  Context {typ func : Type} {RType_typ : RType typ}.
  Context {BF: PairFunc typ func} {RSym_func : RSym func}.
  Context {RelDec_eq : RelDec (@eq typ)}.
  Context {RelDec_eqOk : RelDec_Correct RelDec_eq}.
  
  Context {Typ2_tyArr : Typ2 _ Fun}.
  Context {Typ2_tyProd : Typ2 _ prod}.
  
  Class PairFuncOk := 
    {
      bf_funcAsOk (f : func) (e : @pair_func typ) : 
        pairS f = Some e -> 
        forall t, funcAs f t = 
                  funcAs (RSym_func := RSym_PairFunc) e t;
      bf_fPairOk t u : pairS (fPair t u) = Some (pPair t u)
    }.
  
End PairFuncOk.

Implicit Arguments PairFuncOk [[BF] [RType_typ] [RSym_func] [RelDec_eq]
                                    [Typ2_tyArr] [Typ2_tyProd]].

Section PairFuncBaseOk.
  Context {typ func : Type} {RType_typ : RType typ}.
  Context {BF: PairFunc typ func} {RSym_func : RSym func}.
  Context {RelDec_eq : RelDec (@eq typ)}.
  Context {RelDec_eqOk : RelDec_Correct RelDec_eq}.
  
  Context {Typ2_tyArr : Typ2 _ Fun}.
  Context {Typ2_Pair : Typ2 _ prod}.
  
  Global Program Instance PairFuncBaseOk : 
    PairFuncOk typ (RSym_func := RSym_PairFunc) (pair_func typ) := 
    {
      bf_funcAsOk := fun _ _ _ _ => eq_refl;
      bf_fPairOk t u := eq_refl
    }.

End PairFuncBaseOk.

Section PairFuncExprOk.
  Context {typ func : Type} `{HOK : PairFuncOk typ func}.
  Context {HROk : RTypeOk}.
  Context {A : Type} {RSymA : RSym A}.
  
  Context {Typ2_tyArrOk : Typ2Ok Typ2_tyArr}
          {RSym_funcOk : RSymOk RSym_func0}.
  
  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ Typ2_tyArr.
  Let tyProd : typ -> typ -> typ := @typ2 _ _ _ Typ2_tyProd.
  
  Lemma BaseFunc_typeOk (f : func) (e : pair_func typ) (H : pairS f = Some e) :
    typeof_sym f = typeof_pair_func e.
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
  
  Lemma bf_pair_func_type_eq (f : func) t u v df
        (H1 : pairS f = Some (pPair t u)) (H2 : funcAs f v = Some df) :
    v = tyArr t (tyArr u (tyProd t u)).
  Proof.
    rewrite (bf_funcAsOk _ H1) in H2.
    unfold funcAs in H2; simpl in *.
    forward.
    rewrite <- r; reflexivity.
  Qed.
  
  Lemma pair_func_type_eq (f : func) (t u v : typ) 
        (H1 : pairS f = Some (pPair t u)) (H2 : typeof_sym f = Some v) :
    v = tyArr t (tyArr u (tyProd t u)).
  Proof.
    SearchAbout typeof_expr exprD'.
    destruct (ExprFacts.typeof_expr_exprD' _ _ _ nil nil (Inj f) H2) as [x H].
    autorewrite with exprD_rw in H.
    simpl in H. forward.
    eapply bf_pair_func_type_eq; eassumption.
  Qed.
  
  Lemma bf_pair_type_eq tus tvs (e : expr typ func) t u v df
        (H1 : pairS e = Some (pPair t u)) (H2 : exprD' tus tvs v e = Some df) :
    v = tyArr t (tyArr u (tyProd t u)).
  Proof.
    destruct e; simpl in *; try congruence.
    autorewrite with exprD_rw in H2; simpl in H2; forward; inv_all; subst.
    apply (bf_pair_func_type_eq _ _ H1 H).
  Qed.
  
End PairFuncExprOk.

Section MakePairFuncSound.
  Context {typ func : Type} `{HOK : PairFuncOk typ func}.
  Context {HROk : RTypeOk} {Typ2_tyArrOk : Typ2Ok Typ2_tyArr}
          {RSym_funcOk : RSymOk RSym_func0}.
  
  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ Typ2_tyArr.
  Let tyProd : typ -> typ -> typ := @typ2 _ _ _ Typ2_tyProd.
  
  Lemma bf_pair_func_eq (t u : typ) (f : func) (fD : typD (tyArr t (tyArr u (tyProd t u))))
        (Ho : pairS f = Some (pPair t u))
        (Hf : funcAs f (tyArr t (tyArr u (tyProd t u))) = Some fD) :
    fD = pairD t u.
  Proof.
    rewrite (bf_funcAsOk _ Ho) in Hf.
    unfold funcAs in Hf; simpl in *.
    rewrite type_cast_refl in Hf; [|apply HROk].
    unfold Rcast, Relim_refl in Hf.
    inversion Hf. reflexivity.
  Qed.
  
  Lemma bf_pair_eq tus tvs (t u : typ) (e : expr typ func) 
        (eD : ExprI.exprT tus tvs (typD (tyArr t (tyArr u (tyProd t u)))))
        (Ho : pairS e = Some (pPair t u))
        (Hf : exprD' tus tvs (tyArr t (tyArr u (tyProd t u))) e = Some eD) :
    eD = (fun us vs => pairD t u).
  Proof.
    destruct e; simpl in *; try congruence.
    autorewrite with exprD_rw in Hf; simpl in Hf; forward; inv_all; subst.
    rewrite (bf_pair_func_eq _ Ho H); reflexivity.
  Qed.
  
  Lemma mkPair_sound (t u : typ) (tus tvs : tenv typ) a b
        (aD : ExprI.exprT tus tvs (typD t)) 
        (bD : ExprI.exprT tus tvs (typD u)) 
        (Ha : exprD' tus tvs t a = Some aD) 
        (Hb : exprD' tus tvs u b = Some bD)  :
    exprD' tus tvs (tyProd t u) (mkPair t u a b) = 
    Some (exprT_App (exprT_App (fun _ _ => pairD t u) aD) bD).
  Proof.
    unfold mkPair; simpl.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ b _ Hb).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ a _ Ha).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    pose proof (bf_fPairOk t u) as Ho.
    pose proof (bf_funcAsOk _ Ho) as H1.
    rewrite H1. unfold funcAs; simpl.
    rewrite type_cast_refl; [reflexivity | apply _].
  Qed.
  
End MakePairFuncSound.

Section PairCases.
  Context {typ func : Type} {LF : PairFunc typ func}.
  
  Definition pair_cases (e : expr typ func) (P : expr typ func -> Type)
             (f_prod : forall t u f a b, pairS f = Some (pPair t u) -> P (App (App (Inj f) a) b))
             (f_default : P e) : P e := 
    match e as e' return e = e' -> P e with
      | App (App (Inj f) a) b =>
        match pairS f as e'' return pairS f = e'' -> e = App (App (Inj f) a) b -> P e with
          | Some p => 
            match p as p' return pairS f = Some p' -> e = App (App (Inj f) a) b -> P e with
              | pPair t u => fun eq1 eq2 => eq_rect_r P (f_prod t u f a b eq1) eq2
            end
          | _ => fun _ _ => f_default
        end eq_refl
      | _ => fun _ => f_default
    end eq_refl.
  
End PairCases.      

Section PairInversion.
  Context {typ func : Type} {PF : PairFunc typ func}.
  Context {RType_typ : RType typ} {RTypeOk_typ : RTypeOk} {RSym_func : RSym func}.
  
  Context {HEq : RelDec (@eq typ)}.
    
  Context {Typ2_tyArr : Typ2 _ Fun}.
  Context {Typ2_tyProd : Typ2 _ prod}.
 
  Context {Typ2Ok_tyArr : Typ2Ok Typ2_tyArr}.
  Context {Typ2Ok_tyProd : Typ2Ok Typ2_tyProd}.
 
  Context {PFOk : PairFuncOk typ func}.
  Context {RSym_funcOk : RSymOk RSym_func}.

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ Typ2_tyArr.
  Let tyProd : typ -> typ -> typ := @typ2 _ _ _ Typ2_tyProd.

  Lemma pair_case tus tvs (t u : typ) (e : expr typ func) (P : expr typ func -> Type) (Q : forall e, P e -> Prop)
    (f_pair : forall t u f a b, pairS f = Some (pPair t u) -> P (App (App (Inj f) a) b))
    (f_default : P e) 
    (HType : typeof_expr tus tvs e = Some (tyProd t u))
    (Hdefault : Q e (f_default))
    (Hcons : forall f a b (eq1 : pairS f = Some (pPair t u)), 
               typeof_expr tus tvs a = Some t -> typeof_expr tus tvs b = Some u ->
               TransitiveClosure.leftTrans (expr_acc (func := func)) a e ->
               TransitiveClosure.leftTrans (expr_acc (func := func)) b e ->
               Q (App (App (Inj f) a) b) (f_pair t u f a b eq1)) : 
    (Q e (@pair_cases typ func PF e P f_pair f_default)).
  Proof.
    destruct e; simpl; try apply Hdefault.
    destruct e1; simpl; try apply Hdefault.
    destruct e1_1; simpl; try apply Hdefault.
    generalize (@eq_refl _ (pairS f)).
    change (let x := pairS f in 
            forall e : pairS f = x,
              Q (App (App (Inj f) e1_2) e2)
                (match
                    x as e''
                    return
                    (pairS f = e'' ->
                     App (App (Inj f) e1_2) e2 = App (App (Inj f) e1_2) e2 ->
                     P (App (App (Inj f) e1_2) e2))
                  with
                    | Some p =>
                      match
                        p as p'
                        return
                        (pairS f = Some p' ->
                         App (App (Inj f) e1_2) e2 = App (App (Inj f) e1_2) e2 ->
                         P (App (App (Inj f) e1_2) e2))
                      with
                        | pPair t0 u0 =>
                          fun (eq1 : pairS f = Some (pPair t0 u0))
                              (eq2 : App (App (Inj f) e1_2) e2 = App (App (Inj f) e1_2) e2)
                          => eq_rect_r P (f_pair t0 u0 f e1_2 e2 eq1) eq2
                      end
                    | None =>
                      fun (_ : pairS f = None)
                          (_ : App (App (Inj f) e1_2) e2 = App (App (Inj f) e1_2) e2) =>
                        f_default
                  end e eq_refl)).
    destruct x; intros; try apply Hdefault.
    destruct p.
    unfold eq_rect_r, eq_rect, eq_sym.
    simpl in HType; forward; inv_all; subst.
    assert (t4 = tyArr t0 (tyArr t1 (tyProd t0 t1)))  
      by (eapply pair_func_type_eq; eassumption).
    subst.

    apply ExprFacts.type_of_apply_Some in H2.
    apply typ2_inj in H2; [|apply _].
    destruct H2.
    unfold Rty in *. subst.
    apply ExprFacts.type_of_apply_Some in HType.
    apply typ2_inj in HType; [|apply _].
    destruct HType.
    apply typ2_inj in H3; [|apply _].
    destruct H3.
    unfold Rty in *; subst. subst.
    apply Hcons. assumption. assumption.
    apply TransitiveClosure.LTStep with (App (Inj f) e1_2); repeat constructor.
    repeat constructor.
  Qed.
 
End PairInversion.
