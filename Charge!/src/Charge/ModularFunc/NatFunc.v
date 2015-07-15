Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Data.Map.FMapPositive.
Require Import ExtLib.Data.SumN.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.syms.SymEnv.
Require Import MirrorCore.syms.SymSum.
Require Import MirrorCore.Lambda.Expr.

Require Import Charge.ModularFunc.Denotation.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Inductive natFunc {typ : Type} :=
  | pPlus : natFunc
  | pMinus : natFunc
  | pMult : natFunc.

Implicit Arguments natFunc [].

Class NatFunc (typ func : Type) := {
  fPlus : func;
  fMinus : func;
  fMult :  func;

  natS : func -> option (natFunc typ)
}.

Section NatFuncSumN.
  Context {typ func : Type} {H : NatFunc typ func}.
  
  Global Instance NatFuncPMap (p : positive) (m : pmap Type) 
	 (pf : Some func = pmap_lookup' m p) :
    NatFunc typ (OneOf m) := 
    {
      fPlus := Into fPlus p pf;
      fMinus := Into fMinus p pf;
      fMult := Into fMult p pf;
      
      natS f :=
	match f with
	  | Build_OneOf _ p' pf1 =>
	    match Pos.eq_dec p p' with
	      | left Heq => 
	        natS (eq_rect_r (fun o => match o with | Some T => T | None => Empty_set end) pf1 
	                        (eq_rect _ (fun p =>  Some func = pmap_lookup' m p) pf _ Heq))
	      | right _ => None
	    end
	end
    }.
        
  Global Instance NatFuncExpr :
    NatFunc typ (expr typ func) := 
    {
      fPlus := Inj fPlus;
      fMinus := Inj fMinus;
      fMult := Inj fMult;
      
      natS f := match f with
    	  	  | Inj f => natS f
    	  	  | _     => None
    	  	end
    }.

End NatFuncSumN.

Section NatFuncInst.
  Context {typ : Type} {RType_typ : RType typ}.
  Context {func : Type} {H : NatFunc typ func}.
  Context {Heq : RelDec (@eq typ)} {HC : RelDec_Correct Heq}.
  
  Context {Typ2_tyArr : Typ2 _ Fun}.
  Context {Typ0_tyNat : Typ0 _ nat}.

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ Typ2_tyArr.
  Let tyNat : typ := @typ0 _ _ _ Typ0_tyNat.

  Global Instance BaseFuncInst : NatFunc typ (natFunc typ) := 
    {
      fPlus := pPlus;
      fMinus := pMinus;
      fMult := pMult;
      
      natS := Some
    }.

  Definition typeofNatFunc (nf : natFunc typ) : option typ :=
    match nf with
      | pPlus => Some (tyArr tyNat (tyArr tyNat tyNat))
      | pMinus => Some (tyArr tyNat (tyArr tyNat tyNat))
      | pMult => Some (tyArr tyNat (tyArr tyNat tyNat))
   end.
  
  Definition natFuncEq (a b : natFunc typ) : option bool :=
    match a , b with
    | pPlus, pPlus => Some true
    | pMinus, pMinus => Some true
    | pMult, pMult => Some true

    | _, _ => None
  end.
	
  Definition natR (n : nat) : typD tyNat :=
    trmR n (typ0_cast (Typ0 := Typ0_tyNat)).

  Definition natD (n : typD tyNat) : nat :=
    trmD n (typ0_cast (Typ0 := Typ0_tyNat)).

  Definition plusD : typD (tyArr tyNat (tyArr tyNat tyNat)) :=
    tyArrR2 (fun a b => natR ((natD a) + (natD b))).

  Definition minusD : typD (tyArr tyNat (tyArr tyNat tyNat)) :=
    tyArrR2 (fun a b => natR ((natD a) - (natD b))).

  Definition multD : typD (tyArr tyNat (tyArr tyNat tyNat)) :=
    tyArrR2 (fun a b => natR ((natD a) * (natD b))).

  Definition base_func_symD bf :=
    match bf as bf return match typeofNatFunc bf return Type with
			    | Some t => typD t
			    | None => unit
			  end with
      | pPlus => plusD
      | pMinus => minusD
      | pMult => multD
    end.
  
  Global Instance RSym_NatFunc
  : SymI.RSym (natFunc typ) := 
    {
      typeof_sym := typeofNatFunc;
      symD := base_func_symD ;
      sym_eqb := natFuncEq
    }.
  
  Global Instance RSymOk_NatFunc : SymI.RSymOk RSym_NatFunc.
  Proof.
    split; intros.
    destruct a, b; simpl; reflexivity.
  Qed.

End NatFuncInst.

Section MakeNat.
  Context {typ func : Type} {RType_typ : RType typ}.
  Context {NF : NatFunc typ func}.

  Definition mkPlus (m n : expr typ func) := App (App (Inj fPlus) m) n.
  Definition mkMinus (m n : expr typ func) := App (App (Inj fMinus) m) n.
  Definition mkMult (m n : expr typ func) := App (App (Inj fMult) m) n.

End MakeNat.

Section NatFuncOk.
  Context {typ func : Type} {RType_typ : RType typ}.
  Context {NF: NatFunc typ func} {RSym_func : RSym func}.

  Context {Typ2_tyArr : Typ2 _ Fun}.
  Context {Typ0_tyNat : Typ0 _ nat}.

  Class NatFuncOk := 
    {
      nf_funcAsOk (f : func) (e : @natFunc typ) : 
        natS f = Some e -> 
        forall t, 
          funcAs f t = funcAs (RSym_func := RSym_NatFunc) e t;
      nf_fPlusOk : natS fPlus = Some pPlus;
      nf_fMinusOk : natS fMinus = Some pMinus;
      nf_fMultOk : natS fMult = Some pMult
  }.

End NatFuncOk.

Implicit Arguments NatFuncOk [[NF] [RType_typ] [RSym_func] 
                               [Typ2_tyArr] [Typ0_tyNat]].

Section NatFuncBaseOk.
  Context {typ func : Type} {RType_typ : RType typ}.
  Context {NF: NatFunc typ func} {RSym_func : RSym func}.

  Context {Typ2_tyArr : Typ2 _ Fun}.
  Context {Typ0_tyNat : Typ0 _ nat}.
  
  Global Program Instance BaseFuncBaseOk : 
  	NatFuncOk typ (RSym_func := RSym_NatFunc) (natFunc typ) := {
    nf_funcAsOk := fun _ _ _ _ => eq_refl;
    nf_fPlusOk := eq_refl;
    nf_fMinusOk := eq_refl;
    nf_fMultOk := eq_refl
  }.

End NatFuncBaseOk.

Section NatFuncExprOk.
  Context {typ func : Type} `{HOK : NatFuncOk typ func}.
  Context {HROk : RTypeOk}.
  Context {A : Type} {RSymA : RSym A}.

  Context {Typ2_tyArrOk : Typ2Ok Typ2_tyArr}
          {RSym_funcOk : RSymOk RSym_func0}.

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.
  Let tyNat : typ := @typ0 _ _ _ _.

  Lemma BaseFunc_typeOk (f : func) (e : natFunc typ) (H : natS f = Some e) :
    typeof_sym f = typeofNatFunc e.
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
  
  

  Lemma nf_typeof_plus : typeof_sym fPlus = Some (tyArr tyNat (tyArr tyNat tyNat)).
  Proof.
    pose proof (BaseFunc_typeOk _ nf_fPlusOk).
    rewrite H. reflexivity.
  Qed.
  
  Lemma nf_typeof_minus : typeof_sym fMinus = Some (tyArr tyNat (tyArr tyNat tyNat)).
  Proof.
    pose proof (BaseFunc_typeOk _ nf_fMinusOk).
    rewrite H. reflexivity.
  Qed.
  
  Lemma nf_typeof_mult : typeof_sym fMult = Some (tyArr tyNat (tyArr tyNat tyNat)).
  Proof.
    pose proof (BaseFunc_typeOk _ nf_fMultOk).
    rewrite H. reflexivity.
  Qed.
  
  Lemma nf_plus_func_type_eq (f : func) t df
    (H1 : natS f = Some pPlus) (H2 : funcAs f t = Some df) :
    t = tyArr tyNat (tyArr tyNat tyNat).
  Proof.
    rewrite (nf_funcAsOk _ H1) in H2.
    unfold funcAs in H2; simpl in *.
    forward.
    rewrite <- r. reflexivity.
  Qed.

  Lemma nf_minus_func_type_eq (f : func) t df
    (H1 : natS f = Some pMinus) (H2 : funcAs f t = Some df) :
    t = tyArr tyNat (tyArr tyNat tyNat).
  Proof.
    rewrite (nf_funcAsOk _ H1) in H2.
    unfold funcAs in H2; simpl in *.
    forward.
    rewrite <- r. reflexivity.
  Qed.

  Lemma nf_mult_func_type_eq (f : func) t df
    (H1 : natS f = Some pPlus) (H2 : funcAs f t = Some df) :
    t = tyArr tyNat (tyArr tyNat tyNat).
  Proof.
    rewrite (nf_funcAsOk _ H1) in H2.
    unfold funcAs in H2; simpl in *.
    forward.
    rewrite <- r. reflexivity.
  Qed.

End NatFuncExprOk.

Section TypeOfFunc.
  Context {typ func : Type}.
  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {RSym_func : RSym func}.
  
  Lemma typeof_funcAs f t e (H : funcAs f t = Some e) : typeof_sym f = Some t.
  Proof.
    unfold funcAs in H.
    generalize dependent (symD f).
    destruct (typeof_sym f); intros; [|congruence].
    destruct (type_cast t0 t); [|congruence].
    destruct r; reflexivity.
  Qed.
    
  Lemma funcAs_Some f t (pf : typeof_sym f = Some t) :
    funcAs f t =
    Some (match pf in (_ = z)
      return match z with
               | Some z' => typD z'
               | None => unit
             end
      with
      | eq_refl => symD f
      end).
  Proof.
    unfold funcAs.
    generalize (symD f).
    rewrite pf. intros.
    rewrite type_cast_refl. reflexivity. apply _.
  Qed.

End TypeOfFunc.

Section MakeNatFuncSound.
  Context {typ func : Type} `{HOK : NatFuncOk typ func}.
  Context {RTypeOk_typ : RTypeOk} {Typ2_tyArrOk : Typ2Ok Typ2_tyArr}
          {RSym_funcOk : RSymOk RSym_func0}.

  Let tyNat : typ := @typ0 _ _ _ _.
  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.

  Lemma nf_plus_func_eq (n : nat) (f : func) (fD : typD (tyArr tyNat (tyArr tyNat tyNat)))
    (Ho : natS f = Some pPlus)
    (Hf : funcAs f (tyArr tyNat (tyArr tyNat tyNat)) = Some fD) :
    fD = plusD.
  Proof.
   rewrite (nf_funcAsOk _ Ho) in Hf.
   unfold funcAs in Hf; simpl in *.
   rewrite type_cast_refl in Hf; [|apply RTypeOk_typ].
   unfold Rcast, Relim_refl in Hf.
   inversion Hf. reflexivity.
  Qed.

  Lemma nf_minus_func_eq (n : nat) (f : func) (fD : typD (tyArr tyNat (tyArr tyNat tyNat)))
    (Ho : natS f = Some pMinus)
    (Hf : funcAs f (tyArr tyNat (tyArr tyNat tyNat)) = Some fD) :
    fD = minusD.
  Proof.
   rewrite (nf_funcAsOk _ Ho) in Hf.
   unfold funcAs in Hf; simpl in *.
   rewrite type_cast_refl in Hf; [|apply RTypeOk_typ].
   unfold Rcast, Relim_refl in Hf.
   inversion Hf. reflexivity.
  Qed.

  Lemma nf_mult_func_eq (n : nat) (f : func) (fD : typD (tyArr tyNat (tyArr tyNat tyNat)))
    (Ho : natS f = Some pMult)
    (Hf : funcAs f (tyArr tyNat (tyArr tyNat tyNat)) = Some fD) :
    fD = multD.
  Proof.
   rewrite (nf_funcAsOk _ Ho) in Hf.
   unfold funcAs in Hf; simpl in *.
   rewrite type_cast_refl in Hf; [|apply RTypeOk_typ].
   unfold Rcast, Relim_refl in Hf.
   inversion Hf. reflexivity.
  Qed.

  Lemma mkPlus_sound (tus tvs : tenv typ) a b
    (aD : ExprI.exprT tus tvs (typD tyNat)) 
    (bD : ExprI.exprT tus tvs (typD tyNat)) 
    (Ha : exprD' tus tvs tyNat a = Some aD) 
    (Hb : exprD' tus tvs tyNat b = Some bD)  :
    exprD' tus tvs tyNat (mkPlus a b) = Some (exprT_App (exprT_App (fun _ _ => plusD) aD) bD).
  Proof.
    unfold mkPlus; simpl.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ b _ Hb).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ a _ Ha).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    pose proof nf_fPlusOk as Ho.
    pose proof (nf_funcAsOk _ Ho) as H1.
    rewrite H1. unfold funcAs; simpl.
    rewrite type_cast_refl; [reflexivity | apply _].
  Qed.

  Lemma mkMinus_sound (tus tvs : tenv typ) a b
    (aD : ExprI.exprT tus tvs (typD tyNat)) 
    (bD : ExprI.exprT tus tvs (typD tyNat)) 
    (Ha : exprD' tus tvs tyNat a = Some aD) 
    (Hb : exprD' tus tvs tyNat b = Some bD)  :
    exprD' tus tvs tyNat (mkMinus a b) = Some (exprT_App (exprT_App (fun _ _ => minusD) aD) bD).
  Proof.
    unfold mkMinus; simpl.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ b _ Hb).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ a _ Ha).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    pose proof nf_fMinusOk as Ho.
    pose proof (nf_funcAsOk _ Ho) as H1.
    rewrite H1. unfold funcAs; simpl.
    rewrite type_cast_refl; [reflexivity | apply _].
  Qed.

  Lemma mkMult_sound (tus tvs : tenv typ) a b
    (aD : ExprI.exprT tus tvs (typD tyNat)) 
    (bD : ExprI.exprT tus tvs (typD tyNat)) 
    (Ha : exprD' tus tvs tyNat a = Some aD) 
    (Hb : exprD' tus tvs tyNat b = Some bD)  :
    exprD' tus tvs tyNat (mkMult a b) = Some (exprT_App (exprT_App (fun _ _ => multD) aD) bD).
  Proof.
    unfold mkMult; simpl.
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ b _ Hb).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    rewrite (ExprTac.exprD_typeof_Some _ _ _ a _ Ha).
    autorewrite with exprD_rw; simpl; forward; inv_all; subst.
    pose proof nf_fMultOk as Ho.
    pose proof (nf_funcAsOk _ Ho) as H1.
    rewrite H1. unfold funcAs; simpl.
    rewrite type_cast_refl; [reflexivity | apply _].
  Qed.

End MakeNatFuncSound.
