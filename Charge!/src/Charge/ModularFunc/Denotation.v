Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.Lambda.Expr.

Section TrmDR.
  Context {typ : Type} {RType_typ : RType typ}.
  
  Definition trmD {A B : Type} (p : A) (e : A = B) : B :=
    eq_rect _ id p _ e.
    
  Definition trmR {A B : Type} (p : B) (e : A = B) : A :=
    eq_rect_r id p e.
     
  Lemma trmDR {A B : Type} (p : B) (e : A = B) : trmD (trmR p e) e = p.
  Proof.
    subst. reflexivity.
  Qed.
    
  Lemma trmRD {A B : Type} (p : A) (e : A = B) : trmR (trmD p e) e = p.
  Proof.
    subst. reflexivity.
  Qed.
    
End TrmDR.

Section Denotation.
  Context {typ : Type} {RType_typ : RType typ}.
  Context {Typ2_tyArr : Typ2 _ Fun}.

  Let tyArr := @typ2 _ _ _ _.

  Definition funE {A B : Type} {t u : typ} (e1 : typD t = A) (e2 : typD u = B) : typD (tyArr t u) = (A -> B) :=
    eq_ind (typD t) (fun X : Type => typD (tyArr t u) = (X -> B))
      (eq_ind (typD u) (fun Y : Type => typD (tyArr t u) = (typD t -> Y))
         (typ2_cast t u) B e2) A e1.
         
  Definition tyArrD' {a b : typ} (f : typD (tyArr a b)) e1 e2 : typD a -> typD b :=
    trmD f (funE e1 e2).

  Program Definition tyArrD2' {a b c : typ} (f : typD (tyArr a (tyArr b c))) e1 e2 e3 : 
    typD a -> typD b -> typD c := 
    fun a b => tyArrD' (tyArrD' f e1 e2 a) eq_refl e3 b.

  Program Definition tyArrD3' {a b c d : typ} (f : typD (tyArr a (tyArr b (tyArr c d)))) 
    e1 e2 e3 e4 : typD a -> typD b -> typD c -> typD d := 
    fun a b c => tyArrD' (tyArrD' (tyArrD' f e1 e2 a) eq_refl e3 b) eq_refl e4 c.

  Program Definition tyArrD4' {a b c d e : typ} (f : typD (tyArr a (tyArr b (tyArr c (tyArr d e))))) 
    e1 e2 e3 e4 e5 : typD a -> typD b -> typD c -> typD d -> typD e := 
    fun a b c d => tyArrD' (tyArrD' (tyArrD' (tyArrD' f e1 e2 a) eq_refl e3 b) eq_refl e4 c) eq_refl e5 d.

  Definition tyArrD {a b : typ} (f : typD (tyArr a b)) : typD a -> typD b :=
    tyArrD' f eq_refl eq_refl.

  Program Definition tyArrD2 {a b c : typ} (f : typD (tyArr a (tyArr b c)))  : 
    typD a -> typD b -> typD c := tyArrD2' f eq_refl eq_refl eq_refl.
    
  Program Definition tyArrD3 {a b c d : typ} (f : typD (tyArr a (tyArr b (tyArr c d)))) 
    : typD a -> typD b -> typD c -> typD d := tyArrD3' f eq_refl eq_refl eq_refl eq_refl.

  Program Definition tyArrD4 {a b c d e : typ} (f : typD (tyArr a (tyArr b (tyArr c (tyArr d e))))) 
    : typD a -> typD b -> typD c -> typD d -> typD e := 
	  tyArrD4' f eq_refl eq_refl eq_refl eq_refl eq_refl.


	  
  Definition tyArrR' {a b : typ} (f : typD a -> typD b) e1 e2 : typD (tyArr a b) :=
    trmR f (funE e1 e2).  

  Definition tyArrR2' {a b c : typ} (f : typD a -> typD b -> typD c) e1 e2 e3 : 
    typD (tyArr a (tyArr b c)) :=
    tyArrR' (fun a => tyArrR' (f a) e2 e3) eq_refl e1. 

  Definition tyArrR3' {a b c d : typ} (f : typD a -> typD b -> typD c -> typD d) e1 e2 e3 e4 : 
    typD (tyArr a (tyArr b (tyArr c d))) :=
    tyArrR' (fun a => tyArrR' (fun b => tyArrR' (f a b) e3 e4) eq_refl e2) eq_refl e1. 

  Definition tyArrR4' {a b c d e : typ} (f : typD a -> typD b -> typD c -> typD d -> typD e) 
    e1 e2 e3 e4 e5 : typD (tyArr a (tyArr b (tyArr c (tyArr d e)))) :=
    tyArrR' (fun a => tyArrR' (fun b => tyArrR' (fun c => tyArrR' (f a b c) e5 e4) eq_refl e3) eq_refl e2) eq_refl e1. 

  Definition tyArrR {a b : typ} (f : typD a -> typD b) : typD (tyArr a b) :=
    tyArrR' f eq_refl eq_refl.
    
  Definition tyArrR2 {a b c : typ} (f : typD a -> typD b -> typD c) : 
    typD (tyArr a (tyArr b c)) :=
    tyArrR2' f eq_refl eq_refl eq_refl.

  Definition tyArrR3 {a b c d : typ} (f : typD a -> typD b -> typD c -> typD d) : 
    typD (tyArr a (tyArr b (tyArr c d))) :=
    tyArrR3' f eq_refl eq_refl eq_refl eq_refl.

  Definition tyArrR4 {a b c d e : typ} (f : typD a -> typD b -> typD c -> typD d -> typD e) 
    : typD (tyArr a (tyArr b (tyArr c (tyArr d e)))) :=
    tyArrR4' f eq_refl eq_refl eq_refl eq_refl eq_refl.

  Lemma exprT_App_wrap_tyArrD tus tvs (t u : typ) (f : exprT tus tvs (typD (tyArr t u))) (a : exprT tus tvs (typD t)) :
    exprT_App f a = fun us vs => (tyArrD (f us vs)) (a us vs).
  Proof.
    unfold tyArrD, tyArrD', trmD, funE, exprT_App, eq_rect_r, eq_sym, eq_rect.
    unfold tyArr in *.
    generalize (typ2_cast t u).
    generalize dependent (typ2 t u).
    intros.
    generalize dependent (typD t0).
    intros. subst. reflexivity.
  Qed.

End Denotation.
