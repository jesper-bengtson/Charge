Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.Lambda.Expr.

Section Denotation.
  Context {typ : Type} {RType_typ : RType typ}.
  Context {Typ2_tyArr : Typ2 _ Fun}.

  Let tyArr := @typ2 _ _ _ _.

  Definition fun_to_typ {a b : typ} (f : typD a -> typD b) : typD (tyArr a b) :=
    eq_rect_r id f (typ2_cast a b).
    
  Definition typ_to_fun {a b : typ} (f : typD (tyArr a b)) : typD a -> typD b :=
  fun x => (fun g : typD a -> typD b => g x)
    (eq_rect (typD (typ2 a b)) id f (typD a -> typD b)
       (typ2_cast a b)).
    
  Definition fun_to_typ2 {a b c : typ} (f : typD a -> typD b -> typD c) :=
     fun_to_typ (fun x => fun_to_typ (f x)). 

  Definition fun_to_typ3 {a b c d : typ} (f : typD a -> typD b -> typD c -> typD d) :=
    fun_to_typ (fun x => fun_to_typ (fun y => fun_to_typ (f x y))).

  Definition fun_to_typ4 {a b c d e : typ} (f : typD a -> typD b -> typD c -> typD d -> typD e) :=
    fun_to_typ (fun x => fun_to_typ (fun y => fun_to_typ (fun z => fun_to_typ (f x y z)))).

  Definition typ_to_fun2 {a b c : typ} (f : typD (tyArr a (tyArr b c))) : typD a -> typD b -> typD c :=
    fun x => typ_to_fun (typ_to_fun f x).

  Definition typ_to_fun3 {a b c d : typ} (f : typD (tyArr a (tyArr b (tyArr c d)))) : 
	  typD a -> typD b -> typD c -> typD d :=
    fun x y => typ_to_fun (typ_to_fun (typ_to_fun f x) y).

  Lemma exprT_App_wrap tus tvs (t u : typ) (f : HList.hlist typD tus -> HList.hlist typD tvs -> typD t -> typD u) (a : exprT tus tvs (typD t)) :
    exprT_App (fun us vs => fun_to_typ (f us vs)) a = fun us vs => (f us vs) (a us vs).
  Proof.
    unfold fun_to_typ, exprT_App, eq_rect_r, eq_sym, eq_rect.
    forward.
  Qed.

End Denotation.