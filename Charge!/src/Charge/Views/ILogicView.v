Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Data.Bool.
Require Import ExtLib.Data.String.
Require Import ExtLib.Data.POption.
Require Import ExtLib.Data.Map.FMapPositive.
Require Import ExtLib.Data.SumN.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Tactics.
Require Import ExtLib.Tactics.Consider.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.syms.SymEnv.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.Ptrns.
Require Import MirrorCore.SymI.
Require Import MirrorCore.syms.SymSum.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.Reify.ReifyClass.

Require Import ChargeCore.Logics.ILogic.

Require Import Coq.Bool.Bool.


Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Inductive ilfunc (typ : Type) : Type :=
  | ilf_entails (logic : typ)
  | ilf_true (logic : typ)
  | ilf_false (logic : typ)
  | ilf_and (logic : typ)
  | ilf_or (logic : typ)
  | ilf_impl (logic : typ)
  | ilf_exists (arg logic : typ)
  | ilf_forall (arg logic : typ).

Definition ilfunc_logic typ (x : ilfunc typ) : typ :=
  match x with
    | ilf_entails t => t
    | ilf_true t => t
    | ilf_false t => t
    | ilf_and t => t
    | ilf_or t => t
    | ilf_impl t => t
    | ilf_exists _ t => t
    | ilf_forall _ t => t
  end.

Section ILogicFuncInst.
  
  Context {typ func : Type}.
  Context {HR : RType typ} {Heq : RelDec (@eq typ)} {HC : RelDec_Correct Heq}.

  Context {Typ2_tyArr : Typ2 _ RFun}.
  Context {Typ0_tyProp : Typ0 _ Prop}.

  Context {Typ2Ok_tyArr : Typ2Ok Typ2_tyArr}.

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.
  Let tyProp : typ := @typ0 _ _ _ _.

  Definition logic_ops := forall (t : typ),
    poption (ILogicOps (typD t)).
    
  Definition logic_opsOk (l : logic_ops) : Prop :=
    forall g, match l g return Prop with
                | pSome T => @ILogic _ T
                | pNone => True
              end.

  Variable gs : logic_ops.

  Definition il_pointwise := typ -> bool.
(*
  Definition il_pointwiseOk (ilp : il_pointwise) :=
    forall t,
    typ2_match (fun T : Type => Prop) t
    (fun d r : typ =>
    match ilp (tyArr d r) with
      | true =>
        match gs (tyArr d r), gs r with
          | Some ILOps, Some _ => 
            match eq_sym (typ2_cast d r)  in (_ = t) return ILogicOps t -> Prop with
              | eq_refl => 
                fun _ => 
                  (forall a, ltrue a = ltrue) /\
                  (forall a, lfalse a = lfalse) /\
                  (forall (P Q : typD d -> typD r) a, (P //\\ Q) a = (P a //\\ Q a)) /\
                  (forall (P Q : typD d -> typD r) a, (P \\// Q) a = (P a \\// Q a)) /\
                  (forall (P Q : typD d -> typD r) a, (P -->> Q) a = (P a -->> Q a)) /\
                  (forall (A : Type) (f : A -> typD d -> typD r) a, 
                    (lexists f) a = lexists (fun x => f x a)) /\
                  (forall (A : Type) (f : A -> typD d -> typD r) a, 
                    (lforall f) a = lforall (fun x => f x a))
            end ILOps
          | _, _ => False
        end
      | false => True
    end) True.
 
  Lemma il_pointwise_ilogic (ilp : il_pointwise) (ilpOk : il_pointwiseOk ilp) (t u : typ) (H : ilp (tyArr t u) = true) : exists IL, gs (tyArr t u) = Some IL. 
  Proof.
    specialize (ilpOk (tyArr t u)).
    rewrite typ2_match_zeta in ilpOk; [|apply _].
    rewrite H in ilpOk.
    unfold eq_sym in ilpOk.
    revert ilpOk H. unfold tyArr. 
    generalize (typ2_cast t u).
    generalize (typ2 t u).
    generalize dependent (typD t).
    generalize dependent (gs u).
    generalize dependent (typD u).
    intros ? ? ? ?.
    generalize dependent (gs t0).
    generalize (typD t0).
    intros; subst. 
    forward. eexists. subst. reflexivity.
  Qed.

  Lemma il_pointwise_ilogic_range (ilp : il_pointwise) (ilpOk : il_pointwiseOk ilp) (t u : typ) (H : ilp (tyArr t u) = true) : exists IL, gs u = Some IL. 
  Proof.
    specialize (ilpOk (tyArr t u)).
    rewrite typ2_match_zeta in ilpOk; [|apply _].
    rewrite H in ilpOk.
    unfold eq_sym in ilpOk.
    revert ilpOk H. unfold tyArr. 
    generalize (typ2_cast t u).
    generalize (typ2 t u).
    generalize dependent (typD t).
    generalize dependent (gs u).
    generalize dependent (typD u).
    intros ? ? ? ?.
    generalize dependent (gs t0).
    generalize (typD t0).
    intros; subst. 
    forward. eexists. subst. reflexivity.
  Qed.
  
  Lemma il_pointwise_trueD (ilp : il_pointwise) (ilpOk : il_pointwiseOk ilp) (t u : typ) (H : ilp (tyArr t u) = true) IL1 IL2
    (gstu : gs (tyArr t u) = Some IL1) (gsu : gs u = Some IL2) a :
    (tyArrD ltrue) a = ltrue.
  Proof.
    unfold tyArrD, tyArrD', trmD, funE, eq_rect, id.
    specialize (ilpOk (tyArr t u)).
    rewrite typ2_match_zeta in ilpOk; [|apply _].
    rewrite H in ilpOk.
    unfold eq_sym in ilpOk.
    revert ilpOk.
    rewrite gstu.
    rewrite gsu.
    clear.
    generalize (typ2_cast t u).
    revert IL1 IL2.
    unfold tyArr.
    generalize dependent (typD (typ2 t u)).
    generalize dependent (typD t).
    generalize dependent (typD u).
    intros; subst.
    destruct ilpOk as [HTrue _].
    apply HTrue.
  Qed.

  Lemma il_pointwise_trueR (ilp : il_pointwise) (ilpOk : il_pointwiseOk ilp) (t u : typ) (H : ilp (tyArr t u) = true) IL1 IL2
    (gstu : gs (tyArr t u) = Some IL1) (gsu : gs u = Some IL2) :
    tyArrR (fun _ => ltrue) = ltrue.
  Proof.
    unfold tyArrR, tyArrR', trmR, funE, eq_rect_r, eq_rect, eq_sym, id.
    specialize (ilpOk (tyArr t u)).
    rewrite typ2_match_zeta in ilpOk; [|apply _].
    rewrite H in ilpOk.
    unfold eq_sym in ilpOk.
    revert ilpOk.
    rewrite gstu.
    rewrite gsu.
    clear.
    generalize (typ2_cast t u).
    revert IL1 IL2.
    unfold tyArr.
    generalize dependent (typD (typ2 t u)).
    generalize dependent (typD t).
    generalize dependent (typD u).
    intros; subst.
    destruct ilpOk as [HTrue _].
    unfold RFun in *.
	apply functional_extensionality; intros; rewrite HTrue; reflexivity.
  Qed.    

  Lemma il_pointwise_falseD (ilp : il_pointwise) (ilpOk : il_pointwiseOk ilp) (t u : typ) (H : ilp (tyArr t u) = true) IL1 IL2
    (gstu : gs (tyArr t u) = Some IL1) (gsu : gs u = Some IL2) a :
     (tyArrD lfalse) a = lfalse.
  Proof.
    unfold tyArrD, tyArrD', trmD, funE, eq_rect, id.
    specialize (ilpOk (tyArr t u)).
    rewrite typ2_match_zeta in ilpOk; [|apply _].
    rewrite H in ilpOk.
    unfold eq_sym in ilpOk.
    revert ilpOk.
    rewrite gstu.
    rewrite gsu.
    clear.
    generalize (typ2_cast t u).
    revert IL1 IL2.
    unfold tyArr.
    generalize dependent (typD (typ2 t u)).
    generalize dependent (typD t).
    generalize dependent (typD u).
    intros; subst.
    destruct ilpOk as [_ [HFalse _]].
    apply HFalse.
  Qed.    

  Lemma il_pointwise_falseR (ilp : il_pointwise) (ilpOk : il_pointwiseOk ilp) (t u : typ) (H : ilp (tyArr t u) = true) IL1 IL2
    (gstu : gs (tyArr t u) = Some IL1) (gsu : gs u = Some IL2) :
    tyArrR (fun _ => lfalse) = lfalse.
  Proof.
    unfold tyArrR, tyArrR', trmR, funE, eq_rect_r, eq_rect, eq_sym, id.
    specialize (ilpOk (tyArr t u)).
    rewrite typ2_match_zeta in ilpOk; [|apply _].
    rewrite H in ilpOk.
    unfold eq_sym in ilpOk.
    revert ilpOk.
    rewrite gstu.
    rewrite gsu.
    clear.
    generalize (typ2_cast t u).
    revert IL1 IL2.
    unfold tyArr.
    generalize dependent (typD (typ2 t u)).
    generalize dependent (typD t).
    generalize dependent (typD u).
    intros; subst.
    destruct ilpOk as [_ [HFalse _]].
    unfold RFun in *.
	apply functional_extensionality; intros; rewrite HFalse; reflexivity.
  Qed.    

  Lemma il_pointwise_andD (ilp : il_pointwise) (ilpOk : il_pointwiseOk ilp) (t u : typ) (H : ilp (tyArr t u) = true) IL1 IL2
    (gstu : gs (tyArr t u) = Some IL1) (gsu : gs u = Some IL2) (a b : typD (tyArr t u)) s :
    (tyArrD (land a b)) s = land (tyArrD a s) (tyArrD b s).
  Proof.
    unfold tyArrD, tyArrD', trmD, funE, eq_rect, id.
    specialize (ilpOk (tyArr t u)).
    rewrite typ2_match_zeta in ilpOk; [|apply _].
    rewrite H in ilpOk.
    unfold eq_sym in ilpOk.
    revert ilpOk.
    rewrite gstu.
    rewrite gsu.
    clear.
    generalize (typ2_cast t u).
    revert IL1 IL2 a b.
    unfold tyArr.
    generalize dependent (typD (typ2 t u)).
    generalize dependent (typD t).
    generalize dependent (typD u).
    intros; subst.
    destruct ilpOk as [_ [_ [HAnd _]]].
    apply HAnd.
  Qed.    

  Lemma il_pointwise_andR (ilp : il_pointwise) (ilpOk : il_pointwiseOk ilp) (t u : typ) (H : ilp (tyArr t u) = true) IL1 IL2
    (gstu : gs (tyArr t u) = Some IL1) (gsu : gs u = Some IL2) (a b : typD t -> typD u) :
    (tyArrR (fun s => land (a s) (b s))) = land (tyArrR a) (tyArrR b).
  Proof.
    unfold tyArrR, tyArrR', trmR, funE, eq_rect_r, eq_rect, eq_sym, id.
    specialize (ilpOk (tyArr t u)).
    rewrite typ2_match_zeta in ilpOk; [|apply _].
    rewrite H in ilpOk.
    unfold eq_sym in ilpOk.
    revert ilpOk.
    rewrite gstu.
    rewrite gsu.
    clear.
    generalize (typ2_cast t u).
    revert IL1 IL2.
    unfold tyArr.
    generalize dependent (typD (typ2 t u)).
    generalize dependent (typD t).
    generalize dependent (typD u).
    intros; subst.
    destruct ilpOk as [_ [_ [HAnd _]]].
	apply functional_extensionality; intros; rewrite HAnd; reflexivity.
  Qed.    

  Lemma il_pointwise_orD (ilp : il_pointwise) (ilpOk : il_pointwiseOk ilp) (t u : typ) (H : ilp (tyArr t u) = true) IL1 IL2
    (gstu : gs (tyArr t u) = Some IL1) (gsu : gs u = Some IL2) (a b : typD (tyArr t u)) s :
    (tyArrD (lor a b)) s = lor (tyArrD a s) (tyArrD b s).
  Proof.
    unfold tyArrD, tyArrD', trmD, funE, eq_rect, id.
    specialize (ilpOk (tyArr t u)).
    rewrite typ2_match_zeta in ilpOk; [|apply _].
    rewrite H in ilpOk.
    unfold eq_sym in ilpOk.
    revert ilpOk.
    rewrite gstu.
    rewrite gsu.
    clear.
    generalize (typ2_cast t u).
    revert IL1 IL2 a b.
    unfold tyArr.
    generalize dependent (typD (typ2 t u)).
    generalize dependent (typD t).
    generalize dependent (typD u).
    intros; subst.
    destruct ilpOk as [_ [_ [_ [HOr _]]]].
    apply HOr.
  Qed.    

  Lemma il_pointwise_orR (ilp : il_pointwise) (ilpOk : il_pointwiseOk ilp) (t u : typ) (H : ilp (tyArr t u) = true) IL1 IL2
    (gstu : gs (tyArr t u) = Some IL1) (gsu : gs u = Some IL2) (a b : typD t -> typD u) :
    (tyArrR (fun s => lor (a s) (b s))) = lor (tyArrR a) (tyArrR b).
  Proof.
    unfold tyArrR, tyArrR', trmR, funE, eq_rect_r, eq_rect, eq_sym, id.
    specialize (ilpOk (tyArr t u)).
    rewrite typ2_match_zeta in ilpOk; [|apply _].
    rewrite H in ilpOk.
    unfold eq_sym in ilpOk.
    revert ilpOk.
    rewrite gstu.
    rewrite gsu.
    clear.
    generalize (typ2_cast t u).
    revert IL1 IL2.
    unfold tyArr.
    generalize dependent (typD (typ2 t u)).
    generalize dependent (typD t).
    generalize dependent (typD u).
    intros; subst.
    destruct ilpOk as [_ [_ [_ [HOr _]]]].
	apply functional_extensionality; intros; rewrite HOr; reflexivity.
  Qed.    

  Lemma il_pointwise_implD (ilp : il_pointwise) (ilpOk : il_pointwiseOk ilp) (t u : typ) (H : ilp (tyArr t u) = true) IL1 IL2
    (gstu : gs (tyArr t u) = Some IL1) (gsu : gs u = Some IL2) (a b : typD (tyArr t u)) s :
    (tyArrD (limpl a b)) s = limpl (tyArrD a s) (tyArrD b s).
  Proof.
    unfold tyArrD, tyArrD', trmD, funE, eq_rect, id.
    specialize (ilpOk (tyArr t u)).
    rewrite typ2_match_zeta in ilpOk; [|apply _].
    rewrite H in ilpOk.
    unfold eq_sym in ilpOk.
    revert ilpOk.
    rewrite gstu.
    rewrite gsu.
    clear.
    generalize (typ2_cast t u).
    revert IL1 IL2 a b.
    unfold tyArr.
    generalize dependent (typD (typ2 t u)).
    generalize dependent (typD t).
    generalize dependent (typD u).
    intros; subst.
    destruct ilpOk as [_ [_ [_ [_ [HImpl _]]]]].
    apply HImpl.
  Qed.    

  Lemma il_pointwise_implR (ilp : il_pointwise) (ilpOk : il_pointwiseOk ilp) (t u : typ) (H : ilp (tyArr t u) = true) IL1 IL2
    (gstu : gs (tyArr t u) = Some IL1) (gsu : gs u = Some IL2) (a b : typD t -> typD u) :
    (tyArrR (fun s => limpl (a s) (b s))) = limpl (tyArrR a) (tyArrR b).
  Proof.
    unfold tyArrR, tyArrR', trmR, funE, eq_rect_r, eq_rect, eq_sym, id.
    specialize (ilpOk (tyArr t u)).
    rewrite typ2_match_zeta in ilpOk; [|apply _].
    rewrite H in ilpOk.
    unfold eq_sym in ilpOk.
    revert ilpOk.
    rewrite gstu.
    rewrite gsu.
    clear.
    generalize (typ2_cast t u).
    revert IL1 IL2.
    unfold tyArr.
    generalize dependent (typD (typ2 t u)).
    generalize dependent (typD t).
    generalize dependent (typD u).
    intros; subst.
    destruct ilpOk as [_ [_ [_ [_ [HImpl _]]]]].
	apply functional_extensionality; intros; rewrite HImpl; reflexivity.
  Qed.    
*)

  Definition typeof_ilfunc (f : ilfunc typ) : option typ :=
    match f with
    | ilf_true t
    | ilf_false t => match gs t with
  		     | pSome _ => Some t
		     | pNone => None
  		     end
    | ilf_entails t => match gs t with
		       | pSome _ => Some (tyArr t (tyArr t tyProp))
		       | pNone => None
		       end
    | ilf_and t
    | ilf_or t
    | ilf_impl t => match gs t with
		    | pSome _ => Some (tyArr t (tyArr t t))
		    | pNone => None
		    end
    | ilf_forall a t
    | ilf_exists a t => match gs t with
			| pSome _ => Some (tyArr (tyArr a t) t)
			| pNone => None
			end
    end.
  
  Global Instance RelDec_ilfunc : RelDec (@eq (ilfunc typ)) :=
    { rel_dec := fun a b =>
	           match a, b with
		   | ilf_entails t, ilf_entails t'
		   | ilf_true t, ilf_true t'
		   | ilf_false t, ilf_false t'
		   | ilf_and t, ilf_and t'
		   | ilf_or t, ilf_or t'
		   | ilf_impl t, ilf_impl t' => t ?[eq] t'
		   | ilf_forall a t, ilf_forall a' t'
		   | ilf_exists a t, ilf_exists a' t' => (a ?[eq] a' && t ?[eq] t')%bool
		   | _, _ => false
	         end
    }.

  Global Instance RelDec_Correct_ilfunc : RelDec_Correct RelDec_ilfunc.
  Proof.
    constructor.
    destruct x; destruct y; simpl;
    try solve [ try rewrite Bool.andb_true_iff ;
                repeat rewrite rel_dec_correct; intuition congruence ].
  Qed.

 Definition trueR {t : typ} {IL : ILogicOps (typD t)} := @ltrue (typD t) IL.
 Definition falseR {t : typ} {IL : ILogicOps (typD t)} := @lfalse (typD t) IL.
 Definition andR {t : typ} {IL : ILogicOps (typD t)} :=
   castR id (RFun (typD t) (RFun (typD t) (typD t))) (@land (typD t) IL).
 Definition orR {t : typ} {IL : ILogicOps (typD t)} :=
   castR id (RFun (typD t) (RFun (typD t) (typD t))) (@lor (typD t) IL).
 Definition implR {t : typ} {IL : ILogicOps (typD t)} :=
   castR id (RFun (typD t) (RFun (typD t) (typD t))) (@limpl (typD t) IL).
 Definition entailsR {t : typ} {IL : ILogicOps (typD t)} :=
   castR id (RFun (typD t) (RFun (typD t) Prop)) (@lentails (typD t) IL).
 Definition existsR {t u : typ} {IL : ILogicOps (typD t)} :=
   castR id (RFun (RFun (typD u) (typD t)) (typD t)) (@lexists (typD t) IL (typD u)).
 Definition forallR {t u : typ} {IL : ILogicOps (typD t)} :=
   castR id (RFun (RFun (typD u) (typD t)) (typD t)) (@lforall (typD t) IL (typD u)).
 
 Implicit Arguments trueR [[t] [IL]].
 Implicit Arguments falseR [[t] [IL]].
 Implicit Arguments andR [[t] [IL]]. 
 Implicit Arguments orR [[t] [IL]].
 Implicit Arguments implR [[t] [IL]].
 
 Definition funcD (f : ilfunc typ) : match typeof_ilfunc f return Type with
				     | Some t => typD t
				     | None => unit
				     end :=
   match f as f
         return match typeof_ilfunc f return Type with
		| Some t => typD t
		| None => unit
		end
   with
   | ilf_true t => match gs t as x return (match match x with
						 | pSome _ => Some t
						 | pNone => None
						 end with
				           | Some t0 => typD t0
					   | None => unit
					   end) with
		   | pSome t => @ltrue _ t
		   | pNone => tt
		   end
   | ilf_false t =>
     match gs t as x
           return (match match x with
			 | pSome _ => Some t
			 | pNone => None
			 end with
		   | Some t0 => typD t0
		   | None => unit
		   end) with
     | pSome t => lfalse
     | pNone => tt
     end
   | ilf_entails t =>
     match gs t as x
           return (match match x with
			 | pSome _ => Some (tyArr t (tyArr t tyProp))
			 | pNone => None
			 end with
		   | Some t0 => typD t0
		   | None => unit
		   end) with
     | pSome t => entailsR
     | pNone => tt
     end
   | ilf_and t =>
     match gs t as x
           return (match match x with
			 | pSome _ => Some (tyArr t (tyArr t t))
			 | pNone => None
			 end with
		   | Some t0 => typD t0
		   | None => unit
		   end) with
     | pSome t => andR
     | pNone => tt
     end
   | ilf_impl t =>
     match gs t as x
           return (match match x with
			 | pSome _ => Some (tyArr t (tyArr t t))
			 | pNone => None
			 end with
		   | Some t0 => typD t0
		   | None => unit
		   end) with
     | pSome t => implR
     | pNone => tt
     end
   | ilf_or t =>
     match gs t as x
           return (match match x with
			 | pSome _ => Some (tyArr t (tyArr t t))
			 | pNone => None
			 end with
		   | Some t0 => typD t0
		   | None => unit
		   end) with
     | pSome t => orR
     | pNone => tt
     end
   | ilf_exists a t =>
     match gs t as x return (match match x with
				   | pSome _ => Some (tyArr (tyArr a t) t)
				   | pNone => None
				   end with
			     | Some t0 => typD t0
			     | None => unit
			     end) with
     | pSome t0 => existsR
     | pNone => tt
     end
   | ilf_forall a t =>
     match gs t as x return (match match x with
				   | pSome _ => Some (tyArr (tyArr a t) t)
				   | pNone => None
				   end with
			     | Some t0 => typD t0
			     | None => unit
			     end) with
     | pSome t0 => forallR
     | pNone => tt
     end
   end.
 
  Global Instance RSym_ilfunc : SymI.RSym (ilfunc typ) :=
  { typeof_sym := typeof_ilfunc
  ; sym_eqb := fun a b => Some (rel_dec a b)
  ; symD := funcD
  }.

  Global Instance RSymOk_ilfunc : SymI.RSymOk RSym_ilfunc.
  Proof.
    constructor.
    intros. unfold sym_eqb; simpl.
    consider (a ?[ eq ] b); auto.
  Qed.

End ILogicFuncInst.


Section MakeILogic.
  Context {typ func : Type} {FV : PartialView func (ilfunc typ)}.

  Definition fTrue t := f_insert (ilf_true t).
  Definition fFalse t := f_insert (ilf_false t).
  Definition fAnd t := f_insert (ilf_and t).
  Definition fOr t := f_insert (ilf_or t).
  Definition fImpl t := f_insert (ilf_impl t).
  Definition fEntails t := f_insert (ilf_entails t).
  Definition fExists t u := f_insert (ilf_exists t u).
  Definition fForall t u := f_insert (ilf_forall t u).

  Definition mkEntails (t : typ) (P Q : expr typ func) := App (App (Inj (fEntails t)) P) Q.
  Definition mkTrue t : expr typ func := Inj (fTrue t).
  Definition mkFalse t : expr typ func := Inj (fFalse t).
  Definition mkAnd (t : typ) (P Q : expr typ func) := App (App (Inj (fAnd t)) P) Q.
  Definition mkOr (t : typ) (P Q : expr typ func) := App (App (Inj (fOr t)) P) Q.
  Definition mkImpl (t : typ) (P Q : expr typ func) := App (App (Inj (fImpl t)) P) Q.
  Definition mkExists (t l : typ) (f : expr typ func) := App (Inj (fExists t l)) (Abs t f).
  Definition mkForall (t l : typ) (f : expr typ func) := App (Inj (fForall t l)) (Abs t f).

  Definition fptrnTrue {T : Type} (p : Ptrns.ptrn typ T) : ptrn (ilfunc typ) T :=
    fun f U good bad =>
      match f with
        | ilf_entails t => bad (ilf_entails t)
        | ilf_true t => p t U good (fun x => bad (ilf_true t))
        | ilf_false t => bad (ilf_false t)
        | ilf_and t => bad (ilf_and t)
        | ilf_or t => bad (ilf_or t)
        | ilf_impl t => bad (ilf_impl t)
        | ilf_exists t u => bad (ilf_exists t u)
        | ilf_forall t u => bad (ilf_forall t u)
      end.

  Definition fptrnFalse {T : Type} (p : Ptrns.ptrn typ T) : ptrn (ilfunc typ) T :=
    fun f U good bad =>
      match f with
        | ilf_entails t => bad (ilf_entails t)
        | ilf_true t => bad (ilf_true t)
        | ilf_false t => p t U good (fun x => bad (ilf_false t))
        | ilf_and t => bad (ilf_and t)
        | ilf_or t => bad (ilf_or t)
        | ilf_impl t => bad (ilf_impl t)
        | ilf_exists t u => bad (ilf_exists t u)
        | ilf_forall t u => bad (ilf_forall t u)
      end.

  Definition fptrnAnd {T : Type} (p : Ptrns.ptrn typ T) : ptrn (ilfunc typ) T :=
    fun f U good bad =>
      match f with
        | ilf_entails t => bad (ilf_entails t)
        | ilf_true t => bad (ilf_true t)
        | ilf_false t => bad (ilf_false t)
        | ilf_and t => p t U good (fun x => bad (ilf_and t))
        | ilf_or t => bad (ilf_or t)
        | ilf_impl t => bad (ilf_impl t)
        | ilf_exists t u => bad (ilf_exists t u)
        | ilf_forall t u => bad (ilf_forall t u)
      end.

  Definition fptrnOr {T : Type} (p : Ptrns.ptrn typ T) : ptrn (ilfunc typ) T :=
    fun f U good bad =>
      match f with
        | ilf_entails t => bad (ilf_entails t)
        | ilf_true t => bad (ilf_true t)
        | ilf_false t => bad (ilf_false t)
        | ilf_and t => bad (ilf_and t)
        | ilf_or t => p t U good (fun x => bad (ilf_or t))
        | ilf_impl t => bad (ilf_impl t)
        | ilf_exists t u => bad (ilf_exists t u)
        | ilf_forall t u => bad (ilf_forall t u)
      end.

  Definition fptrnImpl {T : Type} (p : Ptrns.ptrn typ T) : ptrn (ilfunc typ) T :=
    fun f U good bad =>
      match f with
        | ilf_entails t => bad (ilf_entails t)
        | ilf_true t => bad (ilf_true t)
        | ilf_false t => bad (ilf_false t)
        | ilf_and t => bad (ilf_and t)
        | ilf_or t => bad (ilf_or t)
        | ilf_impl t => p t U good (fun x => bad (ilf_impl t))
        | ilf_exists t u => bad (ilf_exists t u)
        | ilf_forall t u => bad (ilf_forall t u)
      end.

  Definition fptrnEntails {T : Type} (p : Ptrns.ptrn typ T) : ptrn (ilfunc typ) T :=
    fun f U good bad =>
      match f with
        | ilf_entails t => p t U good (fun x => bad (ilf_entails t))
        | ilf_true t => bad (ilf_true t)
        | ilf_false t => bad (ilf_false t)
        | ilf_and t => bad (ilf_and t)
        | ilf_or t => bad (ilf_or t)
        | ilf_impl t => bad (ilf_impl t)
        | ilf_exists t u => bad (ilf_exists t u)
        | ilf_forall t u => bad (ilf_forall t u)
      end.

  Definition fptrnExists {T : Type} (p : Ptrns.ptrn (typ * typ) T) : ptrn (ilfunc typ) T :=
    fun f U good bad =>
      match f with
        | ilf_entails t => bad (ilf_entails t)
        | ilf_true t => bad (ilf_true t)
        | ilf_false t => bad (ilf_false t)
        | ilf_and t => bad (ilf_and t)
        | ilf_or t => bad (ilf_or t)
        | ilf_impl t => bad (ilf_impl t)
        | ilf_exists t u => p (t, u) U good (fun x => bad (ilf_exists t u))
        | ilf_forall t u => bad (ilf_forall t u)
      end.

  Definition fptrnForall {T : Type} (p : Ptrns.ptrn (typ * typ) T) : ptrn (ilfunc typ) T :=
    fun f U good bad =>
      match f with
        | ilf_entails t => bad (ilf_entails t)
        | ilf_true t => bad (ilf_true t)
        | ilf_false t => bad (ilf_false t)
        | ilf_and t => bad (ilf_and t)
        | ilf_or t => bad (ilf_or t)
        | ilf_impl t => bad (ilf_impl t)
        | ilf_exists t u => bad (ilf_exists t u)
        | ilf_forall t u => p (t, u) U good (fun x => bad (ilf_forall t u))
      end.

  Global Instance fptrnEntails_ok {T : Type} {p : ptrn typ T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnEntails p).
  Proof.
    red; intros.
    destruct x; simpl; [destruct (Hok logic) | | | | | | |].
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
  Qed.

  Global Instance fptrnTrue_ok {T : Type} {p : ptrn typ T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnTrue p).
  Proof.
    red; intros.
    destruct x; simpl; [|destruct (Hok logic) | | | | | |].
    { right; unfold Fails; reflexivity. }
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
  Qed.

  Global Instance fptrnFalse_ok {T : Type} {p : ptrn typ T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnFalse p).
  Proof.
    red; intros.
    destruct x; simpl; [| |destruct (Hok logic) | | | | |].
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
  Qed.

  Global Instance fptrnAnd_ok {T : Type} {p : ptrn typ T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnAnd p).
  Proof.
    red; intros.
    destruct x; simpl; [| | | destruct (Hok logic) | | | |].
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
  Qed.

  Global Instance fptrnOr_ok {T : Type} {p : ptrn typ T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnOr p).
  Proof.
    red; intros.
    destruct x; simpl; try (right; unfold Fails; reflexivity).
    destruct (Hok logic).
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
  Qed.

  Global Instance fptrnImpl_ok {T : Type} {p : ptrn typ T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnImpl p).
  Proof.
    red; intros.
    destruct x; simpl; try (right; unfold Fails; reflexivity).
    destruct (Hok logic).
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
  Qed.

  Global Instance fptrnExists_ok {T : Type} {p : ptrn (typ * typ) T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnExists p).
  Proof.
    red; intros.
    destruct x; simpl; try (right; unfold Fails; reflexivity).
    destruct (Hok (arg, logic)).
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
  Qed.

  Global Instance fptrnForall_ok {T : Type} {p : ptrn (typ * typ) T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnExists p).
  Proof.
    red; intros.
    destruct x; simpl; try (right; unfold Fails; reflexivity).
    destruct (Hok (arg, logic)).
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
  Qed.

 
  Lemma Succeeds_fptrnTrue {T : Type} (f : ilfunc typ) (p : ptrn typ T) (res : T)
        {pok : ptrn_ok p} (H : Succeeds f (fptrnTrue p) res) :
    exists t, Succeeds t p res /\ f = ilf_true t.
  Proof.
    unfold Succeeds, fptrnTrue in H.
    unfold ptrn_ok in pok.
    specialize (H (option T) Some (fun _ => None)).
    destruct f; try congruence.
    specialize (pok logic).
    destruct pok; [|rewrite H0 in H; congruence].
    destruct H0.
    rewrite H0 in H; inv_all; subst.
    exists logic; split; [assumption | reflexivity].
  Qed.

  Lemma Succeeds_fptrnFalse {T : Type} (f : ilfunc typ) (p : ptrn typ T) (res : T)
        {pok : ptrn_ok p} (H : Succeeds f (fptrnFalse p) res) :
    exists t, Succeeds t p res /\ f = ilf_false t.
  Proof.
    unfold Succeeds, fptrnFalse in H.
    unfold ptrn_ok in pok.
    specialize (H (option T) Some (fun _ => None)).
    destruct f; try congruence.
    specialize (pok logic).
    destruct pok; [|rewrite H0 in H; congruence].
    destruct H0.
    rewrite H0 in H; inv_all; subst.
    exists logic; split; [assumption | reflexivity].
  Qed.

  Lemma Succeeds_fptrnEntails {T : Type} (f : ilfunc typ) (p : ptrn typ T) (res : T)
        {pok : ptrn_ok p} (H : Succeeds f (fptrnEntails p) res) :
    exists t, Succeeds t p res /\ f = ilf_entails t.
  Proof.
    unfold Succeeds, fptrnEntails in H.
    unfold ptrn_ok in pok.
    specialize (H (option T) Some (fun _ => None)).
    destruct f; try congruence.
    specialize (pok logic).
    destruct pok; [|rewrite H0 in H; congruence].
    destruct H0.
    rewrite H0 in H; inv_all; subst.
    exists logic; split; [assumption | reflexivity].
  Qed.

  Lemma Succeeds_fptrnAnd {T : Type} (f : ilfunc typ) (p : ptrn typ T) (res : T)
        {pok : ptrn_ok p} (H : Succeeds f (fptrnAnd p) res) :
    exists t, Succeeds t p res /\ f = ilf_and t.
  Proof.
    unfold Succeeds, fptrnAnd in H.
    unfold ptrn_ok in pok.
    specialize (H (option T) Some (fun _ => None)).
    destruct f; try congruence.
    specialize (pok logic).
    destruct pok; [|rewrite H0 in H; congruence].
    destruct H0.
    rewrite H0 in H; inv_all; subst.
    exists logic; split; [assumption | reflexivity].
  Qed.

  Lemma Succeeds_fptrnOr {T : Type} (f : ilfunc typ) (p : ptrn typ T) (res : T)
        {pok : ptrn_ok p} (H : Succeeds f (fptrnOr p) res) :
    exists t, Succeeds t p res /\ f = ilf_or t.
  Proof.
    unfold Succeeds, fptrnOr in H.
    unfold ptrn_ok in pok.
    specialize (H (option T) Some (fun _ => None)).
    destruct f; try congruence.
    specialize (pok logic).
    destruct pok; [|rewrite H0 in H; congruence].
    destruct H0.
    rewrite H0 in H; inv_all; subst.
    exists logic; split; [assumption | reflexivity].
  Qed.

  Lemma Succeeds_fptrnImpl {T : Type} (f : ilfunc typ) (p : ptrn typ T) (res : T)
        {pok : ptrn_ok p} (H : Succeeds f (fptrnImpl p) res) :
    exists t, Succeeds t p res /\ f = ilf_impl t.
  Proof.
    unfold Succeeds, fptrnImpl in H.
    unfold ptrn_ok in pok.
    specialize (H (option T) Some (fun _ => None)).
    destruct f; try congruence.
    specialize (pok logic).
    destruct pok; [|rewrite H0 in H; congruence].
    destruct H0.
    rewrite H0 in H; inv_all; subst.
    exists logic; split; [assumption | reflexivity].
  Qed.

  Lemma Succeeds_fptrnExists {T : Type} (f : ilfunc typ) (p : ptrn (typ * typ) T) (res : T)
        {pok : ptrn_ok p} (H : Succeeds f (fptrnExists p) res) :
    exists t u, Succeeds (t, u) p res /\ f = ilf_exists t u.
  Proof.
    unfold Succeeds, fptrnExists in H.
    unfold ptrn_ok in pok.
    specialize (H (option T) Some (fun _ => None)).
    destruct f; try congruence.
    specialize (pok (arg, logic)).
    destruct pok; [|rewrite H0 in H; congruence].
    destruct H0.
    rewrite H0 in H; inv_all; subst.
    exists arg, logic; split; [assumption | reflexivity].
  Qed.

  Lemma Succeeds_fptrnForall {T : Type} (f : ilfunc typ) (p : ptrn (typ * typ) T) (res : T)
        {pok : ptrn_ok p} (H : Succeeds f (fptrnForall p) res) :
    exists t u, Succeeds (t, u) p res /\ f = ilf_forall t u.
  Proof.
    unfold Succeeds, fptrnForall in H.
    unfold ptrn_ok in pok.
    specialize (H (option T) Some (fun _ => None)).
    destruct f; try congruence.
    specialize (pok (arg, logic)).
    destruct pok; [|rewrite H0 in H; congruence].
    destruct H0.
    rewrite H0 in H; inv_all; subst.
    exists arg, logic; split; [assumption | reflexivity].
  Qed.
  
  Global Instance fptrnTrue_SucceedsE {T : Type} {f : ilfunc typ} 
         {p : ptrn typ T} {res : T} {pok : ptrn_ok p} :
    SucceedsE f (fptrnTrue p) res := {
      s_result := exists t, Succeeds t p res /\ f = ilf_true t;
      s_elim := @Succeeds_fptrnTrue T f p res pok
    }.

  Global Instance fptrnFalse_SucceedsE {T : Type} {f : ilfunc typ} 
         {p : ptrn typ T} {res : T} {pok : ptrn_ok p} :
    SucceedsE f (fptrnFalse p) res := {
      s_result := exists t, Succeeds t p res /\ f = ilf_false t;
      s_elim := @Succeeds_fptrnFalse T f p res pok
    }.

  Global Instance fptrnEntails_SucceedsE {T : Type} {f : ilfunc typ} 
         {p : ptrn typ T} {res : T} {pok : ptrn_ok p} :
    SucceedsE f (fptrnEntails p) res := {
      s_result := exists t, Succeeds t p res /\ f = ilf_entails t;
      s_elim := @Succeeds_fptrnEntails T f p res pok
    }.

  Global Instance fptrnAnd_SucceedsE {T : Type} {f : ilfunc typ} 
         {p : ptrn typ T} {res : T} {pok : ptrn_ok p} :
    SucceedsE f (fptrnAnd p) res := {
      s_result := exists t, Succeeds t p res /\ f = ilf_and t;
      s_elim := @Succeeds_fptrnAnd T f p res pok
    }.

  Global Instance fptrnOr_SucceedsE {T : Type} {f : ilfunc typ} 
         {p : ptrn typ T} {res : T} {pok : ptrn_ok p} :
    SucceedsE f (fptrnOr p) res := {
      s_result := exists t, Succeeds t p res /\ f = ilf_or t;
      s_elim := @Succeeds_fptrnOr T f p res pok
    }.

  Global Instance fptrnImpl_SucceedsE {T : Type} {f : ilfunc typ} 
         {p : ptrn typ T} {res : T} {pok : ptrn_ok p} :
    SucceedsE f (fptrnImpl p) res := {
      s_result := exists t, Succeeds t p res /\ f = ilf_impl t;
      s_elim := @Succeeds_fptrnImpl T f p res pok
    }.

  Global Instance fptrnExists_SucceedsE {T : Type} {f : ilfunc typ} 
         {p : ptrn (typ * typ) T} {res : T} {pok : ptrn_ok p} :
    SucceedsE f (fptrnExists p) res := {
      s_result := exists t u, Succeeds (t, u) p res /\ f = ilf_exists t u;
      s_elim := @Succeeds_fptrnExists T f p res pok
    }.

  Global Instance fptrnForall_SucceedsE {T : Type} {f : ilfunc typ} 
         {p : ptrn (typ * typ) T} {res : T} {pok : ptrn_ok p} :
    SucceedsE f (fptrnForall p) res := {
      s_result := exists t u, Succeeds (t, u) p res /\ f = ilf_forall t u;
      s_elim := @Succeeds_fptrnForall T f p res pok
    }.

End MakeILogic.

Section ILogicPtrn.
  Context {typ func : Type} {FV : PartialView func (ilfunc typ)}.

 Definition ptrnTrue {T : Type}
             (p : ptrn typ T) : ptrn (expr typ func) T :=
    inj (ptrn_view _ (fptrnTrue p)).

  Definition ptrnFalse {T : Type}
             (p : ptrn typ T) : ptrn (expr typ func) T :=
    inj (ptrn_view _ (fptrnFalse p)).

  Definition ptrnEntails {A B T : Type}
             (p : ptrn typ T)
             (a : ptrn (expr typ func) A) 
             (b : ptrn (expr typ func) B) : ptrn (expr typ func) (T * A * B) :=
    app (app (inj (ptrn_view _ (fptrnEntails p))) a) b.

  Definition ptrnAnd {A B T : Type}
             (p : ptrn typ T)
             (a : ptrn (expr typ func) A) 
             (b : ptrn (expr typ func) B) : ptrn (expr typ func) (T * A * B) :=
    app (app (inj (ptrn_view _ (fptrnAnd p))) a) b.

  Definition ptrnOr {A B T : Type}
             (p : ptrn typ T)
             (a : ptrn (expr typ func) A) 
             (b : ptrn (expr typ func) B) : ptrn (expr typ func) (T * A * B) :=
    app (app (inj (ptrn_view _ (fptrnOr p))) a) b.

  Definition ptrnImpl {A B T : Type}
             (p : ptrn typ T)
             (a : ptrn (expr typ func) A) 
             (b : ptrn (expr typ func) B) : ptrn (expr typ func) (T * A * B) :=
    app (app (inj (ptrn_view _ (fptrnImpl p))) a) b.

  Definition ptrnExists {A T : Type}
             (p : ptrn (typ * typ) T)
             (f : ptrn (expr typ func) A) : ptrn (expr typ func) (T * A) :=
    app (inj (ptrn_view _ (fptrnExists p))) f.

  Definition ptrnForall {A T : Type}
             (p : ptrn (typ * typ) T)
             (f : ptrn (expr typ func) A) : ptrn (expr typ func) (T * A) :=
    app (inj (ptrn_view _ (fptrnForall p))) f.

Definition ilogic_ptrn_cases {T : Type}
           (do_true : typ -> T)
           (do_false : typ -> T)
           (do_and : typ -> expr typ func -> expr typ func -> T)
           (do_or : typ -> expr typ func -> expr typ func -> T)
           (do_impl : typ -> expr typ func -> expr typ func -> T)
           (do_exists : typ -> typ -> expr typ func -> T)
           (do_forall : typ -> typ -> expr typ func -> T) : ptrn (expr typ func) T :=
  por (inj (ptrn_view _ (por (fptrnTrue (pmap do_true get))
                             (fptrnFalse (pmap do_false get)))))
      (appr (por (appr (inj (ptrn_view _ 
                                       (por (fptrnAnd (pmap do_and get)) 
                                            (por (fptrnOr (pmap do_or get))
                                                 (fptrnImpl (pmap do_impl get)))))) get)
                 (inj (ptrn_view _ (por (fptrnExists (pmap 
                                                        (fun x f => do_exists (fst x) 
                                                                              (snd x) f) get))
                                        (fptrnForall (pmap 
                                                        (fun x f => do_forall (fst x) 
                                                                              (snd x) f) get))))))
            get).
Check run_ptrn.
Definition ilogic_cases {T : Type}
           (do_true : typ -> T)
           (do_false : typ -> T)
           (do_and : typ -> expr typ func -> expr typ func -> T)
           (do_or : typ -> expr typ func -> expr typ func -> T)
           (do_impl : typ -> expr typ func -> expr typ func -> T)
           (do_exists : typ -> typ -> expr typ func -> T)
           (do_forall : typ -> typ -> expr typ func -> T)
           (do_default : T) :=
  run_ptrn (ilogic_ptrn_cases
              do_true do_false do_and do_or do_impl do_exists do_forall)
           do_default.
           
End ILogicPtrn.

Section ReifyILogic.
  Context {typ func : Type} {FV : PartialView func (ilfunc typ)}.
  Context {t : Reify typ}.

  Definition reify_ltrue : Command (expr typ func) :=
    CPattern (ls := typ::nil) 
             (RApp (RApp (RExact (@ltrue)) (RGet 0 RIgnore)) RIgnore)
             (fun (x : function (CCall (reify_scheme typ))) => mkTrue x).

  Definition reify_lfalse : Command (expr typ func) :=
    CPattern (ls := typ::nil) 
             (RApp (RApp (RExact (@lfalse)) (RGet 0 RIgnore)) RIgnore)
             (fun (x : function (CCall (reify_scheme typ))) => mkTrue x).

  Definition reify_land : Command (expr typ func) :=
    CPattern (ls := typ::nil) 
             (RApp (RApp (RExact (@land)) (RGet 0 RIgnore)) RIgnore)
             (fun (x : function (CCall (reify_scheme typ))) => Inj (fAnd x)).

  Definition reify_lor : Command (expr typ func) :=
    CPattern (ls := typ::nil) 
             (RApp (RApp (RExact (@lor)) (RGet 0 RIgnore)) RIgnore)
             (fun (x : function (CCall (reify_scheme typ))) => Inj (fOr x)).

  Definition reify_limpl : Command (expr typ func) :=
    CPattern (ls := typ::nil) 
             (RApp (RApp (RExact (@limpl)) (RGet 0 RIgnore)) RIgnore)
             (fun (x : function (CCall (reify_scheme typ))) => Inj (fImpl x)).

  Definition reify_lforall : Command (expr typ func) :=
    CPattern (ls := typ::typ::nil) 
             (RApp (RApp (RApp (RExact (@lforall)) (RGet 0 RIgnore)) RIgnore) (RGet 1 RIgnore))
             (fun (x y : function (CCall (reify_scheme typ))) => Inj (fForall y x)).

  Definition reify_lexists : Command (expr typ func) :=
    CPattern (ls := typ::typ::nil) 
             (RApp (RApp (RApp (RExact (@lexists)) (RGet 0 RIgnore)) RIgnore) (RGet 1 RIgnore))
             (fun (x y : function (CCall (reify_scheme typ))) => Inj (fExists y x)).

  Definition reify_ilogic : Command (expr typ func) :=
    CFirst (reify_ltrue :: reify_lfalse :: reify_land :: reify_lor :: 
            reify_limpl :: reify_lforall :: reify_lexists :: nil).

End ReifyILogic.

Arguments reify_ilogic _ _ {_ _}.

Implicit Arguments RSym_ilfunc [[typ] [HR] [Heq] [Typ2_tyArr] [Typ0_tyProp]].
