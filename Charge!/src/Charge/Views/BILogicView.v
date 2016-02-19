Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.

Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Data.Map.FMapPositive.
Require Import ExtLib.Data.SumN.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Data.POption.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.syms.SymEnv.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.Ptrns.
Require Import MirrorCore.SymI.
Require Import MirrorCore.syms.SymSum.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.Views.Ptrns.

Require Import ChargeCore.Logics.ILogic.
Require Import ChargeCore.Logics.BILogic.

Require Import Charge.Views.ILogicView.

Require Import Coq.Logic.FunctionalExtensionality.


Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Inductive bilfunc typ :=
  | bilf_emp (logic : typ)
  | bilf_star (logic : typ)
  | bilf_wand (logic : typ).

Definition bilfunc_logic typ (x : bilfunc typ) : typ :=
  match x with
    | bilf_emp t => t
    | bilf_star t => t
    | bilf_wand t => t
  end.

Section BILogicFuncInst.

  Context {typ func : Type}.
  Context {HR : RType typ} {Heq : RelDec (@eq typ)} {HC : RelDec_Correct Heq}.
  
  Context {Typ2_tyArr : Typ2 _ RFun}.
  Context {Typ0_tyProp : Typ0 _ Prop}.
  
  Context {Typ2Ok_tyArr : Typ2Ok Typ2_tyArr}.

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.
  Let tyProp : typ := @typ0 _ _ _ _.
	
  Variable is : logic_ops.

  Definition bilogic_ops := forall (t : typ),
    poption (BILOperators (typD t)).
    
  Definition bilogic_opsOk (l : bilogic_ops) : Prop :=
    forall g, match is g, l g return Prop with
                | pSome T, pSome U => BILogic (typD g)
                | _, _ => True
              end.

  Variable gs : bilogic_ops.
  
  Definition bil_pointwise := typ -> bool.
(*
  Definition bil_pointwiseOk (bilp : bil_pointwise) :=
    forall t,
    typ2_match (fun T : Type => Prop) t
    (fun d r : typ =>
    match bilp (tyArr d r) with
      | true =>
        match gs (tyArr d r), gs r with
          | Some BILOps, Some _ => 
            match eq_sym (typ2_cast d r)  in (_ = t) return BILOperators t -> Prop with
              | eq_refl => 
                fun _ => 
                  (forall a, empSP a = empSP) /\
                  (forall (P Q : typD d -> typD r) a, (P ** Q) a = (P a ** Q a)) /\
                  (forall (P Q : typD d -> typD r) a, (wandSP P Q) a = wandSP (P a) (Q a))
            end BILOps
          | _, _ => False
        end
      | false => True
    end) True.

  Lemma bil_pointwise_bilogic (bilp : bil_pointwise) (bilpOk : bil_pointwiseOk bilp) (t u : typ)
    (H : bilp (tyArr t u) = true) : exists BIL, gs (tyArr t u) = Some BIL. 
  Proof.
    specialize (bilpOk (tyArr t u)).
    rewrite typ2_match_zeta in bilpOk; [|apply _].
    rewrite H in bilpOk.
    unfold eq_sym in bilpOk.
    revert bilpOk H. unfold tyArr. 
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

  Lemma bil_pointwise_bilogic_range (bilp : bil_pointwise) (bilpOk : bil_pointwiseOk bilp) (t u : typ)
    (H : bilp (tyArr t u) = true) : exists BIL, gs u = Some BIL. 
  Proof.
    specialize (bilpOk (tyArr t u)).
    rewrite typ2_match_zeta in bilpOk; [|apply _].
    rewrite H in bilpOk.
    unfold eq_sym in bilpOk.
    revert bilpOk H. unfold tyArr. 
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
  
  Lemma bil_pointwise_empD (bilp : bil_pointwise) (bilpOk : bil_pointwiseOk bilp) (t u : typ) 
    (H : bilp (tyArr t u) = true) BIL1 BIL2
    (gstu : gs (tyArr t u) = Some BIL1) (gsu : gs u = Some BIL2) a :
    (tyArrD empSP) a = empSP.
  Proof.
    unfold tyArrD, tyArrD', trmD, funE, eq_rect, id.
    specialize (bilpOk (tyArr t u)).
    rewrite typ2_match_zeta in bilpOk; [|apply _].
    rewrite H in bilpOk.
    unfold eq_sym in bilpOk.
    revert bilpOk.
    rewrite gstu.
    rewrite gsu.
    clear.
    generalize (typ2_cast t u).
    revert BIL1 BIL2.
    unfold tyArr.
    generalize dependent (typD (typ2 t u)).
    generalize dependent (typD t).
    generalize dependent (typD u).
    intros; subst.
    destruct bilpOk as [HEmp _].
    apply HEmp.
  Qed.    

  Lemma bil_pointwise_empR (bilp : bil_pointwise) (bilpOk : bil_pointwiseOk bilp) (t u : typ) 
    (H : bilp (tyArr t u) = true) BIL1 BIL2
    (gstu : gs (tyArr t u) = Some BIL1) (gsu : gs u = Some BIL2) :
    tyArrR (fun _ => empSP) = empSP.
  Proof.
    unfold tyArrR, tyArrR', trmR, funE, eq_rect_r, eq_rect, eq_sym, id.
    specialize (bilpOk (tyArr t u)).
    rewrite typ2_match_zeta in bilpOk; [|apply _].
    rewrite H in bilpOk.
    unfold eq_sym in bilpOk.
    revert bilpOk.
    rewrite gstu.
    rewrite gsu.
    clear.
    generalize (typ2_cast t u).
    revert BIL1 BIL2.
    unfold tyArr.
    generalize dependent (typD (typ2 t u)).
    generalize dependent (typD t).
    generalize dependent (typD u).
    intros; subst.
    destruct bilpOk as [HEmp _].
    unfold RFun in *.
	apply functional_extensionality; intros; rewrite HEmp; reflexivity.
  Qed.    

  Lemma bil_pointwise_starD (bilp : bil_pointwise) (bilpOk : bil_pointwiseOk bilp) (t u : typ)
    (H : bilp (tyArr t u) = true) BIL1 BIL2
    (gstu : gs (tyArr t u) = Some BIL1) (gsu : gs u = Some BIL2) (a b : typD (tyArr t u)) s :
    (tyArrD (sepSP a b)) s = sepSP (tyArrD a s) (tyArrD b s).
  Proof.
    unfold tyArrD, tyArrD', trmD, funE, eq_rect, id.
    specialize (bilpOk (tyArr t u)).
    rewrite typ2_match_zeta in bilpOk; [|apply _].
    rewrite H in bilpOk.
    unfold eq_sym in bilpOk.
    revert bilpOk.
    rewrite gstu.
    rewrite gsu.
    clear.
    generalize (typ2_cast t u).
    revert BIL1 BIL2 a b.
    unfold tyArr.
    generalize dependent (typD (typ2 t u)).
    generalize dependent (typD t).
    generalize dependent (typD u).
    intros; subst.
    destruct bilpOk as [_ [HStar _]].
    apply HStar.
  Qed.    

  Lemma bil_pointwise_starR (bilp : bil_pointwise) (bilpOk : bil_pointwiseOk bilp) (t u : typ) 
    (H : bilp (tyArr t u) = true) BIL1 BIL2
    (gstu : gs (tyArr t u) = Some BIL1) (gsu : gs u = Some BIL2) (a b : typD t -> typD u) :
    (tyArrR (fun s => sepSP (a s) (b s))) = sepSP (tyArrR a) (tyArrR b).
  Proof.
    unfold tyArrR, tyArrR', trmR, funE, eq_rect_r, eq_rect, eq_sym, id.
    specialize (bilpOk (tyArr t u)).
    rewrite typ2_match_zeta in bilpOk; [|apply _].
    rewrite H in bilpOk.
    unfold eq_sym in bilpOk.
    revert bilpOk.
    rewrite gstu.
    rewrite gsu.
    clear.
    generalize (typ2_cast t u).
    revert BIL1 BIL2.
    unfold tyArr.
    generalize dependent (typD (typ2 t u)).
    generalize dependent (typD t).
    generalize dependent (typD u).
    intros; subst.
    destruct bilpOk as [_ [HStar _]].
	apply functional_extensionality; intros; rewrite HStar; reflexivity.
  Qed.    

  Lemma bil_pointwise_wandD (bilp : bil_pointwise) (bilpOk : bil_pointwiseOk bilp) (t u : typ)
    (H : bilp (tyArr t u) = true) BIL1 BIL2
    (gstu : gs (tyArr t u) = Some BIL1) (gsu : gs u = Some BIL2) (a b : typD (tyArr t u)) s :
    (tyArrD (wandSP a b)) s = wandSP (tyArrD a s) (tyArrD b s).
  Proof.
    unfold tyArrD, tyArrD', trmD, funE, eq_rect, id.
    specialize (bilpOk (tyArr t u)).
    rewrite typ2_match_zeta in bilpOk; [|apply _].
    rewrite H in bilpOk.
    unfold eq_sym in bilpOk.
    revert bilpOk.
    rewrite gstu.
    rewrite gsu.
    clear.
    generalize (typ2_cast t u).
    revert BIL1 BIL2 a b.
    unfold tyArr.
    generalize dependent (typD (typ2 t u)).
    generalize dependent (typD t).
    generalize dependent (typD u).
    intros; subst.
    destruct bilpOk as [_ [_ HWand]].
    apply HWand.
  Qed.    

  Lemma bil_pointwise_wandR (bilp : bil_pointwise) (bilpOk : bil_pointwiseOk bilp) (t u : typ) 
    (H : bilp (tyArr t u) = true) BIL1 BIL2
    (gstu : gs (tyArr t u) = Some BIL1) (gsu : gs u = Some BIL2) (a b : typD t -> typD u) :
    (tyArrR (fun s => wandSP (a s) (b s))) = wandSP (tyArrR a) (tyArrR b).
  Proof.
    unfold tyArrR, tyArrR', trmR, funE, eq_rect_r, eq_rect, eq_sym, id.
    specialize (bilpOk (tyArr t u)).
    rewrite typ2_match_zeta in bilpOk; [|apply _].
    rewrite H in bilpOk.
    unfold eq_sym in bilpOk.
    revert bilpOk.
    rewrite gstu.
    rewrite gsu.
    clear.
    generalize (typ2_cast t u).
    revert BIL1 BIL2.
    unfold tyArr.
    generalize dependent (typD (typ2 t u)).
    generalize dependent (typD t).
    generalize dependent (typD u).
    intros; subst.
    destruct bilpOk as [_ [_ HWand]].
	apply functional_extensionality; intros; rewrite HWand; reflexivity.
  Qed.    
*)
  Definition typeof_bilfunc (f : bilfunc typ) : option typ :=
    match f with
    | bilf_emp t => match gs t with
  		    | pSome _ => Some t
		    | pNone => None
  		    end
    | bilf_star t
    | bilf_wand t => match gs t with
		     | pSome _ => Some (tyArr t (tyArr t t))
		     | pNone => None
		     end
    end.
  
  Global Instance RelDec_bilfunc : RelDec (@eq (bilfunc typ)) :=
    { rel_dec := fun a b =>
	           match a, b with
		   | bilf_emp t, bilf_emp t'
		   | bilf_star t, bilf_star t'
		   | bilf_wand t, bilf_wand t' => t ?[eq] t'
		   | _, _ => false
	           end
    }.

  Global Instance RelDec_Correct_bilfunc : RelDec_Correct RelDec_bilfunc.
  Proof.
    constructor.
    destruct x; destruct y; simpl;
    repeat rewrite rel_dec_correct; intuition congruence.
  Qed.

 Definition empR t BIL := @empSP (typD t) BIL.
 Definition starR t BIL := castR id (RFun (typD t) (RFun (typD t) (typD t))) (@sepSP (typD t) BIL).
 Definition wandR t BIL := castR id (RFun (typD t) (RFun (typD t) (typD t))) (@wandSP (typD t) BIL).
 
 Definition funcD (f : bilfunc typ) : match typeof_bilfunc f return Type with
							       | Some t => typD t
							       | None => unit
							      end :=
    match f as f
          return match typeof_bilfunc f return Type with
		   | Some t => typD t
		   | None => unit
		 end
    with
      | bilf_emp t =>
        match gs t as x
          return (match match x with
                          | pSome _ => Some t
                          | pNone => None
                        end with
                    | Some t0 => typD t0
                    | None => unit
                  end) with
        | pSome BIL => empR _ BIL
        | pNone => tt
        end
      | bilf_star t =>
        match gs t as x
              return (match match x with
			      | pSome _ => Some (tyArr t (tyArr t t))
			      | pNone => None
			    end with
			| Some t0 => typD t0
			| None => unit
		      end) with
	  | pSome t => starR _ t
	  | pNone => tt
        end
      | bilf_wand t =>
        match gs t as x
              return (match match x with
			      | pSome _ => Some (tyArr t (tyArr t t))
			      | pNone => None
			    end with
			| Some t0 => typD t0
			| None => unit
		      end) with
	  | pSome t => wandR _ t
	  | pNone => tt
        end
    end.

  Global Instance RSym_bilfunc : SymI.RSym (bilfunc typ) :=
  { typeof_sym := typeof_bilfunc
  ; sym_eqb := fun a b => Some (rel_dec a b)
  ; symD := funcD
  }.

  Global Instance RSymOk_bilfunc : SymI.RSymOk RSym_bilfunc.
  Proof.
    constructor.
    intros. unfold sym_eqb; simpl.
    consider (a ?[ eq ] b); auto.
  Qed.
  
End BILogicFuncInst.

Section MakeBILogic.
  Context {typ func : Type} {FV : FuncView func (bilfunc typ)}.

  Definition fEmp t := f_insert (bilf_emp t).
  Definition fStar t := f_insert (bilf_star t).
  Definition fWand t := f_insert (bilf_wand t).

  Definition mkEmp t : expr typ func := Inj (fEmp t).
  Definition mkStar (t : typ) (P Q : expr typ func) := App (App (Inj (fStar t)) P) Q.
  Definition mkWand (t : typ) (P Q : expr typ func) := App (App (Inj (fWand t)) P) Q.

  Definition fptrnEmp {T : Type} (p : Ptrns.ptrn typ T) : ptrn (bilfunc typ) T :=
    fun f U good bad =>
      match f with
        | bilf_emp t => p t U good (fun x => bad f)
        | _ => bad f
      end.

  Definition fptrnStar {T : Type} (p : Ptrns.ptrn typ T) : ptrn (bilfunc typ) T :=
    fun f U good bad =>
      match f with
        | bilf_star t => p t U good (fun x => bad f)
        | _ => bad f
      end.

  Definition fptrnWand {T : Type} (p : Ptrns.ptrn typ T) : ptrn (bilfunc typ) T :=
    fun f U good bad =>
      match f with
        | bilf_wand t => p t U good (fun x => bad f)
        | _ => bad f
      end.

  Global Instance fptrnEmp_ok {T : Type} {p : ptrn typ T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnEmp p).
  Proof.
    red; intros.
    destruct x; try (right; unfold Fails; reflexivity); destruct (Hok logic).
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
  Qed.

  Global Instance fptrnStar_ok {T : Type} {p : ptrn typ T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnStar p).
  Proof.
    red; intros.
    destruct x; try (right; unfold Fails; reflexivity); destruct (Hok logic).
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
  Qed.

  Global Instance fptrnWand_ok {T : Type} {p : ptrn typ T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnWand p).
  Proof.
    red; intros.
    destruct x; try (right; unfold Fails; reflexivity); destruct (Hok logic).
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
  Qed.

  Lemma Succeeds_fptrnEmp {T : Type} (f : bilfunc typ) (p : ptrn typ T) (res : T)
        {pok : ptrn_ok p} (H : Succeeds f (fptrnEmp p) res) :
    exists t, Succeeds t p res /\ f = bilf_emp t.
  Proof.
    unfold Succeeds, fptrnEmp in H.
    unfold ptrn_ok in pok.
    specialize (H (option T) Some (fun _ => None)).
    destruct f; try congruence.
    specialize (pok logic).
    destruct pok; [|rewrite H0 in H; congruence].
    destruct H0.
    rewrite H0 in H; inv_all; subst.
    exists logic; split; [assumption | reflexivity].
  Qed.

  Lemma Succeeds_fptrnStar {T : Type} (f : bilfunc typ) (p : ptrn typ T) (res : T)
        {pok : ptrn_ok p} (H : Succeeds f (fptrnStar p) res) :
    exists t, Succeeds t p res /\ f = bilf_star t.
  Proof.
    unfold Succeeds, fptrnStar in H.
    unfold ptrn_ok in pok.
    specialize (H (option T) Some (fun _ => None)).
    destruct f; try congruence.
    specialize (pok logic).
    destruct pok; [|rewrite H0 in H; congruence].
    destruct H0.
    rewrite H0 in H; inv_all; subst.
    exists logic; split; [assumption | reflexivity].
  Qed.

  Lemma Succeeds_fptrnWand {T : Type} (f : bilfunc typ) (p : ptrn typ T) (res : T)
        {pok : ptrn_ok p} (H : Succeeds f (fptrnWand p) res) :
    exists t, Succeeds t p res /\ f = bilf_wand t.
  Proof.
    unfold Succeeds, fptrnWand in H.
    unfold ptrn_ok in pok.
    specialize (H (option T) Some (fun _ => None)).
    destruct f; try congruence.
    specialize (pok logic).
    destruct pok; [|rewrite H0 in H; congruence].
    destruct H0.
    rewrite H0 in H; inv_all; subst.
    exists logic; split; [assumption | reflexivity].
  Qed.
  
  Global Instance fptrnEmp_SucceedsE {T : Type} {f : bilfunc typ} 
         {p : ptrn typ T} {res : T} {pok : ptrn_ok p} :
    SucceedsE f (fptrnEmp p) res := {
      s_result := exists t, Succeeds t p res /\ f = bilf_emp t;
      s_elim := @Succeeds_fptrnEmp T f p res pok
    }.

  Global Instance fptrnAnd_SucceedsE {T : Type} {f : bilfunc typ} 
         {p : ptrn typ T} {res : T} {pok : ptrn_ok p} :
    SucceedsE f (fptrnStar p) res := {
      s_result := exists t, Succeeds t p res /\ f = bilf_star t;
      s_elim := @Succeeds_fptrnStar T f p res pok
    }.

  Global Instance fptrnWand_SucceedsE {T : Type} {f : bilfunc typ} 
         {p : ptrn typ T} {res : T} {pok : ptrn_ok p} :
    SucceedsE f (fptrnWand p) res := {
      s_result := exists t, Succeeds t p res /\ f = bilf_wand t;
      s_elim := @Succeeds_fptrnWand T f p res pok
    }.

End MakeBILogic.

Section BILogicPtrn.
  Context {typ func : Type} {FV : FuncView func (bilfunc typ)}.
  
 Definition ptrnEmp {T : Type}
             (p : ptrn typ T) : ptrn (expr typ func) T :=
    inj (ptrn_view _ (fptrnEmp p)).

  Definition ptrnStar {A B T : Type}
             (p : ptrn typ T)
             (a : ptrn (expr typ func) A) 
             (b : ptrn (expr typ func) B) : ptrn (expr typ func) (T * A * B) :=
    app (app (inj (ptrn_view _ (fptrnStar p))) a) b.

  Definition ptrnWand {A B T : Type}
             (p : ptrn typ T)
             (a : ptrn (expr typ func) A) 
             (b : ptrn (expr typ func) B) : ptrn (expr typ func) (T * A * B) :=
    app (app (inj (ptrn_view _ (fptrnWand p))) a) b.

  Definition bilogic_ptrn_cases {T : Type}
             (do_emp : typ -> T)
             (do_star : typ -> expr typ func -> expr typ func -> T)
             (do_wand : typ -> expr typ func -> expr typ func -> T) :=
    por (inj (ptrn_view _ (fptrnEmp (pmap do_emp Ptrns.get))))
        (appr (appr (inj (ptrn_view _ (por (fptrnStar (pmap do_star Ptrns.get))
                                           (fptrnWand (pmap do_wand Ptrns.get))))) 
                    Ptrns.get) 
              Ptrns.get).

  Definition bilogic_cases {T : Type}
             (do_emp : typ -> T)
             (do_star : typ -> expr typ func -> expr typ func -> T)
             (do_wand : typ -> expr typ func -> expr typ func -> T)
             (do_default : T) :=
      run_ptrn (bilogic_ptrn_cases
                  do_emp do_star do_wand)
               do_default.
End BILogicPtrn.