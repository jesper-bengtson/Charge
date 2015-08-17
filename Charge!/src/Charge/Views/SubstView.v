Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.String.
Require Import ExtLib.Data.Map.FMapPositive.
Require Import ExtLib.Data.SumN.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.syms.SymEnv.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprVariables.
Require Import MirrorCore.Lambda.ExprTac.
Require Import MirrorCore.Lambda.Ptrns.
Require Import MirrorCore.SymI.
Require Import MirrorCore.syms.SymSum.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.Views.ApplicativeView.
Require Import MirrorCore.Views.StringView.
Require Import MirrorCore.Views.ListView.
Require Import MirrorCore.Views.ProdView.

Require Import Charge.Views.ILogicView.
Require Import Charge.Views.BILogicView.
Require Import Charge.Views.EmbedView.

Require Import ChargeCore.Logics.ILogic.
Require Import ChargeCore.Open.Stack.
Require Import ChargeCore.Open.Subst.

Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import FunctionalExtensionality.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Inductive subst_func {typ : Type} :=
| of_null
| of_stack_get
| of_stack_set
| of_apply_subst (_ : typ)
| of_single_subst
| of_subst
| of_trunc_subst.
    
Implicit Arguments subst_func [].

Section SubstFuncInst.
  Context {typ func : Type} {RType_typ : RType typ}.
  Context {Heq : RelDec (@eq typ)} {HC : RelDec_Correct Heq}.
  Context {var val : Type}.

  Context {Heq_var : RelDec (@eq var)}.
  Context {HV : ValNull val}.

  Context {Typ0_tyVal : Typ0 _ val}.
  Context {Typ0_tyVar : Typ0 _ var}.
  Context {Typ2_tyArr : Typ2 _ Fun}.
  Context {Typ2_tyProd : Typ2 _ prod}.
  Context {Typ1_tyList : Typ1 _ list}.
  Context {Typ0_tyProp : Typ0 _ Prop}.
  
  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ Typ2_tyArr.
  Let tyProd : typ -> typ -> typ := @typ2 _ _ _ Typ2_tyProd.
  Let tyList : typ -> typ := @typ1 _ _ _ Typ1_tyList.
  Let tyProp : typ := @typ0 _ _ _ Typ0_tyProp.
  Let tyVal : typ := @typ0 _ _ _ Typ0_tyVal.
  Let tyVar : typ := @typ0 _ _ _ Typ0_tyVar.
  
  Local Notation "'tyStack'" := (tyArr tyVar tyVal).
  Local Notation "'tySubst'" := (tyArr tyVar (tyArr tyStack tyVal)).
  Local Notation "'tyExpr'" := (tyArr tyStack tyVal).
  Local Notation "'tySubstList'" := (tyList (tyProd tyVar (tyArr tyStack tyVal))).

  Local Notation "'Tstack'" := (Fun var val).
  Local Notation "'Tsubst'" := (Fun var (Fun (Fun var val) val)).
  Local Notation "'Texpr'" := (Fun (Fun var val) val).
  Local Notation "'Tsubstlist'" := (list (var * Texpr)).
        
  Definition stack := @stack (typD tyVar) (typD tyVal).

  Global Instance typDValNull : ValNull (typD tyVal).
  Proof.
    unfold tyVal.
    rewrite typ0_cast.
    apply _.
  Qed.
  
  Definition typeof_subst_func (f : subst_func typ) : option typ :=
    match f with
    | of_apply_subst t => Some (tyArr (tyArr tyStack t) (tyArr tySubst (tyArr tyStack t)))
    | of_null => Some tyVal
    | of_stack_get => Some (tyArr tyVar tyExpr)
    | of_stack_set => Some (tyArr tyVar (tyArr tyVal (tyArr tyStack tyStack)))
    | of_single_subst => Some (tyArr tyExpr (tyArr tyVar tySubst))
    | of_subst => Some (tyArr tySubstList tySubst)
    | of_trunc_subst => Some (tyArr tySubstList tySubst)
    end.

  Global Instance RelDec_open_func : RelDec (@eq (subst_func typ)) :=
    { rel_dec := fun a b =>
	           match a, b with
	  	   | of_apply_subst t, of_apply_subst t' => t ?[eq] t'
	  	   | of_null, of_null
	  	   | of_stack_get, of_stack_get
	  	   | of_stack_set, of_stack_set
	  	   | of_single_subst, of_single_subst
	  	   | of_subst, of_subst
	  	   | of_trunc_subst, of_trunc_subst => true
	  	   | _, _ => false
	           end
    }.

  Global Instance RelDec_Correct_open_func : RelDec_Correct RelDec_open_func.
  Proof.
    constructor.
    destruct x; destruct y; simpl; try rewrite andb_true_iff;
    repeat rewrite rel_dec_correct; try intuition congruence.
  Qed.
  
	
  Definition stack_getR : typD (tyArr tyVar (tyArr tyStack tyVal)) :=
    castR id (Fun var (Fun Tstack val)) (fun x s => s x).

  Definition stack_setR : typD (tyArr tyVar (tyArr tyVal (tyArr tyStack tyStack))) :=
    castR id (Fun var (Fun val (Fun Tstack Tstack))) stack_add.
  
  Definition applySubstR (t : typ) : typD (tyArr (tyArr tyStack t) 
                                                 (tyArr tySubst (tyArr tyStack t))) :=
    castR id (Fun (Fun Tstack (typD t)) (Fun Tsubst (Fun Tstack (typD t)))) 
          apply_subst.

  Definition singleSubstR : typD (tyArr tyExpr (tyArr tyVar tySubst)) :=
    castR id (Fun Texpr (Fun var Tsubst)) subst1.

  Definition parSubstR : typD (tyArr tySubstList tySubst) :=
    castR id (Fun Tsubstlist Tsubst) substl_aux.

  Definition truncSubstR : typD (tyArr tySubstList tySubst) :=
    castR id (Fun Tsubstlist Tsubst) substl_trunc_aux.
	   
  Definition open_func_symD f : match typeof_subst_func f return Type with
	                        | Some t => typD t
	                        | None => unit
	                        end :=
    match f as f return match typeof_subst_func f return Type with
			| Some t => typD t
			| None => unit
			end with
    | of_null => null
    | of_stack_get => stack_getR
    | of_stack_set => stack_setR
    | of_apply_subst t => applySubstR t
    | of_single_subst => singleSubstR
    | of_subst => parSubstR
    | of_trunc_subst => truncSubstR
    end.

  Global Instance RSym_SubstFunc : SymI.RSym (subst_func typ) := {
    typeof_sym := typeof_subst_func;
    symD := open_func_symD;
    sym_eqb := (fun a b => Some (rel_dec a b))
  }.

  Global Instance RSymOk_lsubst_func : SymI.RSymOk RSym_SubstFunc.
  Proof.
    constructor.
    intros. unfold sym_eqb; simpl.
    consider (a ?[ eq ] b); auto.
  Qed.

End SubstFuncInst.

Section MakeSubst.
  Context {typ func : Type} {FV : FuncView func (subst_func typ)}.

  Definition fNull := f_insert of_null.
  Definition fStackGet := f_insert of_stack_get.
  Definition fStackSet := f_insert of_stack_set.
  Definition fApplySubst t := f_insert (of_apply_subst t).
  Definition fSingleSubst := f_insert of_single_subst.
  Definition fSubst := f_insert of_subst.
  Definition fTruncSubst := f_insert of_trunc_subst.
  
  Definition mkNull : expr typ func := Inj fNull.
  Definition mkStackGet : expr typ func := Inj fStackGet.
  Definition mkStackSet : expr typ func := Inj fStackSet.
  Definition mkApplySubst t : expr typ func := Inj (fApplySubst t).
  Definition mkSingleSubst : expr typ func := Inj fSingleSubst.
  Definition mkSubst : expr typ func := Inj fSubst.
  Definition mkTruncSubst : expr typ func := Inj fTruncSubst.
  
  Definition fptrnNull : ptrn (subst_func typ) unit :=
    fun f U good bad =>
      match f with
      | of_null => good tt
      | of_stack_get => bad of_stack_get
      | of_stack_set => bad of_stack_set
      | of_apply_subst t => bad (of_apply_subst t)
      | of_single_subst => bad of_single_subst
      | of_subst => bad of_subst
      | of_trunc_subst => bad of_trunc_subst
      end.
  
  Definition fptrnStackGet : ptrn (subst_func typ) unit :=
    fun f U good bad =>
      match f with
      | of_null => bad of_null
      | of_stack_get => good tt
      | of_stack_set => bad of_stack_set
      | of_apply_subst t => bad (of_apply_subst t)
      | of_single_subst => bad of_single_subst
      | of_subst => bad of_subst
      | of_trunc_subst => bad of_trunc_subst
      end.
  
  Definition fptrnStackSet : ptrn (subst_func typ) unit :=
    fun f U good bad =>
      match f with
      | of_null => bad of_null
      | of_stack_get => bad of_stack_get
      | of_stack_set => good tt
      | of_apply_subst t => bad (of_apply_subst t)
      | of_single_subst => bad of_single_subst
      | of_subst => bad of_subst
      | of_trunc_subst => bad of_trunc_subst
      end.
  
  Definition fptrnApplySubst {T : Type} (p : Ptrns.ptrn typ T) : ptrn (subst_func typ) T :=
    fun f U good bad =>
      match f with
      | of_null => bad of_null
      | of_stack_get => bad of_stack_get
      | of_stack_set => bad of_stack_set
      | of_apply_subst t => p t U good (fun x => bad f)
      | of_single_subst => bad of_single_subst
      | of_subst => bad of_subst
      | of_trunc_subst => bad of_trunc_subst
      end.
  
  Definition fptrnSingleSubst : ptrn (subst_func typ) unit :=
    fun f U good bad =>
      match f with
      | of_null => bad of_null
      | of_stack_get => bad of_stack_get
      | of_stack_set => bad of_stack_set
      | of_apply_subst t => bad (of_apply_subst t)
      | of_single_subst => good tt
      | of_subst => bad of_subst
      | of_trunc_subst => bad of_trunc_subst
      end.
  
  Definition fptrnSubst : ptrn (subst_func typ) unit :=
    fun f U good bad =>
      match f with
      | of_null => bad of_null
      | of_stack_get => bad of_stack_get
      | of_stack_set => bad of_stack_set
      | of_apply_subst t => bad (of_apply_subst t)
      | of_single_subst => bad of_single_subst
      | of_subst => good tt
      | of_trunc_subst => bad of_trunc_subst
      end.
  
  Definition fptrnTruncSubst : ptrn (subst_func typ) unit :=
    fun f U good bad =>
      match f with
      | of_null => bad of_null
      | of_stack_get => bad of_stack_get
      | of_stack_set => bad of_stack_set
      | of_apply_subst t => bad (of_apply_subst t)
      | of_single_subst => bad of_single_subst
      | of_subst => bad of_subst
      | of_trunc_subst => good tt
      end.
  
  Global Instance fptrnNull_ok {T : Type} : ptrn_ok fptrnNull.
  Proof.
    red; intros.
    destruct x; simpl; try (right; unfold Fails; reflexivity).
    left; exists tt; compute; reflexivity.
  Qed.
  
  Global Instance fptrnStackGet_ok {T : Type} : ptrn_ok fptrnStackGet.
  Proof.
    red; intros.
    destruct x; simpl; try (right; unfold Fails; reflexivity).
    left; exists tt; compute; reflexivity.
  Qed.

  Global Instance fptrnStackSet_ok {T : Type} : ptrn_ok fptrnStackSet.
  Proof.
    red; intros.
    destruct x; simpl; try (right; unfold Fails; reflexivity).
    left; exists tt; compute; reflexivity.
  Qed.

  Global Instance fptrnApplySubst_ok {T : Type} {p : ptrn typ T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnApplySubst p).
  Proof.
    red; intros.
    destruct x; simpl; try (right; unfold Fails; reflexivity); destruct (Hok t).
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
  Qed.

  Global Instance fptrnSingleSubst_ok {T : Type} : ptrn_ok fptrnSingleSubst.
  Proof.
    red; intros.
    destruct x; simpl; try (right; unfold Fails; reflexivity).
    left; exists tt; compute; reflexivity.
  Qed.

  Global Instance fptrnSubst_ok {T : Type} : ptrn_ok fptrnSubst.
  Proof.
    red; intros.
    destruct x; simpl; try (right; unfold Fails; reflexivity).
    left; exists tt; compute; reflexivity.
  Qed.

  Global Instance fptrnTruncSubst_ok {T : Type} : ptrn_ok fptrnTruncSubst.
  Proof.
    red; intros.
    destruct x; simpl; try (right; unfold Fails; reflexivity).
    left; exists tt; compute; reflexivity.
  Qed.

  Lemma Succeeds_fptrnNull (f : subst_func typ) (res : unit) (H : Succeeds f fptrnNull res) :
    f = of_null /\ res = tt.
  Proof.
    split; [|destruct res; reflexivity].
    unfold Succeeds, fptrnNull in H.
    specialize (H bool (fun _ => true) (fun _ => false)).
    destruct f; congruence.
  Qed.

  Lemma Succeeds_fptrnStackGet (f : subst_func typ) (res : unit) 
        (H : Succeeds f fptrnStackGet res) :
    f = of_stack_get /\ res = tt.
  Proof.
    split; [|destruct res; reflexivity].
    unfold Succeeds, fptrnStackGet in H.
    specialize (H bool (fun _ => true) (fun _ => false)).
    destruct f; congruence.
  Qed.

  Lemma Succeeds_fptrnStackSet (f : subst_func typ) (res : unit)
        (H : Succeeds f fptrnStackSet res) :
    f = of_stack_set /\ res = tt.
  Proof.
    split; [|destruct res; reflexivity].
    unfold Succeeds, fptrnStackSet in H.
    specialize (H bool (fun _ => true) (fun _ => false)).
    destruct f; congruence.
  Qed.

  Lemma Succeeds_fptrnApplySubst {T : Type} (f : subst_func typ) (p : ptrn typ T) (res : T)
        {pok : ptrn_ok p} (H : Succeeds f (fptrnApplySubst p) res) :
    exists t, Succeeds t p res /\ f = of_apply_subst t.
  Proof.
    unfold Succeeds, fptrnApplySubst in H.
    unfold ptrn_ok in pok.
    specialize (H (option T) Some (fun _ => None)).
    destruct f; try congruence.
    specialize (pok t).
    destruct pok; [|rewrite H0 in H; congruence].
    destruct H0.
    rewrite H0 in H; inv_all; subst.
    exists t; split; [assumption | reflexivity].
  Qed.

  Lemma Succeeds_fptrnSingleSubst (f : subst_func typ) (res : unit)
        (H : Succeeds f fptrnSingleSubst res) :
    f = of_single_subst /\ res = tt.
  Proof.
    split; [|destruct res; reflexivity].
    unfold Succeeds, fptrnSingleSubst in H.
    specialize (H bool (fun _ => true) (fun _ => false)).
    destruct f; congruence.
  Qed.

  Lemma Succeeds_fptrnSubst (f : subst_func typ) (res : unit)
        (H : Succeeds f fptrnSubst res) :
    f = of_subst /\ res = tt.
  Proof.
    split; [|destruct res; reflexivity].
    unfold Succeeds, fptrnSubst in H.
    specialize (H bool (fun _ => true) (fun _ => false)).
    destruct f; congruence.
  Qed.

  Lemma Succeeds_fptrnTruncSubst (f : subst_func typ) (res : unit)
        (H : Succeeds f fptrnTruncSubst res) :
    f = of_trunc_subst /\ res = tt.
  Proof.
    split; [|destruct res; reflexivity].
    unfold Succeeds, fptrnTruncSubst in H.
    specialize (H bool (fun _ => true) (fun _ => false)).
    destruct f; congruence.
  Qed.

  Global Instance fptrnNull_SucceedsE {f : subst_func typ} {res : unit} :
    SucceedsE f fptrnNull res := {
      s_result := f = of_null /\ res = tt;
      s_elim := @Succeeds_fptrnNull f res
    }.

  Global Instance fptrnStackGet_SucceedsE {f : subst_func typ} {res : unit} :
    SucceedsE f fptrnStackGet res := {
      s_result := f = of_stack_get /\ res = tt;
      s_elim := @Succeeds_fptrnStackGet f res
    }.

  Global Instance fptrnStackSet_SucceedsE {f : subst_func typ} {res : unit} :
    SucceedsE f fptrnStackSet res := {
      s_result := f = of_stack_set /\ res = tt;
      s_elim := @Succeeds_fptrnStackSet f res
    }.

  Global Instance fptrnCons_SucceedsE {T : Type} {f : subst_func typ} 
         {p : ptrn typ T} {res : T} {pok : ptrn_ok p} :
    SucceedsE f (fptrnApplySubst p) res := {
      s_result := exists t, Succeeds t p res /\ f = of_apply_subst t;
      s_elim := @Succeeds_fptrnApplySubst T f p res pok
    }.

  Global Instance fptrnSingleSubst_SucceedsE {f : subst_func typ} {res : unit} :
    SucceedsE f fptrnSingleSubst res := {
      s_result := f = of_single_subst /\ res = tt;
      s_elim := @Succeeds_fptrnSingleSubst f res
    }.

  Global Instance fptrnSubst_SucceedsE {f : subst_func typ} {res : unit} :
    SucceedsE f fptrnSubst res := {
      s_result := f = of_subst /\ res = tt;
      s_elim := @Succeeds_fptrnSubst f res
    }.

  Global Instance fptrnTruncSubst_SucceedsE {f : subst_func typ} {res : unit} :
    SucceedsE f fptrnTruncSubst res := {
      s_result := f = of_trunc_subst /\ res = tt;
      s_elim := @Succeeds_fptrnTruncSubst f res
    }.

End MakeSubst.

Section SubstPtrn.
  Context {typ func : Type} {FV : FuncView func (subst_func typ)}.
  
  Definition ptrnNull : ptrn (expr typ func) unit :=
    inj (ptrn_view _ fptrnNull).

  Definition ptrnStackGet {A B : Type}
             (a : ptrn (expr typ func) A) 
             (b : ptrn (expr typ func) B) : ptrn (expr typ func) (A * B) :=
    pmap (fun t_a_b => let '(t, a, b) := t_a_b in (a, b)) 
         (app (app (inj (ptrn_view _ fptrnStackGet)) a) b).

  Definition ptrnStackSet {A B C : Type}
             (a : ptrn (expr typ func) A) 
             (b : ptrn (expr typ func) B)
             (c : ptrn (expr typ func) C) : ptrn (expr typ func) (A * B * C) :=
    pmap (fun t_a_b_c => let '(t, a, b, c) := t_a_b_c in (a, b, c)) 
         (app (app (app (inj (ptrn_view _ fptrnStackSet)) a) b) c).

  Definition ptrnApplySubst {A B T : Type}
             (p : ptrn typ T)
             (a : ptrn (expr typ func) A) 
             (b : ptrn (expr typ func) B) : ptrn (expr typ func) (T * A * B) :=
    app (app (inj (ptrn_view _ (fptrnApplySubst p))) a) b.

  Definition ptrnSingleSubst {A B : Type}
             (a : ptrn (expr typ func) A) 
             (b : ptrn (expr typ func) B) : ptrn (expr typ func) (A * B) :=
    pmap (fun t_a_b => let '(t, a, b) := t_a_b in (a, b)) 
         (app (app (inj (ptrn_view _ fptrnSingleSubst)) a) b).

  Definition ptrnSubst {A : Type}
             (a : ptrn (expr typ func) A) : ptrn (expr typ func) A :=
    pmap snd (app (inj (ptrn_view _ fptrnSubst)) a).

  Definition ptrnTruncSubst {A : Type}
             (a : ptrn (expr typ func) A) : ptrn (expr typ func) A :=
    pmap snd (app (inj (ptrn_view _ fptrnTruncSubst)) a).
End SubstPtrn.

Section SubstTac.
  Context {typ func : Type} {RType_typ : RType typ}.
  Context {FV_subst : FuncView func (subst_func typ)}.
  Context {FV_ap : FuncView func (ap_func typ)}.
  Context {FV_string : FuncView func stringFunc}.
  Context {FV_list : FuncView func (list_func typ)}.
  Context {FV_prod : FuncView func (prod_func typ)}.
  Context {FV_ilogic : FuncView func (ilfunc typ)}.
  Context {FV_bilogic : FuncView func (bilfunc typ)}.
  Context {FV_embed : FuncView func (embed_func typ)}.
  Context {Heq : RelDec (@eq typ)} {HC : RelDec_Correct Heq}.
  Context {val : Type}.

  Context {HV : ValNull val}.

  Context {Typ0_tyVal : Typ0 _ val}.
  Context {Typ0_tyString : Typ0 _ string}.
  Context {Typ2_tyArr : Typ2 _ Fun}.
  Context {Typ2_tyProd : Typ2 _ prod}.
  Context {Typ1_tyList : Typ1 _ list}.
  Context {Typ0_tyProp : Typ0 _ Prop}.
  
  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ Typ2_tyArr.
  Let tyProd : typ -> typ -> typ := @typ2 _ _ _ Typ2_tyProd.
  Let tyList : typ -> typ := @typ1 _ _ _ Typ1_tyList.
  Let tyProp : typ := @typ0 _ _ _ Typ0_tyProp.
  Let tyVal : typ := @typ0 _ _ _ Typ0_tyVal.
  Let tyString : typ := @typ0 _ _ _ Typ0_tyString.

  Definition red_substF (red_subst : string -> expr typ func -> expr typ func) (x : string)
             (sub : expr typ func) : expr typ func := 
    Eval compute in
      run_tptrn (list_cases
                   (fun _ => mkString x)
                   (fun _ p ps =>
                      run_tptrn (pdefault_id (pmap (fun t_y_e => let '(t, y, e) := t_y_e in
                                                                 if x ?[ eq ] y then
                                                                   e
                                                             else
                                                               red_subst x ps)
                                                   (ptrnPair ignore (ptrnString Ptrns.get) 
                                                             Ptrns.get))) p)
                   (mkString x)) sub.
  
  Fixpoint do_subst (x : string) (sub : expr typ func) {struct sub} : expr typ func :=
    red_substF (do_subst) x sub.
  
  Definition red_substF' (red_subst : string -> expr typ func -> expr typ func) (x : string)
             (sub : expr typ func) : expr typ func := 
    run_tptrn (list_cases
                 (fun _ => mkString x)
                 (fun _ p ps =>
                    run_tptrn (pdefault_id (pmap (fun t_y_e => let '(t, y, e) := t_y_e in
                                                               if x ?[ eq ] y then
                                                                 e
                                                               else
                                                                 red_subst x ps)
                                                 (ptrnPair ignore (ptrnString Ptrns.get) 
                                                           Ptrns.get))) p)
                 (mkString x)) sub.
  
  
  Definition red_apply_subst (x : string) (f : expr typ func) : expr typ func :=
    run_tptrn (pdefault (por (pmap (fun y_e => let '(y, e) := y_e in
                                               if x ?[ eq ] y then e else mkString x)
                                   (ptrnSingleSubst (ptrnString Ptrns.get) Ptrns.get))
                             (pmap (fun sub => do_subst x sub) (ptrnSubst Ptrns.get)))
                        (mkString x)) f.
  Definition rop {X T : Type} (l r : ptrn X T) := por r l.
  
  Definition red_push_substF
             (red_push_subst : typ -> expr typ func -> expr typ func -> expr typ func)
             (t : typ) (e sub : expr typ func) : expr typ func :=
    Eval compute -[red_apply_subst] in
      run_tptrn (pdefault 
                   (rop
                      (appr (inj (ptrn_view FV_subst (pmap (fun _ s => red_apply_subst s sub) 
                                                           fptrnStackGet)))
                            (inj (ptrn_view FV_string (fptrnString Ptrns.get))))
                      (por (applicative_ptrn_cases
                              (fun _ e => e)
                              (fun t u p q =>
                                 mkAp t u
                                      (red_push_subst (tyArr t u) p sub)
                                      (red_push_subst t q sub)))
                           (por (ilogic_ptrn_cases
                                   (fun t => mkTrue t)
                                   (fun t => mkFalse t)
                                   (fun t p q => 
                                      mkAnd t (red_push_subst t p sub) (red_push_subst t q sub))
                                   (fun t p q => 
                                      mkOr t (red_push_subst t p sub) (red_push_subst t q sub))
                                   (fun t p q => 
                                      mkImpl t (red_push_subst t p sub) (red_push_subst t q sub))
                                   mkExists
                                   mkForall)
                                (por (bilogic_ptrn_cases
                                        (fun t => mkEmp t)
                                        (fun t p q =>
                                           mkStar t (red_push_subst t p sub) (red_push_subst t q sub))
                                        (fun t p q =>
                                           mkWand t (red_push_subst t p sub) (red_push_subst t q sub)))
                                     (appr (inj (ptrn_view FV_embed (fptrnEmbed (pmap (fun x e => mkEmbed (fst x) (snd x) (red_push_subst (snd x) e sub)) Ptrns.get)))) 
                                           Ptrns.get)))))
                 (App (App (mkApplySubst t) e) sub)) e.

  Fixpoint red_push_subst (t : typ) (e sub : expr typ func) {struct e} :=
    red_push_substF red_push_subst t e sub.
  
  Lemma red_push_subst_eta (t : typ) (e sub : expr typ func) :
    red_push_subst t e sub =
    run_tptrn (pdefault 
                 (rop
                    (appr (inj (ptrn_view FV_subst (pmap (fun _ s => red_apply_subst s sub) 
                                                         fptrnStackGet)))
                          (inj (ptrn_view FV_string (fptrnString Ptrns.get))))
                    (por (applicative_ptrn_cases
                            (fun _ e => e)
                            (fun t u p q =>
                               mkAp t u
                                    (red_push_subst (tyArr t u) p sub)
                                    (red_push_subst t q sub)))
                         (por (ilogic_ptrn_cases
                                 (fun t => mkTrue t)
                                 (fun t => mkFalse t)
                                 (fun t p q => 
                                    mkAnd t (red_push_subst t p sub) (red_push_subst t q sub))
                                 (fun t p q => 
                                    mkOr t (red_push_subst t p sub) (red_push_subst t q sub))
                                 (fun t p q => 
                                    mkImpl t (red_push_subst t p sub) (red_push_subst t q sub))
                                 mkExists
                                 mkForall)
                              (por (bilogic_ptrn_cases
                                      (fun t => mkEmp t)
                                      (fun t p q =>
                                         mkStar t (red_push_subst t p sub) (red_push_subst t q sub))
                                      (fun t p q =>
                                         mkWand t (red_push_subst t p sub) (red_push_subst t q sub)))
                                   (appr (inj (ptrn_view FV_embed (fptrnEmbed (pmap (fun x e => mkEmbed (fst x) (snd x) (red_push_subst (snd x) e sub)) Ptrns.get)))) 
                                         Ptrns.get)))))
                 (App (App (mkApplySubst t) e) sub)) e.
  Proof.
    destruct e; simpl; reflexivity.
  Qed.
    
  Definition red_subst : expr typ func -> expr typ func :=
    run_tptrn (pdefault_id 
                 (pmap (fun t_e_sub => let '(t, e, sub) := t_e_sub in
                                       red_push_subst t e sub)
                       (ptrnApplySubst Ptrns.get Ptrns.get Ptrns.get))).

End SubstTac.