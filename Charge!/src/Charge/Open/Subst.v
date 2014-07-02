Require Import Stack Open Rel.
Require Import List FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Fixpoint zip {A} {B} (lst1 : list A) (lst2 : list B) : list (A * B) :=
  match (lst1, lst2) with
    | (nil, nil) => nil
    | (x::xs, nil) => nil
    | (nil, y::ys) => nil
    | (x::xs, y::ys) => (x, y) :: zip xs ys
  end.

Section Subst.
  Context {A : Type} `{HEq: DecidableEq A}.
  Context {R : ValNull}.

  Definition subst := A -> @open A R val.

  Definition stack_subst (s: stack A) (sub: subst) : stack A :=
    fun x => sub x s.

  Definition apply_subst {B}
          (e : @open A R B) (sub : subst) : @open A R B :=
    fun s => e (stack_subst s sub).

  Definition substlist := list (A * @expr A R).

  (* The identity substitution *)
  Definition subst0 : subst := fun x => x/V.

  (* Substitution of one variable *)
  Definition subst1 e x : subst :=
    fun x' => if dec_eq x' x then e else x'/V.

  (* Truncating substitution of one variable *)
  Definition subst1_trunc e x : subst :=
    fun x' => if dec_eq x' x then e else empty_open.

  (* Simultaneous substitution of a finite list of variables *)
  Fixpoint substl_aux (subs: substlist) : subst :=
    match subs with
      | nil => subst0
      | (x,e) :: subs' => fun x' => 
        if dec_eq x' x then e else substl_aux subs' x'
    end.

(* Truncating simultaneous substitution of a finite list of variables *)
  Fixpoint substl_trunc_aux (subs: substlist) : subst :=
    match subs with
      | nil => fun _ => empty_open
      | (x,e) :: subs' => fun x' => 
        if dec_eq x' x then e else substl_trunc_aux subs' x'
    end.

  Definition substl es v := substl_aux es v.
  Definition substl_trunc es v := substl_trunc_aux es v.

End Subst.

(* Binds tighter than function application *)
(* We have the e at precedence level one less than the precedence of the infix
   // operator to make parsing work. *)

Notation "g [{ e // x }]" := (apply_subst g (subst1 e x)) (at level 9, e at level 39,
  format "g [{ e // x }]") : open_scope.

Notation "g [{ e //! x }]" := (apply_subst g (subst1_trunc e x)) (at level 9, e at level 39,
  format "g [{ e //! x }]") : open_scope.

Notation " g '//' es " := (apply_subst g (substl es)) (at level 40) : open_scope.

Notation " g '//!' es " := (apply_subst g (substl_trunc es)) (at level 40) : open_scope.

Section Properties.
  Context {A : Type} `{Heq: DecidableEq A}.
  Context {R : ValNull}.

  Lemma open_subst_stack {B} (m: @open A R B) (sub : subst) (s : @stack A R) :
    (apply_subst m sub) s = m (stack_subst s sub).
  Proof. reflexivity. Qed.

  Lemma subst0_id B (g: @open A R B) : (apply_subst g (@subst0 A R)) = g.
  Proof.
    apply functional_extensionality.
    intros s; simpl; reflexivity.
  Qed.

  Lemma subst1_stack (s: @stack A R) e x :
    stack_subst s (subst1 e x) = stack_add x (e s) s.
  Proof.
    apply functional_extensionality; intro x'; simpl.
    unfold stack_subst, subst1, stack_add. 
    destruct (dec_eq x' x); reflexivity.
  Qed.

  Lemma substl_subst1 x e :
    substl ((x,e)::nil) = subst1 e x.
  Proof. 
    reflexivity.
  Qed.

  Lemma substl_subst1_trunc x e :
    substl_trunc ((x,e)::nil) = subst1_trunc e x.
  Proof. 
    reflexivity.
  Qed.

  Local Open Scope open_scope.
  Lemma subst1_stack_add {B} (p : open B) (e : expr) (x : A) (v : val) (s : @stack A R) : 
    p[{e//x}] (stack_add x v s) = p[{e[{`v//x}]//x}] s.
  Proof.
    unfold apply_subst, subst1; simpl.
    apply f_equal.
    unfold stack_subst.
    apply functional_extensionality.
    intros y.
    remember (dec_eq y x) as d.
    destruct d; simpl.
    apply f_equal.
    apply functional_extensionality.
    intros z; simpl.
    remember (dec_eq z x) as d'.
    destruct d'; subst.
    rewrite stack_lookup_add. reflexivity.
    rewrite stack_lookup_add2. reflexivity.
    intuition.
    unfold var_expr.
    rewrite stack_lookup_add2. reflexivity.
    intuition.
  Qed.
      
  Lemma stack_add_var (x : A) (s : @stack A R) (v : val) : (x/V) (stack_add x v s) = v.
  Proof.
    unfold var_expr. rewrite stack_lookup_add. reflexivity.
  Qed.
  
  Lemma subst1_val (v : val) (e : open val) (x : A) :
    `v[{e//x}] = `v.
  Proof.
    reflexivity.
  Qed.

  Lemma subst_identity {B} (x : A) (s : @stack A R) (p : open B) :
    p[{`(s x)//x}] s = p s.
  Proof.
    unfold subst1, apply_subst.
    apply f_equal.
    unfold stack_subst; simpl.
    apply functional_extensionality.
    intros y; simpl.
    destruct (dec_eq y x); subst; reflexivity.
  Qed.

  Lemma substl_trunc_notin x' xs es :
    ~ In x' xs ->
    substl_trunc (zip xs es) x' = @empty_open _ R.
  Proof.
    intro HnotIn. revert es. induction xs as [|x]; intros.
    + simpl. destruct es; reflexivity.
    + destruct es as [|e]; [reflexivity|]. simpl. destruct (dec_eq x' x) as [|_].
      - subst. contradiction HnotIn. simpl. auto.
      - apply IHxs. auto with datatypes.
  Qed.

  Lemma subst1_trunc_singleton_stack {B} (p : open B) (s : @stack A R) x y :
    p[{y/V //! x}] s = p (stack_add x (s y) (stack_empty A)).
  Proof.
    unfold apply_subst, subst1_trunc, stack_subst; simpl.
    apply f_equal.
    apply functional_extensionality.
    intro x'.
    destruct (dec_eq x' x); subst.
    * rewrite stack_lookup_add.
      reflexivity.
    * rewrite stack_lookup_add2; [| auto].
      reflexivity.
  Qed.

End Properties.

Hint Rewrite @subst0_id : open.
Hint Rewrite @substl_subst1 : open.
Hint Rewrite @substl_trunc_notin using assumption : open.

Section MoreLemmas.
  Context {A : Type} {Heq : DecidableEq A}.
  Context {R : ValNull}.

  Open Scope open_scope.

  Lemma subst_singleton {B} : 
    forall x e (P : @open A R B), P[{e//x}] = P // ((x, e)::nil).
  Proof.
    reflexivity.
  Qed.

  Lemma subst_open_expr_nil {B} :
    forall (e : @open A R B), (e // nil) = e.
  Proof.
    reflexivity.
  Qed.

  Lemma subst_var_cons_eq : 
    forall (x:A) es (e : expr), ((x/V) // ((x, e)::es)) = e.
  Proof.
    intros x es e.
    apply functional_extensionality; intros s; simpl.
    unfold var_expr, apply_subst, stack_subst. simpl.
    case (dec_eq x x); intuition congruence.
  Qed.

  Lemma subst_var_cons_ineq : forall (x:A) y es (e : expr)
    (Hneq: x <> y),
    ((x/V) // ((y, e)::es)) = ((x/V) // es).
  Proof.
    intros x y es e Hneq.
    apply functional_extensionality; intros s.
    unfold var_expr, apply_subst, stack_subst; simpl.
    case (dec_eq x y); congruence.
  Qed.

  Lemma val_expr_substs : forall (v : val) es,
    ((V_expr v) // es) = (V_expr v).
  Proof.
    reflexivity.
  Qed.


  Definition subst_substlist (es fs : @substlist A R) : substlist :=
    map (fun x => (fst x, (snd x) // fs)) es.

  Lemma subst_combine {B} (e : @open A R B) (es fs : substlist) :
    (e // es // fs) = (e // ((subst_substlist es fs)++fs)).
  Proof.
    apply functional_extensionality; intros s.
    unfold apply_subst, stack_subst; simpl.
    f_equal. apply functional_extensionality. intros x.
    induction es; simpl.
    + reflexivity.
    + destruct a; simpl.
      destruct (dec_eq x a); simpl.
      * reflexivity.
      * apply IHes.
  Qed.


Close Scope open_scope.

End MoreLemmas.

Section SubstFresh.

  Context {A : Type} `{HEq: DecidableEq A}.
  Context {R : ValNull}.

    Definition subst_fresh (vs: A -> val) (xs: list A) : subst :=
      fun x' => if In_dec dec_eq x' xs then V_expr (vs x') else var_expr x'.

   Fixpoint subst_fresh_l (vs: A -> val) (xs: list A) : list (@expr A R) :=
      match xs with
      | nil => nil
      | x::xs' => V_expr (vs x) :: subst_fresh_l vs xs'
      end.

    (* TODO: switch the two alt. definitions. *)
    Lemma subst_fresh_alt (vs: A -> val) (xs: list A) :
      subst_fresh vs xs = substl (zip xs (subst_fresh_l vs xs)).
    Proof.
      induction xs as [|x]; [reflexivity|].
      apply functional_extensionality.
      intro x'. simpl. destruct (dec_eq x' x).
      + subst x'. unfold subst_fresh. simpl.
        destruct (dec_eq x x); congruence.
      + rewrite <- IHxs. unfold subst_fresh.
        simpl. destruct (dec_eq x x'); [congruence|].
        destruct (in_dec dec_eq x' xs); reflexivity.
    Qed.

End SubstFresh.
