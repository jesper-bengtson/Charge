Require Import Rel.
Require Import FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Class ValNull := {
  val    : Type;
  null   :  val
}.

Section Defs.
  Context {A : Type} {H: DecidableEq A}.
  Context {B : ValNull}.

  Definition stack := A -> val.

  Definition stack_empty : stack := fun x => null.

  Definition stack_add x v s : stack :=
    fun x' => if dec_eq x' x then v else s x'.

  Lemma stack_lookup_add (s : stack) (x : A) (v : val) :
      ((stack_add x v s) : stack) x = v.
  Proof.
    unfold stack_add. destruct (dec_eq x x); congruence.
  Qed.

  Lemma stack_lookup_add2 (x y : A) (v : val) (s : stack) (Hneq: x <> y) :
    (stack_add x v s) y = s y.
  Proof.
    unfold stack_add. destruct (dec_eq y x); congruence.
  Qed.

  Lemma stack_add_same (s: stack) x:
    stack_add x (s x) s = s.
  Proof.
    apply functional_extensionality.
    intro x'. unfold stack_add. destruct (dec_eq x' x); [rewrite e|];
    reflexivity.
  Qed.

  Lemma stack_add_overwrite (s: stack) x v v':
    stack_add x v (stack_add x v' s) = stack_add x v s.
  Proof.
    apply functional_extensionality.
    intro x'. unfold stack_add. destruct (dec_eq x' x); reflexivity.
  Qed.

End Defs.

Implicit Arguments stack [[B]].
Implicit Arguments stack_empty [[B]].

Hint Rewrite @stack_lookup_add
             @stack_add_same
             @stack_add_overwrite : stack.

Hint Rewrite @stack_lookup_add2 using solve [auto] : stack.