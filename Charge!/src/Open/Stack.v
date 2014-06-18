Require Import Rel String.
Require Import FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Class ValNull := {
  val    : Type;
  null   :  val
}.

Section Defs.
  Context {B : ValNull}.

  Definition stack := string -> val.

  Definition stack_empty : stack := fun x => null.

  Definition stack_add x v s : stack :=
    fun x' => if string_dec x' x then v else s x'.

  Lemma stack_lookup_add (s : stack) (x : string) (v : val) :
      ((stack_add x v s) : stack) x = v.
  Proof.
    unfold stack_add. destruct (string_dec x x); congruence.
  Qed.

  Lemma stack_lookup_add2 (x y : string) (v : val) (s : stack) (Hneq: x <> y) :
    (stack_add x v s) y = s y.
  Proof.
    unfold stack_add. destruct (string_dec y x); congruence.
  Qed.

  Lemma stack_add_same (s: stack) x:
    stack_add x (s x) s = s.
  Proof.
    apply functional_extensionality.
    intro x'. unfold stack_add. destruct (string_dec x' x); [rewrite Heq|];
    reflexivity.
  Qed.

  Lemma stack_add_overwrite (s: stack) x v v':
    stack_add x v (stack_add x v' s) = stack_add x v s.
  Proof.
    apply functional_extensionality.
    intro x'. unfold stack_add. destruct (string_dec x' x); reflexivity.
  Qed.
  
  Lemma stack_add_val_eq (s : stack) (x : string) v1 v2 (Hs : stack_add x v1 s = stack_add x v2 s) :
  	v1 = v2.
  Proof.
    assert (stack_add x v1 s x = stack_add x v2 s x).
    rewrite Hs. reflexivity.
    do 2 rewrite stack_lookup_add in H. apply H.
  Qed.
  
End Defs.

Implicit Arguments stack [[B]].
Implicit Arguments stack_empty [[B]].

Hint Rewrite @stack_lookup_add
             @stack_add_same
             @stack_add_overwrite : stack.

Hint Rewrite @stack_lookup_add2 using solve [auto] : stack.