Require Import Charge.Tactics.Base.BaseTacs.
Require Import Charge.Tactics.Lists.ListTacs.
Require Import Charge.Tactics.Open.OpenTacs.
Require Import Charge.Tactics.Base.MirrorCoreTacs.
Require Import Charge.ModularFunc.BaseFunc.
Require Import Charge.ModularFunc.ListFunc.
Require Import Charge.ModularFunc.Denotation.

Ltac forward_step :=
  first [
    lf_forward_step | 
    of_forward_step | 
    bf_forward_step
  ].

Ltac destruct_match_goal :=
  match goal with 
    | |- context [match ?e with _ => _ end] =>
      destruct e eqn:?
  end; subst.

Ltac destruct_exprs :=
  destruct_match_goal; simpl;
  try (Rty_elim; simpl).

Ltac reduce :=
  (try red_exprD_hyp); repeat forward_step; (repeat exprD_saturate_types); (repeat (first [rewrite_in_match | bf_rewrite_in_match])); (try red_exprD_goal); repeat (first [
        progress (unfold foldD, fun_to_typ3) |
        progress (unfold consD, fun_to_typ2) |
        progress (repeat rewrite (exprT_App_wrap) in *)]).
