Require Import Charge.Tactics.Base.BaseTacs.
Require Import Charge.Tactics.Lists.ListTacs.
Require Import Charge.Tactics.Open.OpenTacs.
Require Import Charge.Tactics.ILogic.ILogicTacs.
Require Import Charge.Tactics.BILogic.BILogicTacs.
Require Import Charge.Tactics.ILEmbed.ILEmbedTacs.
Require Import Charge.Tactics.Base.MirrorCoreTacs.
Require Import Charge.ModularFunc.BaseFunc.
Require Import Charge.ModularFunc.ListFunc.
Require Import Charge.ModularFunc.Denotation.

Ltac forward_step :=
  first [
    lf_forward_step | 
    of_forward_step | 
    bf_forward_step |
    ilf_forward_step |
    bilf_forward_step |
    eilf_forward_step
  ].
  
Ltac tyArr_unfold :=
    progress (unfold tyArrD4, tyArrD4', tyArrD3, tyArrD3', tyArrD2, tyArrD2', tyArrD, tyArrD', 
                     tyArrR4, tyArrR4', tyArrR3, tyArrR3', tyArrR2, tyArrR2', tyArrR, tyArrR').  

Ltac red_unfold :=
  first [
    lf_unfold |
    bilf_unfold |
    of_unfold |
    tyArr_unfold |
    list_unfold
  ].

Ltac red_rewrite :=
  first [
    lf_rewrite | bilf_rewrite |
    progress (repeat rewrite (exprT_App_tyArrD) in * ) | 
        progress (repeat rewriteD trmDR) | 
        progress (repeat rewriteD trmRD) |
        progress (repeat rewriteD trmDR2)].
        
Ltac destruct_match_goal :=
  match goal with 
    | |- context [match ?e with _ => _ end] =>
      destruct e eqn:?
  end; subst.

Ltac destruct_exprs :=
  destruct_match_goal; simpl;
  try (Rty_elim; simpl).

Ltac reduce :=
  (try red_exprD_hyp); repeat forward_step; (repeat exprD_saturate_types); (repeat (first [rewrite_in_match | bf_rewrite_in_match])); (try red_exprD_goal); repeat (
        first [red_unfold | red_rewrite]).
        
