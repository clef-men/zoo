From stdpp Require Import
  fin_maps.

From zebre Require Import
  prelude.
From zebre.language Require Export
  language.
From zebre Require Import
  options.

Create HintDb zebre.

Ltac reshape_expr e tac :=
  let rec go K vs e :=
    match e with
    | _ =>
        lazymatch vs with
        | [] =>
            tac K e
        | _ =>
            fail
        end
    | App ?e1 (Val ?v2) =>
        add_ectxi (CtxAppL v2) vs K e1
    | App ?e1 ?e2 =>
        add_ectxi (CtxAppR e1) vs K e2
    | Unop ?op ?e =>
        add_ectxi (CtxUnop op) vs K e
    | Binop ?op ?e1 (Val ?v2) =>
        add_ectxi (CtxBinopL op v2) vs K e1
    | Binop ?op ?e1 ?e2 =>
        add_ectxi (CtxBinopR op e1) vs K e2
    | Equal ?e1 (Val ?v2) =>
        add_ectxi (CtxEqualL v2) vs K e1
    | Equal ?e1 ?e2 =>
        add_ectxi (CtxEqualR e1) vs K e2
    | If ?e0 ?e1 ?e2 =>
        add_ectxi (CtxIf e1 e2) vs K e0
    | Pair ?e1 (Val ?v2) =>
        add_ectxi (CtxPairL v2) vs K e1
    | Pair ?e1 ?e2 =>
        add_ectxi (CtxPairR e1) vs K e2
    | Fst ?e =>
        add_ectxi CtxFst vs K e
    | Snd ?e =>
        add_ectxi CtxSnd vs K e
    | Constr ?b ?e =>
        add_ectxi (CtxConstr b) vs K e
    | Case ?e0 ?e1 ?e2 =>
        add_ectxi (CtxCase e1 e2) vs K e0
    | Alloc ?e1 (Val ?v2) =>
        add_ectxi (CtxAllocL v2) vs K e1
    | Alloc ?e1 ?e2 =>
        add_ectxi (CtxAllocR e1) vs K e2
    | Load ?e =>
        add_ectxi CtxLoad vs K e
    | Store ?e1 (Val ?v2) =>
        add_ectxi (CtxStoreL v2) vs K e1
    | Store ?e1 ?e2 =>
        add_ectxi (CtxStoreR e1) vs K e2
    | Xchg ?e1 (Val ?v2) =>
        add_ectxi (CtxXchgL v2) vs K e1
    | Xchg ?e1 ?e2 =>
        add_ectxi (CtxXchgR e1) vs K e2
    | Cas ?e0 (Val ?v1) (Val ?v2) =>
        add_ectxi (CtxCasL v1 v2) vs K e0
    | Cas ?e0 ?e1 (Val ?v2) =>
        add_ectxi (CtxCasM e0 v2) vs K e1
    | Cas ?e0 ?e1 ?e2 =>
        add_ectxi (CtxCasR e0 e1) vs K e2
    | Faa ?e1 (Val ?v2) =>
        add_ectxi (CtxFaaL v2) vs K e1
    | Faa ?e1 ?e2 =>
        add_ectxi (CtxFaaR e1) vs K e2
    | Resolve ?e0 (Val ?v1) (Val ?v2) =>
        go K ((v1, v2) :: vs) e0
    | Resolve ?e0 ?e1 (Val ?v2) =>
        add_ectxi (CtxResolveM e0 v2) vs K e1
    | Resolve ?e0 ?e1 ?e2 =>
        add_ectxi (CtxResolveR e0 e1) vs K e2
    end
  with add_ectxi k vs K e :=
    lazymatch vs with
    | [] =>
        go (k :: K) (@nil (val * val)) e
    | (?v1, ?v2) :: ?vs =>
        add_ectxi (CtxResolveL k v1 v2) vs K e
    end
  in
  go (@nil ectxi) (@nil (val * val)) e.

Ltac invert_head_step :=
  repeat match goal with
  | _ =>
      progress simplify_map_eq/=
  | H: to_val _ = Some _ |- _ =>
      apply of_to_val in H
  | H: head_step ?e _ _ _ _ _ |- _ =>
     try (is_var e; fail 1);
     invert H
  end.

#[global] Hint Extern 0 (
  head_reducible _ _
) =>
  do 4 eexists; simpl
: zebre.
#[global] Hint Extern 0 (
  head_reducible_no_obs _ _
) =>
  do 3 eexists; simpl
: zebre.

#[global] Hint Extern 1 (
  head_step _ _ _ _ _ _
) =>
  econstructor
: zebre.
#[global] Hint Extern 0 (
  head_step (Equal _ _) _ _ _ _ _
) =>
  eapply head_step_equal_fail
: zebre.
#[global] Hint Extern 0 (
  head_step (Equal _ _) _ _ _ _ _
) =>
  eapply head_step_equal_suc
: zebre.
#[global] Hint Extern 0 (
  head_step (Alloc _ _) _ _ _ _ _
) =>
  apply head_step_alloc'
: zebre.
#[global] Hint Extern 0 (
  head_step (Cas _ _ _) _ _ _ _ _
) =>
  eapply head_step_cas_fail
: zebre.
#[global] Hint Extern 0 (
  head_step (Cas _ _ _) _ _ _ _ _
) =>
  eapply head_step_cas_suc
: zebre.
#[global] Hint Extern 0 (
  head_step Proph _ _ _ _ _
) =>
  apply head_step_proph'
: zebre.
