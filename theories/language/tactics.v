From stdpp Require Import
  fin_maps.

From zebra Require Import
  prelude.
From zebra Require Export
  language.
From zebra Require Import
  options.

Create HintDb zebra.

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
    | App ?e (Val ?v) =>
        add_ectxi (CtxAppL v) vs K e
    | App ?e1 ?e2 =>
        add_ectxi (CtxAppR e1) vs K e2
    | Unop ?op ?e =>
        add_ectxi (CtxUnop op) vs K e
    | Binop ?op ?e (Val ?v) =>
        add_ectxi (CtxBinopL op v) vs K e
    | Binop ?op ?e1 ?e2 =>
        add_ectxi (CtxBinopR op e1) vs K e2
    | If ?e0 ?e1 ?e2 =>
        add_ectxi (CtxIf e1 e2) vs K e0
    | Pair ?e (Val ?v) =>
        add_ectxi (CtxPairL v) vs K e
    | Pair ?e1 ?e2 =>
        add_ectxi (CtxPairR e1) vs K e2
    | Fst ?e =>
        add_ectxi CtxFst vs K e
    | Snd ?e =>
        add_ectxi CtxSnd vs K e
    | Injl ?e =>
        add_ectxi CtxInjl vs K e
    | Injr ?e =>
        add_ectxi CtxInjr vs K e
    | Case ?e0 ?e1 ?e2 =>
        add_ectxi (CtxCase e1 e2) vs K e0
    | Alloc ?e (Val ?v) =>
        add_ectxi (CtxAllocL v) vs K e
    | Alloc ?e1 ?e2 =>
        add_ectxi (CtxAllocR e1) vs K e2
    | Load ?e =>
        add_ectxi CtxLoad vs K e
    | Store ?e (Val ?v) =>
        add_ectxi (CtxStoreL v) vs K e
    | Store ?e1 ?e2 =>
        add_ectxi (CtxStoreR e1) vs K e2
    | Cas ?e0 (Val ?v1) (Val ?v2) =>
        add_ectxi (CtxCasL v1 v2) vs K e0
    | Cas ?e0 ?e1 (Val ?v2) =>
        add_ectxi (CtxCasM e0 v2) vs K e1
    | Cas ?e0 ?e1 ?e2 =>
        add_ectxi (CtxCasR e0 e1) vs K e2
    | Faa ?e (Val ?v) =>
        add_ectxi (CtxFaaL v) vs K e
    | Faa ?e1 ?e2 =>
        add_ectxi (CtxFaaR e1) vs K e2
    | Resolve ?ex (Val ?v1) (Val ?v2) =>
        go K ((v1,v2) :: vs) ex
    | Resolve ?ex ?e1 (Val ?v2) =>
        add_ectxi (CtxResolveM ex v2) vs K e1
    | Resolve ?ex ?e1 ?e2 =>
        add_ectxi (CtxResolveR ex e1) vs K e2
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
  eexists _, _, _, _;
  simpl
: zebra.
#[global] Hint Extern 0 (
  head_reducible_no_obs _ _
) =>
  eexists _, _, _;
  simpl
: zebra.

#[global] Hint Extern 1 (
  head_step _ _ _ _ _ _
) =>
  econstructor
: zebra.
#[global] Hint Extern 0 (
  head_step (Cas _ _ _) _ _ _ _ _
) =>
  eapply head_step_cas
: zebra.
#[global] Hint Extern 0 (
  head_step (Alloc _ _) _ _ _ _ _
) => apply head_step_alloc'
: zebra.
#[global] Hint Extern 0 (
  head_step Proph _ _ _ _ _
) =>
  apply head_step_proph'
: zebra.
