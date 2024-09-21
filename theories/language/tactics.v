From stdpp Require Import
  fin_maps.

From zoo Require Import
  prelude.
From zoo.language Require Export
  language.
From zoo Require Import
  options.

Create HintDb zoo.

Ltac reshape_expr e tac :=
  let rec go K prophs e :=
    match e with
    | _ =>
        lazymatch prophs with
        | nil =>
            tac K e
        | _ =>
            fail
        end
    | App ?e1 (Val ?v2) =>
        add_ectxi (CtxApp1 v2) K prophs e1
    | App ?e1 ?e2 =>
        add_ectxi (CtxApp2 e1) K prophs e2
    | Let ?x ?e1 ?e2 =>
        add_ectxi (CtxLet x e2) K prophs e1
    | Unop ?op ?e =>
        add_ectxi (CtxUnop op) K prophs e
    | Binop ?op ?e1 (Val ?v2) =>
        add_ectxi (CtxBinop1 op v2) K prophs e1
    | Binop ?op ?e1 ?e2 =>
        add_ectxi (CtxBinop2 op e1) K prophs e2
    | Equal ?e1 (Val ?v2) =>
        add_ectxi (CtxEqual1 v2) K prophs e1
    | Equal ?e1 ?e2 =>
        add_ectxi (CtxEqual2 e1) K prophs e2
    | If ?e0 ?e1 ?e2 =>
        add_ectxi (CtxIf e1 e2) K prophs e0
    | For (Val ?v1) ?e2 ?e3 =>
        add_ectxi (CtxFor2 v1 e3) K prophs e2
    | For ?e1 ?e2 ?e3 =>
        add_ectxi (CtxFor1 e2 e3) K prophs e1
    | Alloc ?e1 (Val ?v2) =>
        add_ectxi (CtxAlloc1 v2) K prophs e1
    | Alloc ?e1 ?e2 =>
        add_ectxi (CtxAlloc2 e1) K prophs e2
    | Block ?concrete ?tag ?es =>
        go_list K prophs (CtxBlock concrete tag) es
    | Reveal ?e =>
        add_ectxi CtxReveal K prophs e
    | Match ?e0 ?x ?e1 ?brs =>
        add_ectxi (CtxMatch x e1 brs) K prophs e0
    | GetTag ?e =>
        add_ectxi CtxGetTag K prophs e
    | GetSize ?e =>
        add_ectxi CtxGetSize K prophs e
    | Load ?e1 (Val ?v2) =>
        add_ectxi (CtxLoad1 v2) K prophs e1
    | Load ?e1 ?e2 =>
        add_ectxi (CtxLoad2 e1) K prophs e2
    | Store ?e1 (Val ?v2) (Val ?v3) =>
        add_ectxi (CtxStore1 v2 v3) K prophs e1
    | Store ?e1 ?e2 (Val ?v3) =>
        add_ectxi (CtxStore2 e1 v3) K prophs e2
    | Store ?e1 ?e2 ?e3 =>
        add_ectxi (CtxStore3 e1 e2) K prophs e3
    | Xchg ?e1 (Val ?v2) =>
        add_ectxi (CtxXchg1 v2) K prophs e1
    | Xchg ?e1 ?e2 =>
        add_ectxi (CtxXchg2 e1) K prophs e2
    | CAS ?e0 (Val ?v1) (Val ?v2) =>
        add_ectxi (CtxCAS0 v1 v2) K prophs e0
    | CAS ?e0 ?e1 (Val ?v2) =>
        add_ectxi (CtxCAS1 e0 v2) K prophs e1
    | CAS ?e0 ?e1 ?e2 =>
        add_ectxi (CtxCAS2 e0 e1) K prophs e2
    | FAA ?e1 (Val ?v2) =>
        add_ectxi (CtxFAA1 v2) K prophs e1
    | FAA ?e1 ?e2 =>
        add_ectxi (CtxFAA2 e1) K prophs e2
    | Resolve ?e0 (Val ?v1) (Val ?v2) =>
        go K (cons (v1, v2) prophs) e0
    | Resolve ?e0 ?e1 (Val ?v2) =>
        add_ectxi (CtxResolve1 e0 v2) K prophs e1
    | Resolve ?e0 ?e1 ?e2 =>
        add_ectxi (CtxResolve2 e0 e1) K prophs e2
    end
  with go_list K prophs ctx es :=
    go_list' K prophs ctx (@nil val) es
  with go_list' K prophs ctx vs es :=
    lazymatch es with
    | cons ?e ?es =>
        lazymatch e with
        | Val ?v =>
            go_list' K prophs ctx (cons v vs) es
        | _ =>
            go_list'' K prophs ctx vs e es
        end
    | _ =>
        fail
    end
  with go_list'' K prophs ctx vs e es :=
    first
    [ add_ectxi (ctx (rev vs) es) K prophs e
    | lazymatch vs with
      | nil =>
          fail
      | cons ?v ?vs =>
          go_list'' K prophs ctx vs (Val v) (cons e es)
      end
    ]
  with add_ectxi k K prophs e :=
    lazymatch prophs with
    | nil =>
        go (cons k K) (@nil (val * val)) e
    | cons (?v1, ?v2) ?prophs =>
        add_ectxi (CtxResolve0 k v1 v2) K prophs e
    end
  in
  go (@nil ectxi) (@nil (val * val)) e.

Ltac invert_base_step :=
  repeat match goal with
  | _ =>
      progress simplify_map_eq/=
  | H: to_val _ = Some _ |- _ =>
      apply of_to_val in H
  | H: base_step ?e _ _ _ _ _ |- _ =>
     try (is_var e; fail 1);
     invert H
  end.

#[global] Hint Extern 0 (
  val_neq _ _
) => (
  progress simpl; try injection
) : zoo.
#[global] Hint Extern 0 (
  val_eq _ _
) => (
  progress simpl
) : zoo.

#[global] Hint Extern 0 (
  base_reducible _ _
) =>
  do 4 eexists; simpl
: zoo.
#[global] Hint Extern 0 (
  base_reducible_no_obs _ _
) =>
  do 3 eexists; simpl
: zoo.

#[global] Hint Extern 1 (
  base_step _ _ _ _ _ _
) =>
  econstructor
: zoo.
#[global] Hint Extern 0 (
  base_step (Equal _ _) _ _ _ _ _
) =>
  eapply base_step_equal_fail; simpl; [| | try injection]
: zoo.
#[global] Hint Extern 0 (
  base_step (Equal _ _) _ _ _ _ _
) =>
  eapply base_step_equal_suc; simpl
: zoo.
#[global] Hint Extern 0 (
  base_step (Alloc _ _) _ _ _ _ _
) =>
  apply base_step_alloc'
: zoo.
#[global] Hint Extern 0 (
  base_step (Block Concrete _ _) _ _ _ _ _
) =>
  eapply base_step_block_concrete'
: zoo.
#[global] Hint Extern 0 (
  base_step (Reveal _) _ _ _ _ _
) =>
  eapply base_step_reveal'
: zoo.
#[global] Hint Extern 0 (
  base_step (CAS _ _ _) _ _ _ _ _
) =>
  eapply base_step_cas_fail; simpl; [| | | try injection]
: zoo.
#[global] Hint Extern 0 (
  base_step (CAS _ _ _) _ _ _ _ _
) =>
  eapply base_step_cas_suc; simpl
: zoo.
#[global] Hint Extern 0 (
  base_step Proph _ _ _ _ _
) =>
  apply base_step_proph'
: zoo.
