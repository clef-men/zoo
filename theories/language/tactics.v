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
  let rec go K e :=
    match e with
    | _ =>
        tac K e
    | App ?e1 (Val ?v2) =>
        add_ectxi (CtxApp1 v2) K e1
    | App ?e1 ?e2 =>
        add_ectxi (CtxApp2 e1) K e2
    | Unop ?op ?e =>
        add_ectxi (CtxUnop op) K e
    | Binop ?op ?e1 (Val ?v2) =>
        add_ectxi (CtxBinop1 op v2) K e1
    | Binop ?op ?e1 ?e2 =>
        add_ectxi (CtxBinop2 op e1) K e2
    | Equal ?e1 (Val ?v2) =>
        add_ectxi (CtxEqual1 v2) K e1
    | Equal ?e1 ?e2 =>
        add_ectxi (CtxEqual2 e1) K e2
    | If ?e0 ?e1 ?e2 =>
        add_ectxi (CtxIf e1 e2) K e0
    | Constr ?tag ?es =>
        go_list K (CtxConstr tag) es
    | Proj ?proj ?e =>
        add_ectxi (CtxProj proj) K e
    | Match ?e0 ?x ?e1 ?brs =>
        add_ectxi (CtxMatch x e1 brs) K e0
    | For (Val ?v1) ?e2 ?e3 =>
        add_ectxi (CtxFor2 v1 e3) K e2
    | For ?e1 ?e2 ?e3 =>
        add_ectxi (CtxFor1 e2 e3) K e1
    | Record ?es =>
        go_list K CtxRecord es
    | Alloc ?e1 (Val ?v2) =>
        add_ectxi (CtxAlloc1 v2) K e1
    | Alloc ?e1 ?e2 =>
        add_ectxi (CtxAlloc2 e1) K e2
    | Load ?e =>
        add_ectxi CtxLoad K e
    | Store ?e1 (Val ?v2) =>
        add_ectxi (CtxStore1 v2) K e1
    | Store ?e1 ?e2 =>
        add_ectxi (CtxStore2 e1) K e2
    | Xchg ?e1 (Val ?v2) =>
        add_ectxi (CtxXchg1 v2) K e1
    | Xchg ?e1 ?e2 =>
        add_ectxi (CtxXchg2 e1) K e2
    | Cas ?e0 (Val ?v1) (Val ?v2) =>
        add_ectxi (CtxCas0 v1 v2) K e0
    | Cas ?e0 ?e1 (Val ?v2) =>
        add_ectxi (CtxCas1 e0 v2) K e1
    | Cas ?e0 ?e1 ?e2 =>
        add_ectxi (CtxCas2 e0 e1) K e2
    | Faa ?e1 (Val ?v2) =>
        add_ectxi (CtxFaa1 v2) K e1
    | Faa ?e1 ?e2 =>
        add_ectxi (CtxFaa2 e1) K e2
    end
  with go_list K ctx es :=
    go_list' K ctx (@nil val) es
  with go_list' K ctx vs es :=
    lazymatch es with
    | cons ?e ?es =>
        lazymatch e with
        | Val ?v =>
            go_list' K ctx (cons v vs) es
        | _ =>
            go_list'' K ctx vs e es
        end
    | _ =>
        fail
    end
  with go_list'' K ctx vs e es :=
    first
    [ add_ectxi (ctx (rev vs) es) K e
    | lazymatch vs with
      | nil =>
          fail
      | cons ?v ?vs =>
          go_list'' K ctx vs (Val v) (cons e es)
      end
    ]
  with add_ectxi k K e :=
    go (cons k K) e
  in
  go (@nil ectxi) e.

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
  base_step (Record _) _ _ _ _ _
) =>
  eapply base_step_record'
: zoo.
#[global] Hint Extern 0 (
  base_step (Alloc _ _) _ _ _ _ _
) =>
  apply base_step_alloc'
: zoo.
#[global] Hint Extern 0 (
  base_step (Cas _ _ _) _ _ _ _ _
) =>
  eapply base_step_cas_fail; simpl; [| | | try injection]
: zoo.
#[global] Hint Extern 0 (
  base_step (Cas _ _ _) _ _ _ _ _
) =>
  eapply base_step_cas_suc; simpl
: zoo.
