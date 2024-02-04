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
  let rec go K pvs e :=
    match e with
    | _ =>
        lazymatch pvs with
        | nil =>
            tac K e
        | _ =>
            fail
        end
    | App ?e1 (Val ?v2) =>
        add_ectxi (CtxAppL v2) K pvs e1
    | App ?e1 ?e2 =>
        add_ectxi (CtxAppR e1) K pvs e2
    | Unop ?op ?e =>
        add_ectxi (CtxUnop op) K pvs e
    | Binop ?op ?e1 (Val ?v2) =>
        add_ectxi (CtxBinopL op v2) K pvs e1
    | Binop ?op ?e1 ?e2 =>
        add_ectxi (CtxBinopR op e1) K pvs e2
    | Equal ?e1 (Val ?v2) =>
        add_ectxi (CtxEqualL v2) K pvs e1
    | Equal ?e1 ?e2 =>
        add_ectxi (CtxEqualR e1) K pvs e2
    | If ?e0 ?e1 ?e2 =>
        add_ectxi (CtxIf e1 e2) K pvs e0
    | Tuple ?es =>
        go_list K pvs CtxTuple es
    | Proj ?i ?e =>
        add_ectxi (CtxProj i) K pvs e
    | Constr ?tag ?es =>
        go_list K pvs (CtxConstr tag) es
    | Case ?e0 ?e1 ?brs =>
        add_ectxi (CtxCase e1 brs) K pvs e0
    | Record ?es =>
        go_list K pvs CtxRecord es
    | Alloc ?e1 (Val ?v2) =>
        add_ectxi (CtxAllocL v2) K pvs e1
    | Alloc ?e1 ?e2 =>
        add_ectxi (CtxAllocR e1) K pvs e2
    | Load ?e =>
        add_ectxi CtxLoad K pvs e
    | Store ?e1 (Val ?v2) =>
        add_ectxi (CtxStoreL v2) K pvs e1
    | Store ?e1 ?e2 =>
        add_ectxi (CtxStoreR e1) K pvs e2
    | Xchg ?e1 (Val ?v2) =>
        add_ectxi (CtxXchgL v2) K pvs e1
    | Xchg ?e1 ?e2 =>
        add_ectxi (CtxXchgR e1) K pvs e2
    | Cas ?e0 (Val ?v1) (Val ?v2) =>
        add_ectxi (CtxCasL v1 v2) K pvs e0
    | Cas ?e0 ?e1 (Val ?v2) =>
        add_ectxi (CtxCasM e0 v2) K pvs e1
    | Cas ?e0 ?e1 ?e2 =>
        add_ectxi (CtxCasR e0 e1) K pvs e2
    | Faa ?e1 (Val ?v2) =>
        add_ectxi (CtxFaaL v2) K pvs e1
    | Faa ?e1 ?e2 =>
        add_ectxi (CtxFaaR e1) K pvs e2
    | Resolve ?e0 (Val ?v1) (Val ?v2) =>
        go K (cons (v1, v2) pvs) e0
    | Resolve ?e0 ?e1 (Val ?v2) =>
        add_ectxi (CtxResolveM e0 v2) K pvs e1
    | Resolve ?e0 ?e1 ?e2 =>
        add_ectxi (CtxResolveR e0 e1) K pvs e2
    end
  with go_list K pvs ctx es :=
    go_list' K pvs ctx (@nil val) es
  with go_list' K pvs ctx vs es :=
    lazymatch es with
    | cons ?e ?es =>
        lazymatch e with
        | Val ?v =>
            go_list' K pvs ctx (cons v vs) es
        | _ =>
            go_list'' K pvs ctx vs e es
        end
    | _ =>
        fail
    end
  with go_list'' K pvs ctx vs e es :=
    first
    [ add_ectxi (ctx (rev vs) es) K pvs e
    | lazymatch vs with
      | nil =>
          fail
      | cons ?v ?vs =>
          go_list'' K pvs ctx vs (Val v) (cons e es)
      end
    ]
  with add_ectxi k K pvs e :=
    lazymatch pvs with
    | nil =>
        go (cons k K) (@nil (val * val)) e
    | cons (?v1, ?v2) ?pvs =>
        add_ectxi (CtxResolveL k v1 v2) K pvs e
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
  val_neq _ _
) => (
  progress simpl; try injection
) : zebre.
#[global] Hint Extern 0 (
  val_eq _ _
) => (
  progress simpl
) : zebre.

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
  eapply head_step_equal_fail; simpl; [| | try injection]
: zebre.
#[global] Hint Extern 0 (
  head_step (Equal _ _) _ _ _ _ _
) =>
  eapply head_step_equal_suc; simpl
: zebre.
#[global] Hint Extern 0 (
  head_step (Record  _) _ _ _ _ _
) =>
  eapply head_step_record'
: zebre.
#[global] Hint Extern 0 (
  head_step (Alloc _ _) _ _ _ _ _
) =>
  apply head_step_alloc'
: zebre.
#[global] Hint Extern 0 (
  head_step (Cas _ _ _) _ _ _ _ _
) =>
  eapply head_step_cas_fail; simpl; [| | | try injection]
: zebre.
#[global] Hint Extern 0 (
  head_step (Cas _ _ _) _ _ _ _ _
) =>
  eapply head_step_cas_suc; simpl
: zebre.
#[global] Hint Extern 0 (
  head_step Proph _ _ _ _ _
) =>
  apply head_step_proph'
: zebre.
