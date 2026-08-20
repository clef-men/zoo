Require Import zoo.prelude.
Require Export zoo.language.language.
Require Import zoo.options.

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
    | Block ?mut ?tag ?es =>
        go_list K prophs (CtxBlock mut tag) es
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
    | LocalSet ?e =>
        add_ectxi CtxLocalSet K prophs e
    | Resolve ?e0 (Val ?v1) (Val ?v2) =>
        go K (cons (v1, v2) prophs) e0
    | Resolve ?e0 ?e1 (Val ?v2) =>
        add_ectxi (CtxResolve1 e0 v2) K prophs e1
    | Resolve ?e0 ?e1 ?e2 =>
        add_ectxi (CtxResolve2 e0 e1) K prophs e2
    end
  with go_list K prophs ctx es :=
    let es := eval simpl in (rev es) in
    go_list' K prophs ctx es (@nil val)
  with go_list' K prophs ctx es vs :=
    lazymatch es with
    | cons ?e ?es =>
        lazymatch e with
        | Val ?v =>
            go_list' K prophs ctx es (cons v vs)
        | _ =>
            add_ectxi (ctx (rev es) vs) K prophs e
        end
    | _ =>
        fail
    end
  with add_ectxi k K prophs e :=
    lazymatch prophs with
    | nil =>
        go (cons k K) (@nil (val * val)) e
    | cons (?v1, ?v2) ?prophs =>
        add_ectxi (CtxResolve0 k v1 v2) K prophs e
    end
  in
  go (@nil ectxi) (@nil (val * val)) e.

Tactic Notation "zoo۰fold_typeclasses" "in" hyp(H) :=
  try match type of H with
  | val۰nonsimilar _ _ =>
      change val۰nonsimilar with (@nonsimilar val val۰nonsimilar) in H
  | val۰similar _ _ =>
      change val۰similar with (@similar val val۰similar) in H
  end.
Tactic Notation "zoo۰fold_typeclasses" :=
  try match goal with
  | |- val۰nonsimilar _ _ =>
      change val۰nonsimilar with (@nonsimilar val val۰nonsimilar)
  | |- val۰similar _ _ =>
      change val۰similar with (@similar val val۰similar)
  end.
Tactic Notation "zoo۰fold_typeclasses" "in" "*" :=
  repeat_on_hyps (fun H =>
    zoo۰fold_typeclasses in H
  );
  zoo۰fold_typeclasses.

Tactic Notation "zoo۰simpl" "in" hyp(H) :=
  simpl in H;
  zoo۰fold_typeclasses in H.
Tactic Notation "zoo۰simpl" :=
  simpl;
  zoo۰fold_typeclasses.

Tactic Notation "zoo۰simp" "in" hyp(H) :=
  zoo۰simpl in H;
  try match type of H with
  | to_val _ = Some _ =>
      apply of_valｰto_val in H

  | @nonsimilar val _ (ValLit (LitBool _)) (ValLit (LitBool _)) =>
      apply valｰnonsimilarｰbool in H
  | @nonsimilar val _ (ValLit (LitChar _)) (ValLit (LitChar _)) =>
      apply valｰnonsimilarｰchar in H
  | @nonsimilar val _ (ValLit (LitInt (Z.of_nat _))) (ValLit (LitInt (Z.of_nat _))) =>
      apply valｰnonsimilarｰnat in H
  | @nonsimilar val _ (ValLit (LitInt _)) (ValLit (LitInt _)) =>
      apply valｰnonsimilarｰint in H
  | @nonsimilar val _ (ValLit (LitLoc _)) (ValLit (LitLoc _)) =>
      apply valｰnonsimilarｰlocation in H
  | @nonsimilar val _ (ValBlock _ _ nil) (ValBlock _ _ nil) =>
      apply valｰnonsimilarｰblockｰempty in H
  | @nonsimilar val _ (ValBlock (Generative (Some _)) _ _) (ValBlock (Generative (Some _)) _ _) =>
      apply valｰnonsimilarｰblockｰgenerative in H; try done

  | @similar val _ (ValLit (LitBool _)) (ValLit (LitBool _)) =>
      apply valｰsimilarｰbool in H
  | @similar val _ (ValLit (LitChar _)) (ValLit (LitChar _)) =>
      apply valｰsimilarｰchar in H
  | @similar val _ (ValLit (LitInt (Z.of_nat _))) (ValLit (LitInt (Z.of_nat _))) =>
      apply valｰsimilarｰnat in H
  | @similar val _ (ValLit (LitInt _)) (ValLit (LitInt _)) =>
      apply valｰsimilarｰint in H
  | @similar val _ (ValLit (LitLoc _)) (ValLit (LitLoc _)) =>
      apply valｰsimilarｰlocation in H
  | @similar val _ (ValBlock _ _ nil) (ValBlock _ _ nil) =>
      apply valｰsimilarｰblockｰempty in H
  | @similar val _ (ValBlock _ _ nil) (ValBlock _ _ (cons _ _)) =>
      apply valｰsimilarｰblockｰempty₁ in H as []
  | @similar val _ (ValBlock _ _ (cons _ _)) (ValBlock _ _ nil) =>
      apply valｰsimilarｰblockｰempty₂ in H as []
  | @similar val _ (ValBlock (Generative _) _ _) (ValBlock (Generative _) _ _) =>
      let H1 := fresh in
      let H2 := fresh in
      let H3 := fresh in
      apply valｰsimilarｰblockｰgenerative in H as (H1 & H2 & H3); last naive_solver;
      zoo۰simpl in H1;
      zoo۰simpl in H2;
      zoo۰simpl in H3
  | @similar val _ (ValBlock Nongenerative _ _) (ValBlock Nongenerative _ _) =>
      let H1 := fresh in
      let H2 := fresh in
      apply valｰsimilarｰblockｰnongenerative in H as (H1 & H2);
      zoo۰simpl in H1;
      zoo۰simpl in H2
  | @similar val _ (ValLit (LitLoc _)) (ValBlock _ _ _) =>
      apply valｰsimilarｰlocationｰblock in H as []
  | @similar val _ (ValBlock _ _ _) (ValLit (LitLoc _)) =>
      apply valｰsimilarｰblockｰlocation in H as []
  | @similar val _ (ValBlock (Generative _) _ _) (ValBlock Nongenerative _ _) =>
      apply valｰsimilarｰblockｰgenerativeｰnongenerative in H as []; done
  | @similar val _ (ValBlock Nongenerative _ _) (ValBlock (Generative _) _ _) =>
      apply valｰsimilarｰblockｰnongenerativeｰgenerative in H as []; done
  end;
  try zoo۰simpl in H.
Tactic Notation "zoo۰simp" :=
  repeat_on_hyps (fun H =>
    zoo۰simp in H
  );
  simplify_eq/=;
  zoo۰fold_typeclasses in *.

Ltac inv_base_step :=
  simpl in *;
  repeat match goal with
  | H: base_step _ ?e _ _ _ _ _ |- _ =>
      try (is_var e; fail 1);
      inv/= H
  end;
  zoo۰simp.

Create HintDb zoo.

#[global] Hint Resolve
  valｰsimilarｰrefl

  base_reducible_no_obsｰequal
  base_reducibleｰequal
  reducibleｰequal

  base_reducible_no_obsｰcas
  base_reducibleｰcas
  reducibleｰcas
: zoo.

#[global] Hint Extern 0 (
  @nonsimilar val _ _ _
) => (
  progress simpl; try injection
) : zoo.
#[global] Hint Extern 0 (
  @similar val _ _ _
) => (
  progress simpl
) : zoo.

#[global] Hint Extern 0 (
  base_reducible _ _ _
) =>
  do 4 eexists; simpl
: zoo.
#[global] Hint Extern 0 (
  base_reducible_no_obs _ _ _
) =>
  do 3 eexists; simpl
: zoo.

#[global] Hint Extern 1 (
  base_step _ _ _ _ _ _ _
) =>
  econstructor
: zoo.
#[global] Hint Extern 0 (
  base_step _ (Equal _ _) _ _ _ _ _
) =>
  eapply base_stepｰequalｰfail;
  simpl; try naive_solver done
: zoo.
#[global] Hint Extern 0 (
  base_step _ (Equal _ _) _ _ _ _ _
) =>
  eapply base_stepｰequalｰsuccess;
  simpl
: zoo.
#[global] Hint Extern 0 (
  base_step _ (Alloc _ _) _ _ _ _ _
) =>
  apply base_stepｰalloc'
: zoo.
#[global] Hint Extern 0 (
  base_step _ (Block Mutable _ _) _ _ _ _ _
) =>
  eapply base_stepｰblockｰmutable'
: zoo.
#[global] Hint Extern 0 (
  base_step _ (Block ImmutableGenerativeStrong _ _) _ _ _ _ _
) =>
  eapply base_stepｰblockｰimmutableｰgenerativeｰstrong'
: zoo.
#[global] Hint Extern 0 (
  base_step _ (CAS _ _ _) _ _ _ _ _
) =>
  eapply base_stepｰcasｰfail;
  [ try done
  | simpl; try naive_solver done
  ]
: zoo.
#[global] Hint Extern 0 (
  base_step _ (CAS _ _ _) _ _ _ _ _
) =>
  eapply base_stepｰcasｰsuccess;
  simpl
: zoo.
#[global] Hint Extern 0 (
  base_step _ (Fork _) _ _ _ _ _
) =>
  apply base_stepｰfork'
: zoo.
#[global] Hint Extern 0 (
  base_step _ Proph _ _ _ _ _
) =>
  apply base_stepｰproph'
: zoo.
