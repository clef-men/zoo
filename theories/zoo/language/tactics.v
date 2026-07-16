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
    | SetLocal ?e =>
        add_ectxi CtxSetLocal K prophs e
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

Tactic Notation "zoo_fold_typeclasses" "in" hyp(H) :=
  try match type of H with
  | val۰nonsimilar _ _ =>
      change val۰nonsimilar with (@nonsimilar val val۰nonsimilar) in H
  | val۰similar _ _ =>
      change val۰similar with (@similar val val۰similar) in H
  end.
Tactic Notation "zoo_fold_typeclasses" :=
  try match goal with
  | |- val۰nonsimilar _ _ =>
      change val۰nonsimilar with (@nonsimilar val val۰nonsimilar)
  | |- val۰similar _ _ =>
      change val۰similar with (@similar val val۰similar)
  end.
Tactic Notation "zoo_fold_typeclasses" "in" "*" :=
  repeat_on_hyps (fun H =>
    zoo_fold_typeclasses in H
  );
  zoo_fold_typeclasses.

Tactic Notation "zoo_simpl" "in" hyp(H) :=
  simpl in H;
  zoo_fold_typeclasses in H.
Tactic Notation "zoo_simpl" :=
  simpl;
  zoo_fold_typeclasses.

Tactic Notation "zoo_simplify" "in" hyp(H) :=
  zoo_simpl in H;
  try match type of H with
  | to_val _ = Some _ =>
      apply of_val𑁒to_val in H

  | @nonsimilar val _ (ValLit (LitBool _)) (ValLit (LitBool _)) =>
      apply val𑁒nonsimilar𑁒bool in H
  | @nonsimilar val _ (ValLit (LitInt (Z.of_nat _))) (ValLit (LitInt (Z.of_nat _))) =>
      apply val𑁒nonsimilar𑁒nat in H
  | @nonsimilar val _ (ValLit (LitInt _)) (ValLit (LitInt _)) =>
      apply val𑁒nonsimilar𑁒int in H
  | @nonsimilar val _ (ValLit (LitLoc _)) (ValLit (LitLoc _)) =>
      apply val𑁒nonsimilar𑁒location in H
  | @nonsimilar val _ (ValBlock _ _ nil) (ValBlock _ _ nil) =>
      apply val𑁒nonsimilar𑁒block𑁒empty in H
  | @nonsimilar val _ (ValBlock (Generative (Some _)) _ _) (ValBlock (Generative (Some _)) _ _) =>
      apply val𑁒nonsimilar𑁒block𑁒generative in H; try done

  | @similar val _ (ValLit (LitBool _)) (ValLit (LitBool _)) =>
      apply val𑁒similar𑁒bool in H
  | @similar val _ (ValLit (LitInt (Z.of_nat _))) (ValLit (LitInt (Z.of_nat _))) =>
      apply val𑁒similar𑁒nat in H
  | @similar val _ (ValLit (LitInt _)) (ValLit (LitInt _)) =>
      apply val𑁒similar𑁒int in H
  | @similar val _ (ValLit (LitLoc _)) (ValLit (LitLoc _)) =>
      apply val𑁒similar𑁒location in H
  | @similar val _ (ValBlock _ _ nil) (ValBlock _ _ nil) =>
      apply val𑁒similar𑁒block𑁒empty in H
  | @similar val _ (ValBlock _ _ nil) (ValBlock _ _ (cons _ _)) =>
      apply val𑁒similar𑁒block𑁒empty₁ in H as []
  | @similar val _ (ValBlock _ _ (cons _ _)) (ValBlock _ _ nil) =>
      apply val𑁒similar𑁒block𑁒empty₂ in H as []
  | @similar val _ (ValBlock (Generative _) _ _) (ValBlock (Generative _) _ _) =>
      let H1 := fresh in
      let H2 := fresh in
      let H3 := fresh in
      apply val𑁒similar𑁒block𑁒generative in H as (H1 & H2 & H3); last naive_solver;
      zoo_simpl in H1;
      zoo_simpl in H2;
      zoo_simpl in H3
  | @similar val _ (ValBlock Nongenerative _ _) (ValBlock Nongenerative _ _) =>
      let H1 := fresh in
      let H2 := fresh in
      apply val𑁒similar𑁒block𑁒nongenerative in H as (H1 & H2);
      zoo_simpl in H1;
      zoo_simpl in H2
  | @similar val _ (ValLit (LitLoc _)) (ValBlock _ _ _) =>
      apply val𑁒similar𑁒location𑁒block in H as []
  | @similar val _ (ValBlock _ _ _) (ValLit (LitLoc _)) =>
      apply val𑁒similar𑁒block𑁒location in H as []
  | @similar val _ (ValBlock (Generative _) _ _) (ValBlock Nongenerative _ _) =>
      apply val𑁒similar𑁒block𑁒generative𑁒nongenerative in H as []; done
  | @similar val _ (ValBlock Nongenerative _ _) (ValBlock (Generative _) _ _) =>
      apply val𑁒similar𑁒block𑁒nongenerative𑁒generative in H as []; done
  end;
  try zoo_simpl in H.
Tactic Notation "zoo_simplify" :=
  repeat_on_hyps (fun H =>
    zoo_simplify in H
  );
  simplify_eq/=;
  zoo_fold_typeclasses in *.

Ltac invert_base_step :=
  simpl in *;
  repeat match goal with
  | H: base_step _ ?e _ _ _ _ _ |- _ =>
      try (is_var e; fail 1);
      invert H
  end;
  zoo_simplify.

Create HintDb zoo.

#[global] Hint Resolve
  val𑁒similar𑁒refl

  base_reducible_no_obs𑁒equal
  base_reducible𑁒equal
  reducible𑁒equal

  base_reducible_no_obs𑁒cas
  base_reducible𑁒cas
  reducible𑁒cas
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
  eapply base_step𑁒equal𑁒fail;
  simpl; try naive_solver done
: zoo.
#[global] Hint Extern 0 (
  base_step _ (Equal _ _) _ _ _ _ _
) =>
  eapply base_step𑁒equal𑁒success;
  simpl
: zoo.
#[global] Hint Extern 0 (
  base_step _ (Alloc _ _) _ _ _ _ _
) =>
  apply base_step𑁒alloc'
: zoo.
#[global] Hint Extern 0 (
  base_step _ (Block Mutable _ _) _ _ _ _ _
) =>
  eapply base_step𑁒block𑁒mutable'
: zoo.
#[global] Hint Extern 0 (
  base_step _ (Block ImmutableGenerativeStrong _ _) _ _ _ _ _
) =>
  eapply base_step𑁒block𑁒immutable𑁒generative𑁒strong'
: zoo.
#[global] Hint Extern 0 (
  base_step _ (CAS _ _ _) _ _ _ _ _
) =>
  eapply base_step𑁒cas𑁒fail;
  [ try done
  | simpl; try naive_solver done
  ]
: zoo.
#[global] Hint Extern 0 (
  base_step _ (CAS _ _ _) _ _ _ _ _
) =>
  eapply base_step𑁒cas𑁒success;
  simpl
: zoo.
#[global] Hint Extern 0 (
  base_step _ (Fork _) _ _ _ _ _
) =>
  apply base_step𑁒fork'
: zoo.
#[global] Hint Extern 0 (
  base_step _ Proph _ _ _ _ _
) =>
  apply base_step𑁒proph'
: zoo.
