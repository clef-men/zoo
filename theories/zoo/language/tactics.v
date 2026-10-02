Require Import zoo.prelude.
Require Export zoo.language.language.
Require Import zoo.options.

Ltac expr۰reshape_apply e tac :=
  let rec go K resolves e :=
    match e with
    | _ =>
        lazymatch resolves with
        | [] =>
            tac K e
        | _ =>
            fail
        end
    | Apply ?e1 (Val ?v2) =>
        add_ectxi (CtxApply1 v2) K resolves e1
    | Apply ?e1 ?e2 =>
        add_ectxi (CtxApply2 e1) K resolves e2
    | Let ?x ?e1 ?e2 =>
        add_ectxi (CtxLet x e2) K resolves e1
    | If ?e0 ?e1 ?e2 =>
        add_ectxi (CtxIf e1 e2) K resolves e0
    | For (Val ?v1) ?e2 ?e3 =>
        add_ectxi (CtxFor2 v1 e3) K resolves e2
    | For ?e1 ?e2 ?e3 =>
        add_ectxi (CtxFor1 e2 e3) K resolves e1
    | Match ?e0 ?x ?e1 ?brs =>
        add_ectxi (CtxMatch x e1 brs) K resolves e0
    | Primitive1 ?prim ?e =>
        add_ectxi (CtxPrimitive1 prim) K resolves e
    | Primitive2 ?prim ?e1 (Val ?v2) =>
        add_ectxi (CtxPrimitive21 prim v2) K resolves e1
    | Primitive2 ?prim ?e1 ?e2 =>
        add_ectxi (CtxPrimitive22 prim e1) K resolves e2
    | Primitive3 ?prim ?e1 (Val ?v2) (Val ?v3) =>
        add_ectxi (CtxPrimitive31 prim v2 v3) K resolves e1
    | Primitive3 ?prim ?e1 ?e2 (Val ?v3) =>
        add_ectxi (CtxPrimitive32 prim e1 v3) K resolves e2
    | Primitive3 ?prim ?e1 ?e2 ?e3 =>
        add_ectxi (CtxPrimitive33 prim e1 e2) K resolves e3
    | Block ?mut ?tag ?es =>
        lazymatch eval simpl in (expr۰to_vals_suffix es) with
        | Ok _ =>
            fail
        | Error (?es, ?e, ?vs) =>
            add_ectxi (CtxBlock mut tag es vs) K resolves e
        end
    | Resolve ?e0 (Val ?v1) (Val ?v2) =>
        go K ((v1, v2) :: resolves) e0
    | Resolve ?e0 ?e1 (Val ?v2) =>
        add_ectxi (CtxResolve1 e0 v2) K resolves e1
    | Resolve ?e0 ?e1 ?e2 =>
        add_ectxi (CtxResolve2 e0 e1) K resolves e2
    end
  with add_ectxi k K resolves e :=
    let k := eval simpl in (ectxi۰make_resolves resolves k) in
    go (k :: K) (@nil (val * val)) e
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
  | expr۰to_val _ = Some _ =>
      apply expr۰of_valｰto_val in H

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
  | @nonsimilar val _ (ValBlock _ _ []) (ValBlock _ _ []) =>
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
  | @similar val _ (ValLit (LitString _)) (ValLit (LitString _)) =>
      apply valｰsimilarｰstring in H
  | @similar val _ (ValLit (LitLoc _)) (ValLit (LitLoc _)) =>
      apply valｰsimilarｰlocation in H
  | @similar val _ (ValBlock _ _ []) (ValBlock _ _ []) =>
      apply valｰsimilarｰblockｰempty in H
  | @similar val _ (ValBlock _ _ []) (ValBlock _ _ (_ :: _)) =>
      apply valｰsimilarｰblockｰempty₁ in H as []
  | @similar val _ (ValBlock _ _ (_ :: _)) (ValBlock _ _ []) =>
      apply valｰsimilarｰblockｰempty₂ in H as []
  | @similar val _ (ValBlock (Generative _) _ _) (ValBlock (Generative _) _ _) =>
      let H1 := fresh in
      let H2 := fresh in
      let H3 := fresh in
      apply valｰsimilarｰblockｰgenerative in H as (H1 & H2 & H3); last naive;
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
  base_step _ (Primitive2 Equal _ _) _ _ _ _ _
) =>
  eapply base_stepｰequalｰfail;
  simpl; try naive done
: zoo.
#[global] Hint Extern 0 (
  base_step _ (Primitive2 Equal _ _) _ _ _ _ _
) =>
  eapply base_stepｰequalｰsuccess;
  simpl
: zoo.
#[global] Hint Extern 0 (
  base_step _ (Primitive2 Alloc _ _) _ _ _ _ _
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
  base_step _ (Primitive3 CAS _ _ _) _ _ _ _ _
) =>
  eapply base_stepｰcasｰfail;
  [ try done
  | simpl; try naive done
  ]
: zoo.
#[global] Hint Extern 0 (
  base_step _ (Primitive3 CAS _ _ _) _ _ _ _ _
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
  base_step _ (Primitive0 Proph) _ _ _ _ _
) =>
  apply base_stepｰproph'
: zoo.
