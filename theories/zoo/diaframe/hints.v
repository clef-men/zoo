From iris.base_logic Require Export
  lib.fancy_updates.

From diaframe Require Import
  steps.pure_solver
  lib.persistently
  lib.intuitionistically
  lib.iris_hints.

From zoo Require Import
  prelude.
From zoo.iris Require Import
  diaframe.
From zoo.language Require Import
  notations.
From zoo.program_logic Require Export
  state_interp.
From zoo Require Import
  options.

Section pointsto.
  Context `{zoo_G : !ZooG Σ}.

  Section mergable.
    #[global] Instance mergable_consume_pointsto_persist l v1 v2 :
      MergableConsume
        (l ↦□ v1)%I
        true
        (λ p Pin Pout,
          TCAnd (TCEq Pin (l ↦□ v2)) $
          TCEq Pout (l ↦□ v1 ∗ ⌜v1 = v2⌝)
        )%I
    | 40.
    Proof.
      intros p Pin Pout (-> & ->).
      rewrite bi.intuitionistically_if_elim.
      iStep as "Hl1 Hl2".
      iCombine "Hl1 Hl2" gives %[_ ->].
      iSteps.
    Qed.

    #[global] Instance mergable_consume_pointsto_own q1 q2 q l v1 v2 :
      MergableConsume
        (l ↦{#q1} v1)%I
        true
        (λ p Pin Pout,
          TCAnd (TCEq Pin (l ↦{#q2} v2)) $
          TCAnd (proofmode_classes.IsOp (A := fracR) q q1 q2) $
          TCEq Pout (l ↦{#q} v1 ∗ ⌜v1 = v2⌝ ∗ ⌜q ≤ 1⌝%Qp)
        )%I
    | 30.
    Proof.
      intros p Pin Pout (-> & Hq & ->).
      rewrite bi.intuitionistically_if_elim.
      iStep as "Hl1 Hl2".
      iCombine "Hl1 Hl2" as "H" gives %[Hl ->].
      rewrite dfrac_op_own Hq.
      rewrite dfrac_valid_own in Hl.
      iSteps.
    Qed.

    #[global] Instance mergable_persist_pointsto_dfrac_own q1 dq2 l v1 v2 :
      MergablePersist
        (l ↦{#q1} v1)%I
        (λ p Pin Pout,
          TCAnd (TCEq Pin (l ↦{dq2} v2)) $
          TCEq Pout ⌜v1 = v2 ∧ q1 < 1⌝%Qp
        )%I
    | 50.
    Proof.
      intros p Pin Pout (-> & ->).
      rewrite bi.intuitionistically_if_elim.
      iStep as "Hl1 Hl2".
      iCombine "Hl1 Hl2" gives %[?%dfrac_valid_own_l ->].
      iSteps.
    Qed.

    #[global] Instance mergable_persist_pointsto_dfrac_own2 q1 dq2 l v1 v2 :
      MergablePersist
        (l ↦{dq2} v1)%I
        (λ p Pin Pout,
          TCAnd (TCEq Pin (l ↦{#q1} v2)) $
          TCEq Pout ⌜v1 = v2 ∧ q1 < 1⌝%Qp
        )%I
    | 50.
    Proof.
      intros p Pin Pout (-> & ->).
      rewrite bi.intuitionistically_if_elim.
      iSteps.
    Qed.

    #[global] Instance mergable_persist_pointsto_last_resort dq1 dq2 l v1 v2 :
      MergablePersist
        (l ↦{dq1} v1)%I
        (λ p Pin Pout,
          TCAnd (TCEq Pin (l ↦{dq2} v2)) $
          TCEq Pout ⌜v1 = v2⌝
        )%I
    | 99.
    Proof.
      intros p Pin Pout (-> & ->).
      rewrite bi.intuitionistically_if_elim.
      iStep as "Hl1 Hl2".
      iCombine "Hl1 Hl2" gives %[_ ->].
      iSteps.
    Qed.

    #[global] Instance proph_exclusive pid prophs prophs' :
      MergableConsume
        (prophet_model' pid prophs)
        true
        (λ b Pin Pout,
          TCAnd (TCEq Pin (prophet_model' pid prophs')) $
          TCEq Pout (False%I)
        ).
    Proof.
      intros b Pin Pout (-> & ->).
      rewrite bi.intuitionistically_if_elim.
      iIntros "[Hp1 Hp2]". by iApply (prophet_model_exclusive with "[$]").
    Qed.

    #[global] Instance prophs_are_ne pid prophs pid' prophs' :
      MergablePersist
      (prophet_model' pid prophs)
      (λ b Pin Pout,
        TCAnd (TCEq Pin (prophet_model' pid' prophs')) $
        TCEq Pout ⌜pid ≠ pid'⌝
      )%I.
    Proof.
      intros b Pin Pout (-> & ->).
      rewrite bi.intuitionistically_if_elim.
      destruct_decide (pid = pid') as -> | Hneq; iSteps.
    Qed.
  End mergable.

  Section biabd.
    #[global] Instance diahint_pointsto_may_need_more l v1 v2 q1 q2 mq q :
      FracSub q2 q1 mq →
      TCEq mq (Some q) →
      HINT
        l ↦{#q1} v1
      ✱ [v';
        ⌜v1 = v2⌝ ∗
        l ↦{#q} v'
      ] ⊫ [id];
        l ↦{#q2} v2
      ✱ [
        ⌜v1 = v2⌝ ∗
        ⌜v' = v1⌝
      ]
    | 55.
    Proof.
      rewrite /FracSub => <- -> v' /=.
      iSteps.
    Qed.
    #[global] Instance diahint_pointsto_have_enough l v1 v2 q1 q2 mq :
      FracSub q1 q2 mq →
      HINT
        l ↦{#q1} v1
      ✱ [- ;
        ⌜v1 = v2⌝
      ] ⊫ [id];
        l ↦{#q2} v2
      ✱ [
        ⌜v1 = v2⌝ ∗
        match mq with
        | Some q =>
            l ↦{#q} v1
        | _ =>
            True
        end
      ]
    | 54.
    Proof.
      rewrite /FracSub => <-.
      destruct mq; iSteps as "Hl".
      iDestruct "Hl" as "[Hl Hl']".
      iSteps.
    Qed.
    #[global] Instance diahint_pointsto_discarded l v1 v2 :
      HINT
        l ↦□ v1
      ✱ [- ;
        ⌜v1 = v2⌝
      ] ⊫ [id];
        l ↦□ v2
      ✱ [
        ⌜v1 = v2⌝
      ]
    | 54.
    Proof.
      iSteps.
    Qed.

    #[global] Instance diahint_pointsto_persist p l q v :
      HINT
        □⟨p⟩ l ↦{q} v
      ✱ [- ;
        emp
      ] ⊫ [bupd];
        l ↦□ v
      ✱ [
        l ↦□ v
      ]
    | 100.
    Proof.
      iIntros "Hl" => /=.
      rewrite right_id bi.intuitionistically_if_elim.
      iMod (pointsto_persist with "Hl") as "#Hl".
      iSteps.
    Qed.
  End biabd.
End pointsto.

Section side_condition_lemmas.
  Lemma val_nonsimilar_lit_neq lit1 lit2 :
    lit1 ≠ lit2 →
    ValLit lit1 ≠ ValLit lit2.
  Proof.
    congruence.
  Qed.

  Lemma lit_neq_Z_neq n1 n2 :
    n1 ≠ n2 →
    LitInt n1 ≠ LitInt n2.
  Proof.
    congruence.
  Qed.

  Lemma lit_neq_bool_neq b1 b2 :
    b1 ≠ b2 →
    LitBool b1 ≠ LitBool b2.
  Proof.
    congruence.
  Qed.

  Lemma val_block_neq bid1 tag1 vs1 bid2 tag2 vs2 :
    bid1 ≠ bid2 →
    tag1 ≠ tag2 →
    vs1 ≠ vs2 →
    ValBlock bid1 tag1 vs1 ≠ ValBlock bid2 tag2 vs2.
  Proof.
    congruence.
  Qed.

  #[global] Instance simplify_lit_location_neq l1 l2 :
    SimplifyPureHypSafe
      (ValLit l1 ≠ ValLit l2)
      (l1 ≠ l2).
  Proof.
    split; congruence.
  Qed.

  #[global] Instance simplify_lit_int_neq n1 n2 :
    SimplifyPureHypSafe
      (LitInt n1 ≠ LitInt n2)
      (n1 ≠ n2).
  Proof.
    split; congruence.
  Qed.

  #[global] Instance simplify_lit_bool_neq b1 b2 :
    SimplifyPureHypSafe
      (LitBool b1 ≠ LitBool b2)
      (b1 ≠ b2).
  Proof.
    split; congruence.
  Qed.

  #[global] Instance simplify_block_neq bid1 tag1 vs1 bid2 tag2 vs2 :
    SimplifyPureHypSafe
      (ValBlock bid1 tag1 vs1 ≠ ValBlock bid2 tag2 vs2)
      (bid1 ≠ bid2 ∨ tag1 ≠ tag2 ∨ vs1 ≠ vs2).
  Proof.
    split.
    - rewrite -!not_and_l. naive_solver.
    - naive_solver.
  Qed.
End side_condition_lemmas.

Ltac solveValEq :=
  progress f_equal;
  trySolvePureEq.

Ltac trySolvePureEqAdd1 :=
  lazymatch goal with
  | |- @eq ?ty _ _ =>
      match ty with
      | val =>
          solveValEq
      | literal =>
          solveValEq
      end
  end.

#[global] Hint Extern 4 (
  _ = _
) =>
  trySolvePureEqAdd1
: solve_pure_eq_add.

Ltac trySolvePureAdd1 :=
  match goal with
  | |- ValLit ?lit1 ≠ ValLit ?lit2 =>
      assert_fails (has_evar lit1);
      assert_fails (has_evar lit2);
      eapply val_nonsimilar_lit_neq;
      solve [pure_solver.trySolvePure]
  | |- LitInt ?n1 ≠ LitInt ?n2 =>
      assert_fails (has_evar n1);
      assert_fails (has_evar n2);
      eapply lit_neq_Z_neq;
      solve [pure_solver.trySolvePure]
  | |- LitBool ?b1 ≠ LitBool ?b2 =>
      assert_fails (has_evar b1);
      assert_fails (has_evar b2);
      eapply lit_neq_bool_neq;
      solve [pure_solver.trySolvePure]
  | |- ValBlock ?bid1 ?tag1 ?vs1 ≠ ValBlock ?bid2 ?tag2 ?vs2 =>
      assert_fails (has_evar bid1);
      assert_fails (has_evar bid2);
      assert_fails (has_evar tag1);
      assert_fails (has_evar tag2);
      assert_fails (has_evar vs1);
      assert_fails (has_evar vs2);
      eapply val_block_neq;
      solve [pure_solver.trySolvePure]
  end.

#[global] Hint Extern 4 =>
  trySolvePureAdd1
: solve_pure_add.

#[global] Hint Extern 4 (
  length _ ≤ length _
) =>
  simpl;
  solve [pure_solver.trySolvePure]
: solve_pure_add.
