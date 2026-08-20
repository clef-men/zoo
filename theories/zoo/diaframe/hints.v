Require Export iris.base_logic.lib.fancy_updates.

Require Import diaframe.steps.pure_solver.
Require Import diaframe.lib.persistently.
Require Import diaframe.lib.intuitionistically.
Require Import diaframe.lib.iris_hints.

Require Import zoo.prelude.
Require Export zoo.iris.diaframe.
Require Import zoo.language.notations.
Require Export zoo.program_logic.state_interp.
Require Import zoo.options.

Section pointsto.
  Context `{zoo۰G : !ZooG Σ}.

  Section mergable.
    #[global] Instance mergable_consumeｰpointstoｰpersist l v1 v2 :
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

    #[global] Instance mergable_consumeｰpointstoｰown q1 q2 q l v1 v2 :
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

    #[global] Instance mergable_persistｰpointstoｰdfracｰown q1 dq2 l v1 v2 :
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

    #[global] Instance mergable_persistｰpointstoｰdfracｰown2 q1 dq2 l v1 v2 :
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

    #[global] Instance mergable_persistｰpointstoｰlast_resort dq1 dq2 l v1 v2 :
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

    #[global] Instance mergable_consumeｰprophet۰modelｰexclusive pid prophs prophs' :
      MergableConsume
        (prophet۰model pid prophs)
        true
        (λ b Pin Pout,
          TCAnd (TCEq Pin (prophet۰model pid prophs')) $
          TCEq Pout (False%I)
        ).
    Proof.
      intros b Pin Pout (-> & ->).
      rewrite bi.intuitionistically_if_elim.
      iIntros "[Hp1 Hp2]". by iApply (prophet۰modelｰexclusive with "[$]").
    Qed.

    #[global] Instance mergable_persistｰprophet۰modelｰne pid prophs pid' prophs' :
      MergablePersist
      (prophet۰model pid prophs)
      (λ b Pin Pout,
        TCAnd (TCEq Pin (prophet۰model pid' prophs')) $
        TCEq Pout ⌜pid ≠ pid'⌝
      )%I.
    Proof.
      intros b Pin Pout (-> & ->).
      rewrite bi.intuitionistically_if_elim.
      destruct_decide (pid = pid') as -> | Hneq; iSteps.
    Qed.
  End mergable.

  Section biabd.
    #[global] Instance diahintｰpointstoｰmay_need_more l v1 v2 q1 q2 mq q :
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
    #[global] Instance diahintｰpointstoｰhave_enough l v1 v2 q1 q2 mq :
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
    #[global] Instance diahintｰpointstoｰdiscarded l v1 v2 :
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

    #[global] Instance diahintｰpointstoｰpersist p l q v :
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
      iMod (pointstoｰpersist with "Hl") as "#Hl".
      iSteps.
    Qed.
  End biabd.
End pointsto.

Section side_condition_lemmas.
  Lemma litｰneqｰboolｰneq b1 b2 :
    b1 ≠ b2 →
    LitBool b1 ≠ LitBool b2.
  Proof.
    congruence.
  Qed.
  Lemma litｰneqｰcharｰneq chr1 chr2 :
    chr1 ≠ chr2 →
    LitChar chr1 ≠ LitChar chr2.
  Proof.
    congruence.
  Qed.
  Lemma litｰneqｰZｰneq n1 n2 :
    n1 ≠ n2 →
    LitInt n1 ≠ LitInt n2.
  Proof.
    congruence.
  Qed.

  Lemma valｰnonsimilarｰlitｰneq lit1 lit2 :
    lit1 ≠ lit2 →
    ValLit lit1 ≠ ValLit lit2.
  Proof.
    congruence.
  Qed.

  Lemma valｰblockｰneq bid1 tag1 vs1 bid2 tag2 vs2 :
    bid1 ≠ bid2 →
    tag1 ≠ tag2 →
    vs1 ≠ vs2 →
    ValBlock bid1 tag1 vs1 ≠ ValBlock bid2 tag2 vs2.
  Proof.
    congruence.
  Qed.

  #[global] Instance simplifyｰlitｰlocationｰneq l1 l2 :
    SimplifyPureHypSafe
      (ValLit l1 ≠ ValLit l2)
      (l1 ≠ l2).
  Proof.
    split; congruence.
  Qed.
  #[global] Instance simplifyｰlitｰboolｰneq b1 b2 :
    SimplifyPureHypSafe
      (LitBool b1 ≠ LitBool b2)
      (b1 ≠ b2).
  Proof.
    split; congruence.
  Qed.
  #[global] Instance simplifyｰlitｰchar chr1 chr2 :
    SimplifyPureHypSafe
      (LitChar chr1 ≠ LitChar chr2)
      (chr1 ≠ chr2).
  Proof.
    split; congruence.
  Qed.
  #[global] Instance simplifyｰlitｰintｰneq n1 n2 :
    SimplifyPureHypSafe
      (LitInt n1 ≠ LitInt n2)
      (n1 ≠ n2).
  Proof.
    split; congruence.
  Qed.

  #[global] Instance simplifyｰblockｰneq bid1 tag1 vs1 bid2 tag2 vs2 :
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
  | |- LitBool ?b1 ≠ LitBool ?b2 =>
      assert_fails (has_evar b1);
      assert_fails (has_evar b2);
      eapply litｰneqｰboolｰneq;
      solve [pure_solver.trySolvePure]
  | |- LitChar ?chr1 ≠ LitChar ?chr2 =>
      assert_fails (has_evar chr1);
      assert_fails (has_evar chr2);
      eapply litｰneqｰcharｰneq;
      solve [pure_solver.trySolvePure]
  | |- LitInt ?n1 ≠ LitInt ?n2 =>
      assert_fails (has_evar n1);
      assert_fails (has_evar n2);
      eapply litｰneqｰZｰneq;
      solve [pure_solver.trySolvePure]
  | |- ValLit ?lit1 ≠ ValLit ?lit2 =>
      assert_fails (has_evar lit1);
      assert_fails (has_evar lit2);
      eapply valｰnonsimilarｰlitｰneq;
      solve [pure_solver.trySolvePure]
  | |- ValBlock ?bid1 ?tag1 ?vs1 ≠ ValBlock ?bid2 ?tag2 ?vs2 =>
      assert_fails (has_evar bid1);
      assert_fails (has_evar bid2);
      assert_fails (has_evar tag1);
      assert_fails (has_evar tag2);
      assert_fails (has_evar vs1);
      assert_fails (has_evar vs2);
      eapply valｰblockｰneq;
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
