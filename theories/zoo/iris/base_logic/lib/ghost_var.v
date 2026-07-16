Require Import iris.algebra.lib.dfrac_agree.

Require Import zoo.prelude.
Require Export zoo.iris.base_logic.lib.base.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

Class GhostVarG Σ F :=
  { #[local] ghost_var۰G۰inG :: inG Σ (dfrac_agreeR $ oFunctor_apply F $ iPropO Σ)
  }.

Definition ghost_var۰Σ F `{!oFunctorContractive F} :=
  #[GFunctor (dfrac_agreeRF F)
  ].
#[global] Instance subG𑁒ghost_var۰Σ Σ F `{!oFunctorContractive F} :
  subG (ghost_var۰Σ F) Σ →
  GhostVarG Σ F.
Proof.
  solve_inG.
Qed.

Section ghost_var۰G.
  Context `{ghost_var۰G : !GhostVarG Σ F}.

  Definition ghost_var γ dq a :=
    own γ (to_dfrac_agree dq a).

  #[global] Instance ghost_var𑁒nonexpansive γ dq :
    NonExpansive (ghost_var γ dq).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance ghost_var𑁒proper γ dq :
    Proper ((≡) ==> (≡)) (ghost_var γ dq).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance ghost_var𑁒timeless γ dq a :
    Discrete a →
    Timeless (ghost_var γ dq a).
  Proof.
    apply _.
  Qed.

  #[global] Instance ghost_var𑁒persistent γ a :
    Persistent (ghost_var γ DfracDiscarded a).
  Proof.
    apply _.
  Qed.

  #[global] Instance ghost_var𑁒fractional γ a :
    Fractional (λ q, ghost_var γ (DfracOwn q) a).
  Proof.
    intros q1 q2.
    rewrite -own_op -frac_agree_op //.
  Qed.
  #[global] Instance ghost_var𑁒as_fractional γ a q :
    AsFractional (ghost_var γ (DfracOwn q) a) (λ q, ghost_var γ (DfracOwn q) a) q.
  Proof.
    split; [done | apply _].
  Qed.

  Lemma ghost_var𑁒alloc a :
    ⊢ |==>
      ∃ γ,
      ghost_var γ (DfracOwn 1) a.
  Proof.
    apply own_alloc. done.
  Qed.
  Lemma ghost_var𑁒alloc𑁒cofinite (γs : gset gname) a :
    ⊢ |==>
      ∃ γ,
      ⌜γ ∉ γs⌝ ∗
      ghost_var γ (DfracOwn 1) a.
  Proof.
    apply own_alloc_cofinite. done.
  Qed.

  Lemma ghost_var𑁒valid γ dq a :
    ghost_var γ dq a ⊢
    ⌜✓ dq⌝.
  Proof.
    rewrite /ghost_var own_valid dfrac_agree_validI //.
  Qed.
  Lemma ghost_var𑁒combine γ dq1 a1 dq2 a2 :
    ghost_var γ dq1 a1 -∗
    ghost_var γ dq2 a2 -∗
      a1 ≡ a2 ∗
      ghost_var γ (dq1 ⋅ dq2) a1.
  Proof.
    iIntros "H1 H2".
    iCombine "H1 H2" as "H".
    iDestruct (own_valid with "H") as "#Hvalid".
    iDestruct (dfrac_agree_validI_2 with "Hvalid") as "(_ & Heq)".
    iRewrite -"Heq" in "H".
    rewrite -dfrac_agree_op. auto.
  Qed.
  Lemma ghost_var𑁒valid𑁒2 γ dq1 a1 dq2 a2 :
    ghost_var γ dq1 a1 -∗
    ghost_var γ dq2 a2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      a1 ≡ a2.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_var𑁒combine with "H1 H2") as "($ & H)".
    iApply (ghost_var𑁒valid with "H").
  Qed.
  Lemma ghost_var𑁒agree γ dq1 a1 dq2 a2 :
    ghost_var γ dq1 a1 -∗
    ghost_var γ dq2 a2 -∗
    a1 ≡ a2.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_var𑁒valid𑁒2 with "H1 H2") as "(_ & $)".
  Qed.
  Lemma ghost_var𑁒dfrac𑁒ne γ1 dq1 a1 γ2 dq2 a2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    ghost_var γ1 dq1 a1 -∗
    ghost_var γ2 dq2 a2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    iIntros "% H1 H2 ->".
    iDestruct (ghost_var𑁒valid𑁒2 with "H1 H2") as "(% & _)". done.
  Qed.
  Lemma ghost_var𑁒ne γ1 a1 γ2 dq2 a2 :
    ghost_var γ1 (DfracOwn 1) a1 -∗
    ghost_var γ2 dq2 a2 -∗
    ⌜γ1 ≠ γ2⌝.
  Proof.
    iApply ghost_var𑁒dfrac𑁒ne; [done.. | intros []%(exclusive_l _)].
  Qed.
  Lemma ghost_var𑁒exclusive γ a1 dq2 a2 :
    ghost_var γ (DfracOwn 1) a1 -∗
    ghost_var γ dq2 a2 -∗
    False.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_var𑁒ne with "H1 H2") as %?. done.
  Qed.
  Lemma ghost_var𑁒persist γ dq a :
    ghost_var γ dq a ⊢ |==>
    ghost_var γ DfracDiscarded a.
  Proof.
    apply own_update, dfrac_agree_persist.
  Qed.
  Section discrete.
    Context `{!OfeDiscrete $ oFunctor_apply F $ iPropO Σ}.
    Lemma ghost_var𑁒combine𑁒discrete γ dq1 a1 dq2 a2 :
      ghost_var γ dq1 a1 -∗
      ghost_var γ dq2 a2 -∗
        ⌜a1 ≡ a2⌝ ∗
        ghost_var γ (dq1 ⋅ dq2) a1.
    Proof.
      iIntros "H1 H2".
      iDestruct (ghost_var𑁒combine with "H1 H2") as "(% & $)".
      iSteps.
    Qed.
    Lemma ghost_var𑁒valid𑁒2𑁒discrete γ dq1 a1 dq2 a2 :
      ghost_var γ dq1 a1 -∗
      ghost_var γ dq2 a2 -∗
        ⌜✓ (dq1 ⋅ dq2)⌝ ∗
        ⌜a1 ≡ a2⌝.
    Proof.
      iIntros "H1 H2".
      iDestruct (ghost_var𑁒valid𑁒2 with "H1 H2") as "($ & %)".
      iSteps.
    Qed.
    Lemma ghost_var𑁒agree𑁒discrete γ dq1 a1 dq2 a2 :
      ghost_var γ dq1 a1 -∗
      ghost_var γ dq2 a2 -∗
      ⌜a1 ≡ a2⌝.
    Proof.
      iIntros "H1 H2".
      iDestruct (ghost_var𑁒agree with "H1 H2") as %?.
      iSteps.
    Qed.
    Section leibniz_equiv.
      Context `{!LeibnizEquiv $ oFunctor_apply F $ iPropO Σ}.
      Lemma ghost_var𑁒combine𑁒L γ dq1 a1 dq2 a2 :
        ghost_var γ dq1 a1 -∗
        ghost_var γ dq2 a2 -∗
          ⌜a1 = a2⌝ ∗
          ghost_var γ (dq1 ⋅ dq2) a1.
      Proof.
        iIntros "H1 H2".
        iDestruct (ghost_var𑁒combine𑁒discrete with "H1 H2") as "(%Heq & $)".
        apply leibniz_equiv in Heq.
        iSteps.
      Qed.
      Lemma ghost_var𑁒valid𑁒2𑁒L γ dq1 a1 dq2 a2 :
        ghost_var γ dq1 a1 -∗
        ghost_var γ dq2 a2 -∗
          ⌜✓ (dq1 ⋅ dq2)⌝ ∗
          ⌜a1 = a2⌝.
      Proof.
        iIntros "H1 H2".
        iDestruct (ghost_var𑁒valid𑁒2𑁒discrete with "H1 H2") as %(? & ?%leibniz_equiv).
        iSteps.
      Qed.
      Lemma ghost_var𑁒agree𑁒L γ dq1 a1 dq2 a2 :
        ghost_var γ dq1 a1 -∗
        ghost_var γ dq2 a2 -∗
        ⌜a1 = a2⌝.
      Proof.
        iIntros "H1 H2".
        iDestruct (ghost_var𑁒agree𑁒discrete with "H1 H2") as %?%leibniz_equiv.
        iSteps.
      Qed.
    End leibniz_equiv.
  End discrete.

  Lemma ghost_var𑁒update {γ a} a' :
    ghost_var γ (DfracOwn 1) a ⊢ |==>
    ghost_var γ (DfracOwn 1) a'.
  Proof.
    apply own_update, cmra_update_exclusive. done.
  Qed.
End ghost_var۰G.

#[global] Opaque ghost_var.
