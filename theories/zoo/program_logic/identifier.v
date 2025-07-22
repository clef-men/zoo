From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.program_logic Require Export
  wp.
From zoo.diaframe Require Import
  diaframe.
From zoo Require Import
  options.

Definition identifier :=
  prophet_id.
Canonical identifier_O {SI : sidx} :=
  leibnizO identifier.

Implicit Types id : identifier.

Definition LitIdentifier id :=
  LitProph id.
Coercion LitIdentifier : identifier >-> literal.

Definition Id :=
  Proph.
Notation ValId id := (
  ValProph id
)(only parsing
).

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition identifier_model id dq : iProp Σ :=
    ∃ prophs,
    prophet_model id dq prophs.
  Definition identifier_model' id :=
    identifier_model id (DfracOwn 1).

  #[global] Instance identifier_model_timeless id dq :
    Timeless (identifier_model id dq).
  Proof.
    apply _.
  Qed.
  #[global] Instance identifier_model_persistent id :
    Persistent (identifier_model id DfracDiscarded).
  Proof.
    apply _.
  Qed.

  #[global] Instance identifier_model_fractional id :
    Fractional (λ q, identifier_model id (DfracOwn q)).
  Proof.
    intros q1 q2. iSplit.
    - iIntros "(%prophs & ($ & $))".
    - iIntros "((%prophs1 & Hmodel1) & (%prophs2 & Hmodel2))".
      iDestruct (prophet_model_combine with "Hmodel1 Hmodel2") as "(_ & $)".
  Qed.
  #[global] Instance identifier_model_as_fractional id q :
    AsFractional (identifier_model id (DfracOwn q)) (λ q, identifier_model id (DfracOwn q)) q.
  Proof.
    split; [done | apply _].
  Qed.

  Lemma identifier_model_valid id dq :
    identifier_model id dq ⊢
    ⌜✓ dq⌝.
  Proof.
    iIntros "(%prophs & Hmodel)".
    iApply (prophet_model_valid with "Hmodel").
  Qed.
  Lemma identifier_model_combine id dq1 dq2 :
    identifier_model id dq1 -∗
    identifier_model id dq2 -∗
    identifier_model id (dq1 ⋅ dq2).
  Proof.
    iIntros "(%prophs1 & Hmodel1) (%prophs2 & Hmodel2)".
    iDestruct (prophet_model_combine with "Hmodel1 Hmodel2") as "(<- & Hmodel)".
    iExists prophs1. iSteps.
  Qed.
  Lemma identifier_model_valid_2 id dq1 dq2 :
    identifier_model id dq1 -∗
    identifier_model id dq2 -∗
    ⌜✓ (dq1 ⋅ dq2)⌝.
  Proof.
    iIntros "Hmodel1 Hmodel2".
    iDestruct (identifier_model_combine with "Hmodel1 Hmodel2") as "Hmodel".
    iApply (identifier_model_valid with "Hmodel").
  Qed.
  Lemma identifier_model_dfrac_ne id1 dq1 id2 dq2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    identifier_model id1 dq1 -∗
    identifier_model id2 dq2 -∗
    ⌜id1 ≠ id2⌝.
  Proof.
    iIntros "% Hmodel1 Hmodel2 <-".
    iDestruct (identifier_model_valid_2 with "Hmodel1 Hmodel2") as %?. done.
  Qed.
  Lemma identifier_model_ne id1 id2 dq2 :
    identifier_model id1 (DfracOwn 1) -∗
    identifier_model id2 dq2 -∗
    ⌜id1 ≠ id2⌝.
  Proof.
    iApply identifier_model_dfrac_ne; [done.. | intros []%(exclusive_l _)].
  Qed.
  Lemma identifier_model_exclusive id dq :
    identifier_model id (DfracOwn 1) -∗
    identifier_model id dq -∗
    False.
  Proof.
    iIntros "Hmodel1 Hmodel2".
    iDestruct (identifier_model_ne with "Hmodel1 Hmodel2") as %?. done.
  Qed.
  Lemma identifier_model_persist id dq :
    identifier_model id dq ⊢ |==>
    identifier_model id DfracDiscarded.
  Proof.
    iIntros "(%prophs & Hmodel)".
    iMod (prophet_model_persist with "Hmodel") as "Hmodel".
    iExists prophs. iSteps.
  Qed.

  Lemma wp_id E :
    {{{
      True
    }}}
      Id @ E
    {{{ id,
      RET #id;
      identifier_model' id
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_apply (wp_proph with "[//]") as (prophs pid) "Hmodel".
    iApply "HΦ".
    iExists prophs. iSteps.
  Qed.
End zoo_G.

#[global] Opaque identifier_model.
