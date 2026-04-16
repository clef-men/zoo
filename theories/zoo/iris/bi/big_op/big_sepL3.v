From zoo Require Import
  prelude.
From zoo.common Require Import
  list.
From zoo.iris.bi Require Export
  big_op.big_sepL.
From zoo.iris Require Import
  diaframe.
From zoo Require Import
  options.

Fixpoint big_sepL3 {PROP : bi} `(Φ : nat → A1 → A2 → A3 → PROP) l1 l2 l3 : PROP :=
  match l1, l2, l3 with
  | [], [], [] =>
      emp
  | x1 :: l1, x2 :: l2, x3 :: l3 =>
      Φ 0 x1 x2 x3 ∗
      big_sepL3 (λ n, Φ (S n)) l1 l2 l3
  | _, _, _ =>
      False
  end%I.
#[global] Instance : Params (@big_sepL3) 4 :=
  {}.
#[global] Arguments big_sepL3 {_ _ _ _} _ !_ !_ !_ / : assert.
#[global] Typeclasses Opaque big_sepL3.

Notation "'[∗' 'list]' k ↦ x1 ; x2 ; x3 ∈ l1 ; l2 ; l3 , P" := (
  big_sepL3 (λ k x1 x2 x3, P%I) l1 l2 l3
)(at level 200,
  l1, l2, l3 at level 10,
  k binder,
  x1 binder,
  x2 binder,
  x3 binder,
  right associativity,
  format "[∗  list]  k  ↦  x1 ;  x2 ;  x3  ∈  l1 ;  l2 ;  l3 ,  P"
) : bi_scope.
Notation "'[∗' 'list]' x1 ; x2 ; x3 ∈ l1 ; l2 ; l3 , P" := (
  big_sepL3 (λ _ x1 x2 x3, P%I) l1 l2 l3
)(at level 200,
  l1, l2, l3 at level 10,
  x1 binder,
  x2 binder,
  x3 binder,
  right associativity,
  format "[∗  list]  x1 ;  x2 ;  x3  ∈  l1 ;  l2 ;  l3 ,  P"
) : bi_scope.

Section bi.
  Context {PROP : bi}.

  Section big_sepL3.
    Context {A1 A2 A3 : Type}.

    Implicit Types Φ : nat → A1 → A2 → A3 → PROP.

    Lemma big_sepL3_cons Φ y1 l1 y2 l2 y3 l3 :
      ([∗ list] k ↦ x1; x2; x3 ∈ y1 :: l1; y2 :: l2; y3 :: l3, Φ k x1 x2 x3) ⊣⊢
        Φ 0 y1 y2 y3 ∗
        [∗ list] k ↦ x1; x2; x3 ∈ l1; l2; l3, Φ (S k) x1 x2 x3.
    Proof.
      done.
    Qed.
    Lemma big_sepL3_cons_1 Φ y1 l1 y2 l2 y3 l3 :
      ([∗ list] k ↦ x1; x2; x3 ∈ y1 :: l1; y2 :: l2; y3 :: l3, Φ k x1 x2 x3) ⊢
        Φ 0 y1 y2 y3 ∗
        [∗ list] k ↦ x1; x2; x3 ∈ l1; l2; l3, Φ (S k) x1 x2 x3.
    Proof.
      rewrite big_sepL3_cons //.
    Qed.
    Lemma big_sepL3_cons_2 Φ y1 l1 y2 l2 y3 l3 :
      Φ 0 y1 y2 y3 -∗
      ([∗ list] k ↦ x1; x2; x3 ∈ l1; l2; l3, Φ (S k) x1 x2 x3) -∗
      [∗ list] k ↦ x1; x2; x3 ∈ y1 :: l1; y2 :: l2; y3 :: l3, Φ k x1 x2 x3.
    Proof.
      rewrite big_sepL3_cons.
      iSteps.
    Qed.

    Lemma big_sepL3_alt `{!BiAffine PROP} Φ l1 l2 l3 :
      ([∗ list] k ↦ x1; x2; x3 ∈ l1; l2; l3, Φ k x1 x2 x3) ⊣⊢
        ⌜length l1 = length l2⌝ ∗
        ⌜length l2 = length l3⌝ ∗
        [∗ list] k ↦ x ∈ zip3 l1 l2 l3, Φ k x.1.1 x.1.2 x.2.
    Proof.
      iInduction l1 as [| x1 l1] "IH" forall (l2 l3 Φ).
      all: destruct l2 as [| x2 l2].
      all: destruct l3 as [| x3 l3].
      all: try iSmash.
      iEval (rewrite zip3_cons /=).
      iSplit; iIntros "H".
      - iDestruct (big_sepL3_cons_1 with "H") as "($ & H)".
        iDestruct ("IH" with "H") as "(% & % & $)".
        iFrameSteps.
      - iApply big_sepL3_cons.
        iDestruct "H" as "(% & % & $ & H)".
        iApply ("IH" with "[$H]"). 1: auto.
    Qed.

    Lemma big_sepL3_flip_1 `{!BiAffine PROP} Φ l1 l2 l3 :
      ([∗ list] k ↦ x1; x2; x3 ∈ l1; l2; l3, Φ k x1 x2 x3) ⊣⊢
      [∗ list] k ↦ x1; x3; x2 ∈ l1; l3; l2, Φ k x1 x2 x3.
    Proof.
      iInduction l1 as [| x1 l1] "IH" forall (l2 l3 Φ).
      all: destruct l2 as [| x2 l2].
      all: destruct l3 as [| x3 l3].
      all: iSteps.
      all: iApply "IH" => //.
    Qed.
    Lemma big_sepL3_flip_2 `{!BiAffine PROP} Φ l1 l2 l3 :
      ([∗ list] k ↦ x1; x2; x3 ∈ l1; l2; l3, Φ k x1 x2 x3) ⊣⊢
      [∗ list] k ↦ x3; x2; x1 ∈ l3; l2; l1, Φ k x1 x2 x3.
    Proof.
      iInduction l1 as [| x1 l1] "IH" forall (l2 l3 Φ).
      all: destruct l2 as [| x2 l2].
      all: destruct l3 as [| x3 l3].
      all: iSteps.
      all: iApply "IH" => //.
    Qed.
    Lemma big_sepL3_flip_3 `{!BiAffine PROP} Φ l1 l2 l3 :
      ([∗ list] k ↦ x1; x2; x3 ∈ l1; l2; l3, Φ k x1 x2 x3) ⊣⊢
      [∗ list] k ↦ x2; x1; x3 ∈ l2; l1; l3, Φ k x1 x2 x3.
    Proof.
      iInduction l1 as [| x1 l1] "IH" forall (l2 l3 Φ).
      all: destruct l2 as [| x2 l2].
      all: destruct l3 as [| x3 l3].
      all: iSteps.
      all: iApply "IH" => //.
    Qed.

    Lemma big_sepL3_sepL2_3 `{!BiAffine PROP} Φ l1 l2 l3 :
      ([∗ list] k ↦ x1; x2; x3 ∈ l1; l2; l3, Φ k x1 x2 x3) ⊣⊢
        ⌜length l1 = length l2⌝ ∗
        [∗ list] k ↦ x; x3 ∈ zip l1 l2; l3, Φ k x.1 x.2 x3.
    Proof.
      rewrite big_sepL3_alt big_sepL2_alt zip_zip.
      simpl_length. iSteps.
    Qed.
  End big_sepL3.

  Section big_sepL3.
    Context {A1 A2 A3 : Type}.

    Implicit Types Φ : nat → A1 → A2 → A3 → PROP.

    Lemma big_sepL3_sepL2_1 `{!BiAffine PROP} Φ l1 l2 l3 :
      ([∗ list] k ↦ x1; x2; x3 ∈ l1; l2; l3, Φ k x1 x2 x3) ⊣⊢
        ⌜length l2 = length l3⌝ ∗
        [∗ list] k ↦ x1; x ∈ l1; zip l2 l3, Φ k x1 x.1 x.2.
    Proof.
      rewrite big_sepL3_flip_2 big_sepL3_flip_3 big_sepL2_flip.
      apply: big_sepL3_sepL2_3.
    Qed.
    Lemma big_sepL3_sepL2_2 `{!BiAffine PROP} Φ l1 l2 l3 :
      ([∗ list] k ↦ x1; x2; x3 ∈ l1; l2; l3, Φ k x1 x2 x3) ⊣⊢
        ⌜length l1 = length l3⌝ ∗
        [∗ list] k ↦ x2; x ∈ l2; zip l1 l3, Φ k x.1 x2 x.2.
    Proof.
      rewrite big_sepL3_flip_1 big_sepL2_flip.
      apply: big_sepL3_sepL2_3.
    Qed.

    Lemma big_sepL2_exists `{!BiAffine PROP} Φ l1 l2 :
      ( [∗ list] k ↦ x1; x2 ∈ l1; l2,
        ∃ x3,
        Φ k x1 x2 x3
      ) ⊢
        ∃ l3,
        ⌜length l1 = length l3⌝ ∗
        ⌜length l2 = length l3⌝ ∗
        [∗ list] k ↦ x1; x2; x3 ∈ l1; l2; l3,
          Φ k x1 x2 x3.
    Proof.
      rewrite big_sepL2_alt.
      rewrite big_sepL_exists.
      setoid_rewrite big_sepL2_alt.
      setoid_rewrite zip_zip.
      setoid_rewrite big_sepL3_alt.
      simpl_length.
      iIntros "(% & %l3 & % & % & $)". iSteps.
    Qed.

    Lemma big_sepL3_const_sepL2_1 `{!BiAffine PROP} (Φ : nat → A2 → A3 → PROP) (l1 : list A1) l2 l3 :
      ([∗ list] k ↦ _; x2; x3 ∈ l1; l2; l3, Φ k x2 x3) ⊣⊢
        ⌜length l1 = length l2⌝ ∗
        ⌜length l1 = length l3⌝ ∗
        [∗ list] k ↦ x2; x3 ∈ l2; l3, Φ k x2 x3.
    Proof.
      rewrite big_sepL3_sepL2_1 big_sepL2_const_sepL_r big_sepL2_alt.
      simpl_length. iSteps.
    Qed.
    Lemma big_sepL3_const_sepL2_2 `{!BiAffine PROP} (Φ : nat → A1 → A3 → PROP) l1 (l2 : list A2) l3 :
      ([∗ list] k ↦ x1; _; x3 ∈ l1; l2; l3, Φ k x1 x3) ⊣⊢
        ⌜length l2 = length l1⌝ ∗
        ⌜length l2 = length l3⌝ ∗
        [∗ list] k ↦ x1; x3 ∈ l1; l3, Φ k x1 x3.
    Proof.
      rewrite big_sepL3_sepL2_2 big_sepL2_const_sepL_r big_sepL2_alt.
      simpl_length. iSteps.
    Qed.
    Lemma big_sepL3_const_sepL2_3 `{!BiAffine PROP} (Φ : nat → A1 → A2 → PROP) l1 l2 (l3 : list A3) :
      ([∗ list] k ↦ x1; x2; _ ∈ l1; l2; l3, Φ k x1 x2) ⊣⊢
        ⌜length l3 = length l1⌝ ∗
        ⌜length l3 = length l2⌝ ∗
        [∗ list] k ↦ x1; x2 ∈ l1; l2, Φ k x1 x2.
    Proof.
      rewrite big_sepL3_sepL2_3 big_sepL2_const_sepL_l big_sepL2_alt.
      simpl_length. iSteps.
    Qed.

    Lemma big_sepL3_sep `{!BiAffine PROP} Φ1 Φ2 l1 l2 l3 :
      ([∗ list] k ↦ x1; x2; x3 ∈ l1; l2; l3, Φ1 k x1 x2 x3 ∗ Φ2 k x1 x2 x3) ⊣⊢
        ([∗ list] k ↦ x1; x2; x3 ∈ l1; l2; l3, Φ1 k x1 x2 x3) ∗
        ([∗ list] k ↦ x1; x2; x3 ∈ l1; l2; l3, Φ2 k x1 x2 x3).
    Proof.
      rewrite !big_sepL3_alt big_sepL_sep.
      iSteps.
    Qed.
  End big_sepL3.
End bi.
