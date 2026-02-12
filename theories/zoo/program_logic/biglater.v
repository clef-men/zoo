From zoo Require Import
  prelude.
From zoo.program_logic Require Export
  wp.
From zoo.diaframe Require Import
  diaframe.
From zoo Require Import
  options.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Implicit Types P : iProp Σ.

  Definition biglater P : iProp Σ :=
    ∃ ns,
    ⧖ ns ∗
    ▷^(later_function ns) P.
End zoo_G.

Notation "▶ P" := (
  biglater P
)(at level 20,
  right associativity
) : bi_scope.

#[local] Instance : CustomIpat "biglater" :=
  " ( %ns{} &
      #H⧖{_{}} &
      HP{}
    )
  ".

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Implicit Types P : iProp Σ.

  #[global] Instance biglater_ne :
    NonExpansive biglater.
  Proof.
    solve_proper.
  Qed.
  #[global] Instance biglater_proper :
    Proper ((≡) ==> (≡)) biglater.
  Proof.
    solve_proper.
  Qed.

  Lemma biglater_intro P :
    P ⊢ |==>
    ▶ P.
  Proof.
    iIntros "HP".
    iMod steps_lb_0 as "$" => //.
  Qed.

  Lemma biglater_mono P1 P2 :
    (P1 ⊢ P2) →
    (▶ P1) ⊢ ▶ P2.
  Proof.
    iIntros "%HP (:biglater =1)".
    iFrame "#". iNext.
    iApply (HP with "HP1").
  Qed.
  #[global] Instance biglater_mono' :
    Proper ((⊢) ==> (⊢)) biglater.
  Proof.
    iIntros "%P1 %P2 %HP".
    iApply biglater_mono; first done.
  Qed.
  #[global] Instance biglater_flip_mono' :
    Proper (flip (⊢) ==> flip (⊢)) biglater.
  Proof.
    iIntros "%P1 %P2 %HP".
    iApply biglater_mono; first done.
  Qed.

  Lemma biglater_or_1 P1 P2 :
    ▶ (P1 ∨ P2) ⊢
    ▶ P1 ∨ ▶ P2.
  Proof.
    iIntros "(:biglater)".
    iFrame "#".
    rewrite bi.laterN_or //.
  Qed.
  Lemma biglater_or_2 P1 P2 :
    ▶ P1 ∨ ▶ P2 ⊢
    ▶ (P1 ∨ P2).
  Proof.
    iSteps.
  Qed.
  Lemma biglater_or P1 P2 :
    ▶ (P1 ∨ P2) ⊣⊢
    ▶ P1 ∨ ▶ P2.
  Proof.
    iSplit.
    - iApply biglater_or_1.
    - iApply biglater_or_2.
  Qed.

  Lemma biglater_and P1 P2 :
    ▶ (P1 ∧ P2) ⊢
    ▶ P1 ∧ ▶ P2.
  Proof.
    iIntros "(:biglater)".
    iFrame "#".
    iApply bi.laterN_and.
    iApply (bi.laterN_mono with "HP"); first done.
  Qed.

  Lemma biglater_exist_1 `{!Inhabited X} (Φ : X → iProp Σ) :
    ▶ (∃ x, Φ x) ⊢
    ∃ x, ▶ Φ x.
  Proof.
    iSteps.
  Qed.
  Lemma biglater_exist_2 `(Φ : X → iProp Σ) :
    (∃ x, ▶ Φ x) ⊢
    ▶ ∃ x, Φ x.
  Proof.
    iSteps.
  Qed.
  Lemma biglater_exist `{!Inhabited X} (Φ : X → iProp Σ) :
    ▶ (∃ x, Φ x) ⊣⊢
    ∃ x, ▶ Φ x.
  Proof.
    iSplit.
    - iApply @biglater_exist_1.
    - iApply biglater_exist_2.
  Qed.

  Lemma biglater_forall `(Φ : X → iProp Σ) :
    ▶ (∀ x, Φ x) ⊢
    ∀ x, ▶ Φ x.
  Proof.
    iSteps.
  Qed.

  Lemma biglater_sep_1 P1 P2 :
    ▶ (P1 ∗ P2) ⊢
      ▶ P1 ∗
      ▶ P2.
  Proof.
    iSteps.
  Qed.
  Lemma biglater_sep_2 P1 P2 :
    ▶ P1 -∗
    ▶ P2 -∗
    ▶ (P1 ∗ P2).
  Proof.
    iIntros "(:biglater =1) (:biglater =2)".
    iExists (ns1 `max` ns2). iSplitR.
    - iApply (steps_lb_max with "H⧖_1 H⧖_2").
    - iApply bi.laterN_sep.
      iDestruct (bi.laterN_le with "HP1") as "$".
      { auto with lia. }
      iDestruct (bi.laterN_le with "HP2") as "$".
      { auto with lia. }
  Qed.
  Lemma biglater_sep P1 P2 :
    ▶ (P1 ∗ P2) ⊣⊢
      ▶ P1 ∗
      ▶ P2.
  Proof.
    iSplit.
    - iApply biglater_sep_1.
    - iIntros "(HP1 & HP2)".
      iApply (biglater_sep_2 with "HP1 HP2").
  Qed.

  Lemma biglater_frame_l P1 P2 :
    P1 -∗
    ▶ P2 -∗
    ▶ (P1 ∗ P2).
  Proof.
    iSteps.
  Qed.
  Lemma biglater_frame_r P1 P2 :
    ▶ P1 -∗
    P2 -∗
    ▶ (P1 ∗ P2).
  Proof.
    rewrite bi.sep_comm.
    iIntros "HP1 HP2".
    iApply (biglater_frame_l with "HP2 HP1").
  Qed.

  Lemma biglater_wand_l P1 P2 :
    (P1 -∗ P2) -∗
    (▶ P1) -∗
    ▶ P2.
  Proof.
    iSteps.
  Qed.
  Lemma biglater_wand_r P1 P2 :
    (▶ P1) -∗
    (P1 -∗ P2) -∗
    ▶ P2.
  Proof.
    iIntros "HP1 HP2".
    iApply (biglater_wand_l with "HP2 HP1").
  Qed.

  Lemma biglater_persistently P :
    ▶ <pers> P ⊢
    <pers> ▶ P.
  Proof.
    iIntros "(:biglater)".
    iFrame "#".
    rewrite bi.laterN_persistently //.
  Qed.
End zoo_G.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Implicit Types P : iProp Σ.

  #[global] Instance into_wand_biglater p q R P Q :
    IntoWand false false R P Q →
    IntoWand p q (▶ R) (▶ P) (▶ Q).
  Proof.
    rewrite /IntoWand /=.
    rewrite !bi.intuitionistically_if_elim.
    iIntros "%H HR HP".
    iDestruct (biglater_sep_2 with "HR HP") as "H".
    iApply (biglater_wand_r with "H"). iIntros "(HR & HP)".
    iApply (H with "HR HP").
  Qed.
  #[global] Instance into_wand_biglater_args p q R P Q :
    IntoWand p false R P Q →
    IntoWand' p q R (▶ P) (▶ Q).
  Proof.
    rewrite /IntoWand' /IntoWand /=.
    rewrite (bi.intuitionistically_if_elim q).
    iIntros "%H HR HP".
    iApply (biglater_wand_r with "HP"). iIntros "HP".
    iApply (H with "HR HP").
  Qed.

  #[global] Instance from_sep_biglater P Q1 Q2 :
    FromSep P Q1 Q2 →
    FromSep (▶ P) (▶ Q1) (▶ Q2).
  Proof.
    rewrite /FromSep.
    rewrite -biglater_sep.
    apply biglater_mono.
  Qed.

  #[global] Instance maybe_combine_sep_as_biglater Q1 Q2 P progress :
    MaybeCombineSepAs Q1 Q2 P progress →
    MaybeCombineSepAs (▶ Q1) (▶ Q2) (▶ P) progress.
  Proof.
    rewrite /MaybeCombineSepAs.
    rewrite -biglater_sep => -> //.
  Qed.

  #[global] Instance maybe_combine_sep_gives_biglater Q1 Q2 P :
    CombineSepGives Q1 Q2 P →
    CombineSepGives (▶ Q1) (▶ Q2) (▶ P).
  Proof.
    rewrite /CombineSepGives.
    rewrite -biglater_sep -biglater_persistently => -> //.
  Qed.

  #[global] Instance into_and_biglater P Q1 Q2 :
    IntoAnd false P Q1 Q2 →
    IntoAnd false (▶ P) (▶ Q1) (▶ Q2).
  Proof.
    rewrite /IntoAnd /= => ->.
    apply biglater_and.
  Qed.

  #[global] Instance into_sep_biglater P Q1 Q2 :
    IntoSep P Q1 Q2 →
    IntoSep (▶ P) (▶ Q1) (▶ Q2).
  Proof.
    rewrite /IntoSep => ->.
    rewrite biglater_sep //.
  Qed.

  #[global] Instance from_or_biglater P Q1 Q2 :
    FromOr P Q1 Q2 →
    FromOr (▶ P) (▶ Q1) (▶ Q2).
  Proof.
    rewrite /FromOr.
    rewrite -biglater_or.
    apply biglater_mono.
  Qed.

  #[global] Instance into_or_biglater P Q1 Q2 :
    IntoOr P Q1 Q2 →
    IntoOr (▶ P) (▶ Q1) (▶ Q2).
  Proof.
    rewrite /IntoOr => ->.
    rewrite biglater_or //.
  Qed.

  #[global] Instance from_exist_biglater {X} P (Φ : X → iProp Σ) :
    FromExist P Φ →
    FromExist (▶ P) (λ x, ▶ Φ x)%I.
  Proof.
    rewrite /FromExist.
    rewrite biglater_exist_2.
    apply biglater_mono.
  Qed.

  #[global] Instance into_exist_biglater {X} P (Φ : X → iProp Σ) name :
    IntoExist P Φ name →
    Inhabited X →
    IntoExist (▶ P) (λ a, ▶ (Φ a))%I name.
  Proof.
    rewrite /IntoExist => HP HX.
    rewrite HP biglater_exist //.
  Qed.

  #[global] Instance into_forall_biglater {X} P (Φ : X → iProp Σ) :
    IntoForall P Φ →
    IntoForall (▶ P) (λ x, ▶ Φ x)%I.
  Proof.
    rewrite /IntoForall.
    rewrite -biglater_forall.
    apply biglater_mono.
  Qed.

  #[global] Instance frame_biglater p R P Q :
    Frame p R P Q →
    Frame p R (▶ P) (▶ Q)
  | 2.
  Proof.
    rewrite /Frame => <-.
    iIntros "(HR & HQ)".
    iApply (biglater_frame_l with "HR HQ").
  Qed.

  #[global] Instance biglater_strong_modality :
    ModalityStrongMono biglater.
  Proof.
    split=> P Q.
    - move=> -> //.
    - iIntros "(HP & HQ)".
      iApply (biglater_frame_r with "HP HQ").
  Qed.
End zoo_G.
