Require Import zoo.prelude.
Require Export zoo.program_logic.wp.
Require Import zoo.diaframe.
Require Import zoo.options.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Implicit Types P : iProp Σ.

  Definition biglater P : iProp Σ :=
    ∃ ns,
    ⧖ ns ∗
    ▷^(later۰function ns) P.
End zoo۰G.

Notation "▶ P" := (
  biglater P
)(at level 20,
  right associativity
) : bi_scope.

#[local] Instance : CustomIpat "biglater" :=
  " ( %ns{}
    & #H⧖{_{}}
    & HP{}
    )
  ".

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Implicit Types P : iProp Σ.

  #[global] Instance biglater𑁒ne :
    NonExpansive biglater.
  Proof.
    solve_proper.
  Qed.
  #[global] Instance biglater𑁒proper :
    Proper ((≡) ==> (≡)) biglater.
  Proof.
    solve_proper.
  Qed.

  Lemma biglater𑁒intro P :
    P ⊢ |==>
    ▶ P.
  Proof.
    iIntros "HP".
    iMod steps۰lb𑁒0 as "$" => //.
  Qed.

  Lemma biglater𑁒mono P1 P2 :
    (P1 ⊢ P2) →
    (▶ P1) ⊢ ▶ P2.
  Proof.
    iIntros "%HP (:biglater =1)".
    iFrame "#". iNext.
    iApply (HP with "HP1").
  Qed.
  #[global] Instance biglater𑁒mono' :
    Proper ((⊢) ==> (⊢)) biglater.
  Proof.
    iIntros "%P1 %P2 %HP".
    iApply biglater𑁒mono; first done.
  Qed.
  #[global] Instance biglater𑁒flip𑁒mono' :
    Proper (flip (⊢) ==> flip (⊢)) biglater.
  Proof.
    iIntros "%P1 %P2 %HP".
    iApply biglater𑁒mono; first done.
  Qed.

  Lemma biglater𑁒or₁ P1 P2 :
    ▶ (P1 ∨ P2) ⊢
    ▶ P1 ∨ ▶ P2.
  Proof.
    iIntros "(:biglater)".
    iFrame "#".
    rewrite bi.laterN_or //.
  Qed.
  Lemma biglater𑁒or₂ P1 P2 :
    ▶ P1 ∨ ▶ P2 ⊢
    ▶ (P1 ∨ P2).
  Proof.
    iSteps.
  Qed.
  Lemma biglater𑁒or P1 P2 :
    ▶ (P1 ∨ P2) ⊣⊢
    ▶ P1 ∨ ▶ P2.
  Proof.
    iSplit.
    - iApply biglater𑁒or₁.
    - iApply biglater𑁒or₂.
  Qed.

  Lemma biglater𑁒and P1 P2 :
    ▶ (P1 ∧ P2) ⊢
    ▶ P1 ∧ ▶ P2.
  Proof.
    iIntros "(:biglater)".
    iFrame "#".
    iApply bi.laterN_and.
    iApply (bi.laterN_mono with "HP"); first done.
  Qed.

  Lemma biglater𑁒exist₁ `{!Inhabited X} (Φ : X → iProp Σ) :
    ▶ (∃ x, Φ x) ⊢
    ∃ x, ▶ Φ x.
  Proof.
    iSteps.
  Qed.
  Lemma biglater𑁒exist₂ `(Φ : X → iProp Σ) :
    (∃ x, ▶ Φ x) ⊢
    ▶ ∃ x, Φ x.
  Proof.
    iSteps.
  Qed.
  Lemma biglater𑁒exist `{!Inhabited X} (Φ : X → iProp Σ) :
    ▶ (∃ x, Φ x) ⊣⊢
    ∃ x, ▶ Φ x.
  Proof.
    iSplit.
    - iApply @biglater𑁒exist₁.
    - iApply biglater𑁒exist₂.
  Qed.

  Lemma biglater𑁒forall `(Φ : X → iProp Σ) :
    ▶ (∀ x, Φ x) ⊢
    ∀ x, ▶ Φ x.
  Proof.
    iSteps.
  Qed.

  Lemma biglater𑁒sep₁ P1 P2 :
    ▶ (P1 ∗ P2) ⊢
      ▶ P1 ∗
      ▶ P2.
  Proof.
    iSteps.
  Qed.
  Lemma biglater𑁒sep₂ P1 P2 :
    ▶ P1 -∗
    ▶ P2 -∗
    ▶ (P1 ∗ P2).
  Proof.
    iIntros "(:biglater =1) (:biglater =2)".
    iExists (ns1 `max` ns2). iSplitR.
    - iApply (steps۰lb𑁒max with "H⧖_1 H⧖_2").
    - iApply bi.laterN_sep.
      iDestruct (bi.laterN_le with "HP1") as "$".
      { auto with lia. }
      iDestruct (bi.laterN_le with "HP2") as "$".
      { auto with lia. }
  Qed.
  Lemma biglater𑁒sep P1 P2 :
    ▶ (P1 ∗ P2) ⊣⊢
      ▶ P1 ∗
      ▶ P2.
  Proof.
    iSplit.
    - iApply biglater𑁒sep₁.
    - iIntros "(HP1 & HP2)".
      iApply (biglater𑁒sep₂ with "HP1 HP2").
  Qed.

  Lemma biglater𑁒frame𑁒l P1 P2 :
    P1 -∗
    ▶ P2 -∗
    ▶ (P1 ∗ P2).
  Proof.
    iSteps.
  Qed.
  Lemma biglater𑁒frame𑁒r P1 P2 :
    ▶ P1 -∗
    P2 -∗
    ▶ (P1 ∗ P2).
  Proof.
    rewrite bi.sep_comm.
    iIntros "HP1 HP2".
    iApply (biglater𑁒frame𑁒l with "HP2 HP1").
  Qed.

  Lemma biglater𑁒wand𑁒l P1 P2 :
    (P1 -∗ P2) -∗
    (▶ P1) -∗
    ▶ P2.
  Proof.
    iSteps.
  Qed.
  Lemma biglater𑁒wand𑁒r P1 P2 :
    (▶ P1) -∗
    (P1 -∗ P2) -∗
    ▶ P2.
  Proof.
    iIntros "HP1 HP2".
    iApply (biglater𑁒wand𑁒l with "HP2 HP1").
  Qed.

  Lemma biglater𑁒persistently P :
    ▶ <pers> P ⊢
    <pers> ▶ P.
  Proof.
    iIntros "(:biglater)".
    iFrame "#".
    rewrite bi.laterN_persistently //.
  Qed.
End zoo۰G.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Implicit Types P : iProp Σ.

  #[global] Instance into_wand𑁒biglater p q R P Q :
    IntoWand false false R P Q →
    IntoWand p q (▶ R) (▶ P) (▶ Q).
  Proof.
    rewrite /IntoWand /=.
    rewrite !bi.intuitionistically_if_elim.
    iIntros "%H HR HP".
    iDestruct (biglater𑁒sep₂ with "HR HP") as "H".
    iApply (biglater𑁒wand𑁒r with "H"). iIntros "(HR & HP)".
    iApply (H with "HR HP").
  Qed.
  #[global] Instance into_wand𑁒biglater𑁒args p q R P Q :
    IntoWand p false R P Q →
    IntoWand' p q R (▶ P) (▶ Q).
  Proof.
    rewrite /IntoWand' /IntoWand /=.
    rewrite (bi.intuitionistically_if_elim q).
    iIntros "%H HR HP".
    iApply (biglater𑁒wand𑁒r with "HP"). iIntros "HP".
    iApply (H with "HR HP").
  Qed.

  #[global] Instance from_sep𑁒biglater P Q1 Q2 :
    FromSep P Q1 Q2 →
    FromSep (▶ P) (▶ Q1) (▶ Q2).
  Proof.
    rewrite /FromSep.
    rewrite -biglater𑁒sep.
    apply biglater𑁒mono.
  Qed.

  #[global] Instance maybe_combine_sep_as𑁒biglater Q1 Q2 P progress :
    MaybeCombineSepAs Q1 Q2 P progress →
    MaybeCombineSepAs (▶ Q1) (▶ Q2) (▶ P) progress.
  Proof.
    rewrite /MaybeCombineSepAs.
    rewrite -biglater𑁒sep => -> //.
  Qed.

  #[global] Instance combine_sep_gives𑁒biglater Q1 Q2 P :
    CombineSepGives Q1 Q2 P →
    CombineSepGives (▶ Q1) (▶ Q2) (▶ P).
  Proof.
    rewrite /CombineSepGives.
    rewrite -biglater𑁒sep -biglater𑁒persistently => -> //.
  Qed.

  #[global] Instance into_and𑁒biglater P Q1 Q2 :
    IntoAnd false P Q1 Q2 →
    IntoAnd false (▶ P) (▶ Q1) (▶ Q2).
  Proof.
    rewrite /IntoAnd /= => ->.
    apply biglater𑁒and.
  Qed.

  #[global] Instance into_sep𑁒biglater P Q1 Q2 :
    IntoSep P Q1 Q2 →
    IntoSep (▶ P) (▶ Q1) (▶ Q2).
  Proof.
    rewrite /IntoSep => ->.
    rewrite biglater𑁒sep //.
  Qed.

  #[global] Instance from_or𑁒biglater P Q1 Q2 :
    FromOr P Q1 Q2 →
    FromOr (▶ P) (▶ Q1) (▶ Q2).
  Proof.
    rewrite /FromOr.
    rewrite -biglater𑁒or.
    apply biglater𑁒mono.
  Qed.

  #[global] Instance into_or𑁒biglater P Q1 Q2 :
    IntoOr P Q1 Q2 →
    IntoOr (▶ P) (▶ Q1) (▶ Q2).
  Proof.
    rewrite /IntoOr => ->.
    rewrite biglater𑁒or //.
  Qed.

  #[global] Instance from_exist𑁒biglater {X} P (Φ : X → iProp Σ) :
    FromExist P Φ →
    FromExist (▶ P) (λ x, ▶ Φ x)%I.
  Proof.
    rewrite /FromExist.
    rewrite biglater𑁒exist₂.
    apply biglater𑁒mono.
  Qed.

  #[global] Instance into_exist𑁒biglater {X} P (Φ : X → iProp Σ) name :
    IntoExist P Φ name →
    Inhabited X →
    IntoExist (▶ P) (λ a, ▶ (Φ a))%I name.
  Proof.
    rewrite /IntoExist => HP HX.
    rewrite HP biglater𑁒exist //.
  Qed.

  #[global] Instance into_forall𑁒biglater {X} P (Φ : X → iProp Σ) :
    IntoForall P Φ →
    IntoForall (▶ P) (λ x, ▶ Φ x)%I.
  Proof.
    rewrite /IntoForall.
    rewrite -biglater𑁒forall.
    apply biglater𑁒mono.
  Qed.

  #[global] Instance frame𑁒biglater p R P Q :
    Frame p R P Q →
    Frame p R (▶ P) (▶ Q)
  | 2.
  Proof.
    rewrite /Frame => <-.
    iIntros "(HR & HQ)".
    iApply (biglater𑁒frame𑁒l with "HR HQ").
  Qed.

  #[global] Instance biglater𑁒strong_modality :
    ModalityStrongMono biglater.
  Proof.
    split=> P Q.
    - move=> -> //.
    - iIntros "(HP & HQ)".
      iApply (biglater𑁒frame𑁒r with "HP HQ").
  Qed.
End zoo۰G.
