Require Import zoo.prelude.
Require Export zoo.program_logic.wp.
Require Import zoo.diaframe.
Require Import zoo.options.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Implicit Type P : iProp Σ.

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

  Implicit Type P : iProp Σ.

  #[global] Instance biglaterｰne :
    NonExpansive biglater.
  Proof.
    solve_proper.
  Qed.
  #[global] Instance biglaterｰproper :
    Proper ((≡) ==> (≡)) biglater.
  Proof.
    solve_proper.
  Qed.

  Lemma biglaterｰintro P :
    P ⊢ |==>
    ▶ P.
  Proof.
    iIntros "HP".
    iMod steps۰lbｰ0 as "$" => //.
  Qed.

  Lemma biglaterｰmono P1 P2 :
    (P1 ⊢ P2) →
    (▶ P1) ⊢ ▶ P2.
  Proof.
    iIntros "%HP (:biglater =1)".
    iFrame "#". iNext.
    iApply (HP with "HP1").
  Qed.
  #[global] Instance biglaterｰmono' :
    Proper ((⊢) ==> (⊢)) biglater.
  Proof.
    iIntros "%P1 %P2 %HP".
    iApply biglaterｰmono; first done.
  Qed.
  #[global] Instance biglaterｰflipｰmono' :
    Proper (flip (⊢) ==> flip (⊢)) biglater.
  Proof.
    iIntros "%P1 %P2 %HP".
    iApply biglaterｰmono; first done.
  Qed.

  Lemma biglaterｰor₁ P1 P2 :
    ▶ (P1 ∨ P2) ⊢
    ▶ P1 ∨ ▶ P2.
  Proof.
    iIntros "(:biglater)".
    iFrame "#".
    rewrite bi.laterN_or //.
  Qed.
  Lemma biglaterｰor₂ P1 P2 :
    ▶ P1 ∨ ▶ P2 ⊢
    ▶ (P1 ∨ P2).
  Proof.
    iSteps.
  Qed.
  Lemma biglaterｰor P1 P2 :
    ▶ (P1 ∨ P2) ⊣⊢
    ▶ P1 ∨ ▶ P2.
  Proof.
    iSplit.
    - iApply biglaterｰor₁.
    - iApply biglaterｰor₂.
  Qed.

  Lemma biglaterｰand P1 P2 :
    ▶ (P1 ∧ P2) ⊢
    ▶ P1 ∧ ▶ P2.
  Proof.
    iIntros "(:biglater)".
    iFrame "#".
    iApply bi.laterN_and.
    iApply (bi.laterN_mono with "HP"); first done.
  Qed.

  Lemma biglaterｰexist₁ `{!Inhabited X} (Φ : X → iProp Σ) :
    ▶ (∃ x, Φ x) ⊢
    ∃ x, ▶ Φ x.
  Proof.
    iSteps.
  Qed.
  Lemma biglaterｰexist₂ `(Φ : X → iProp Σ) :
    (∃ x, ▶ Φ x) ⊢
    ▶ ∃ x, Φ x.
  Proof.
    iSteps.
  Qed.
  Lemma biglaterｰexist `{!Inhabited X} (Φ : X → iProp Σ) :
    ▶ (∃ x, Φ x) ⊣⊢
    ∃ x, ▶ Φ x.
  Proof.
    iSplit.
    - iApply @biglaterｰexist₁.
    - iApply biglaterｰexist₂.
  Qed.

  Lemma biglaterｰforall `(Φ : X → iProp Σ) :
    ▶ (∀ x, Φ x) ⊢
    ∀ x, ▶ Φ x.
  Proof.
    iSteps.
  Qed.

  Lemma biglaterｰsep₁ P1 P2 :
    ▶ (P1 ∗ P2) ⊢
      ▶ P1 ∗
      ▶ P2.
  Proof.
    iSteps.
  Qed.
  Lemma biglaterｰsep₂ P1 P2 :
    ▶ P1 -∗
    ▶ P2 -∗
    ▶ (P1 ∗ P2).
  Proof.
    iIntros "(:biglater =1) (:biglater =2)".
    iExists (ns1 `max` ns2). iSplitR.
    - iApply (steps۰lbｰmax with "H⧖_1 H⧖_2").
    - iApply bi.laterN_sep.
      iDestruct (bi.laterN_le with "HP1") as "$".
      { auto with lia. }
      iDestruct (bi.laterN_le with "HP2") as "$".
      { auto with lia. }
  Qed.
  Lemma biglaterｰsep P1 P2 :
    ▶ (P1 ∗ P2) ⊣⊢
      ▶ P1 ∗
      ▶ P2.
  Proof.
    iSplit.
    - iApply biglaterｰsep₁.
    - iIntros "(HP1 & HP2)".
      iApply (biglaterｰsep₂ with "HP1 HP2").
  Qed.

  Lemma biglaterｰframeｰl P1 P2 :
    P1 -∗
    ▶ P2 -∗
    ▶ (P1 ∗ P2).
  Proof.
    iSteps.
  Qed.
  Lemma biglaterｰframeｰr P1 P2 :
    ▶ P1 -∗
    P2 -∗
    ▶ (P1 ∗ P2).
  Proof.
    rewrite bi.sep_comm.
    iIntros "HP1 HP2".
    iApply (biglaterｰframeｰl with "HP2 HP1").
  Qed.

  Lemma biglaterｰwandｰl P1 P2 :
    (P1 -∗ P2) -∗
    (▶ P1) -∗
    ▶ P2.
  Proof.
    iSteps.
  Qed.
  Lemma biglaterｰwandｰr P1 P2 :
    (▶ P1) -∗
    (P1 -∗ P2) -∗
    ▶ P2.
  Proof.
    iIntros "HP1 HP2".
    iApply (biglaterｰwandｰl with "HP2 HP1").
  Qed.

  Lemma biglaterｰpersistently P :
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

  Implicit Type P : iProp Σ.

  #[global] Instance into_wandｰbiglater p q R P Q :
    IntoWand false false R P Q →
    IntoWand p q (▶ R) (▶ P) (▶ Q).
  Proof.
    rewrite /IntoWand /=.
    rewrite !bi.intuitionistically_if_elim.
    iIntros "%H HR HP".
    iDestruct (biglaterｰsep₂ with "HR HP") as "H".
    iApply (biglaterｰwandｰr with "H"). iIntros "(HR & HP)".
    iApply (H with "HR HP").
  Qed.
  #[global] Instance into_wandｰbiglaterｰargs p q R P Q :
    IntoWand p false R P Q →
    IntoWand' p q R (▶ P) (▶ Q).
  Proof.
    rewrite /IntoWand' /IntoWand /=.
    rewrite (bi.intuitionistically_if_elim q).
    iIntros "%H HR HP".
    iApply (biglaterｰwandｰr with "HP"). iIntros "HP".
    iApply (H with "HR HP").
  Qed.

  #[global] Instance from_sepｰbiglater P Q1 Q2 :
    FromSep P Q1 Q2 →
    FromSep (▶ P) (▶ Q1) (▶ Q2).
  Proof.
    rewrite /FromSep.
    rewrite -biglaterｰsep.
    apply biglaterｰmono.
  Qed.

  #[global] Instance maybe_combine_sep_asｰbiglater Q1 Q2 P progress :
    MaybeCombineSepAs Q1 Q2 P progress →
    MaybeCombineSepAs (▶ Q1) (▶ Q2) (▶ P) progress.
  Proof.
    rewrite /MaybeCombineSepAs.
    rewrite -biglaterｰsep => -> //.
  Qed.

  #[global] Instance combine_sep_givesｰbiglater Q1 Q2 P :
    CombineSepGives Q1 Q2 P →
    CombineSepGives (▶ Q1) (▶ Q2) (▶ P).
  Proof.
    rewrite /CombineSepGives.
    rewrite -biglaterｰsep -biglaterｰpersistently => -> //.
  Qed.

  #[global] Instance into_andｰbiglater P Q1 Q2 :
    IntoAnd false P Q1 Q2 →
    IntoAnd false (▶ P) (▶ Q1) (▶ Q2).
  Proof.
    rewrite /IntoAnd /= => ->.
    apply biglaterｰand.
  Qed.

  #[global] Instance into_sepｰbiglater P Q1 Q2 :
    IntoSep P Q1 Q2 →
    IntoSep (▶ P) (▶ Q1) (▶ Q2).
  Proof.
    rewrite /IntoSep => ->.
    rewrite biglaterｰsep //.
  Qed.

  #[global] Instance from_orｰbiglater P Q1 Q2 :
    FromOr P Q1 Q2 →
    FromOr (▶ P) (▶ Q1) (▶ Q2).
  Proof.
    rewrite /FromOr.
    rewrite -biglaterｰor.
    apply biglaterｰmono.
  Qed.

  #[global] Instance into_orｰbiglater P Q1 Q2 :
    IntoOr P Q1 Q2 →
    IntoOr (▶ P) (▶ Q1) (▶ Q2).
  Proof.
    rewrite /IntoOr => ->.
    rewrite biglaterｰor //.
  Qed.

  #[global] Instance from_existｰbiglater {X} P (Φ : X → iProp Σ) :
    FromExist P Φ →
    FromExist (▶ P) (λ x, ▶ Φ x)%I.
  Proof.
    rewrite /FromExist.
    rewrite biglaterｰexist₂.
    apply biglaterｰmono.
  Qed.

  #[global] Instance into_existｰbiglater {X} P (Φ : X → iProp Σ) name :
    IntoExist P Φ name →
    Inhabited X →
    IntoExist (▶ P) (λ a, ▶ (Φ a))%I name.
  Proof.
    rewrite /IntoExist => HP HX.
    rewrite HP biglaterｰexist //.
  Qed.

  #[global] Instance into_forallｰbiglater {X} P (Φ : X → iProp Σ) :
    IntoForall P Φ →
    IntoForall (▶ P) (λ x, ▶ Φ x)%I.
  Proof.
    rewrite /IntoForall.
    rewrite -biglaterｰforall.
    apply biglaterｰmono.
  Qed.

  #[global] Instance frameｰbiglater p R P Q :
    Frame p R P Q →
    Frame p R (▶ P) (▶ Q)
  | 2.
  Proof.
    rewrite /Frame => <-.
    iIntros "(HR & HQ)".
    iApply (biglaterｰframeｰl with "HR HQ").
  Qed.

  #[global] Instance biglaterｰstrong_modality :
    ModalityStrongMono biglater.
  Proof.
    split=> P Q.
    - move=> -> //.
    - iIntros "(HP & HQ)".
      iApply (biglaterｰframeｰr with "HP HQ").
  Qed.
End zoo۰G.
