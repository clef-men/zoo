Require Import iris.base_logic.lib.invariants.

Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Export zoo.iris.base_logic.lib.base.
Require Import zoo.iris.base_logic.lib.excl.
Require Import zoo.iris.base_logic.lib.oneshot.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

Class SpscPropG Σ `{inv۰G : !invGS Σ} :=
  { #[local] spsc_prop۰G۰state۰G :: OneshotG Σ () ()
  ; #[local] spsc_prop۰G۰consumer۰G :: ExclG Σ unitO
  }.

Definition spsc_prop۰Σ :=
  #[oneshot۰Σ () ()
  ; excl۰Σ unitO
  ].
#[global] Instance subG𑁒spsc_prop۰Σ Σ `{inv۰G : !invGS Σ} :
  subG spsc_prop۰Σ Σ →
  SpscPropG Σ.
Proof.
  solve_inG.
Qed.

Section spsc_prop۰G.
  Context `{spsc_prop۰G : SpscPropG Σ}.

  Implicit Type P : iProp Σ.

  Record spsc_prop۰name :=
    { spsc_prop۰name۰state : gname
    ; spsc_prop۰name۰consumer : gname
    }.
  Implicit Type γ : spsc_prop۰name.

  #[global] Instance spsc_prop۰name𑁒eq_dec : EqDecision spsc_prop۰name :=
    ltac:(solve_decision).
  #[global] Instance spsc_prop۰name𑁒countable :
    Countable spsc_prop۰name.
  Proof.
    solve_countable.
  Qed.

  #[local] Definition state۰unset₁' γ_state :=
    oneshot۰pending γ_state (DfracOwn (2/3)) ().
  #[local] Definition state۰unset₁ γ :=
    state۰unset₁' γ.(spsc_prop۰name۰state).
  #[local] Definition state۰unset₂' γ_state :=
    oneshot۰pending γ_state (DfracOwn (1/3)) ().
  #[local] Definition state۰unset₂ γ :=
    state۰unset₂' γ.(spsc_prop۰name۰state).
  #[local] Definition state۰set' γ_state :=
    oneshot۰shot γ_state ().
  #[local] Definition state۰set γ :=
    state۰set' γ.(spsc_prop۰name۰state).

  #[local] Definition consumer' γ_consumer :=
    excl γ_consumer ().
  #[local] Definition consumer γ :=
    consumer' γ.(spsc_prop۰name۰consumer).

  #[local] Definition inv۰consumer γ P : iProp Σ :=
    P ∨ consumer γ.
  #[local] Instance : CustomIpat "inv۰consumer" :=
    " [ HP{_{!}}
      | >Hconsumer{_{!}}
      ]
    ".
  #[local] Definition inv۰inner γ P : iProp Σ :=
    ( state۰unset₂ γ
    ) ∨ (
      state۰set γ ∗
      inv۰consumer γ P
    ).
  #[local] Instance : CustomIpat "inv۰inner" :=
    " [ >Hstate_unset₂
      | ( >Hstate_set{_{!}}
        & Hinv_consumer
        )
      ]
    ".
  Definition spsc_prop۰inv γ ι P :=
    inv ι (inv۰inner γ P).
  #[local] Instance : CustomIpat "inv" :=
    " #Hinv
    ".

  Definition spsc_prop۰producer :=
    state۰unset₁.
  #[local] Instance : CustomIpat "producer" :=
    " Hstate_unset₁
    ".

  Definition spsc_prop۰consumer :=
    consumer.
  #[local] Instance : CustomIpat "consumer" :=
    " Hconsumer
    ".

  Definition spsc_prop۰resolved :=
    state۰set.
  #[local] Instance : CustomIpat "resolved" :=
    " #Hstate_set
    ".

  #[global] Instance spsc_prop۰inv𑁒contractive γ ι :
    Contractive (spsc_prop۰inv γ ι).
  Proof.
    rewrite /spsc_prop۰inv /inv۰inner /inv۰consumer.
    solve_contractive.
  Qed.
  #[global] Instance spsc_prop۰inv𑁒ne γ ι :
    NonExpansive (spsc_prop۰inv γ ι).
  Proof.
    apply _.
  Qed.
  #[global] Instance spsc_prop۰inv𑁒proper γ ι :
    Proper ((≡) ==> (≡)) (spsc_prop۰inv γ ι).
  Proof.
    apply _.
  Qed.

  #[global] Instance spsc_prop۰producer𑁒timeless γ :
    Timeless (spsc_prop۰producer γ).
  Proof.
    apply _.
  Qed.
  #[global] Instance spsc_prop۰consumer𑁒timeless γ :
    Timeless (spsc_prop۰consumer γ).
  Proof.
    apply _.
  Qed.
  #[global] Instance spsc_prop۰resolved𑁒timeless γ :
    Timeless (spsc_prop۰resolved γ).
  Proof.
    apply _.
  Qed.

  #[global] Instance spsc_prop۰inv𑁒persistent γ ι P :
    Persistent (spsc_prop۰inv γ ι P).
  Proof.
    apply _.
  Qed.
  #[global] Instance spsc_prop۰resolved𑁒persistent γ :
    Persistent (spsc_prop۰resolved γ).
  Proof.
    apply _.
  Qed.

  #[local] Lemma state𑁒alloc :
    ⊢ |==>
      ∃ γ_state,
      state۰unset₁' γ_state ∗
      state۰unset₂' γ_state.
  Proof.
    iMod oneshot𑁒alloc as "(%γ_state & Hstate_unset)".
    assert (1 = 2/3 + 1/3)%Qp as -> by compute_done.
    iDestruct "Hstate_unset" as "($ & $)" => //.
  Qed.
  #[local] Lemma state۰unset₁𑁒exclusive γ :
    state۰unset₁ γ -∗
    state۰unset₁ γ -∗
    False.
  Proof.
    iIntros "Hunset₁_1 Hunset₁_2".
    iDestruct (oneshot۰pending𑁒valid𑁒2 with "Hunset₁_1 Hunset₁_2") as %(? & _) => //.
  Qed.
  #[local] Lemma state۰unset₁𑁒set γ :
    state۰unset₁ γ -∗
    state۰set γ -∗
    False.
  Proof.
    apply oneshot𑁒pending𑁒shot.
  Qed.
  #[local] Lemma state۰unset₂𑁒set γ :
    state۰unset₂ γ -∗
    state۰set γ -∗
    False.
  Proof.
    apply oneshot𑁒pending𑁒shot.
  Qed.
  #[local] Lemma state𑁒update γ :
    state۰unset₁ γ -∗
    state۰unset₂ γ ==∗
    state۰set γ.
  Proof.
    iIntros "Hstate_unset₁ Hstate_unset₂".
    iCombine "Hstate_unset₁ Hstate_unset₂" as "Hstate_unset".
    assert (2/3 + 1/3 = 1)%Qp as -> by compute_done.
    iApply (oneshot𑁒update𑁒shot with "Hstate_unset").
  Qed.

  #[local] Lemma consumer𑁒alloc :
    ⊢ |==>
      ∃ γ_consumer,
      consumer' γ_consumer.
  Proof.
    apply excl𑁒alloc.
  Qed.
  #[local] Lemma consumer𑁒exclusive γ :
    consumer γ -∗
    consumer γ -∗
    False.
  Proof.
    apply excl𑁒exclusive.
  Qed.

  Lemma spsc_prop𑁒alloc ι P E :
    ⊢ |={E}=>
      ∃ γ,
      spsc_prop۰inv γ ι P ∗
      spsc_prop۰producer γ ∗
      spsc_prop۰consumer γ.
  Proof.
    iMod state𑁒alloc as "(%γ_state & Hstate_unset₁ & Hstate_unset₂)".
    iMod consumer𑁒alloc as "(%γ_consumer & Hconsumer)".
    pose γ :=
      {|spsc_prop۰name۰state := γ_state
      ; spsc_prop۰name۰consumer := γ_consumer
      |}.
    iExists γ. iFrame.
    iApply inv_alloc.
    iFrame.
  Qed.

  Lemma spsc_prop۰producer𑁒exclusive γ :
    spsc_prop۰producer γ -∗
    spsc_prop۰producer γ -∗
    False.
  Proof.
    apply state۰unset₁𑁒exclusive.
  Qed.
  Lemma spcc_prop۰producer𑁒resolved γ :
    spsc_prop۰producer γ -∗
    spsc_prop۰resolved γ -∗
    False.
  Proof.
    apply state۰unset₁𑁒set.
  Qed.

  Lemma spsc_prop۰consumer𑁒exclusive γ :
    spsc_prop۰consumer γ -∗
    spsc_prop۰consumer γ -∗
    False.
  Proof.
    apply consumer𑁒exclusive.
  Qed.

  Lemma spsc_prop𑁒produce γ ι P E :
    ↑ι ⊆ E →
    spsc_prop۰inv γ ι P -∗
    spsc_prop۰producer γ -∗
    ▷ P ={E}=∗
    spsc_prop۰resolved γ.
  Proof.
    iIntros "%HE (:inv) (:producer) HP".
    iInv "Hinv" as "(:inv۰inner)".
    - iMod (state𑁒update with "Hstate_unset₁ Hstate_unset₂") as "#Hstate_set".
      iSteps.
    - iDestruct (state۰unset₁𑁒set with "Hstate_unset₁ Hstate_set") as %[].
  Qed.
  Lemma spsc_prop𑁒consume γ ι P E :
    ↑ι ⊆ E →
    spsc_prop۰inv γ ι P -∗
    spsc_prop۰consumer γ -∗
    spsc_prop۰resolved γ ={E}=∗
    ▷ P.
  Proof.
    iIntros "%H (:inv) (:consumer) (:resolved)".
    iInv "Hinv" as "(:inv۰inner !=)".
    - iDestruct (state۰unset₂𑁒set with "Hstate_unset₂ Hstate_set") as %[].
    - iDestruct "Hinv_consumer" as "(:inv۰consumer !=)".
      + iFrameSteps.
      + iDestruct (consumer𑁒exclusive with "Hconsumer Hconsumer_") as %[].
  Qed.
End spsc_prop۰G.

#[global] Opaque spsc_prop۰inv.
#[global] Opaque spsc_prop۰producer.
#[global] Opaque spsc_prop۰consumer.
#[global] Opaque spsc_prop۰resolved.
