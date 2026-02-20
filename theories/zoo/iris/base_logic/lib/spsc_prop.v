From iris.base_logic Require Import
  lib.invariants.

From zoo Require Import
  prelude.
From zoo.common Require Import
  countable.
From zoo.iris.base_logic Require Export
  lib.base.
From zoo.iris.base_logic Require Import
  lib.excl
  lib.oneshot.
From zoo.iris Require Import
  diaframe.
From zoo Require Import
  options.

Class SpscPropG Σ `{inv_G : !invGS Σ} := {
  #[local] spsc_prop_G_state_G :: OneshotG Σ () () ;
  #[local] spsc_prop_G_consumer_G :: ExclG Σ unitO ;
}.

Definition spsc_prop_Σ := #[
  oneshot_Σ () () ;
  excl_Σ unitO
].
#[global] Instance subG_spsc_prop_Σ Σ `{inv_G : !invGS Σ} :
  subG spsc_prop_Σ Σ →
  SpscPropG Σ.
Proof.
  solve_inG.
Qed.

Section spsc_prop_G.
  Context `{spsc_prop_G : SpscPropG Σ}.

  Implicit Types P : iProp Σ.

  Record spsc_prop_name := {
    spsc_prop_name_state : gname ;
    spsc_prop_name_consumer : gname ;
  }.
  Implicit Types γ : spsc_prop_name.

  #[global] Instance spsc_prop_name_eq_dec : EqDecision spsc_prop_name :=
    ltac:(solve_decision).
  #[global] Instance spsc_prop_name_countable :
    Countable spsc_prop_name.
  Proof.
    solve_countable.
  Qed.

  #[local] Definition state_unset₁' γ_state :=
    oneshot_pending γ_state (DfracOwn (2/3)) ().
  #[local] Definition state_unset₁ γ :=
    state_unset₁' γ.(spsc_prop_name_state).
  #[local] Definition state_unset₂' γ_state :=
    oneshot_pending γ_state (DfracOwn (1/3)) ().
  #[local] Definition state_unset₂ γ :=
    state_unset₂' γ.(spsc_prop_name_state).
  #[local] Definition state_set' γ_state :=
    oneshot_shot γ_state ().
  #[local] Definition state_set γ :=
    state_set' γ.(spsc_prop_name_state).

  #[local] Definition consumer' γ_consumer :=
    excl γ_consumer ().
  #[local] Definition consumer γ :=
    consumer' γ.(spsc_prop_name_consumer).

  #[local] Definition inv_consumer γ P : iProp Σ :=
    P ∨ consumer γ.
  #[local] Instance : CustomIpat "inv_consumer" :=
    " [ HP{_{!}}
      | >Hconsumer{_{!}}
      ]
    ".
  #[local] Definition inv_inner γ P : iProp Σ :=
    ( state_unset₂ γ
    ) ∨ (
      state_set γ ∗
      inv_consumer γ P
    ).
  #[local] Instance : CustomIpat "inv_inner" :=
    " [ >Hstate_unset₂
      | ( >Hstate_set{_{!}} &
          Hinv_consumer
        )
      ]
    ".
  Definition spsc_prop_inv γ ι P :=
    inv ι (inv_inner γ P).
  #[local] Instance : CustomIpat "inv" :=
    " #Hinv
    ".

  Definition spsc_prop_producer :=
    state_unset₁.
  #[local] Instance : CustomIpat "producer" :=
    " Hstate_unset₁
    ".

  Definition spsc_prop_consumer :=
    consumer.
  #[local] Instance : CustomIpat "consumer" :=
    " Hconsumer
    ".

  Definition spsc_prop_resolved :=
    state_set.
  #[local] Instance : CustomIpat "resolved" :=
    " #Hstate_set
    ".

  #[global] Instance spsc_prop_inv_contractive γ ι :
    Contractive (spsc_prop_inv γ ι).
  Proof.
    rewrite /spsc_prop_inv /inv_inner /inv_consumer.
    solve_contractive.
  Qed.
  #[global] Instance spsc_prop_inv_ne γ ι :
    NonExpansive (spsc_prop_inv γ ι).
  Proof.
    apply _.
  Qed.
  #[global] Instance spsc_prop_inv_proper γ ι :
    Proper ((≡) ==> (≡)) (spsc_prop_inv γ ι).
  Proof.
    apply _.
  Qed.

  #[global] Instance spsc_prop_producer_timeless γ :
    Timeless (spsc_prop_producer γ).
  Proof.
    apply _.
  Qed.
  #[global] Instance spsc_prop_consumer_timeless γ :
    Timeless (spsc_prop_consumer γ).
  Proof.
    apply _.
  Qed.
  #[global] Instance spsc_prop_resolved_timeless γ :
    Timeless (spsc_prop_resolved γ).
  Proof.
    apply _.
  Qed.

  #[global] Instance spsc_prop_inv_persistent γ ι P :
    Persistent (spsc_prop_inv γ ι P).
  Proof.
    apply _.
  Qed.
  #[global] Instance spsc_prop_resolved_persistent γ :
    Persistent (spsc_prop_resolved γ).
  Proof.
    apply _.
  Qed.

  #[local] Lemma state_alloc :
    ⊢ |==>
      ∃ γ_state,
      state_unset₁' γ_state ∗
      state_unset₂' γ_state.
  Proof.
    iMod oneshot_alloc as "(%γ_state & Hstate_unset)".
    assert (1 = 2/3 + 1/3)%Qp as -> by compute_done.
    iDestruct "Hstate_unset" as "($ & $)" => //.
  Qed.
  #[local] Lemma state_unset₁_exclusive γ :
    state_unset₁ γ -∗
    state_unset₁ γ -∗
    False.
  Proof.
    iIntros "Hunset₁_1 Hunset₁_2".
    iDestruct (oneshot_pending_valid_2 with "Hunset₁_1 Hunset₁_2") as %(? & _) => //.
  Qed.
  #[local] Lemma state_unset₁_set γ :
    state_unset₁ γ -∗
    state_set γ -∗
    False.
  Proof.
    apply oneshot_pending_shot.
  Qed.
  #[local] Lemma state_unset₂_set γ :
    state_unset₂ γ -∗
    state_set γ -∗
    False.
  Proof.
    apply oneshot_pending_shot.
  Qed.
  #[local] Lemma state_update γ :
    state_unset₁ γ -∗
    state_unset₂ γ ==∗
    state_set γ.
  Proof.
    iIntros "Hstate_unset₁ Hstate_unset₂".
    iCombine "Hstate_unset₁ Hstate_unset₂" as "Hstate_unset".
    assert (2/3 + 1/3 = 1)%Qp as -> by compute_done.
    iApply (oneshot_update_shot with "Hstate_unset").
  Qed.

  #[local] Lemma consumer_alloc :
    ⊢ |==>
      ∃ γ_consumer,
      consumer' γ_consumer.
  Proof.
    apply excl_alloc.
  Qed.
  #[local] Lemma consumer_exclusive γ :
    consumer γ -∗
    consumer γ -∗
    False.
  Proof.
    apply excl_exclusive.
  Qed.

  Lemma spsc_prop_alloc ι P E :
    ⊢ |={E}=>
      ∃ γ,
      spsc_prop_inv γ ι P ∗
      spsc_prop_producer γ ∗
      spsc_prop_consumer γ.
  Proof.
    iMod state_alloc as "(%γ_state & Hstate_unset₁ & Hstate_unset₂)".
    iMod consumer_alloc as "(%γ_consumer & Hconsumer)".
    pose γ := {|
      spsc_prop_name_state := γ_state ;
      spsc_prop_name_consumer := γ_consumer ;
    |}.
    iExists γ. iFrame.
    iApply inv_alloc.
    iFrame.
  Qed.

  Lemma spsc_prop_producer_exclusive γ :
    spsc_prop_producer γ -∗
    spsc_prop_producer γ -∗
    False.
  Proof.
    apply state_unset₁_exclusive.
  Qed.
  Lemma spcc_prop_producer_resolved γ :
    spsc_prop_producer γ -∗
    spsc_prop_resolved γ -∗
    False.
  Proof.
    apply state_unset₁_set.
  Qed.

  Lemma spsc_prop_consumer_exclusive γ :
    spsc_prop_consumer γ -∗
    spsc_prop_consumer γ -∗
    False.
  Proof.
    apply consumer_exclusive.
  Qed.

  Lemma spsc_prop_produce γ ι P E :
    ↑ι ⊆ E →
    spsc_prop_inv γ ι P -∗
    spsc_prop_producer γ -∗
    ▷ P ={E}=∗
    spsc_prop_resolved γ.
  Proof.
    iIntros "%HE (:inv) (:producer) HP".
    iInv "Hinv" as "(:inv_inner)".
    - iMod (state_update with "Hstate_unset₁ Hstate_unset₂") as "#Hstate_set".
      iSteps.
    - iDestruct (state_unset₁_set with "Hstate_unset₁ Hstate_set") as %[].
  Qed.
  Lemma spsc_prop_consume γ ι P E :
    ↑ι ⊆ E →
    spsc_prop_inv γ ι P -∗
    spsc_prop_consumer γ -∗
    spsc_prop_resolved γ ={E}=∗
    ▷ P.
  Proof.
    iIntros "%H (:inv) (:consumer) (:resolved)".
    iInv "Hinv" as "(:inv_inner !=)".
    - iDestruct (state_unset₂_set with "Hstate_unset₂ Hstate_set") as %[].
    - iDestruct "Hinv_consumer" as "(:inv_consumer !=)".
      + iFrameSteps.
      + iDestruct (consumer_exclusive with "Hconsumer Hconsumer_") as %[].
  Qed.
End spsc_prop_G.

#[global] Opaque spsc_prop_inv.
#[global] Opaque spsc_prop_producer.
#[global] Opaque spsc_prop_consumer.
#[global] Opaque spsc_prop_resolved.
