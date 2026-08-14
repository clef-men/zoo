Require Import iris.base_logic.lib.invariants.

Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Export zoo.iris.base_logic.lib.base.
Require Import zoo.iris.base_logic.lib.excl.
Require Import zoo.iris.base_logic.lib.oneshot.
Require Import zoo.iris.diaframe.
Require Import zoo.options.

Class PropSpscG Σ `{inv۰G : !invGS Σ} :=
  { #[local] prop_spsc۰G۰state۰G :: OneshotG Σ () ()
  ; #[local] prop_spsc۰G۰consumer۰G :: ExclG Σ unitO
  }.

Definition prop_spsc۰Σ :=
  #[oneshot۰Σ () ()
  ; excl۰Σ unitO
  ].
#[global] Instance subGｰprop_spsc۰Σ Σ `{inv۰G : !invGS Σ} :
  subG prop_spsc۰Σ Σ →
  PropSpscG Σ.
Proof.
  solve_inG.
Qed.

Section prop_spsc۰G.
  Context `{prop_spsc۰G : PropSpscG Σ}.

  Implicit Type P : iProp Σ.

  Record prop_spsc۰name :=
    { prop_spsc۰name۰state : gname
    ; prop_spsc۰name۰consumer : gname
    }.
  Implicit Type γ : prop_spsc۰name.

  #[global] Instance prop_spsc۰nameｰeq_dec : EqDecision prop_spsc۰name :=
    ltac:(solve_decision).
  #[global] Instance prop_spsc۰nameｰcountable :
    Countable prop_spsc۰name.
  Proof.
    solve_countable.
  Qed.

  #[local] Definition state۰unset₁' γ_state :=
    oneshot۰pending γ_state (DfracOwn (2/3)) ().
  #[local] Definition state۰unset₁ γ :=
    state۰unset₁' γ.(prop_spsc۰name۰state).
  #[local] Definition state۰unset₂' γ_state :=
    oneshot۰pending γ_state (DfracOwn (1/3)) ().
  #[local] Definition state۰unset₂ γ :=
    state۰unset₂' γ.(prop_spsc۰name۰state).
  #[local] Definition state۰set' γ_state :=
    oneshot۰shot γ_state ().
  #[local] Definition state۰set γ :=
    state۰set' γ.(prop_spsc۰name۰state).

  #[local] Definition consumer' γ_consumer :=
    excl γ_consumer ().
  #[local] Definition consumer γ :=
    consumer' γ.(prop_spsc۰name۰consumer).

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
  Definition prop_spsc۰inv γ ι P :=
    inv ι (inv۰inner γ P).
  #[local] Instance : CustomIpat "inv" :=
    " #Hinv
    ".

  Definition prop_spsc۰producer :=
    state۰unset₁.
  #[local] Instance : CustomIpat "producer" :=
    " Hstate_unset₁
    ".

  Definition prop_spsc۰consumer :=
    consumer.
  #[local] Instance : CustomIpat "consumer" :=
    " Hconsumer
    ".

  Definition prop_spsc۰resolved :=
    state۰set.
  #[local] Instance : CustomIpat "resolved" :=
    " #Hstate_set
    ".

  #[global] Instance prop_spsc۰invｰcontractive γ ι :
    Contractive (prop_spsc۰inv γ ι).
  Proof.
    rewrite /prop_spsc۰inv /inv۰inner /inv۰consumer.
    solve_contractive.
  Qed.
  #[global] Instance prop_spsc۰invｰne γ ι :
    NonExpansive (prop_spsc۰inv γ ι).
  Proof.
    apply _.
  Qed.
  #[global] Instance prop_spsc۰invｰproper γ ι :
    Proper ((≡) ==> (≡)) (prop_spsc۰inv γ ι).
  Proof.
    apply _.
  Qed.

  #[global] Instance prop_spsc۰producerｰtimeless γ :
    Timeless (prop_spsc۰producer γ).
  Proof.
    apply _.
  Qed.
  #[global] Instance prop_spsc۰consumerｰtimeless γ :
    Timeless (prop_spsc۰consumer γ).
  Proof.
    apply _.
  Qed.
  #[global] Instance prop_spsc۰resolvedｰtimeless γ :
    Timeless (prop_spsc۰resolved γ).
  Proof.
    apply _.
  Qed.

  #[global] Instance prop_spsc۰invｰpersistent γ ι P :
    Persistent (prop_spsc۰inv γ ι P).
  Proof.
    apply _.
  Qed.
  #[global] Instance prop_spsc۰resolvedｰpersistent γ :
    Persistent (prop_spsc۰resolved γ).
  Proof.
    apply _.
  Qed.

  #[local] Lemma stateｰalloc :
    ⊢ |==>
      ∃ γ_state,
      state۰unset₁' γ_state ∗
      state۰unset₂' γ_state.
  Proof.
    iMod oneshotｰalloc as "(%γ_state & Hstate_unset)".
    assert (1 = 2/3 + 1/3)%Qp as -> by compute_done.
    iDestruct "Hstate_unset" as "($ & $)" => //.
  Qed.
  #[local] Lemma state۰unset₁ｰexclusive γ :
    state۰unset₁ γ -∗
    state۰unset₁ γ -∗
    False.
  Proof.
    iIntros "Hunset₁_1 Hunset₁_2".
    iDestruct (oneshot۰pendingｰvalidｰ2 with "Hunset₁_1 Hunset₁_2") as %(? & _) => //.
  Qed.
  #[local] Lemma state۰unset₁ｰset γ :
    state۰unset₁ γ -∗
    state۰set γ -∗
    False.
  Proof.
    apply oneshotｰpendingｰshot.
  Qed.
  #[local] Lemma state۰unset₂ｰset γ :
    state۰unset₂ γ -∗
    state۰set γ -∗
    False.
  Proof.
    apply oneshotｰpendingｰshot.
  Qed.
  #[local] Lemma stateｰupdate γ :
    state۰unset₁ γ -∗
    state۰unset₂ γ ==∗
    state۰set γ.
  Proof.
    iIntros "Hstate_unset₁ Hstate_unset₂".
    iCombine "Hstate_unset₁ Hstate_unset₂" as "Hstate_unset".
    assert (2/3 + 1/3 = 1)%Qp as -> by compute_done.
    iApply (oneshotｰupdateｰshot with "Hstate_unset").
  Qed.

  #[local] Lemma consumerｰalloc :
    ⊢ |==>
      ∃ γ_consumer,
      consumer' γ_consumer.
  Proof.
    apply exclｰalloc.
  Qed.
  #[local] Lemma consumerｰexclusive γ :
    consumer γ -∗
    consumer γ -∗
    False.
  Proof.
    apply exclｰexclusive.
  Qed.

  Lemma prop_spscｰalloc ι P E :
    ⊢ |={E}=>
      ∃ γ,
      prop_spsc۰inv γ ι P ∗
      prop_spsc۰producer γ ∗
      prop_spsc۰consumer γ.
  Proof.
    iMod stateｰalloc as "(%γ_state & Hstate_unset₁ & Hstate_unset₂)".
    iMod consumerｰalloc as "(%γ_consumer & Hconsumer)".
    pose γ :=
      {|prop_spsc۰name۰state := γ_state
      ; prop_spsc۰name۰consumer := γ_consumer
      |}.
    iExists γ. iFrame.
    iApply inv_alloc.
    iFrame.
  Qed.

  Lemma prop_spsc۰producerｰexclusive γ :
    prop_spsc۰producer γ -∗
    prop_spsc۰producer γ -∗
    False.
  Proof.
    apply state۰unset₁ｰexclusive.
  Qed.
  Lemma spcc_prop۰producerｰresolved γ :
    prop_spsc۰producer γ -∗
    prop_spsc۰resolved γ -∗
    False.
  Proof.
    apply state۰unset₁ｰset.
  Qed.

  Lemma prop_spsc۰consumerｰexclusive γ :
    prop_spsc۰consumer γ -∗
    prop_spsc۰consumer γ -∗
    False.
  Proof.
    apply consumerｰexclusive.
  Qed.

  Lemma prop_spscｰproduce γ ι P E :
    ↑ι ⊆ E →
    prop_spsc۰inv γ ι P -∗
    prop_spsc۰producer γ -∗
    ▷ P ={E}=∗
    prop_spsc۰resolved γ.
  Proof.
    iIntros "%HE (:inv) (:producer) HP".
    iInv "Hinv" as "(:inv۰inner)".
    - iMod (stateｰupdate with "Hstate_unset₁ Hstate_unset₂") as "#Hstate_set".
      iSteps.
    - iDestruct (state۰unset₁ｰset with "Hstate_unset₁ Hstate_set") as %[].
  Qed.
  Lemma prop_spscｰconsume γ ι P E :
    ↑ι ⊆ E →
    prop_spsc۰inv γ ι P -∗
    prop_spsc۰consumer γ -∗
    prop_spsc۰resolved γ ={E}=∗
    ▷ P.
  Proof.
    iIntros "%H (:inv) (:consumer) (:resolved)".
    iInv "Hinv" as "(:inv۰inner !=)".
    - iDestruct (state۰unset₂ｰset with "Hstate_unset₂ Hstate_set") as %[].
    - iDestruct "Hinv_consumer" as "(:inv۰consumer !=)".
      + iFrameSteps.
      + iDestruct (consumerｰexclusive with "Hconsumer Hconsumer_") as %[].
  Qed.
End prop_spsc۰G.

#[global] Opaque prop_spsc۰inv.
#[global] Opaque prop_spsc۰producer.
#[global] Opaque prop_spsc۰consumer.
#[global] Opaque prop_spsc۰resolved.
