From zoo Require Import
  prelude.
From zoo.common Require Import
  countable.
From zoo.iris.base_logic Require Import
  lib.excl
  lib.oneshot.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
  base
  mpsc_flag__code.
From zoo Require Import
  options.

Implicit Types b : bool.

Class MpscFlagG Σ `{zoo_G : !ZooG Σ} :=
  { #[local] mpsc_flag_G_state_G :: OneshotG Σ () ()
  ; #[local] mpsc_flag_G_consumer_G :: ExclG Σ unitO
  }.

Definition mpsc_flag_Σ := #[
  oneshot_Σ () () ;
  excl_Σ unitO
].
#[global] Instance subG_mpsc_flag_Σ `{zoo_G : !ZooG Σ} :
  subG mpsc_flag_Σ Σ →
  MpscFlagG Σ.
Proof.
  solve_inG.
Qed.

Module base.
  Section mpsc_flag_G.
    Context `{mpsc_flag_G : MpscFlagG Σ}.

    Implicit Types t : location.
    Implicit Types P : iProp Σ.

    Record mpsc_flag_name :=
      { mpsc_flag_name_state : gname
      ; mpsc_flag_name_consumer : gname
      }.
    Implicit Types γ : mpsc_flag_name.

    #[global] Instance mpsc_flag_name_eq_dec : EqDecision mpsc_flag_name :=
      ltac:(solve_decision).
    #[global] Instance mpsc_flag_name_countable :
      Countable mpsc_flag_name.
    Proof.
      solve_countable.
    Qed.

    #[local] Definition state_unset' γ_state :=
      oneshot_pending γ_state Own ().
    #[local] Definition state_unset γ :=
      state_unset' γ.(mpsc_flag_name_state).
    #[local] Definition state_set' γ_state :=
      oneshot_shot γ_state ().
    #[local] Definition state_set γ :=
      state_set' γ.(mpsc_flag_name_state).

    #[local] Definition consumer' γ_consumer :=
      excl γ_consumer ().
    #[local] Definition consumer γ :=
      consumer' γ.(mpsc_flag_name_consumer).

    #[local] Definition inv_consumer γ P : iProp Σ :=
      P ∨ consumer γ.
    #[local] Instance : CustomIpat "inv_consumer" :=
      " [ HP
        | Hconsumer{_{!}}
        ]
      ".
    #[local] Definition inv_set γ P : iProp Σ :=
      state_set γ ∗
      inv_consumer γ P.
    #[local] Instance : CustomIpat "inv_set" :=
      " ( #Hstate_set
        & Hinv_consumer
        )
      ".
    #[local] Definition inv_inner t γ P : iProp Σ :=
      ∃ b,
      t ↦ᵣ #b ∗
      if b then
        inv_set γ P
      else
        state_unset γ.
    #[local] Instance : CustomIpat "inv_inner" :=
      " ( %b
        & >Ht
        & Hb
        )
      ".
    Definition mpsc_flag_inv t γ P :=
      inv nroot (inv_inner t γ P).
    #[local] Instance : CustomIpat "inv" :=
      " #Hinv
      ".

    Definition mpsc_flag_consumer :=
      consumer.
    #[local] Instance : CustomIpat "consumer" :=
      " Hconsumer
      ".

    Definition mpsc_flag_resolved :=
      state_set.
    #[local] Instance : CustomIpat "resolved" :=
      " #Hstate_set
      ".

    #[global] Instance mpsc_flag_inv_contractive t γ :
      Contractive (mpsc_flag_inv t γ).
    Proof.
      rewrite /mpsc_flag_inv /inv_inner /inv_set  /inv_consumer.
      solve_contractive.
    Qed.
    #[global] Instance mpsc_flag_inv_ne t γ :
      NonExpansive (mpsc_flag_inv t γ).
    Proof.
      apply _.
    Qed.
    #[global] Instance mpsc_flag_inv_proper t γ :
      Proper ((≡) ==> (≡)) (mpsc_flag_inv t γ).
    Proof.
      apply _.
    Qed.

    #[global] Instance mpsc_flag_consumer_timeless γ :
      Timeless (mpsc_flag_consumer γ).
    Proof.
      apply _.
    Qed.
    #[global] Instance mpsc_flag_resolved_timeless γ :
      Timeless (mpsc_flag_resolved γ).
    Proof.
      apply _.
    Qed.

    #[global] Instance mpsc_flag_inv_persistent t γ P :
      Persistent (mpsc_flag_inv t γ P).
    Proof.
      apply _.
    Qed.
    #[global] Instance mpsc_flag_resolved_persistent γ :
      Persistent (mpsc_flag_resolved γ).
    Proof.
      apply _.
    Qed.

    #[local] Lemma state_alloc :
      ⊢ |==>
        ∃ γ_state,
        state_unset' γ_state.
    Proof.
      apply: oneshot_alloc.
    Qed.
    #[local] Lemma state_unset_set γ :
      state_unset γ -∗
      state_set γ -∗
      False.
    Proof.
      apply oneshot_pending_shot.
    Qed.
    #[local] Lemma state_update γ :
      state_unset γ ⊢ |==>
      state_set γ.
    Proof.
      apply oneshot_update_shot.
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

    Lemma mpsc_flag_consumer_exclusive γ :
      mpsc_flag_consumer γ -∗
      mpsc_flag_consumer γ -∗
      False.
    Proof.
      apply consumer_exclusive.
    Qed.

    Lemma mpsc_flag_create_spec P :
      {{{
        True
      }}}
        mpsc_flag_create ()
      {{{
        t γ
      , RET #t;
        meta_token t ⊤ ∗
        mpsc_flag_inv t γ P ∗
        mpsc_flag_consumer γ
      }}}.
    Proof.
      iIntros "%Φ _ HΦ".

      wp_rec.
      wp_ref t as "Ht" "Hmeta".

      iMod state_alloc as "(%γ_state & Hstate_unset)".
      iMod consumer_alloc as "(%γ_consumer & Hconsumer)".

      pose γ := {|
        mpsc_flag_name_state := γ_state ;
        mpsc_flag_name_consumer := γ_consumer ;
      |}.

      iApply ("HΦ" $! t γ).
      iFrameSteps.
    Qed.

    Lemma mpsc_flag_get_spec t γ P :
      {{{
        mpsc_flag_inv t γ P ∗
        mpsc_flag_consumer γ
      }}}
        mpsc_flag_get #t
      {{{
        b
      , RET #b;
        if b then
          P
        else
          mpsc_flag_consumer γ
      }}}.
    Proof.
      iIntros "%Φ ((:inv) & (:consumer)) HΦ".

      wp_rec credit:"H£".

      iInv "Hinv" as "(:inv_inner)".
      wp_load.
      destruct b.

      - iDestruct "Hb" as "(:inv_set)".
        iDestruct "Hinv_consumer" as "(:inv_consumer !=)".
        + iFrameSteps.
        + iDestruct (consumer_exclusive with "Hconsumer Hconsumer_") as %[].

      - iFrameSteps.
    Qed.

    Lemma mpsc_flag_set_spec t γ P :
      {{{
        mpsc_flag_inv t γ P ∗
        ▷ P
      }}}
        mpsc_flag_set #t
      {{{
        RET ();
        mpsc_flag_resolved γ
      }}}.
    Proof.
      iIntros "%Φ ((:inv) & HP) HΦ".

      wp_rec.

      iInv "Hinv" as "(:inv_inner)".
      wp_store.
      destruct b. 1: iFrameSteps.
      iMod (state_update with "Hb") as "#Hstate_set".
      iFrameSteps.
    Qed.
  End mpsc_flag_G.

  #[global] Opaque mpsc_flag_inv.
  #[global] Opaque mpsc_flag_consumer.
  #[global] Opaque mpsc_flag_resolved.
End base.

From zoo_std Require
  mpsc_flag__opaque.

Section mpsc_flag_G.
  Context `{mpsc_flag_G : MpscFlagG Σ}.

  Implicit Types 𝑡 : location.
  Implicit Types t : val.
  Implicit Types P : iProp Σ.

  Definition mpsc_flag_inv t P : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.mpsc_flag_inv 𝑡 γ P.
  #[local] Instance : CustomIpat "inv" :=
    " ( %l{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hinv{_{}}
      )
    ".

  Definition mpsc_flag_consumer t : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.mpsc_flag_consumer γ.
  #[local] Instance : CustomIpat "consumer" :=
    " ( %l{;_}
      & %γ{;_}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hconsumer{_{}}
      )
    ".

  Definition mpsc_flag_resolved t : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.mpsc_flag_resolved γ.
  #[local] Instance : CustomIpat "resolved" :=
    " ( %l{;_}
      & %γ{;_}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hresolved{_{}}
      )
    ".

  #[global] Instance mpsc_flag_inv_contractive t :
    Contractive (mpsc_flag_inv t).
  Proof.
    solve_contractive.
  Qed.
  #[global] Instance mpsc_flag_inv_ne t :
    NonExpansive (mpsc_flag_inv t).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpsc_flag_inv_proper t :
    Proper ((≡) ==> (≡)) (mpsc_flag_inv t).
  Proof.
    apply _.
  Qed.

  #[global] Instance mpsc_flag_consumer_timeless t :
    Timeless (mpsc_flag_consumer t).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpsc_flag_resolved_timeless t :
    Timeless (mpsc_flag_resolved t).
  Proof.
    apply _.
  Qed.

  #[global] Instance mpsc_flag_inv_persistent t P :
    Persistent (mpsc_flag_inv t P).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpsc_flag_resolved_persistent t :
    Persistent (mpsc_flag_resolved t).
  Proof.
    apply _.
  Qed.

  Lemma mpsc_flag_consumer_exclusive t :
    mpsc_flag_consumer t -∗
    mpsc_flag_consumer t -∗
    False.
  Proof.
    iIntros "(:consumer =1) (:consumer =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.mpsc_flag_consumer_exclusive with "Hconsumer_1 Hconsumer_2").
  Qed.

  Lemma mpsc_flag_create_spec P :
    {{{
      True
    }}}
      mpsc_flag_create ()
    {{{
      t
    , RET t;
      mpsc_flag_inv t P ∗
      mpsc_flag_consumer t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    iApply wp_fupd.
    wp_apply (base.mpsc_flag_create_spec with "[//]") as (𝑡 γ) "(Hmeta & Hinv & Hconsumer)".
    iMod (meta_set γ with "Hmeta") as "#Hmeta"; first done.
    iSteps.
  Qed.

  Lemma mpsc_flag_get_spec t P :
    {{{
      mpsc_flag_inv t P ∗
      mpsc_flag_consumer t
    }}}
      mpsc_flag_get t
    {{{
      b
    , RET #b;
      if b then
        P
      else
        mpsc_flag_consumer t
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:consumer =2)) HΦ". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp_apply (base.mpsc_flag_get_spec with "[$]") as (b) "Hb".
    destruct b; iSteps.
  Qed.

  Lemma mpsc_flag_set_spec t P :
    {{{
      mpsc_flag_inv t P ∗
      ▷ P
    }}}
      mpsc_flag_set t
    {{{
      RET ();
      mpsc_flag_resolved t
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & HP) HΦ".

    wp_apply (base.mpsc_flag_set_spec _ _ P with "[$]").
    iSteps.
  Qed.
End mpsc_flag_G.

#[global] Opaque mpsc_flag_inv.
#[global] Opaque mpsc_flag_consumer.
#[global] Opaque mpsc_flag_resolved.
