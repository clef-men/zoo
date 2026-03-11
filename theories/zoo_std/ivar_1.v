From zoo Require Import
  prelude.
From zoo.common Require Import
  countable.
From zoo.iris.base_logic Require Import
  lib.oneshot
  lib.subpreds.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
  base
  ivar_1__code.
From zoo_std Require Import
  option.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types v : val.
Implicit Types o state : option val.

Class Ivar1G Σ `{zoo_G : !ZooG Σ} := {
  #[local] ivar_1_G_lstate_G :: OneshotG Σ unit val ;
  #[local] ivar_1_G_consumer_G :: SubpredsG Σ val ;
}.

Definition ivar_1_Σ := #[
  oneshot_Σ unit val ;
  subpreds_Σ val
].
#[global] Instance subG_ivar_1_Σ Σ `{zoo_G : !ZooG Σ} :
  subG ivar_1_Σ Σ →
  Ivar1G Σ .
Proof.
  solve_inG.
Qed.

Module base.
  Section ivar_1_G.
    Context `{ivar_1_G : Ivar1G Σ}.

    Implicit Types t : location.
    Implicit Types Ψ Χ Ξ : val → iProp Σ.

    Record ivar_1_name := {
      metadata_lstate : gname ;
      metadata_consumer : gname ;
    }.
    Implicit Types γ : ivar_1_name.

    #[global] Instance ivar_1_name_eq_dec : EqDecision ivar_1_name :=
      ltac:(solve_decision).
    #[global] Instance ivar_1_name_countable :
      Countable ivar_1_name.
    Proof.
      solve_countable.
    Qed.

    #[local] Definition lstate_unset₁' γ_lstate :=
      oneshot_pending γ_lstate (DfracOwn (1/3)) ().
    #[local] Definition lstate_unset₁ γ :=
      lstate_unset₁' γ.(metadata_lstate).
    #[local] Definition lstate_unset₂' γ_lstate :=
      oneshot_pending γ_lstate (DfracOwn (2/3)) ().
    #[local] Definition lstate_unset₂ γ :=
      lstate_unset₂' γ.(metadata_lstate).
    #[local] Definition lstate_set' γ_lstate :=
      oneshot_shot γ_lstate.
    #[local] Definition lstate_set γ :=
      lstate_set' γ.(metadata_lstate).

    #[local] Definition consumer_auth' :=
      subpreds_auth.
    #[local] Definition consumer_auth γ :=
      consumer_auth' γ.(metadata_consumer).
    #[local] Definition consumer_frag' :=
      subpreds_frag.
    #[local] Definition consumer_frag γ :=
      consumer_frag' γ.(metadata_consumer).

    #[local] Definition inv_state_unset γ :=
      lstate_unset₁ γ.
    #[local] Instance : CustomIpat "inv_state_unset" :=
      " {>;}Hlstate_unset₁
      ".
    #[local] Definition inv_state_set γ Ξ v : iProp Σ :=
      lstate_set γ v ∗
      □ Ξ v.
    #[local] Instance : CustomIpat "inv_state_set" :=
      " ( {>;}#Hlstate_set{_{}} &
          #HΞ{_{}}
        )
      ".
    #[local] Definition inv_state γ Ξ state :=
      match state with
      | None =>
          inv_state_unset γ
      | Some v =>
          inv_state_set γ Ξ v
      end.

    #[local] Definition inv_inner t γ Ψ Ξ : iProp Σ :=
      ∃ state,
      t ↦ᵣ state ∗
      consumer_auth γ Ψ state ∗
      inv_state γ Ξ state.
    #[local] Instance : CustomIpat "inv_inner" :=
      " ( %state &
          Ht &
          Hconsumer_auth &
          Hstate
        )
      ".
    Definition ivar_1_inv t γ Ψ Ξ : iProp Σ :=
      inv nroot (inv_inner t γ Ψ Ξ).
    #[local] Instance : CustomIpat "inv" :=
      " #Hinv
      ".

    Definition ivar_1_producer :=
      lstate_unset₂.
    #[local] Instance : CustomIpat "producer" :=
      " Hlstate_unset₂{_{}}
      ".

    Definition ivar_1_consumer :=
      consumer_frag.
    #[local] Instance : CustomIpat "consumer" :=
      " Hconsumer{}_frag
      ".

    Definition ivar_1_result :=
      lstate_set.
    #[local] Instance : CustomIpat "result" :=
      " #Hlstate_set{_{}}
      ".
    Definition ivar_1_resolved γ : iProp Σ :=
      ∃ v,
      ivar_1_result γ v.

    #[global] Instance ivar_1_inv_contractive t γ n :
      Proper (
        (pointwise_relation _ (dist_later n)) ==>
        (pointwise_relation _ (dist_later n)) ==>
        (≡{n}≡)
      ) (ivar_1_inv t γ).
    Proof.
      rewrite /ivar_1_inv /inv_inner /inv_state /inv_state_unset /inv_state_set.
      solve_contractive.
    Qed.
    #[global] Instance ivar_1_inv_proper t γ :
      Proper (
        (pointwise_relation _ (≡)) ==>
        (pointwise_relation _ (≡)) ==>
        (≡)
      ) (ivar_1_inv t γ).
    Proof.
      rewrite /ivar_1_inv /inv_inner /inv_state /inv_state_unset /inv_state_set.
      solve_proper.
    Qed.
    #[global] Instance ivar_1_consumer_contractive γ n :
      Proper (
        (pointwise_relation _ (dist_later n)) ==>
        (≡{n}≡)
      ) (ivar_1_consumer γ).
    Proof.
      apply _.
    Qed.
    #[global] Instance ivar_1_consumer_proper γ :
      Proper (
        (pointwise_relation _ (≡)) ==>
        (≡)
      ) (ivar_1_consumer γ).
    Proof.
      apply _.
    Qed.

    #[global] Instance ivar_1_producer_timeless γ :
      Timeless (ivar_1_producer γ).
    Proof.
      apply _.
    Qed.
    #[global] Instance ivar_1_result_timeless γ v :
      Timeless (ivar_1_result γ v).
    Proof.
      apply _.
    Qed.

    #[global] Instance ivar_1_inv_persistent t γ Ψ Ξ :
      Persistent (ivar_1_inv t γ Ψ Ξ).
    Proof.
      apply _.
    Qed.
    #[global] Instance ivar_1_result_persistent γ v :
      Persistent (ivar_1_result γ v).
    Proof.
      apply _.
    Qed.

    #[local] Lemma lstate_alloc :
      ⊢ |==>
        ∃ γ_lstate,
        lstate_unset₁' γ_lstate ∗
        lstate_unset₂' γ_lstate.
    Proof.
      iMod oneshot_alloc as "(%γ_lstate & Hpending)".
      assert (1 = 1/3 + 2/3)%Qp as -> by compute_done.
      iDestruct "Hpending" as "(Hpending₁ & Hpending₂)".
      iSteps.
    Qed.
    #[local] Lemma lstate_unset₂_exclusive γ :
      lstate_unset₂ γ -∗
      lstate_unset₂ γ -∗
      False.
    Proof.
      iIntros "Hunset1 Hunset2".
      iDestruct (oneshot_pending_valid_2 with "Hunset1 Hunset2") as %(? & _). done.
    Qed.
    #[local] Lemma lstate_set_agree γ v1 v2 :
      lstate_set γ v1 -∗
      lstate_set γ v2 -∗
      ⌜v1 = v2⌝.
    Proof.
      apply oneshot_shot_agree.
    Qed.
    #[local] Lemma lstate_unset₁_set γ v :
      lstate_unset₁ γ -∗
      lstate_set γ v -∗
      False.
    Proof.
      apply oneshot_pending_shot.
    Qed.
    #[local] Lemma lstate_unset₂_set γ v :
      lstate_unset₂ γ -∗
      lstate_set γ v -∗
      False.
    Proof.
      apply oneshot_pending_shot.
    Qed.
    #[local] Lemma lstate_update {γ} v :
      lstate_unset₁ γ -∗
      lstate_unset₂ γ ==∗
      lstate_set γ v.
    Proof.
      iIntros "Hpending₁ Hpending₂".
      iCombine "Hpending₁ Hpending₂" as "Hpending".
      assert (1/3 + 2/3 = 1)%Qp as -> by compute_done.
      iApply (oneshot_update_shot with "Hpending").
    Qed.

    #[local] Lemma consumer_alloc Ψ :
      ⊢ |==>
        ∃ γ_consumer,
        consumer_auth' γ_consumer Ψ None ∗
        consumer_frag' γ_consumer Ψ.
    Proof.
      apply subpreds_alloc.
    Qed.
    #[local] Lemma consumer_wand {γ Ψ state Χ1} Χ2 E :
      ▷ consumer_auth γ Ψ state -∗
      consumer_frag γ Χ1 -∗
      (∀ v, Χ1 v -∗ Χ2 v) ={E}=∗
        ▷ consumer_auth γ Ψ state ∗
        consumer_frag γ Χ2.
    Proof.
      apply subpreds_wand.
    Qed.
    #[local] Lemma consumer_divide {γ Ψ state} Χs E :
      ▷ consumer_auth γ Ψ state -∗
      consumer_frag γ (λ v, [∗ list] Χ ∈ Χs, Χ v) ={E}=∗
        ▷ consumer_auth γ Ψ state ∗
        [∗ list] Χ ∈ Χs, consumer_frag γ Χ.
    Proof.
      apply subpreds_divide.
    Qed.
    #[local] Lemma consumer_produce {γ Ψ} v :
      consumer_auth γ Ψ None -∗
      Ψ v -∗
      consumer_auth γ Ψ (Some v).
    Proof.
      apply subpreds_produce.
    Qed.
    #[local] Lemma consumer_consume γ Ψ v Χ E :
      ▷ consumer_auth γ Ψ (Some v) -∗
      consumer_frag γ Χ ={E}=∗
        ▷ consumer_auth γ Ψ (Some v) ∗
        ▷^2 Χ v.
    Proof.
      apply subpreds_consume.
    Qed.

    Lemma ivar_1_producer_exclusive γ :
      ivar_1_producer γ -∗
      ivar_1_producer γ -∗
      False.
    Proof.
      apply lstate_unset₂_exclusive.
    Qed.

    Lemma ivar_1_consumer_wand {t γ Ψ Ξ Χ1} Χ2 :
      ivar_1_inv t γ Ψ Ξ -∗
      ivar_1_consumer γ Χ1 -∗
      (∀ v, Χ1 v -∗ Χ2 v) ={⊤}=∗
      ivar_1_consumer γ Χ2.
    Proof.
      iIntros "(:inv) (:consumer) H".
      iInv "Hinv" as "(:inv_inner)".
      iMod (consumer_wand with "Hconsumer_auth Hconsumer_frag H") as "($ & $)".
      iFrameSteps.
    Qed.
    Lemma ivar_1_consumer_divide {t γ Ψ Ξ} Χs :
      ivar_1_inv t γ Ψ Ξ -∗
      ivar_1_consumer γ (λ v, [∗ list] Χ ∈ Χs, Χ v) ={⊤}=∗
      [∗ list] Χ ∈ Χs, ivar_1_consumer γ Χ.
    Proof.
      iIntros "(:inv) (:consumer)".
      iInv "Hinv" as "(:inv_inner)".
      iMod (consumer_divide with "Hconsumer_auth Hconsumer_frag") as "($ & $)".
      iFrameSteps.
    Qed.

    Lemma ivar_1_result_agree γ v1 v2 :
      ivar_1_result γ v1 -∗
      ivar_1_result γ v2 -∗
      ⌜v1 = v2⌝.
    Proof.
      apply lstate_set_agree.
    Qed.

    Lemma ivar_1_producer_result γ v :
      ivar_1_producer γ -∗
      ivar_1_result γ v -∗
      False.
    Proof.
      apply lstate_unset₂_set.
    Qed.

    Lemma ivar_1_inv_result t γ Ψ Ξ v :
      ivar_1_inv t γ Ψ Ξ -∗
      ivar_1_result γ v ={⊤}=∗
      ▷ □ Ξ v.
    Proof.
      iIntros "(:inv) (:result)".
      iInv "Hinv" as "(:inv_inner)".
      destruct state as [v_ |]; last first.
      { iDestruct "Hstate" as "(:inv_state_unset >)".
        iDestruct (lstate_unset₁_set with "Hlstate_unset₁ Hlstate_set") as %[].
      }
      iDestruct "Hstate" as "(:inv_state_set =1 >)".
      iDestruct (lstate_set_agree with "Hlstate_set Hlstate_set_1") as %<-.
      iSplitL. { iFrameSteps. }
      iSteps.
    Qed.
    Lemma ivar_1_inv_result_consumer t γ Ψ Ξ v Χ :
      ivar_1_inv t γ Ψ Ξ -∗
      ivar_1_result γ v -∗
      ivar_1_consumer γ Χ ={⊤}=∗
        ▷^2 Χ v ∗
        ▷ □ Ξ v.
    Proof.
      iIntros "(:inv) (:result) (:consumer)".
      iInv "Hinv" as "(:inv_inner)".
      destruct state as [v_ |]; last first.
      { iDestruct "Hstate" as "(:inv_state_unset >)".
        iDestruct (lstate_unset₁_set with "Hlstate_unset₁ Hlstate_set") as %[].
      }
      iDestruct "Hstate" as "(:inv_state_set =1 >)".
      iDestruct (lstate_set_agree with "Hlstate_set Hlstate_set_1") as %<-.
      iMod (consumer_consume with "Hconsumer_auth Hconsumer_frag") as "(Hconsumer_auth & HΧ)".
      iSplitR "HΧ". { iFrameSteps. }
      iSteps.
    Qed.

    Lemma ivar_1_create_spec Ψ Ξ :
      {{{
        True
      }}}
        ivar_1_create ()
      {{{ t γ,
        RET #t;
        meta_token t ⊤ ∗
        ivar_1_inv t γ Ψ Ξ ∗
        ivar_1_producer γ ∗
        ivar_1_consumer γ Ψ
      }}}.
    Proof.
      iIntros "%Φ _ HΦ".

      wp_rec.
      wp_ref t as "Hmeta" "Ht".

      iMod lstate_alloc as "(%γ_lstate & Hlstate_unset₁ & Hlstate_unset₂)".
      iMod consumer_alloc as "(%γ_consumer & Hconsumer_auth & Hconsumer_frag)".

      pose γ := {|
        metadata_lstate := γ_lstate ;
        metadata_consumer := γ_consumer ;
      |}.

      iApply ("HΦ" $! t γ).
      iFrameSteps. iExists None. iSteps.
    Qed.

    Lemma ivar_1_make_spec Ψ Ξ v :
      {{{
        ▷ Ψ v ∗
        ▷ □ Ξ v
      }}}
        ivar_1_make v
      {{{ t γ,
        RET #t;
        meta_token t ⊤ ∗
        ivar_1_inv t γ Ψ Ξ ∗
        ivar_1_result γ v ∗
        ivar_1_consumer γ Ψ
      }}}.
    Proof.
      iIntros "%Φ (HΨ & #HΞ) HΦ".

      wp_rec.
      wp_ref t as "Hmeta" "Ht".

      iMod lstate_alloc as "(%γ_lstate & Hlstate_unset₁ & Hlstate_unset₂)".
      iMod consumer_alloc as "(%γ_consumer & Hconsumer_auth & Hconsumer_frag)".

      pose γ := {|
        metadata_lstate := γ_lstate ;
        metadata_consumer := γ_consumer ;
      |}.

      iMod (lstate_update (γ := γ) v with "Hlstate_unset₁ Hlstate_unset₂") as "#Hlstate_set".
      iDestruct (consumer_produce (γ := γ) v with "Hconsumer_auth HΨ") as "Hconsumer_auth".

      iApply ("HΦ" $! t γ).
      iFrameSteps. iExists (Some v). iSteps.
    Qed.

    Lemma ivar_1_try_get_spec t γ Ψ Ξ :
      {{{
        ivar_1_inv t γ Ψ Ξ
      }}}
        ivar_1_try_get #t
      {{{ o,
        RET o;
        if o is Some v then
          £ 2 ∗
          ivar_1_result γ v
        else
          True
      }}}.
    Proof.
      iIntros "%Φ (:inv) HΦ".

      wp_rec credits:"H£".
      iApply (lc_weaken 2) in "H£"; first done.

      iInv "Hinv" as "(:inv_inner)".
      wp_load.
      iSpecialize ("HΦ" $! state).
      destruct state as [v |].

      - iDestruct "Hstate" as "(:inv_state_set)".
        iSplitR "H£ HΦ". { iFrameSteps. }
        iSteps.

      - iSplitR "HΦ". { iFrameSteps. }
        iSteps.
    Qed.
    Lemma ivar_1_try_get_spec_result t γ Ψ Ξ v :
      {{{
        ivar_1_inv t γ Ψ Ξ ∗
        ivar_1_result γ v
      }}}
        ivar_1_try_get #t
      {{{
        RET Some v;
        £ 2
      }}}.
    Proof.
      iIntros "%Φ ((:inv) & (:result)) HΦ".

      wp_rec credits:"H£".
      iApply (lc_weaken 2) in "H£"; first done.

      iInv "Hinv" as "(:inv_inner)".
      wp_load.
      destruct state as [v_ |]; last first.
      { iDestruct (lstate_unset₁_set with "Hstate Hlstate_set") as %[]. }
      iDestruct "Hstate" as "(:inv_state_set =1)".
      iDestruct (lstate_set_agree with "Hlstate_set Hlstate_set_1") as %<-. iClear "Hlstate_set_1".
      iSplitR "H£ HΦ". { iFrameSteps. }
      iSteps.
    Qed.

    Lemma ivar_1_is_unset_spec t γ Ψ Ξ :
      {{{
        ivar_1_inv t γ Ψ Ξ
      }}}
        ivar_1_is_unset #t
      {{{ b,
        RET #b;
        if b then
          True
        else
          £ 2 ∗
          ivar_1_resolved γ
      }}}.
    Proof.
      iIntros "%Φ #Hinv HΦ".

      wp_rec.
      wp_apply (ivar_1_try_get_spec with "Hinv") as ([v |]) "H".
      all: iSteps.
    Qed.
    Lemma ivar_1_is_unset_spec_result t γ Ψ Ξ v :
      {{{
        ivar_1_inv t γ Ψ Ξ ∗
        ivar_1_result γ v
      }}}
        ivar_1_is_unset #t
      {{{
        RET false;
        £ 2
      }}}.
    Proof.
      iIntros "%Φ (#Hinv & #Hresult) HΦ".

      wp_rec.
      wp_apply (ivar_1_try_get_spec_result with "[$Hinv $Hresult]").
      iSteps.
    Qed.

    Lemma ivar_1_is_set_spec t γ Ψ Ξ :
      {{{
        ivar_1_inv t γ Ψ Ξ
      }}}
        ivar_1_is_set #t
      {{{ b,
        RET #b;
        if b then
          £ 2 ∗
          ivar_1_resolved γ
        else
          True
      }}}.
    Proof.
      iIntros "%Φ #Hinv HΦ".

      wp_rec.
      wp_apply (ivar_1_is_unset_spec with "[$]") as (b) "Hb".
      destruct b; iSteps.
    Qed.
    Lemma ivar_1_is_set_spec_result t γ Ψ Ξ v :
      {{{
        ivar_1_inv t γ Ψ Ξ ∗
        ivar_1_result γ v
      }}}
        ivar_1_is_set #t
      {{{
        RET true;
        £ 2
      }}}.
    Proof.
      iIntros "%Φ (#Hinv & #Hresult) HΦ".

      wp_rec.
      wp_apply (ivar_1_is_unset_spec_result with "[$]").
      iSteps.
    Qed.

    Lemma ivar_1_get_spec t γ Ψ Ξ v :
      {{{
        ivar_1_inv t γ Ψ Ξ ∗
        ivar_1_result γ v
      }}}
        ivar_1_get #t
      {{{
        RET v;
        £ 2
      }}}.
    Proof.
      iIntros "%Φ (#Hinv & Hresult) HΦ".

      wp_rec.
      wp_apply (ivar_1_try_get_spec_result with "[$Hinv $Hresult]").
      iSteps.
    Qed.

    Lemma ivar_1_set_spec t γ Ψ Ξ v :
      {{{
        ivar_1_inv t γ Ψ Ξ ∗
        ivar_1_producer γ ∗
        ▷ Ψ v ∗
        ▷ □ Ξ v
      }}}
        ivar_1_set #t v
      {{{
        RET ();
        ivar_1_result γ v
      }}}.
    Proof.
      iIntros "%Φ ((:inv) & (:producer) & HΨ & #HΞ) HΦ".

      wp_rec. wp_pures.

      iInv "Hinv" as "(:inv_inner)".
      wp_store.
      destruct state.
      { iDestruct "Hstate" as "(:inv_state_set =1)".
        iDestruct (lstate_unset₂_set with "Hlstate_unset₂ Hlstate_set_1") as %[].
      }
      iMod (lstate_update with "Hstate Hlstate_unset₂") as "#Hlstate_set".
      iDestruct (consumer_produce with "Hconsumer_auth HΨ") as "Hconsumer_auth".
      iSplitR "HΦ". { iFrameSteps. }
      iSteps.
    Qed.
  End ivar_1_G.

  #[global] Opaque ivar_1_inv.
  #[global] Opaque ivar_1_producer.
  #[global] Opaque ivar_1_consumer.
  #[global] Opaque ivar_1_result.
End base.

From zoo_std Require
  ivar_1__opaque.

Section ivar_1_G.
  Context `{ivar_1_G : Ivar1G Σ}.

  Implicit Types 𝑡 : location.
  Implicit Types t : val.
  Implicit Types γ : base.ivar_1_name.
  Implicit Types Ψ Χ Ξ : val → iProp Σ.

  Definition ivar_1_inv t Ψ Ξ : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.ivar_1_inv 𝑡 γ Ψ Ξ.
  #[local] Instance : CustomIpat "inv" :=
    " ( %l{} &
        %γ{} &
        {%Heq{};->} &
        #Hmeta{_{}} &
        Hinv{_{}}
      )
    ".

  Definition ivar_1_producer t : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.ivar_1_producer γ.
  #[local] Instance : CustomIpat "producer" :=
    " ( %l{;_} &
        %γ{;_} &
        {%Heq{};->} &
        #Hmeta{_{}} &
        Hproducer{_{}}
      )
    ".

  Definition ivar_1_consumer t Χ : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.ivar_1_consumer γ Χ.
  #[local] Instance : CustomIpat "consumer" :=
    " ( %l{;_} &
        %γ{;_} &
        {%Heq{};->} &
        #Hmeta{_{}} &
        Hconsumer{_{}}
      )
    ".

  Definition ivar_1_result t v : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.ivar_1_result γ v.
  #[local] Instance : CustomIpat "result" :=
    " ( %l{;_} &
        %γ{;_} &
        {%Heq{};->} &
        #Hmeta{_{}} &
        Hresult{_{}}
      )
    ".
  Definition ivar_1_resolved t : iProp Σ :=
    ∃ v,
    ivar_1_result t v.

  #[global] Instance ivar_1_inv_contractive t n :
    Proper (
      (pointwise_relation _ (dist_later n)) ==>
      (pointwise_relation _ (dist_later n)) ==>
      (≡{n}≡)
    ) (ivar_1_inv t).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance ivar_1_inv_proper t :
    Proper (
      (pointwise_relation _ (≡)) ==>
      (pointwise_relation _ (≡)) ==>
      (≡)
    ) (ivar_1_inv t).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance ivar_1_consumer_contractive t n :
    Proper (
      (pointwise_relation _ (dist_later n)) ==>
      (≡{n}≡)
    ) (ivar_1_consumer t).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance ivar_1_consumer_proper t :
    Proper (
      (pointwise_relation _ (≡)) ==>
      (≡)
    ) (ivar_1_consumer t).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance ivar_1_producer_timeless t :
    Timeless (ivar_1_producer t).
  Proof.
    apply _.
  Qed.
  #[global] Instance ivar_1_result_timeless t v :
    Timeless (ivar_1_result t v).
  Proof.
    apply _.
  Qed.

  #[global] Instance ivar_1_inv_persistent t Ψ Ξ :
    Persistent (ivar_1_inv t Ψ Ξ).
  Proof.
    apply _.
  Qed.
  #[global] Instance ivar_1_result_persistent t v :
    Persistent (ivar_1_result t v).
  Proof.
    apply _.
  Qed.

  Lemma ivar_1_producer_exclusive t :
    ivar_1_producer t -∗
    ivar_1_producer t -∗
    False.
  Proof.
    iIntros "(:producer =1) (:producer =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.ivar_1_producer_exclusive with "Hproducer_1 Hproducer_2").
  Qed.

  Lemma ivar_1_consumer_wand {t Ψ Ξ Χ1} Χ2 :
    ivar_1_inv t Ψ Ξ -∗
    ivar_1_consumer t Χ1 -∗
    (∀ v, Χ1 v -∗ Χ2 v) ={⊤}=∗
    ivar_1_consumer t Χ2.
  Proof.
    iIntros "(:inv =1) (:consumer =2) H". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iDestruct (base.ivar_1_consumer_wand with "Hinv_1 Hconsumer_2 H") as "H".
    iSteps.
  Qed.
  Lemma ivar_1_consumer_divide {t Ψ Ξ} Χs :
    ivar_1_inv t Ψ Ξ -∗
    ivar_1_consumer t (λ v, [∗ list] Χ ∈ Χs, Χ v) ={⊤}=∗
    [∗ list] Χ ∈ Χs, ivar_1_consumer t Χ.
  Proof.
    iIntros "(:inv =1) (:consumer =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iDestruct (base.ivar_1_consumer_divide with "Hinv_1 Hconsumer_2") as "H".
    iApply (big_sepL_impl with "H").
    iSteps.
  Qed.
  Lemma ivar_1_consumer_split {t Ψ Ξ} Χ1 Χ2 :
    ivar_1_inv t Ψ Ξ -∗
    ivar_1_consumer t (λ v, Χ1 v ∗ Χ2 v) ={⊤}=∗
      ivar_1_consumer t Χ1 ∗
      ivar_1_consumer t Χ2.
  Proof.
    iIntros "Hinv Hconsumer".
    iMod (ivar_1_consumer_divide [Χ1;Χ2] with "Hinv [Hconsumer]") as "($ & $ & _)" => //.
    { simpl. setoid_rewrite bi.sep_emp => //. }
  Qed.

  Lemma ivar_1_result_agree t v1 v2 :
    ivar_1_result t v1 -∗
    ivar_1_result t v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    iIntros "(:result =1) (:result =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.ivar_1_result_agree with "Hresult_1 Hresult_2").
  Qed.

  Lemma ivar_1_producer_result t v :
    ivar_1_producer t -∗
    ivar_1_result t v -∗
    False.
  Proof.
    iIntros "(:producer =1) (:result =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.ivar_1_producer_result with "Hproducer_1 Hresult_2").
  Qed.

  Lemma ivar_1_inv_result t Ψ Ξ v :
    ivar_1_inv t Ψ Ξ -∗
    ivar_1_result t v ={⊤}=∗
    ▷ □ Ξ v.
  Proof.
    iIntros "(:inv =1) (:result =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.ivar_1_inv_result with "Hinv_1 Hresult_2").
  Qed.
  Lemma ivar_1_inv_result' t Ψ Ξ v :
    £ 1 -∗
    ivar_1_inv t Ψ Ξ -∗
    ivar_1_result t v ={⊤}=∗
    □ Ξ v.
  Proof.
    iIntros "H£ Hinv Hresult".
    iMod (ivar_1_inv_result with "Hinv Hresult") as "HΞ".
    iApply (lc_fupd_elim_later with "H£ HΞ").
  Qed.
  Lemma ivar_1_inv_result_consumer t Ψ Ξ v Χ :
    ivar_1_inv t Ψ Ξ -∗
    ivar_1_result t v -∗
    ivar_1_consumer t Χ ={⊤}=∗
      ▷^2 Χ v ∗
      ▷ □ Ξ v.
  Proof.
    iIntros "(:inv =1) (:result =2) (:consumer =3)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iDestruct (meta_agree with "Hmeta_2 Hmeta_3") as %<-.
    iApply (base.ivar_1_inv_result_consumer with "Hinv_1 Hresult_2 Hconsumer_3").
  Qed.
  Lemma ivar_1_inv_result_consumer' t Ψ Ξ v Χ :
    £ 2 -∗
    ivar_1_inv t Ψ Ξ -∗
    ivar_1_result t v -∗
    ivar_1_consumer t Χ ={⊤}=∗
      Χ v ∗
      □ Ξ v.
  Proof.
    iIntros "(H£1 & H£2) Hinv Hresult Hconsumer".
    iMod (ivar_1_inv_result_consumer with "Hinv Hresult Hconsumer") as "H".
    rewrite -bi.later_sep.
    iMod (lc_fupd_elim_later with "H£1 H") as "(HΧ & $)".
    iApply (lc_fupd_elim_later with "H£2 HΧ").
  Qed.

  Lemma ivar_1_create_spec Ψ Ξ :
    {{{
      True
    }}}
      ivar_1_create ()
    {{{ t,
      RET t;
      ivar_1_inv t Ψ Ξ ∗
      ivar_1_producer t ∗
      ivar_1_consumer t Ψ
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    iApply wp_fupd.
    wp_apply (base.ivar_1_create_spec with "[//]") as (𝑡 γ) "(Hmeta & Hinv & Hproducer & Hconsumer)".
    iMod (meta_set γ with "Hmeta") as "#Hmeta"; first done.
    iSteps.
  Qed.

  Lemma ivar_1_make_spec Ψ Ξ v :
    {{{
      ▷ Ψ v ∗
      ▷ □ Ξ v
    }}}
      ivar_1_make v
    {{{ t,
      RET t;
      ivar_1_inv t Ψ Ξ ∗
      ivar_1_result t v ∗
      ivar_1_consumer t Ψ
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #HΞ) HΦ".

    iApply wp_fupd.
    wp_apply (base.ivar_1_make_spec Ψ with "[$]") as (𝑡 γ) "(Hmeta & Hinv & Hproducer & Hconsumer)".
    iMod (meta_set γ with "Hmeta") as "#Hmeta"; first done.
    iSteps.
  Qed.

  Lemma ivar_1_try_get_spec t Ψ Ξ :
    {{{
      ivar_1_inv t Ψ Ξ
    }}}
      ivar_1_try_get t
    {{{ o,
      RET o;
      if o is Some v then
        £ 2 ∗
        ivar_1_result t v
      else
        True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_apply (base.ivar_1_try_get_spec with "[$]") as (o) "Ho".
    iSpecialize ("HΦ" $! o).
    destruct o; iSteps.
  Qed.
  Lemma ivar_1_try_get_spec_result t Ψ Ξ v :
    {{{
      ivar_1_inv t Ψ Ξ ∗
      ivar_1_result t v
    }}}
      ivar_1_try_get t
    {{{
      RET Some v;
      £ 2
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:result =2)) HΦ". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp_apply (base.ivar_1_try_get_spec_result with "[$] HΦ").
  Qed.

  Lemma ivar_1_is_unset_spec t Ψ Ξ :
    {{{
      ivar_1_inv t Ψ Ξ
    }}}
      ivar_1_is_unset t
    {{{ b,
      RET #b;
      if b then
        True
      else
        £ 2 ∗
        ivar_1_resolved t
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_apply (base.ivar_1_is_unset_spec with "[$]") as (b) "Hb".
    rewrite /ivar_1_resolved. destruct b; iSteps.
  Qed.
  Lemma ivar_1_is_unset_spec_result t Ψ Ξ v :
    {{{
      ivar_1_inv t Ψ Ξ ∗
      ivar_1_result t v
    }}}
      ivar_1_is_unset t
    {{{
      RET false;
      £ 2
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:result =2)) HΦ". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp_apply (base.ivar_1_is_unset_spec_result with "[$] HΦ").
  Qed.

  Lemma ivar_1_is_set_spec t Ψ Ξ :
    {{{
      ivar_1_inv t Ψ Ξ
    }}}
      ivar_1_is_set t
    {{{ b,
      RET #b;
      if b then
        £ 2 ∗
        ivar_1_resolved t
      else
        True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_apply (base.ivar_1_is_set_spec with "[$]") as (b) "Hb".
    rewrite /ivar_1_resolved. destruct b; iSteps.
  Qed.
  Lemma ivar_1_is_set_spec_result t Ψ Ξ v :
    {{{
      ivar_1_inv t Ψ Ξ ∗
      ivar_1_result t v
    }}}
      ivar_1_is_set t
    {{{
      RET true;
      £ 2
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:result =2)) HΦ". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp_apply (base.ivar_1_is_set_spec_result with "[$] HΦ").
  Qed.

  Lemma ivar_1_get_spec t Ψ Ξ v :
    {{{
      ivar_1_inv t Ψ Ξ ∗
      ivar_1_result t v
    }}}
      ivar_1_get t
    {{{
      RET v;
      £ 2
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:result =2)) HΦ". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp_apply (base.ivar_1_get_spec with "[$] HΦ").
  Qed.

  Lemma ivar_1_set_spec t Ψ Ξ v :
    {{{
      ivar_1_inv t Ψ Ξ ∗
      ivar_1_producer t ∗
      ▷ Ψ v ∗
      ▷ □ Ξ v
    }}}
      ivar_1_set t v
    {{{
      RET ();
      ivar_1_result t v
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:producer =2) & HΨ & HΞ) HΦ". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp_apply (base.ivar_1_set_spec _ _ Ψ with "[$]").
    iSteps.
  Qed.
End ivar_1_G.

#[global] Opaque ivar_1_inv.
#[global] Opaque ivar_1_producer.
#[global] Opaque ivar_1_consumer.
#[global] Opaque ivar_1_result.
