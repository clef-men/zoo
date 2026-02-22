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
  ivar_2__code.
From zoo_std Require Import
  ivar_2__types
  option
  condition.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types v : val.
Implicit Types o state : option val.

Class Ivar2G Σ `{zoo_G : !ZooG Σ} := {
  #[local] ivar_2_G_mutex_G :: MutexG Σ ;
  #[local] ivar_2_G_lstate_G :: OneshotG Σ unit val ;
  #[local] ivar_2_G_consumer_G :: SubpredsG Σ val ;
}.

Definition ivar_2_Σ := #[
  mutex_Σ ;
  oneshot_Σ unit val ;
  subpreds_Σ val
].
#[global] Instance subG_ivar_2_Σ Σ `{zoo_G : !ZooG Σ} :
  subG ivar_2_Σ Σ →
  Ivar2G Σ .
Proof.
  solve_inG.
Qed.

Module base.
  Section ivar_2_G.
    Context `{ivar_2_G : Ivar2G Σ}.

    Implicit Types t : location.
    Implicit Types Ψ Χ Ξ : val → iProp Σ.

    Record ivar_2_name := {
      ivar_2_name_mutex : val ;
      ivar_2_name_condition : val ;
      ivar_2_name_lstate : gname ;
      ivar_2_name_consumer : gname ;
    }.
    Implicit Types γ : ivar_2_name.

    #[global] Instance ivar_2_name_eq_dec : EqDecision ivar_2_name :=
      ltac:(solve_decision).
    #[global] Instance ivar_2_name_countable :
      Countable ivar_2_name.
    Proof.
      solve_countable.
    Qed.

    #[local] Definition lstate_unset₁' γ_lstate :=
      oneshot_pending γ_lstate (DfracOwn (1/3)) ().
    #[local] Definition lstate_unset₁ γ :=
      lstate_unset₁' γ.(ivar_2_name_lstate).
    #[local] Definition lstate_unset₂' γ_lstate :=
      oneshot_pending γ_lstate (DfracOwn (2/3)) ().
    #[local] Definition lstate_unset₂ γ :=
      lstate_unset₂' γ.(ivar_2_name_lstate).
    #[local] Definition lstate_set γ :=
      oneshot_shot γ.(ivar_2_name_lstate).

    #[local] Definition consumer_auth' :=
      subpreds_auth.
    #[local] Definition consumer_auth γ :=
      consumer_auth' γ.(ivar_2_name_consumer).
    #[local] Definition consumer_frag' :=
      subpreds_frag.
    #[local] Definition consumer_frag γ :=
      consumer_frag' γ.(ivar_2_name_consumer).

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
      t.[result] ↦ state ∗
      consumer_auth γ Ψ state ∗
      inv_state γ Ξ state.
    #[local] Instance : CustomIpat "inv_inner" :=
      " ( %state &
          H𝑡_result &
          Hconsumer_auth &
          Hstate
        )
      ".
    Definition ivar_2_inv t γ Ψ Ξ : iProp Σ :=
      t.[mutex] ↦□ γ.(ivar_2_name_mutex) ∗
      mutex_inv γ.(ivar_2_name_mutex) True ∗
      t.[condition] ↦□ γ.(ivar_2_name_condition) ∗
      condition_inv γ.(ivar_2_name_condition) ∗
      inv nroot (inv_inner t γ Ψ Ξ).
    #[local] Instance : CustomIpat "inv" :=
      " ( #Ht_mutex &
          #Hmutex_inv &
          #Ht_condition &
          #Hcondition_inv &
          #Hinv
        )
      ".

    Definition ivar_2_producer :=
      lstate_unset₂.
    #[local] Instance : CustomIpat "producer" :=
      " Hlstate_unset₂{_{}}
      ".

    Definition ivar_2_consumer :=
      consumer_frag.
    #[local] Instance : CustomIpat "consumer" :=
      " Hconsumer{}_frag
      ".

    Definition ivar_2_result :=
      lstate_set.
    #[local] Instance : CustomIpat "result" :=
      " #Hlstate_set{_{}}
      ".
    Definition ivar_2_resolved γ : iProp Σ :=
      ∃ v,
      ivar_2_result γ v.

    Definition ivar_2_synchronized γ : iProp Σ :=
      True.

    #[global] Instance ivar_2_inv_contractive t γ n :
      Proper (
        (pointwise_relation _ (dist_later n)) ==>
        (pointwise_relation _ (dist_later n)) ==>
        (≡{n}≡)
      ) (ivar_2_inv t γ).
    Proof.
      rewrite /ivar_2_inv /inv_inner /inv_state /inv_state_unset /inv_state_set.
      solve_contractive.
    Qed.
    #[global] Instance ivar_2_inv_proper t γ :
      Proper (
        (pointwise_relation _ (≡)) ==>
        (pointwise_relation _ (≡)) ==>
        (≡)
      ) (ivar_2_inv t γ).
    Proof.
      rewrite /ivar_2_inv /inv_inner /inv_state /inv_state_unset /inv_state_set.
      solve_proper.
    Qed.
    #[global] Instance ivar_2_consumer_contractive γ n :
      Proper (
        (pointwise_relation _ (dist_later n)) ==>
        (≡{n}≡)
      ) (ivar_2_consumer γ).
    Proof.
      apply _.
    Qed.
    #[global] Instance ivar_2_consumer_proper γ :
      Proper (
        (pointwise_relation _ (≡)) ==>
        (≡)
      ) (ivar_2_consumer γ).
    Proof.
      apply _.
    Qed.

    #[global] Instance ivar_2_producer_timeless γ :
      Timeless (ivar_2_producer γ).
    Proof.
      apply _.
    Qed.
    #[global] Instance ivar_2_result_timeless γ v :
      Timeless (ivar_2_result γ v).
    Proof.
      apply _.
    Qed.
    #[global] Instance ivar_2_synchronized_timeless γ :
      Timeless (ivar_2_synchronized γ).
    Proof.
      apply _.
    Qed.

    #[global] Instance ivar_2_inv_persistent t γ Ψ Ξ :
      Persistent (ivar_2_inv t γ Ψ Ξ).
    Proof.
      apply _.
    Qed.
    #[global] Instance ivar_2_result_persistent γ v :
      Persistent (ivar_2_result γ v).
    Proof.
      apply _.
    Qed.
    #[global] Instance ivar_2_synchronized_persistent γ :
      Persistent (ivar_2_synchronized γ).
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
      iDestruct "Hpending" as "(Hunset₁ & Hpending₂)".
      iSteps.
    Qed.
    #[local] Lemma lstate_unset₂_exclusive γ :
      lstate_unset₂ γ -∗
      lstate_unset₂ γ -∗
      False.
    Proof.
      iIntros "Hpending1 Hpending2".
      iDestruct (oneshot_pending_valid_2 with "Hpending1 Hpending2") as %(? & _). done.
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

    Lemma ivar_2_producer_exclusive γ :
      ivar_2_producer γ -∗
      ivar_2_producer γ -∗
      False.
    Proof.
      apply lstate_unset₂_exclusive.
    Qed.

    Lemma ivar_2_consumer_wand {t γ Ψ Ξ Χ1} Χ2 :
      ivar_2_inv t γ Ψ Ξ -∗
      ivar_2_consumer γ Χ1 -∗
      (∀ v, Χ1 v -∗ Χ2 v) ={⊤}=∗
      ivar_2_consumer γ Χ2.
    Proof.
      iIntros "(:inv) (:consumer) H".
      iInv "Hinv" as "(:inv_inner)".
      iMod (consumer_wand with "Hconsumer_auth Hconsumer_frag H") as "($ & $)".
      iFrameSteps.
    Qed.
    Lemma ivar_2_consumer_divide {t γ Ψ Ξ} Χs :
      ivar_2_inv t γ Ψ Ξ -∗
      ivar_2_consumer γ (λ v, [∗ list] Χ ∈ Χs, Χ v) ={⊤}=∗
      [∗ list] Χ ∈ Χs, ivar_2_consumer γ Χ.
    Proof.
      iIntros "(:inv) (:consumer)".
      iInv "Hinv" as "(:inv_inner)".
      iMod (consumer_divide with "Hconsumer_auth Hconsumer_frag") as "($ & $)".
      iFrameSteps.
    Qed.

    Lemma ivar_2_result_agree γ v1 v2 :
      ivar_2_result γ v1 -∗
      ivar_2_result γ v2 -∗
      ⌜v1 = v2⌝.
    Proof.
      apply lstate_set_agree.
    Qed.

    Lemma ivar_2_producer_result γ v :
      ivar_2_producer γ -∗
      ivar_2_result γ v -∗
      False.
    Proof.
      apply lstate_unset₂_set.
    Qed.

    Lemma ivar_2_inv_result t γ Ψ Ξ v :
      ivar_2_inv t γ Ψ Ξ -∗
      ivar_2_result γ v -∗
      ivar_2_synchronized γ ={⊤}=∗
      ▷ □ Ξ v.
    Proof.
      iIntros "(:inv) (:result) _".
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
    Lemma ivar_2_inv_result_consumer t γ Ψ Ξ v Χ :
      ivar_2_inv t γ Ψ Ξ -∗
      ivar_2_result γ v -∗
      ivar_2_synchronized γ -∗
      ivar_2_consumer γ Χ ={⊤}=∗
        ▷^2 Χ v ∗
        ▷ □ Ξ v.
    Proof.
      iIntros "(:inv) (:result) _ (:consumer)".
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

    Lemma ivar_2_create_spec Ψ Ξ :
      {{{
        True
      }}}
        ivar_2_create ()
      {{{ t γ,
        RET #t;
        meta_token t ⊤ ∗
        ivar_2_inv t γ Ψ Ξ ∗
        ivar_2_producer γ ∗
        ivar_2_consumer γ Ψ
      }}}.
    Proof.
      iIntros "%Φ _ HΦ".

      wp_rec.
      wp_smart_apply (condition_create_spec _ with "[//]") as "%cond #Hcondition_inv".
      wp_smart_apply (mutex_create_spec True with "[//]") as "%mtx #Hmutex_inv".
      wp_block t as "Hmeta" "(Ht_result & Ht_mutex & Ht_condition & _)".
      iMod (pointsto_persist with "Ht_mutex") as "Ht_mutex".
      iMod (pointsto_persist with "Ht_condition") as "Ht_condition".

      iMod lstate_alloc as "(%γ_lstate & Hlstate_unset₁ & Hlstate_unset₂)".
      iMod consumer_alloc as "(%γ_consumer & Hconsumer_auth & Hconsumer_frag)".

      pose γ := {|
        ivar_2_name_mutex := mtx ;
        ivar_2_name_condition := cond ;
        ivar_2_name_lstate := γ_lstate ;
        ivar_2_name_consumer := γ_consumer ;
      |}.

      iApply ("HΦ" $! t γ).
      iFrameSteps. iExists None. iSteps.
    Qed.

    Lemma ivar_2_make_spec Ψ Ξ v :
      {{{
        ▷ Ψ v ∗
        ▷ □ Ξ v
      }}}
        ivar_2_make v
      {{{ t γ,
        RET #t;
        meta_token t ⊤ ∗
        ivar_2_inv t γ Ψ Ξ ∗
        ivar_2_result γ v ∗
        ivar_2_synchronized γ ∗
        ivar_2_consumer γ Ψ
      }}}.
    Proof.
      iIntros "%Φ (HΨ & #HΞ) HΦ".

      wp_rec.
      wp_smart_apply (condition_create_spec _ with "[//]") as "%cond #Hcondition_inv".
      wp_smart_apply (mutex_create_spec True with "[//]") as "%mtx #Hmutex_inv".
      wp_block t as "Hmeta" "(Ht_result & Ht_mutex & Ht_condition & _)".
      iMod (pointsto_persist with "Ht_mutex") as "Ht_mutex".
      iMod (pointsto_persist with "Ht_condition") as "Ht_condition".

      iMod lstate_alloc as "(%γ_lstate & Hlstate_unset₁ & Hlstate_unset₂)".
      iMod consumer_alloc as "(%γ_consumer & Hconsumer_auth & Hconsumer_frag)".

      pose γ := {|
        ivar_2_name_mutex := mtx ;
        ivar_2_name_condition := cond ;
        ivar_2_name_lstate := γ_lstate ;
        ivar_2_name_consumer := γ_consumer ;
      |}.

      iMod (lstate_update (γ := γ) v with "Hlstate_unset₁ Hlstate_unset₂") as "#Hlstate_set".
      iDestruct (consumer_produce (γ := γ) v with "Hconsumer_auth HΨ") as "Hconsumer_auth".

      iApply ("HΦ" $! t γ).
      iFrameSteps. iExists (Some v). iSteps.
    Qed.

    Lemma ivar_2_try_get_spec t γ Ψ Ξ :
      {{{
        ivar_2_inv t γ Ψ Ξ
      }}}
        ivar_2_try_get #t
      {{{ o,
        RET o;
        if o is Some v then
          £ 2 ∗
          ivar_2_result γ v ∗
          ivar_2_synchronized γ
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
    Lemma ivar_2_try_get_spec_result t γ Ψ Ξ v :
      {{{
        ivar_2_inv t γ Ψ Ξ ∗
        ivar_2_result γ v
      }}}
        ivar_2_try_get #t
      {{{
        RET Some v;
        £ 2 ∗
        ivar_2_synchronized γ
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

    Lemma ivar_2_is_unset_spec t γ Ψ Ξ :
      {{{
        ivar_2_inv t γ Ψ Ξ
      }}}
        ivar_2_is_unset #t
      {{{ b,
        RET #b;
        if b then
          True
        else
          £ 2 ∗
          ivar_2_resolved γ
      }}}.
    Proof.
      iIntros "%Φ #Hinv HΦ".

      wp_rec.
      wp_apply (ivar_2_try_get_spec with "Hinv") as ([v |]) "H".
      all: wp_pures.
      2: iSteps.
      iDestruct "H" as "(H£ & Hresult & Hsynchronized)".
      iSteps.
    Qed.
    Lemma ivar_2_is_unset_spec_result t γ Ψ Ξ v :
      {{{
        ivar_2_inv t γ Ψ Ξ ∗
        ivar_2_result γ v
      }}}
        ivar_2_is_unset #t
      {{{
        RET false;
        £ 2
      }}}.
    Proof.
      iIntros "%Φ (#Hinv & #Hresult) HΦ".

      wp_rec.
      wp_apply (ivar_2_try_get_spec_result with "[$Hinv $Hresult]").
      iSteps.
    Qed.

    Lemma ivar_2_is_set_spec t γ Ψ Ξ :
      {{{
        ivar_2_inv t γ Ψ Ξ
      }}}
        ivar_2_is_set #t
      {{{ b,
        RET #b;
        if b then
          £ 2 ∗
          ivar_2_resolved γ
        else
          True
      }}}.
    Proof.
      iIntros "%Φ #Hinv HΦ".

      wp_rec.
      wp_apply (ivar_2_is_unset_spec with "[$]") as (b) "Hb".
      destruct b; iSteps.
    Qed.
    Lemma ivar_2_is_set_spec_result t γ Ψ Ξ v :
      {{{
        ivar_2_inv t γ Ψ Ξ ∗
        ivar_2_result γ v
      }}}
        ivar_2_is_set #t
      {{{
        RET true;
        £ 2
      }}}.
    Proof.
      iIntros "%Φ (#Hinv & #Hresult) HΦ".

      wp_rec.
      wp_apply (ivar_2_is_unset_spec_result with "[$]").
      iSteps.
    Qed.

    Lemma ivar_2_get_spec t γ Ψ Ξ :
      {{{
        ivar_2_inv t γ Ψ Ξ
      }}}
        ivar_2_get #t
      {{{ v,
        RET v;
        £ 2 ∗
        ivar_2_result γ v ∗
        ivar_2_synchronized γ
      }}}.
    Proof.
      iIntros "%Φ #Hinv HΦ".

      wp_rec credits:"H£".
      iApply (lc_weaken 2) in "H£"; first done.
      wp_apply (ivar_2_try_get_spec with "Hinv") as (state) "H".
      iDestruct "Hinv" as "(:inv)".
      destruct state; first iSteps.
      do 2 wp_load.

      pose Ψ_mutex (_ : val) := (
        ∃ v,
        lstate_set γ v
      )%I.
      wp_smart_apply (mutex_protect_spec Ψ_mutex with "[$Hmutex_inv]") as (res) "(%v & #Hlstate_set)".
      { iIntros "Hmutex_locked _".
        pose (Ψ_condition b := (
          if b then
            True
          else
            ∃ v,
            lstate_set γ v
        )%I).
        wp_smart_apply (condition_wait_while_spec Ψ_condition with "[$Hcondition_inv $Hmutex_inv $Hmutex_locked]") as "(Hmutex_locked & _ & Hlstate_set)"; last iFrameSteps.
        iStep. iIntros "!> Hmutex_locked _ _".
        wp_pures.

        wp_bind (_.{result})%E.
        iInv "Hinv" as "(:inv_inner)".
        wp_load.
        destruct state as [v |].

        - iDestruct "Hstate" as "(:inv_state_set)".
          iSplitR "Hmutex_locked". { iFrameSteps. }
          iSteps.

        - iSplitR "Hmutex_locked". { iFrameSteps. }
          iSteps.
      }
      wp_pures.

      wp_bind (_.{result})%E.
      iInv "Hinv" as "(:inv_inner)".
      wp_load.
      destruct state as [v_ |]; last first.
      { iDestruct (lstate_unset₁_set with "Hstate Hlstate_set") as %[]. }
      iDestruct "Hstate" as "(:inv_state_set =1)".
      iDestruct (lstate_set_agree with "Hlstate_set Hlstate_set_1") as %<-. iClear "Hlstate_set_1".
      iSplitR "H£ HΦ". { iFrameSteps. }
      iSteps.
    Qed.
    Lemma ivar_2_get_spec_result t γ Ψ Ξ v :
      {{{
        ivar_2_inv t γ Ψ Ξ ∗
        ivar_2_result γ v
      }}}
        ivar_2_get #t
      {{{
        RET v;
        £ 2 ∗
        ivar_2_synchronized γ
      }}}.
    Proof.
      iIntros "%Φ (#Hinv & #Hresult) HΦ".

      wp_apply (ivar_2_get_spec with "Hinv") as (v_) "(H£ & Hresult_ & Hsynchronized)".
      iDestruct (ivar_2_result_agree with "Hresult Hresult_")as %<-.
      iSteps.
    Qed.

    Lemma ivar_2_set_spec t γ Ψ Ξ v :
      {{{
        ivar_2_inv t γ Ψ Ξ ∗
        ivar_2_producer γ ∗
        ▷ Ψ v ∗
        ▷ □ Ξ v
      }}}
        ivar_2_set #t v
      {{{
        RET ();
        ivar_2_result γ v
      }}}.
    Proof.
      iIntros "%Φ ((:inv) & (:producer) & HΨ & #HΞ) HΦ".

      wp_rec. wp_load.

      pose Ψ_mutex (_ : val) :=
        lstate_set γ v.
      wp_apply (mutex_protect_spec Ψ_mutex with "[$Hmutex_inv Hlstate_unset₂ HΨ]") as (res) "#Hlstate_set"; last iSteps.
      iIntros "Hmutex_locked _".
      wp_pures.

      iInv "Hinv" as "(:inv_inner)".
      wp_store.
      destruct state.
      { iDestruct "Hstate" as "(:inv_state_set =1)".
        iDestruct (lstate_unset₂_set with "Hlstate_unset₂ Hlstate_set_1") as %[].
      }
      iMod (lstate_update with "Hstate Hlstate_unset₂") as "#Hlstate_set".
      iDestruct (consumer_produce with "Hconsumer_auth HΨ") as "Hconsumer_auth".
      iSplitR "Hmutex_locked". { iFrameSteps. }
      iSteps.
    Qed.
  End ivar_2_G.

  #[global] Opaque ivar_2_inv.
  #[global] Opaque ivar_2_producer.
  #[global] Opaque ivar_2_consumer.
  #[global] Opaque ivar_2_result.
  #[global] Opaque ivar_2_synchronized.
End base.

From zoo_std Require
  ivar_2__opaque.

Section ivar_2_G.
  Context `{ivar_2_G : Ivar2G Σ}.

  Implicit Types 𝑡 : location.
  Implicit Types t : val.
  Implicit Types γ : base.ivar_2_name.
  Implicit Types Ψ Χ Ξ : val → iProp Σ.

  Definition ivar_2_inv t Ψ Ξ : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.ivar_2_inv 𝑡 γ Ψ Ξ.
  #[local] Instance : CustomIpat "inv" :=
    " ( %l{} &
        %γ{} &
        {%Heq{};->} &
        #Hmeta{_{}} &
        Hinv{_{}}
      )
    ".

  Definition ivar_2_producer t : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.ivar_2_producer γ.
  #[local] Instance : CustomIpat "producer" :=
    " ( %l{;_} &
        %γ{;_} &
        {%Heq{};->} &
        #Hmeta{_{}} &
        Hproducer{_{}}
      )
    ".

  Definition ivar_2_consumer t Χ : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.ivar_2_consumer γ Χ.
  #[local] Instance : CustomIpat "consumer" :=
    " ( %l{;_} &
        %γ{;_} &
        {%Heq{};->} &
        #Hmeta{_{}} &
        Hconsumer{_{}}
      )
    ".

  Definition ivar_2_result t v : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.ivar_2_result γ v.
  #[local] Instance : CustomIpat "result" :=
    " ( %l{;_} &
        %γ{;_} &
        {%Heq{};->} &
        #Hmeta{_{}} &
        Hresult{_{}}
      )
    ".
  Definition ivar_2_resolved t : iProp Σ :=
    ∃ v,
    ivar_2_result t v.

  Definition ivar_2_synchronized t : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.ivar_2_synchronized γ.
  #[local] Instance : CustomIpat "synchronized" :=
    " ( %l{;_} &
        %γ{;_} &
        {%Heq{};->} &
        #Hmeta{_{}} &
        Hsynchronized{_{}}
      )
    ".

  #[global] Instance ivar_2_inv_contractive t n :
    Proper (
      (pointwise_relation _ (dist_later n)) ==>
      (pointwise_relation _ (dist_later n)) ==>
      (≡{n}≡)
    ) (ivar_2_inv t).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance ivar_2_inv_proper t :
    Proper (
      (pointwise_relation _ (≡)) ==>
      (pointwise_relation _ (≡)) ==>
      (≡)
    ) (ivar_2_inv t).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance ivar_2_consumer_contractive t n :
    Proper (
      (pointwise_relation _ (dist_later n)) ==>
      (≡{n}≡)
    ) (ivar_2_consumer t).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance ivar_2_consumer_proper t :
    Proper (
      (pointwise_relation _ (≡)) ==>
      (≡)
    ) (ivar_2_consumer t).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance ivar_2_producer_timeless t :
    Timeless (ivar_2_producer t).
  Proof.
    apply _.
  Qed.
  #[global] Instance ivar_2_result_timeless t v :
    Timeless (ivar_2_result t v).
  Proof.
    apply _.
  Qed.
  #[global] Instance ivar_2_synchronized_timeless t :
    Timeless (ivar_2_synchronized t).
  Proof.
    apply _.
  Qed.

  #[global] Instance ivar_2_inv_persistent t Ψ Ξ :
    Persistent (ivar_2_inv t Ψ Ξ).
  Proof.
    apply _.
  Qed.
  #[global] Instance ivar_2_result_persistent t v :
    Persistent (ivar_2_result t v).
  Proof.
    apply _.
  Qed.
  #[global] Instance ivar_2_synchronized_persistent t :
    Persistent (ivar_2_synchronized t).
  Proof.
    apply _.
  Qed.

  Lemma ivar_2_producer_exclusive t :
    ivar_2_producer t -∗
    ivar_2_producer t -∗
    False.
  Proof.
    iIntros "(:producer =1) (:producer =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.ivar_2_producer_exclusive with "Hproducer_1 Hproducer_2").
  Qed.

  Lemma ivar_2_consumer_wand {t Ψ Ξ Χ1} Χ2 :
    ivar_2_inv t Ψ Ξ -∗
    ivar_2_consumer t Χ1 -∗
    (∀ v, Χ1 v -∗ Χ2 v) ={⊤}=∗
    ivar_2_consumer t Χ2.
  Proof.
    iIntros "(:inv =1) (:consumer =2) H". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iDestruct (base.ivar_2_consumer_wand with "Hinv_1 Hconsumer_2 H") as "H".
    iSteps.
  Qed.
  Lemma ivar_2_consumer_divide {t Ψ Ξ} Χs :
    ivar_2_inv t Ψ Ξ -∗
    ivar_2_consumer t (λ v, [∗ list] Χ ∈ Χs, Χ v) ={⊤}=∗
    [∗ list] Χ ∈ Χs, ivar_2_consumer t Χ.
  Proof.
    iIntros "(:inv =1) (:consumer =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iDestruct (base.ivar_2_consumer_divide with "Hinv_1 Hconsumer_2") as "H".
    iApply (big_sepL_impl with "H").
    iSteps.
  Qed.
  Lemma ivar_2_consumer_split {t Ψ Ξ} Χ1 Χ2 :
    ivar_2_inv t Ψ Ξ -∗
    ivar_2_consumer t (λ v, Χ1 v ∗ Χ2 v) ={⊤}=∗
      ivar_2_consumer t Χ1 ∗
      ivar_2_consumer t Χ2.
  Proof.
    iIntros "Hinv Hconsumer".
    iMod (ivar_2_consumer_divide [Χ1;Χ2] with "Hinv [Hconsumer]") as "($ & $ & _)" => //.
    { simpl. setoid_rewrite bi.sep_emp => //. }
  Qed.

  Lemma ivar_2_result_agree t v1 v2 :
    ivar_2_result t v1 -∗
    ivar_2_result t v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    iIntros "(:result =1) (:result =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.ivar_2_result_agree with "Hresult_1 Hresult_2").
  Qed.

  Lemma ivar_2_producer_result t v :
    ivar_2_producer t -∗
    ivar_2_result t v -∗
    False.
  Proof.
    iIntros "(:producer =1) (:result =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.ivar_2_producer_result with "Hproducer_1 Hresult_2").
  Qed.

  Lemma ivar_2_inv_result t Ψ Ξ v :
    ivar_2_inv t Ψ Ξ -∗
    ivar_2_result t v -∗
    ivar_2_synchronized t ={⊤}=∗
    ▷ □ Ξ v.
  Proof.
    iIntros "(:inv =1) (:result =2) (:synchronized =3)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iDestruct (meta_agree with "Hmeta_2 Hmeta_3") as %<-.
    iApply (base.ivar_2_inv_result with "Hinv_1 Hresult_2 Hsynchronized_3").
  Qed.
  Lemma ivar_2_inv_result' t Ψ Ξ v :
    £ 1 -∗
    ivar_2_inv t Ψ Ξ -∗
    ivar_2_result t v -∗
    ivar_2_synchronized t ={⊤}=∗
    □ Ξ v.
  Proof.
    iIntros "H£ Hinv Hresult Hsynchronized".
    iMod (ivar_2_inv_result with "Hinv Hresult Hsynchronized") as "HΞ".
    iApply (lc_fupd_elim_later with "H£ HΞ").
  Qed.
  Lemma ivar_2_inv_result_consumer t Ψ Ξ v Χ :
    ivar_2_inv t Ψ Ξ -∗
    ivar_2_result t v -∗
    ivar_2_synchronized t -∗
    ivar_2_consumer t Χ ={⊤}=∗
      ▷^2 Χ v ∗
      ▷ □ Ξ v.
  Proof.
    iIntros "(:inv =1) (:result =2) (:synchronized =3) (:consumer =4)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iDestruct (meta_agree with "Hmeta_2 Hmeta_3") as %<-.
    iDestruct (meta_agree with "Hmeta_2 Hmeta_4") as %<-.
    iApply (base.ivar_2_inv_result_consumer with "Hinv_1 Hresult_2 Hsynchronized_3 Hconsumer_4").
  Qed.
  Lemma ivar_2_inv_result_consumer' t Ψ Ξ v Χ :
    £ 2 -∗
    ivar_2_inv t Ψ Ξ -∗
    ivar_2_result t v -∗
    ivar_2_synchronized t -∗
    ivar_2_consumer t Χ ={⊤}=∗
      Χ v ∗
      □ Ξ v.
  Proof.
    iIntros "(H£1 & H£2) Hinv Hresult Hsynchronized Hconsumer".
    iMod (ivar_2_inv_result_consumer with "Hinv Hresult Hsynchronized Hconsumer") as "H".
    rewrite -bi.later_sep.
    iMod (lc_fupd_elim_later with "H£1 H") as "(HΧ & $)".
    iApply (lc_fupd_elim_later with "H£2 HΧ").
  Qed.

  Lemma ivar_2_create_spec Ψ Ξ :
    {{{
      True
    }}}
      ivar_2_create ()
    {{{ t,
      RET t;
      ivar_2_inv t Ψ Ξ ∗
      ivar_2_producer t ∗
      ivar_2_consumer t Ψ
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    iApply wp_fupd.
    wp_apply (base.ivar_2_create_spec with "[//]") as (𝑡 γ) "(Hmeta & Hinv & Hproducer & Hconsumer)".
    iMod (meta_set γ with "Hmeta") as "#Hmeta"; first done.
    iSteps.
  Qed.

  Lemma ivar_2_make_spec Ψ Ξ v :
    {{{
      ▷ Ψ v ∗
      ▷ □ Ξ v
    }}}
      ivar_2_make v
    {{{ t,
      RET t;
      ivar_2_inv t Ψ Ξ ∗
      ivar_2_result t v ∗
      ivar_2_consumer t Ψ
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #HΞ) HΦ".

    iApply wp_fupd.
    wp_apply (base.ivar_2_make_spec with "[$]") as (𝑡 γ) "(Hmeta & Hinv & Hproducer & Hconsumer)".
    iMod (meta_set γ with "Hmeta") as "#Hmeta"; first done.
    iSteps.
  Qed.

  Lemma ivar_2_try_get_spec t Ψ Ξ :
    {{{
      ivar_2_inv t Ψ Ξ
    }}}
      ivar_2_try_get t
    {{{ o,
      RET o;
      if o is Some v then
        £ 2 ∗
        ivar_2_result t v ∗
        ivar_2_synchronized t
      else
        True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_apply (base.ivar_2_try_get_spec with "[$]") as (o) "Ho".
    iSpecialize ("HΦ" $! o).
    destruct o; iSteps.
  Qed.
  Lemma ivar_2_try_get_spec_result t Ψ Ξ v :
    {{{
      ivar_2_inv t Ψ Ξ ∗
      ivar_2_result t v
    }}}
      ivar_2_try_get t
    {{{
      RET Some v;
      £ 2 ∗
      ivar_2_synchronized t
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:result =2)) HΦ". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp_apply (base.ivar_2_try_get_spec_result with "[$]").
    iSteps.
  Qed.

  Lemma ivar_2_is_unset_spec t Ψ Ξ :
    {{{
      ivar_2_inv t Ψ Ξ
    }}}
      ivar_2_is_unset t
    {{{ b,
      RET #b;
      if b then
        True
      else
        £ 2 ∗
        ivar_2_resolved t
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_apply (base.ivar_2_is_unset_spec with "[$]") as (b) "Hb".
    rewrite /ivar_2_resolved. destruct b; iSteps.
  Qed.
  Lemma ivar_2_is_unset_spec_result t Ψ Ξ v :
    {{{
      ivar_2_inv t Ψ Ξ ∗
      ivar_2_result t v
    }}}
      ivar_2_is_unset t
    {{{
      RET false;
      £ 2
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:result =2)) HΦ". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp_apply (base.ivar_2_is_unset_spec_result with "[$] HΦ").
  Qed.

  Lemma ivar_2_is_set_spec t Ψ Ξ :
    {{{
      ivar_2_inv t Ψ Ξ
    }}}
      ivar_2_is_set t
    {{{ b,
      RET #b;
      if b then
        £ 2 ∗
        ivar_2_resolved t
      else
        True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_apply (base.ivar_2_is_set_spec with "[$]") as (b) "Hb".
    rewrite /ivar_2_resolved. destruct b; iSteps.
  Qed.
  Lemma ivar_2_is_set_spec_result t Ψ Ξ v :
    {{{
      ivar_2_inv t Ψ Ξ ∗
      ivar_2_result t v
    }}}
      ivar_2_is_set t
    {{{
      RET true;
      £ 2
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:result =2)) HΦ". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp_apply (base.ivar_2_is_set_spec_result with "[$] HΦ").
  Qed.

  Lemma ivar_2_get_spec t Ψ Ξ :
    {{{
      ivar_2_inv t Ψ Ξ
    }}}
      ivar_2_get t
    {{{ v,
      RET v;
      £ 2 ∗
      ivar_2_result t v ∗
      ivar_2_synchronized t
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_apply (base.ivar_2_get_spec with "[$]").
    iSteps.
  Qed.

  Lemma ivar_2_set_spec t Ψ Ξ v :
    {{{
      ivar_2_inv t Ψ Ξ ∗
      ivar_2_producer t ∗
      ▷ Ψ v ∗
      ▷ □ Ξ v
    }}}
      ivar_2_set t v
    {{{
      RET ();
      ivar_2_result t v
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:producer =2) & HΨ & HΞ) HΦ". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp_apply (base.ivar_2_set_spec with "[$]").
    iSteps.
  Qed.
End ivar_2_G.

#[global] Opaque ivar_2_inv.
#[global] Opaque ivar_2_producer.
#[global] Opaque ivar_2_consumer.
#[global] Opaque ivar_2_result.
#[global] Opaque ivar_2_synchronized.
