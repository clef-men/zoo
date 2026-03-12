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
  lazy__code.
From zoo_std Require Import
  lazy__types
  mutex.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types v fn mtx : val.

Class LazyG Σ `{zoo_G : !ZooG Σ} := {
  #[local] lazy_G_mutex_G :: MutexG Σ ;
  #[local] lazy_G_lstate_G :: OneshotG Σ unit val ;
  #[local] lazy_G_consumer_G :: SubpredsG Σ val ;
}.

Definition lazy_Σ := #[
  mutex_Σ ;
  oneshot_Σ unit val ;
  subpreds_Σ val
].
#[global] Instance subG_lazy_Σ Σ `{zoo_G : !ZooG Σ} :
  subG lazy_Σ Σ →
  LazyG Σ .
Proof.
  solve_inG.
Qed.

Module base.
  Section lazy_G.
    Context `{lazy_G : LazyG Σ}.

    Implicit Types t : location.
    Implicit Types Ψ Χ Ξ : val → iProp Σ.

    Record lazy_name := {
      metadata_thunk : val ;
      metadata_lstate : gname ;
      metadata_consumer : gname ;
    }.
    Implicit Types γ : lazy_name.

    #[global] Instance lazy_name_eq_dec : EqDecision lazy_name :=
      ltac:(solve_decision).
    #[global] Instance lazy_name_countable :
      Countable lazy_name.
    Proof.
      solve_countable.
    Qed.

    Inductive state :=
      | Unset
      | Setting mtx
      | Set_ v.
    Implicit Types state : state.

    #[local] Instance state_inhabited : Inhabited state :=
      populate Unset.

    #[local] Definition state_to_bool state :=
      match state with
      | Set_ _ =>
          true
      | _ =>
          false
      end.
    #[local] Definition state_to_option state :=
      match state with
      | Set_ v =>
          Some v
      | _ =>
          None
      end.
    #[local] Definition state_to_val γ state :=
      match state with
      | Unset =>
          ‘Unset( γ.(metadata_thunk) )
      | Setting mtx =>
          ‘Setting( mtx )
      | Set_ v =>
          ‘Set( v )
      end%V.

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

    Definition lazy_result :=
      lstate_set.
    #[local] Instance : CustomIpat "result" :=
      " #Hlstate_set{_{}}
      ".
    Definition lazy_resolved γ : iProp Σ :=
      ∃ v,
      lazy_result γ v.

    #[local] Definition inv_state_unset γ Ψ Ξ : iProp Σ :=
      lstate_unset₁ γ ∗
      lstate_unset₂ γ ∗
      WP γ.(metadata_thunk) () {{ v,
        ▷ Ψ v ∗
        ▷ □ Ξ v
      }}.
    #[local] Instance : CustomIpat "inv_state_unset" :=
      " ( {>;}Hlstate_unset₁{_{}} &
          {>;}Hlstate_unset₂{_{}} &
          Hthunk
        )
      ".
    #[local] Definition inv_state_setting γ mtx : iProp Σ :=
      lstate_unset₁ γ ∗
      mutex_inv mtx (lazy_resolved γ).
    #[local] Instance : CustomIpat "inv_state_setting" :=
      " ( {>;}Hlstate_unset₁{_{}} &
          #Hmtx_inv{_{}}
        )
      ".
    #[local] Definition inv_state_set γ Ξ v : iProp Σ :=
      lstate_set γ v ∗
      □ Ξ v.
    #[local] Instance : CustomIpat "inv_state_set" :=
      " ( {>;}#Hlstate_set{_{}} &
          #HΞ{_{}}
        )
      ".
    #[local] Definition inv_state γ Ψ Ξ state :=
      match state with
      | Unset =>
          inv_state_unset γ Ψ Ξ
      | Setting mtx =>
          inv_state_setting γ mtx
      | Set_ v =>
          inv_state_set γ Ξ v
      end.

    #[local] Definition inv_inner t γ Ψ Ξ : iProp Σ :=
      ∃ state,
      t ↦ᵣ state_to_val γ state ∗
      consumer_auth γ Ψ (state_to_option state) ∗
      inv_state γ Ψ Ξ state.
    #[local] Instance : CustomIpat "inv_inner" :=
      " ( %state &
          Ht &
          Hconsumer_auth &
          Hstate
        )
      ".
    Definition lazy_inv t γ Ψ Ξ : iProp Σ :=
      inv nroot (inv_inner t γ Ψ Ξ).
    #[local] Instance : CustomIpat "inv" :=
      " #Hinv
      ".

    Definition lazy_consumer :=
      consumer_frag.
    #[local] Instance : CustomIpat "consumer" :=
      " Hconsumer{}_frag
      ".

    #[global] Instance lazy_inv_contractive t γ n :
      Proper (
        (pointwise_relation _ (dist_later n)) ==>
        (pointwise_relation _ (dist_later n)) ==>
        (≡{n}≡)
      ) (lazy_inv t γ).
    Proof.
      rewrite /lazy_inv /inv_inner /inv_state /inv_state_unset /inv_state_setting /inv_state_set.
      intros Ψ1 Ψ2 HΨ Ξ1 Ξ2 HΞ.
      repeat (f_contractive || f_equiv).
      { eapply dist_lt. apply HΨ. done. }
      { eapply dist_lt. apply HΞ. done. }
    Qed.
    #[global] Instance lazy_inv_proper t γ :
      Proper (
        (pointwise_relation _ (≡)) ==>
        (pointwise_relation _ (≡)) ==>
        (≡)
      ) (lazy_inv t γ).
    Proof.
      rewrite /lazy_inv /inv_inner /inv_state /inv_state_unset /inv_state_setting /inv_state_set.
      solve_proper.
    Qed.
    #[global] Instance lazy_consumer_contractive γ n :
      Proper (
        (pointwise_relation _ (dist_later n)) ==>
        (≡{n}≡)
      ) (lazy_consumer γ).
    Proof.
      apply _.
    Qed.
    #[global] Instance lazy_consumer_proper γ :
      Proper (
        (pointwise_relation _ (≡)) ==>
        (≡)
      ) (lazy_consumer γ).
    Proof.
      apply _.
    Qed.

    #[global] Instance lazy_result_timeless γ v :
      Timeless (lazy_result γ v).
    Proof.
      apply _.
    Qed.

    #[global] Instance lazy_inv_persistent t γ Ψ Ξ :
      Persistent (lazy_inv t γ Ψ Ξ).
    Proof.
      apply _.
    Qed.
    #[global] Instance lazy_result_persistent γ v :
      Persistent (lazy_result γ v).
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
    #[local] Lemma consumer_wand {γ Ψ} {state : option val} {Χ1} Χ2 E :
      ▷ consumer_auth γ Ψ state -∗
      consumer_frag γ Χ1 -∗
      (∀ v, Χ1 v -∗ Χ2 v) ={E}=∗
        ▷ consumer_auth γ Ψ state ∗
        consumer_frag γ Χ2.
    Proof.
      apply subpreds_wand.
    Qed.
    #[local] Lemma consumer_divide {γ Ψ} {state : option val} Χs E :
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

    #[local] Lemma inv_state_lstate_set γ Ψ Ξ state v :
      ▷ inv_state γ Ψ Ξ state -∗
      lstate_set γ v -∗
      ◇ (
        ⌜state = Set_ v⌝ ∗
        ▷ inv_state_set γ Ξ v
      ).
    Proof.
      iIntros "Hstate Hlstate_set".
      destruct state as [| mtx | v_].
      - iDestruct "Hstate" as "(:inv_state_unset >)".
        iDestruct (lstate_unset₁_set with "Hlstate_unset₁ Hlstate_set") as %[].
      - iDestruct "Hstate" as "(:inv_state_setting >)".
        iDestruct (lstate_unset₁_set with "Hlstate_unset₁ Hlstate_set") as %[].
      - iDestruct "Hstate" as "(:inv_state_set =1 >)".
        iDestruct (lstate_set_agree with "Hlstate_set Hlstate_set_1") as %<-.
        iFrame "#∗" => //.
    Qed.

    Lemma lazy_consumer_wand {t γ Ψ Ξ Χ1} Χ2 :
      lazy_inv t γ Ψ Ξ -∗
      lazy_consumer γ Χ1 -∗
      (∀ v, Χ1 v -∗ Χ2 v) ={⊤}=∗
      lazy_consumer γ Χ2.
    Proof.
      iIntros "(:inv) (:consumer) H".
      iInv "Hinv" as "(:inv_inner)".
      iMod (consumer_wand with "Hconsumer_auth Hconsumer_frag H") as "($ & $)".
      iFrameSteps.
    Qed.
    Lemma lazy_consumer_divide {t γ Ψ Ξ} Χs :
      lazy_inv t γ Ψ Ξ -∗
      lazy_consumer γ (λ v, [∗ list] Χ ∈ Χs, Χ v) ={⊤}=∗
      [∗ list] Χ ∈ Χs, lazy_consumer γ Χ.
    Proof.
      iIntros "(:inv) (:consumer)".
      iInv "Hinv" as "(:inv_inner)".
      iMod (consumer_divide with "Hconsumer_auth Hconsumer_frag") as "($ & $)".
      iFrameSteps.
    Qed.

    Lemma lazy_result_agree γ v1 v2 :
      lazy_result γ v1 -∗
      lazy_result γ v2 -∗
      ⌜v1 = v2⌝.
    Proof.
      apply lstate_set_agree.
    Qed.

    Lemma lazy_inv_result t γ Ψ Ξ v :
      lazy_inv t γ Ψ Ξ -∗
      lazy_result γ v ={⊤}=∗
      ▷ □ Ξ v.
    Proof.
      iIntros "(:inv) (:result)".
      iInv "Hinv" as "(:inv_inner)".
      iMod (inv_state_lstate_set with "Hstate Hlstate_set") as "(-> & (:inv_state_set =1 >))".
      iSplitL. { iFrameSteps. }
      iSteps.
    Qed.
    Lemma lazy_inv_result_consumer t γ Ψ Ξ v Χ :
      lazy_inv t γ Ψ Ξ -∗
      lazy_result γ v -∗
      lazy_consumer γ Χ ={⊤}=∗
        ▷^2 Χ v ∗
        ▷ □ Ξ v.
    Proof.
      iIntros "(:inv) (:result) (:consumer)".
      iInv "Hinv" as "(:inv_inner)".
      iMod (inv_state_lstate_set with "Hstate Hlstate_set") as "(-> & (:inv_state_set =1 >))".
      iMod (consumer_consume with "Hconsumer_auth Hconsumer_frag") as "(Hconsumer_auth & HΧ)".
      iSplitR "HΧ". { iFrameSteps. }
      iSteps.
    Qed.

    Lemma lazy_make_spec Ψ Ξ fn :
      {{{
        WP fn () {{ v,
          ▷ Ψ v ∗
          ▷ □ Ξ v
        }}
      }}}
        lazy_make fn
      {{{
        t γ
      , RET #t;
        meta_token t ⊤ ∗
        lazy_inv t γ Ψ Ξ ∗
        lazy_consumer γ Ψ
      }}}.
    Proof.
      iIntros "%Φ Hfn HΦ".

      wp_rec.
      wp_ref t as "Hmeta" "Ht".

      iMod lstate_alloc as "(%γ_lstate & Hlstate_unset₁ & Hlstate_unset₂)".
      iMod consumer_alloc as "(%γ_consumer & Hconsumer_auth & Hconsumer_frag)".

      pose γ := {|
        metadata_thunk := fn ;
        metadata_lstate := γ_lstate ;
        metadata_consumer := γ_consumer ;
      |}.

      iApply ("HΦ" $! t γ).
      iFrameSteps. iExists Unset. iSteps.
    Qed.

    Lemma lazy_return_spec Ψ Ξ v :
      {{{
        ▷ Ψ v ∗
        ▷ □ Ξ v
      }}}
        lazy_return v
      {{{
        t γ
      , RET #t;
        meta_token t ⊤ ∗
        lazy_inv t γ Ψ Ξ ∗
        lazy_result γ v ∗
        lazy_consumer γ Ψ
      }}}.
    Proof.
      iIntros "%Φ (HΨ & #HΞ) HΦ".

      wp_rec.
      wp_ref t as "Hmeta" "Ht".

      iMod lstate_alloc as "(%γ_lstate & Hlstate_unset₁ & Hlstate_unset₂)".
      iMod consumer_alloc as "(%γ_consumer & Hconsumer_auth & Hconsumer_frag)".

      pose γ := {|
        metadata_thunk := () ;
        metadata_lstate := γ_lstate ;
        metadata_consumer := γ_consumer ;
      |}.

      iMod (lstate_update (γ := γ) v with "Hlstate_unset₁ Hlstate_unset₂") as "#Hlstate_set".
      iDestruct (consumer_produce (γ := γ) v with "Hconsumer_auth HΨ") as "Hconsumer_auth".

      iApply ("HΦ" $! t γ).
      iFrameSteps. iExists (Set_ v). iSteps.
    Qed.

    Lemma lazy_is_set_spec t γ Ψ Ξ :
      {{{
        lazy_inv t γ Ψ Ξ
      }}}
        lazy_is_set #t
      {{{
        b
      , RET #b;
        if b then
          £ 2 ∗
          lazy_resolved γ
        else
          True
      }}}.
    Proof.
      iIntros "%Φ (:inv) HΦ".

      wp_rec credits:"H£".
      iApply (lc_weaken 2) in "H£"; first done.

      wp_bind (!_)%E.
      iInv "Hinv" as "(:inv_inner)".
      wp_load.
      iSpecialize ("HΦ" $! (state_to_bool state)).
      destruct state as [| mtx | v].

      - iSplitR "HΦ". { iFrameSteps. }
        iSteps.

      - iSplitR "HΦ". { iFrameSteps. }
        iSteps.

      - iDestruct "Hstate" as "(:inv_state_set)".
        iSplitR "H£ HΦ". { iFrameSteps. }
        iSteps.
    Qed.
    Lemma lazy_is_set_spec_result t γ Ψ Ξ v :
      {{{
        lazy_inv t γ Ψ Ξ ∗
        lazy_result γ v
      }}}
        lazy_is_set #t
      {{{
        RET true;
        £ 2
      }}}.
    Proof.
      iIntros "%Φ ((:inv) & (:result)) HΦ".

      wp_rec credits:"H£".
      iApply (lc_weaken 2) in "H£"; first done.

      wp_bind (!_)%E.
      iInv "Hinv" as "(:inv_inner)".
      wp_load.
      iMod (inv_state_lstate_set with "Hstate Hlstate_set") as "(-> & (:inv_state_set =1))".
      iSplitR "H£ HΦ". { iFrameSteps. }
      iSteps.
    Qed.

    Lemma lazy_is_unset_spec t γ Ψ Ξ :
      {{{
        lazy_inv t γ Ψ Ξ
      }}}
        lazy_is_unset #t
      {{{
        b
      , RET #b;
        if b then
          True
        else
          £ 2 ∗
          lazy_resolved γ
      }}}.
    Proof.
      iIntros "%Φ #Hinv HΦ".

      wp_rec.
      wp_apply (lazy_is_set_spec with "[$]") as (b) "Hb".
      destruct b; iSteps.
    Qed.
    Lemma lazy_is_unset_spec_result t γ Ψ Ξ v :
      {{{
        lazy_inv t γ Ψ Ξ ∗
        lazy_result γ v
      }}}
        lazy_is_unset #t
      {{{
        RET false;
        £ 2
      }}}.
    Proof.
      iIntros "%Φ (#Hinv & #Hresult) HΦ".

      wp_rec.
      wp_apply (lazy_is_set_spec_result with "[$]").
      iSteps.
    Qed.

    Lemma lazy_get_spec t γ Ψ Ξ :
      {{{
        lazy_inv t γ Ψ Ξ
      }}}
        lazy_get #t
      {{{
        v
      , RET v;
        £ 2 ∗
        lazy_result γ v
      }}}.
    Proof.
      iIntros "%Φ (:inv) HΦ".

      iLöb as "HLöb" forall (Φ).

      wp_rec credits:"H£".
      iApply (lc_weaken 2) in "H£"; first done.
      iApply (wp_frame_wand with "[H£]"); first iAccu.

      wp_bind (!_)%E.
      iInv "Hinv" as "(:inv_inner)".
      wp_load.
      destruct state as [| mtx | v_].

      - iSplitR "HΦ". { iFrameSteps. }
        iIntros "!> {%}".

        wp_smart_apply (mutex_create_lock_spec_init with "[//]") as (mtx) "(Hmtx_init & Hmtx_locked)".
        wp_pures.

        wp_bind (CAS _ _ _).
        iInv "Hinv" as "(:inv_inner)".
        wp_cas as Hcas.

        + iSplitR "Hmtx_init Hmtx_locked HΦ". { iFrameSteps. }
          iIntros "!> {%}".

          wp_smart_apply (mutex_unlock_spec_init with "[$]") as "_".
          wp_smart_apply "HLöb".
          iSteps.

        + destruct state; zoo_simplify.
          iDestruct "Hstate" as "(:inv_state_unset)".
          iMod (mutex_init_to_inv (lazy_resolved γ) with "Hmtx_init [//]") as "#Hmtx_inv".
          iSplitR "Hmtx_locked Hlstate_unset₂ Hthunk HΦ".
          { iExists (Setting mtx). iFrameSteps. }
          iIntros "!> {%}".

          wp_smart_apply (wp_wand with "Hthunk") as (v) "(HΨ & #HΞ)".
          wp_pures.

          wp_bind (_ <- _)%E.
          iInv "Hinv" as "(:inv_inner)".
          wp_store.
          destruct state.

          * iDestruct "Hstate" as "(:inv_state_unset =1)".
            iDestruct (lstate_unset₂_exclusive with "Hlstate_unset₂ Hlstate_unset₂_1") as %[].

          * iDestruct "Hstate" as "(:inv_state_setting =1)".
            iMod (lstate_update with "Hlstate_unset₁_1 Hlstate_unset₂") as "#Hlstate_set".
            iDestruct (consumer_produce with "Hconsumer_auth HΨ") as "Hconsumer_auth".
            iSplitR "Hmtx_locked HΦ". { iExists (Set_ v). iFrameSteps. }
            iIntros "!> {%}".

            wp_smart_apply (mutex_unlock_spec with "[$Hmtx_inv $Hmtx_locked]"); iSteps.

          * iDestruct "Hstate" as "(:inv_state_set =1)".
            iDestruct (lstate_unset₂_set with "Hlstate_unset₂ Hlstate_set_1") as %[].

      - iDestruct "Hstate" as "(:inv_state_setting)".
        iSplitR "HΦ". { iFrameSteps. }
        iIntros "!> {%}".

        wp_smart_apply (mutex_synchronize_spec with "[$]") as "_".
        wp_smart_apply "HLöb".
        iSteps.

      - iDestruct "Hstate" as "(:inv_state_set)".
        iSplitR "HΦ". { iFrameSteps. }
        iSteps.
    Qed.
    Lemma lazy_get_spec_result t γ Ψ Ξ v :
      {{{
        lazy_inv t γ Ψ Ξ ∗
        lazy_result γ v
      }}}
        lazy_get #t
      {{{
        RET v;
        £ 2
      }}}.
    Proof.
      iIntros "%Φ ((:inv) & (:result)) HΦ".

      wp_rec credits:"H£".
      iApply (lc_weaken 2) in "H£"; first done.

      wp_bind (!_)%E.
      iInv "Hinv" as "(:inv_inner)".
      wp_load.
      iMod (inv_state_lstate_set with "Hstate Hlstate_set") as "(-> & (:inv_state_set =1))".
      iSplitR "H£ HΦ". { iFrameSteps. }
      iSteps.
    Qed.
  End lazy_G.

  #[global] Opaque lazy_inv.
  #[global] Opaque lazy_consumer.
  #[global] Opaque lazy_result.
End base.

From zoo_std Require
  lazy__opaque.

Section lazy_G.
  Context `{lazy_G : LazyG Σ}.

  Implicit Types 𝑡 : location.
  Implicit Types t : val.
  Implicit Types γ : base.lazy_name.
  Implicit Types Ψ Χ Ξ : val → iProp Σ.

  Definition lazy_inv t Ψ Ξ : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.lazy_inv 𝑡 γ Ψ Ξ.
  #[local] Instance : CustomIpat "inv" :=
    " ( %l{} &
        %γ{} &
        {%Heq{};->} &
        #Hmeta{_{}} &
        Hinv{_{}}
      )
    ".

  Definition lazy_consumer t Χ : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.lazy_consumer γ Χ.
  #[local] Instance : CustomIpat "consumer" :=
    " ( %l{;_} &
        %γ{;_} &
        {%Heq{};->} &
        #Hmeta{_{}} &
        Hconsumer{_{}}
      )
    ".

  Definition lazy_result t v : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.lazy_result γ v.
  #[local] Instance : CustomIpat "result" :=
    " ( %l{;_} &
        %γ{;_} &
        {%Heq{};->} &
        #Hmeta{_{}} &
        Hresult{_{}}
      )
    ".
  Definition lazy_resolved t : iProp Σ :=
    ∃ v,
    lazy_result t v.

  #[global] Instance lazy_inv_contractive t n :
    Proper (
      (pointwise_relation _ (dist_later n)) ==>
      (pointwise_relation _ (dist_later n)) ==>
      (≡{n}≡)
    ) (lazy_inv t).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance lazy_inv_proper t :
    Proper (
      (pointwise_relation _ (≡)) ==>
      (pointwise_relation _ (≡)) ==>
      (≡)
    ) (lazy_inv t).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance lazy_consumer_contractive t n :
    Proper (
      (pointwise_relation _ (dist_later n)) ==>
      (≡{n}≡)
    ) (lazy_consumer t).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance lazy_consumer_proper t :
    Proper (
      (pointwise_relation _ (≡)) ==>
      (≡)
    ) (lazy_consumer t).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance lazy_result_timeless t v :
    Timeless (lazy_result t v).
  Proof.
    apply _.
  Qed.

  #[global] Instance lazy_inv_persistent t Ψ Ξ :
    Persistent (lazy_inv t Ψ Ξ).
  Proof.
    apply _.
  Qed.
  #[global] Instance lazy_result_persistent t v :
    Persistent (lazy_result t v).
  Proof.
    apply _.
  Qed.

  Lemma lazy_consumer_wand {t Ψ Ξ Χ1} Χ2 :
    lazy_inv t Ψ Ξ -∗
    lazy_consumer t Χ1 -∗
    (∀ v, Χ1 v -∗ Χ2 v) ={⊤}=∗
    lazy_consumer t Χ2.
  Proof.
    iIntros "(:inv =1) (:consumer =2) H". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iDestruct (base.lazy_consumer_wand with "Hinv_1 Hconsumer_2 H") as "H".
    iSteps.
  Qed.
  Lemma lazy_consumer_divide {t Ψ Ξ} Χs :
    lazy_inv t Ψ Ξ -∗
    lazy_consumer t (λ v, [∗ list] Χ ∈ Χs, Χ v) ={⊤}=∗
    [∗ list] Χ ∈ Χs, lazy_consumer t Χ.
  Proof.
    iIntros "(:inv =1) (:consumer =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iDestruct (base.lazy_consumer_divide with "Hinv_1 Hconsumer_2") as "H".
    iApply (big_sepL_impl with "H").
    iSteps.
  Qed.
  Lemma lazy_consumer_split {t Ψ Ξ} Χ1 Χ2 :
    lazy_inv t Ψ Ξ -∗
    lazy_consumer t (λ v, Χ1 v ∗ Χ2 v) ={⊤}=∗
      lazy_consumer t Χ1 ∗
      lazy_consumer t Χ2.
  Proof.
    iIntros "Hinv Hconsumer".
    iMod (lazy_consumer_divide [Χ1;Χ2] with "Hinv [Hconsumer]") as "($ & $ & _)" => //.
    { simpl. setoid_rewrite bi.sep_emp => //. }
  Qed.

  Lemma lazy_result_agree t v1 v2 :
    lazy_result t v1 -∗
    lazy_result t v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    iIntros "(:result =1) (:result =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.lazy_result_agree with "Hresult_1 Hresult_2").
  Qed.

  Lemma lazy_inv_result t Ψ Ξ v :
    lazy_inv t Ψ Ξ -∗
    lazy_result t v ={⊤}=∗
    ▷ □ Ξ v.
  Proof.
    iIntros "(:inv =1) (:result =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.lazy_inv_result with "Hinv_1 Hresult_2").
  Qed.
  Lemma lazy_inv_result' t Ψ Ξ v :
    £ 1 -∗
    lazy_inv t Ψ Ξ -∗
    lazy_result t v ={⊤}=∗
    □ Ξ v.
  Proof.
    iIntros "H£ Hinv Hresult".
    iMod (lazy_inv_result with "Hinv Hresult") as "HΞ".
    iApply (lc_fupd_elim_later with "H£ HΞ").
  Qed.
  Lemma lazy_inv_result_consumer t Ψ Ξ v Χ :
    lazy_inv t Ψ Ξ -∗
    lazy_result t v -∗
    lazy_consumer t Χ ={⊤}=∗
      ▷^2 Χ v ∗
      ▷ □ Ξ v.
  Proof.
    iIntros "(:inv =1) (:result =2) (:consumer =3)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iDestruct (meta_agree with "Hmeta_2 Hmeta_3") as %<-.
    iApply (base.lazy_inv_result_consumer with "Hinv_1 Hresult_2 Hconsumer_3").
  Qed.
  Lemma lazy_inv_result_consumer' t Ψ Ξ v Χ :
    £ 2 -∗
    lazy_inv t Ψ Ξ -∗
    lazy_result t v -∗
    lazy_consumer t Χ ={⊤}=∗
      Χ v ∗
      □ Ξ v.
  Proof.
    iIntros "(H£1 & H£2) Hinv Hresult Hconsumer".
    iMod (lazy_inv_result_consumer with "Hinv Hresult Hconsumer") as "H".
    rewrite -bi.later_sep.
    iMod (lc_fupd_elim_later with "H£1 H") as "(HΧ & $)".
    iApply (lc_fupd_elim_later with "H£2 HΧ").
  Qed.

  Lemma lazy_make_spec Ψ Ξ fn :
    {{{
      WP fn () {{ v,
        ▷ Ψ v ∗
        ▷ □ Ξ v
      }}
    }}}
      lazy_make fn
    {{{
      t
    , RET t;
      lazy_inv t Ψ Ξ ∗
      lazy_consumer t Ψ
    }}}.
  Proof.
    iIntros "%Φ Hfn HΦ".

    iApply wp_fupd.
    wp_apply (base.lazy_make_spec with "Hfn") as (𝑡 γ) "(Hmeta & Hinv & Hconsumer)".
    iMod (meta_set γ with "Hmeta") as "#Hmeta"; first done.
    iSteps.
  Qed.

  Lemma lazy_return_spec Ψ Ξ v :
    {{{
      ▷ Ψ v ∗
      ▷ □ Ξ v
    }}}
      lazy_return v
    {{{
      t
    , RET t;
      lazy_inv t Ψ Ξ ∗
      lazy_result t v ∗
      lazy_consumer t Ψ
    }}}.
  Proof.
    iIntros "%Φ (HΨ & HΞ) HΦ".

    iApply wp_fupd.
    wp_apply (base.lazy_return_spec Ψ with "[$]") as (𝑡 γ) "(Hmeta & Hinv & Hresult & Hconsumer)".
    iMod (meta_set γ with "Hmeta") as "#Hmeta"; first done.
    iSteps.
  Qed.

  Lemma lazy_is_set_spec t Ψ Ξ :
    {{{
      lazy_inv t Ψ Ξ
    }}}
      lazy_is_set t
    {{{
      b
    , RET #b;
      if b then
        £ 2 ∗
        lazy_resolved t
      else
        True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_apply (base.lazy_is_set_spec with "[$]") as (b) "Hb".
    rewrite /lazy_resolved. destruct b; iSteps.
  Qed.
  Lemma lazy_is_set_spec_result t Ψ Ξ v :
    {{{
      lazy_inv t Ψ Ξ ∗
      lazy_result t v
    }}}
      lazy_is_set t
    {{{
      RET true;
      £ 2
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:result =2)) HΦ". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp_apply (base.lazy_is_set_spec_result with "[$] HΦ").
  Qed.

  Lemma lazy_is_unset_spec t Ψ Ξ :
    {{{
      lazy_inv t Ψ Ξ
    }}}
      lazy_is_unset t
    {{{
      b
    , RET #b;
      if b then
        True
      else
        £ 2 ∗
        lazy_resolved t
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_apply (base.lazy_is_unset_spec with "[$]") as (b) "Hb".
    rewrite /lazy_resolved. destruct b; iSteps.
  Qed.
  Lemma lazy_is_unset_spec_result t Ψ Ξ v :
    {{{
      lazy_inv t Ψ Ξ ∗
      lazy_result t v
    }}}
      lazy_is_unset t
    {{{
      RET false;
      £ 2
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:result =2)) HΦ". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp_apply (base.lazy_is_unset_spec_result with "[$] HΦ").
  Qed.

  Lemma lazy_get_spec t Ψ Ξ :
    {{{
      lazy_inv t Ψ Ξ
    }}}
      lazy_get t
    {{{
      v
    , RET v;
      £ 2 ∗
      lazy_result t v
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_apply (base.lazy_get_spec with "[$]").
    iSteps.
  Qed.
  Lemma lazy_get_spec_result t Ψ Ξ v :
    {{{
      lazy_inv t Ψ Ξ ∗
      lazy_result t v
    }}}
      lazy_get t
    {{{
      RET v;
      £ 2
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:result =2)) HΦ". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp_apply (base.lazy_get_spec_result with "[$] HΦ").
  Qed.
End lazy_G.

#[global] Opaque lazy_inv.
#[global] Opaque lazy_consumer.
#[global] Opaque lazy_result.
