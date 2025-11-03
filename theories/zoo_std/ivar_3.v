From zoo Require Import
  prelude.
From zoo.common Require Import
  countable.
From zoo.iris.bi Require Import
  big_op.
From zoo.iris.base_logic Require Import
  lib.mono_gmultiset
  lib.oneshot
  lib.subpreds.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
  base
  ivar_3__code.
From zoo_std Require Import
  ivar_3__types
  option
  lst.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types v waiter : val.
Implicit Types waiters : list val.
Implicit Types own : ownership.

Class Ivar3G Σ `{zoo_G : !ZooG Σ} waiter_name `{Countable waiter_name} := {
  #[local] ivar_3_G_lstate_G :: OneshotG Σ unit val ;
  #[local] ivar_3_G_consumer_G :: SubpredsG Σ val ;
  #[local] ivar_3_G_waiters_G :: MonoGmultisetG Σ (val * waiter_name) ;
}.

Definition ivar_3_Σ waiter_name `{Countable waiter_name} := #[
  oneshot_Σ unit val ;
  subpreds_Σ val ;
  mono_gmultiset_Σ (val * waiter_name)
].
#[global] Instance subG_ivar_3_Σ Σ `{zoo_G : !ZooG Σ} waiter_name `{Countable waiter_name} :
  subG (ivar_3_Σ waiter_name) Σ →
  Ivar3G Σ waiter_name.
Proof.
  solve_inG.
Qed.

Module base.
  Inductive state :=
    | Unset waiters
    | Set_ v.
  Implicit Types state : state.

  #[local] Instance state_inhabited : Inhabited state :=
    populate (Unset []).

  #[local] Definition state_to_bool state :=
    match state with
    | Unset _ =>
        false
    | Set_ _ =>
        true
    end.
  #[local] Definition state_to_option state :=
    match state with
    | Unset _ =>
        None
    | Set_ v =>
        Some v
    end.
  #[local] Coercion state_to_val state :=
    match state with
    | Unset waiters =>
        ‘Unset[ lst_to_val waiters ]
    | Set_ v =>
        ‘Set( v )
    end%V.

  Section ivar_3_G.
    Context `{ivar_3_G : Ivar3G Σ waiter_name}.

    Implicit Types t : location.
    Implicit Types ω : waiter_name.
    Implicit Types ωs : list waiter_name.
    Implicit Types Ψ Χ Ξ : val → iProp Σ.
    Implicit Types Ω : val → val → waiter_name → iProp Σ.

    Record ivar_3_name := {
      ivar_3_name_lstate : gname ;
      ivar_3_name_consumer : gname ;
      ivar_3_name_waiters : gname ;
    }.
    Implicit Types γ : ivar_3_name.

    #[global] Instance ivar_3_name_eq_dec : EqDecision ivar_3_name :=
      ltac:(solve_decision).
    #[global] Instance ivar_3_name_countable :
      Countable ivar_3_name.
    Proof.
      solve_countable.
    Qed.

    #[local] Definition lstate_unset₁' γ_lstate :=
      oneshot_pending γ_lstate (DfracOwn (1/3)) ().
    #[local] Definition lstate_unset₁ γ :=
      lstate_unset₁' γ.(ivar_3_name_lstate).
    #[local] Definition lstate_unset₂' γ_lstate :=
      oneshot_pending γ_lstate (DfracOwn (2/3)) ().
    #[local] Definition lstate_unset₂ γ :=
      lstate_unset₂' γ.(ivar_3_name_lstate).
    #[local] Definition lstate_set γ :=
      oneshot_shot γ.(ivar_3_name_lstate).

    #[local] Definition consumer_auth' :=
      subpreds_auth.
    #[local] Definition consumer_auth γ :=
      consumer_auth' γ.(ivar_3_name_consumer).
    #[local] Definition consumer_frag' :=
      subpreds_frag.
    #[local] Definition consumer_frag γ :=
      consumer_frag' γ.(ivar_3_name_consumer).

    #[local] Definition waiters_auth' γ_waiters own waiters ωs : iProp Σ :=
      ∃ 𝑤𝑎𝑖𝑡𝑒𝑟𝑠,
      ⌜𝑤𝑎𝑖𝑡𝑒𝑟𝑠 = list_to_set_disj (zip waiters ωs)⌝ ∗
      mono_gmultiset_auth γ_waiters own 𝑤𝑎𝑖𝑡𝑒𝑟𝑠.
    #[local] Definition waiters_auth γ :=
      waiters_auth' γ.(ivar_3_name_waiters).
    #[local] Instance : CustomIpatFormat "waiters_auth" :=
      " ( %𝑤𝑎𝑖𝑡𝑒𝑟𝑠 &
          -> &
          Hauth
        )
      ".
    #[local] Definition waiters_elem γ waiter ω :=
      mono_gmultiset_elem γ.(ivar_3_name_waiters) (waiter, ω).

    #[local] Definition inv_state_unset t γ Ω waiters : iProp Σ :=
      ∃ ωs,
      lstate_unset₁ γ ∗
      waiters_auth γ Own waiters ωs ∗
      [∗ list] waiter; ω ∈ waiters; ωs, Ω #t waiter ω.
    #[local] Instance : CustomIpatFormat "inv_state_unset" :=
      " ( %ωs &
          {>;}Hlstate_unset₁ &
          {>;}Hwaiters_auth &
          Hwaiters
        )
      ".
    #[local] Definition inv_state_set γ Ξ v : iProp Σ :=
      lstate_set γ v ∗
      □ Ξ v.
    #[local] Instance : CustomIpatFormat "inv_state_set" :=
      " ( {>;}#Hlstate_set{_{}} &
          #HΞ{_{}}
        )
      ".
    #[local] Definition inv_state t γ Ξ Ω state :=
      match state with
      | Unset waiters =>
          inv_state_unset t γ Ω waiters
      | Set_ v =>
          inv_state_set γ Ξ v
      end.

    #[local] Definition inv_inner t γ Ψ Ξ Ω : iProp Σ :=
      ∃ state,
      t.[contents] ↦ state ∗
      consumer_auth γ Ψ (state_to_option state) ∗
      inv_state t γ Ξ Ω state.
    #[local] Instance : CustomIpatFormat "inv_inner" :=
      " ( %state &
          Ht &
          Hconsumer_auth &
          Hstate
        )
      ".
    Definition ivar_3_inv t γ Ψ Ξ Ω : iProp Σ :=
      inv nroot (inv_inner t γ Ψ Ξ Ω).
    #[local] Instance : CustomIpatFormat "inv" :=
      " #Hinv
      ".

    Definition ivar_3_producer :=
      lstate_unset₂.
    #[local] Instance : CustomIpatFormat "producer" :=
      " Hlstate_unset₂{_{}}
      ".

    Definition ivar_3_consumer :=
      consumer_frag.
    #[local] Instance : CustomIpatFormat "consumer" :=
      " Hconsumer{}_frag
      ".

    Definition ivar_3_result :=
      lstate_set.
    #[local] Instance : CustomIpatFormat "result" :=
      " #Hlstate_set{_{}}
      ".
    Definition ivar_3_resolved γ : iProp Σ :=
      ∃ v,
      ivar_3_result γ v.

    Definition ivar_3_waiters γ :=
      waiters_auth γ Discard.

    Definition ivar_3_waiter :=
      waiters_elem.

    #[global] Instance ivar_3_inv_contractive t γ n :
      Proper (
        (pointwise_relation _ $ dist_later n) ==>
        (pointwise_relation _ $ dist_later n) ==>
        (pointwise_relation _ $ pointwise_relation _ $ pointwise_relation _ $ dist_later n) ==>
        (≡{n}≡)
      ) (ivar_3_inv t γ).
    Proof.
      rewrite /ivar_3_inv /inv_inner /inv_state /inv_state_unset /inv_state_set.
      intros Ψ1 Ψ2 HΨ Ξ1 Ξ2 HΞ Ω1 Ω2 HΩ.
      repeat (apply HΩ || f_contractive || f_equiv). done.
    Qed.
    #[global] Instance ivar_3_inv_proper t γ :
      Proper (
        (pointwise_relation _ (≡)) ==>
        (pointwise_relation _ (≡)) ==>
        (pointwise_relation _ $ pointwise_relation _ $ pointwise_relation _ (≡)) ==>
        (≡)
      ) (ivar_3_inv t γ).
    Proof.
      intros Ψ1 Ψ2 HΨ Ξ1 Ξ2 HΞ Ω1 Ω2 HΩ.
      apply equiv_dist => n.
      apply ivar_3_inv_contractive.
      - intros v.
        apply dist_dist_later, equiv_dist, HΨ.
      - intros v.
        apply dist_dist_later, equiv_dist, HΞ.
      - clear t. intros t waiter ω.
        apply dist_dist_later, equiv_dist, HΩ.
    Qed.
    #[global] Instance ivar_3_consumer_contractive γ n :
      Proper (
        (pointwise_relation _ $ dist_later n) ==>
        (≡{n}≡)
      ) (ivar_3_consumer γ).
    Proof.
      apply _.
    Qed.
    #[global] Instance ivar_3_consumer_proper γ :
      Proper (
        (pointwise_relation _ (≡)) ==>
        (≡)
      ) (ivar_3_consumer γ).
    Proof.
      apply _.
    Qed.

    #[local] Instance waiters_auth_timeless γ own waiters ωs :
      Timeless (waiters_auth γ own waiters ωs).
    Proof.
      apply _.
    Qed.
    #[global] Instance ivar_3_producer_timeless γ :
      Timeless (ivar_3_producer γ).
    Proof.
      apply _.
    Qed.
    #[global] Instance ivar_3_result_timeless γ v :
      Timeless (ivar_3_result γ v).
    Proof.
      apply _.
    Qed.
    #[global] Instance ivar_3_waiters_timeless γ waiters ωs :
      Timeless (ivar_3_waiters γ waiters ωs).
    Proof.
      apply _.
    Qed.
    #[global] Instance ivar_3_waiter_timeless γ waiter ω :
      Timeless (ivar_3_waiter γ waiter ω).
    Proof.
      apply _.
    Qed.

    #[global] Instance ivar_3_inv_persistent t γ Ψ Ξ Ω :
      Persistent (ivar_3_inv t γ Ψ Ξ Ω).
    Proof.
      apply _.
    Qed.
    #[global] Instance ivar_3_result_persistent γ v :
      Persistent (ivar_3_result γ v).
    Proof.
      apply _.
    Qed.
    #[global] Instance ivar_3_waiters_persistent γ waiters ωs :
      Persistent (ivar_3_waiters γ waiters ωs).
    Proof.
      apply _.
    Qed.
    #[global] Instance ivar_3_waiter_persistent γ waiter ω :
      Persistent (ivar_3_waiter γ waiter ω).
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
    #[local] Lemma consumer_divide {γ Ψ} {state : option val} {Χ} Χs E :
      ▷ consumer_auth γ Ψ state -∗
      consumer_frag γ Χ -∗
      (∀ v, Χ v -∗ [∗ list] Χ ∈ Χs, Χ v) ={E}=∗
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

    #[local] Lemma waiters_alloc :
      ⊢ |==>
        ∃ γ_waiters,
        waiters_auth' γ_waiters Own [] [].
    Proof.
      iMod (mono_gmultiset_alloc ∅) as "(%γ_waiters & $)".
      iSteps.
    Qed.
    #[local] Lemma waiters_elem_valid γ own waiters ωs waiter ω :
      waiters_auth γ own waiters ωs -∗
      waiters_elem γ waiter ω -∗
        ∃ i,
        ⌜waiters !! i = Some waiter⌝ ∗
        ⌜ωs !! i = Some ω⌝.
    Proof.
      iIntros "(:waiters_auth) Helem".
      iDestruct (mono_gmultiset_elem_valid with "Hauth Helem") as %(i & (Hwaiters_lookup & Hωs_lookup)%lookup_zip_Some)%elem_of_list_to_set_disj%elem_of_list_lookup.
      iSteps.
    Qed.
    #[local] Lemma waiters_insert {γ waiters ωs} waiter ω :
      waiters_auth γ Own waiters ωs ⊢ |==>
        waiters_auth γ Own (waiter :: waiters) (ω :: ωs) ∗
        waiters_elem γ waiter ω.
    Proof.
      iIntros "(:waiters_auth)".
      iMod (mono_gmultiset_insert' (waiter, ω) with "Hauth") as "($ & $)".
      iSteps.
    Qed.
    #[local] Lemma waiters_auth_discard γ waiters ωs :
      waiters_auth γ Own waiters ωs ⊢ |==>
      waiters_auth γ Discard waiters ωs.
    Proof.
      iIntros "(:waiters_auth)".
      iMod (mono_gmultiset_auth_persist with "Hauth") as "$".
      iSteps.
    Qed.
    Opaque waiters_auth'.

    Lemma ivar_3_producer_exclusive γ :
      ivar_3_producer γ -∗
      ivar_3_producer γ -∗
      False.
    Proof.
      iIntros "(:producer =1) (:producer =2)".
      iApply (lstate_unset₂_exclusive with "Hlstate_unset₂_1 Hlstate_unset₂_2").
    Qed.

    Lemma ivar_3_consumer_divide {t γ Ψ Ξ Ω Χ} Χs :
      ivar_3_inv t γ Ψ Ξ Ω -∗
      ivar_3_consumer γ Χ -∗
      (∀ v, Χ v -∗ [∗ list] Χ ∈ Χs, Χ v) ={⊤}=∗
      [∗ list] Χ ∈ Χs, ivar_3_consumer γ Χ.
    Proof.
      iIntros "(:inv) (:consumer) H".
      iInv "Hinv" as "(:inv_inner)".
      iMod (consumer_divide with "Hconsumer_auth Hconsumer_frag H") as "(Hconsumer_auth & H)".
      iSplitR "H". { iFrameSteps. }
      iApply (big_sepL_impl with "H").
      iSteps.
    Qed.

    Lemma ivar_3_result_agree γ v1 v2 :
      ivar_3_result γ v1 -∗
      ivar_3_result γ v2 -∗
      ⌜v1 = v2⌝.
    Proof.
      iIntros "(:result =1) (:result =2)".
      iApply (lstate_set_agree with "Hlstate_set_1 Hlstate_set_2").
    Qed.

    Lemma ivar_3_producer_result γ v :
      ivar_3_producer γ -∗
      ivar_3_result γ v -∗
      False.
    Proof.
      iIntros "(:producer =1) (:result =2)".
      iApply (lstate_unset₂_set with "Hlstate_unset₂_1 Hlstate_set_2").
    Qed.

    Lemma ivar_3_inv_result t γ Ψ Ξ Ω v :
      ivar_3_inv t γ Ψ Ξ Ω -∗
      ivar_3_result γ v ={⊤}=∗
      ▷ □ Ξ v.
    Proof.
      iIntros "(:inv) (:result)".
      iInv "Hinv" as "(:inv_inner)".
      destruct state as [waiters | v_].
      { iDestruct "Hstate" as "(:inv_state_unset >)".
        iDestruct (lstate_unset₁_set with "Hlstate_unset₁ Hlstate_set") as %[].
      }
      iDestruct "Hstate" as "(:inv_state_set =1 >)".
      iDestruct (lstate_set_agree with "Hlstate_set Hlstate_set_1") as %<-.
      iSplitL. { iFrameSteps. }
      iSteps.
    Qed.
    Lemma ivar_3_inv_result_consumer t γ Ψ Ξ Ω v Χ :
      ivar_3_inv t γ Ψ Ξ Ω -∗
      ivar_3_result γ v -∗
      ivar_3_consumer γ Χ ={⊤}=∗
        ▷^2 Χ v ∗
        ▷ □ Ξ v.
    Proof.
      iIntros "(:inv) (:result) (:consumer)".
      iInv "Hinv" as "(:inv_inner)".
      destruct state as [v_ |].
      { iDestruct "Hstate" as "(:inv_state_unset >)".
        iDestruct (lstate_unset₁_set with "Hlstate_unset₁ Hlstate_set") as %[].
      }
      iDestruct "Hstate" as "(:inv_state_set =1 >)".
      iDestruct (lstate_set_agree with "Hlstate_set Hlstate_set_1") as %<-.
      iMod (consumer_consume with "Hconsumer_auth Hconsumer_frag") as "(Hconsumer_auth & HΧ)".
      iSplitR "HΧ". { iFrameSteps. }
      iSteps.
    Qed.

    Lemma ivar_3_waiter_valid γ waiters ωs waiter ω :
      ivar_3_waiters γ waiters ωs -∗
      ivar_3_waiter γ waiter ω -∗
        ∃ i,
        ⌜waiters !! i = Some waiter⌝ ∗
        ⌜ωs !! i = Some ω⌝.
    Proof.
      apply waiters_elem_valid.
    Qed.

    Lemma ivar_3_create_spec Ψ Ξ Ω :
      {{{
        True
      }}}
        ivar_3_create ()
      {{{ t γ,
        RET #t;
        meta_token t ⊤ ∗
        ivar_3_inv t γ Ψ Ξ Ω ∗
        ivar_3_producer γ ∗
        ivar_3_consumer γ Ψ
      }}}.
    Proof.
      iIntros "%Φ _ HΦ".

      wp_rec.
      wp_ref t as "Hmeta" "Ht".

      iMod lstate_alloc as "(%γ_lstate & Hlstate_unset₁ & Hlstate_unset₂)".
      iMod consumer_alloc as "(%γ_consumer & Hconsumer_auth & Hconsumer_frag)".
      iMod waiters_alloc as "(%γ_waiters & Hwaiters_auth)".

      pose γ := {|
        ivar_3_name_lstate := γ_lstate ;
        ivar_3_name_consumer := γ_consumer ;
        ivar_3_name_waiters := γ_waiters ;
      |}.

      iApply ("HΦ" $! t γ).
      iFrame.
      iApply inv_alloc.
      iSteps. iExists (Unset []). iSteps.
      iApply (big_sepL2_nil with "[//]").
    Qed.

    Lemma ivar_3_make_spec Ψ Ξ Ω v :
      {{{
        ▷ Ψ v ∗
        ▷ □ Ξ v
      }}}
        ivar_3_make v
      {{{ t γ,
        RET #t;
        meta_token t ⊤ ∗
        ivar_3_inv t γ Ψ Ξ Ω ∗
        ivar_3_consumer γ Ψ ∗
        ivar_3_result γ v ∗
        ivar_3_waiters γ [] []
      }}}.
    Proof.
      iIntros "%Φ (HΨ & #HΞ) HΦ".

      wp_rec.
      wp_ref t as "Hmeta" "Ht".

      iMod lstate_alloc as "(%γ_lstate & Hlstate_unset₁ & Hlstate_unset₂)".
      iMod consumer_alloc as "(%γ_consumer & Hconsumer_auth & Hconsumer_frag)".
      iMod waiters_alloc as "(%γ_waiters & Hwaiters_auth)".

      pose γ := {|
        ivar_3_name_lstate := γ_lstate ;
        ivar_3_name_consumer := γ_consumer ;
        ivar_3_name_waiters := γ_waiters ;
      |}.

      iMod (lstate_update (γ := γ) v with "Hlstate_unset₁ Hlstate_unset₂") as "#Hlstate_set".
      iDestruct (consumer_produce (γ := γ) v with "Hconsumer_auth HΨ") as "Hconsumer_auth".
      iMod (waiters_auth_discard γ with "Hwaiters_auth") as "#Hwaiters_auth".

      iApply ("HΦ" $! t γ).
      iFrameSteps. iExists (Set_ v). iSteps.
    Qed.

    Lemma ivar_3_is_set_spec t γ Ψ Ξ Ω :
      {{{
        ivar_3_inv t γ Ψ Ξ Ω
      }}}
        ivar_3_is_set #t
      {{{ b,
        RET #b;
        if b then
          £ 2 ∗
          ivar_3_resolved γ
        else
          True
      }}}.
    Proof.
      iIntros "%Φ (:inv) HΦ".

      wp_rec credits:"H£".
      iDestruct (lc_weaken 2 with "H£") as "H£"; first done.

      wp_bind (!_)%E.
      iInv "Hinv" as "(:inv_inner)".
      wp_load.
      iSpecialize ("HΦ" $! (state_to_bool state)).
      destruct state as [waiters | v].

      - iSplitR "HΦ". { iFrameSteps. }
        iSteps.

      - iDestruct "Hstate" as "(:inv_state_set)".
        iSplitR "H£ HΦ". { iFrameSteps. }
        iStep 5. iExists v. iSteps.
    Qed.
    Lemma ivar_3_is_set_spec_result t γ Ψ Ξ Ω v :
      {{{
        ivar_3_inv t γ Ψ Ξ Ω ∗
        ivar_3_result γ v
      }}}
        ivar_3_is_set #t
      {{{
        RET #true;
        £ 2
      }}}.
    Proof.
      iIntros "%Φ ((:inv) & (:result)) HΦ".

      wp_rec credits:"H£".
      iDestruct (lc_weaken 2 with "H£") as "H£"; first done.

      wp_bind (!_)%E.
      iInv "Hinv" as "(:inv_inner)".
      wp_load.
      destruct state as [waiters | v_].
      { iDestruct "Hstate" as "(:inv_state_unset)".
        iDestruct (lstate_unset₁_set with "Hlstate_unset₁ Hlstate_set") as %[].
      }
      iDestruct "Hstate" as "(:inv_state_set =1)".
      iDestruct (lstate_set_agree with "Hlstate_set Hlstate_set_1") as %<-. iClear "Hlstate_set_1".
      iSplitR "H£ HΦ". { iFrameSteps. }
      iSteps.
    Qed.

    Lemma ivar_3_try_get_spec t γ Ψ Ξ Ω :
      {{{
        ivar_3_inv t γ Ψ Ξ Ω
      }}}
        ivar_3_try_get #t
      {{{ o,
        RET o : val;
        if o is Some v then
          £ 2 ∗
          ivar_3_result γ v
        else
          True
      }}}.
    Proof.
      iIntros "%Φ (:inv) HΦ".

      wp_rec credits:"H£".
      iDestruct (lc_weaken 2 with "H£") as "H£"; first done.

      wp_bind (!_)%E.
      iInv "Hinv" as "(:inv_inner)".
      wp_load.
      iSpecialize ("HΦ" $! (state_to_option state)).
      destruct state as [waiters | v].

      - iSplitR "HΦ". { iFrameSteps. }
        iSteps.

      - iDestruct "Hstate" as "(:inv_state_set)".
        iSplitR "H£ HΦ". { iFrameSteps. }
        iSteps.
    Qed.
    Lemma ivar_3_try_get_spec_result t γ Ψ Ξ Ω v :
      {{{
        ivar_3_inv t γ Ψ Ξ Ω ∗
        ivar_3_result γ v
      }}}
        ivar_3_try_get #t
      {{{
        RET Some v : val;
        £ 2
      }}}.
    Proof.
      iIntros "%Φ ((:inv) & (:result)) HΦ".

      wp_rec credits:"H£".
      iDestruct (lc_weaken 2 with "H£") as "H£"; first done.

      wp_bind (!_)%E.
      iInv "Hinv" as "(:inv_inner)".
      wp_load.
      destruct state as [waiters | v_].
      { iDestruct "Hstate" as "(:inv_state_unset)".
        iDestruct (lstate_unset₁_set with "Hlstate_unset₁ Hlstate_set") as %[].
      }
      iDestruct "Hstate" as "(:inv_state_set =1)".
      iDestruct (lstate_set_agree with "Hlstate_set Hlstate_set_1") as %<-. iClear "Hlstate_set_1".
      iSplitR "H£ HΦ". { iFrameSteps. }
      iSteps.
    Qed.

    Lemma ivar_3_get_spec t γ Ψ Ξ Ω v :
      {{{
        ivar_3_inv t γ Ψ Ξ Ω ∗
        ivar_3_result γ v
      }}}
        ivar_3_get #t
      {{{
        RET v;
        £ 2
      }}}.
    Proof.
      iIntros "%Φ ((:inv) & (:result)) HΦ".

      wp_rec credits:"H£".
      iDestruct (lc_weaken 2 with "H£") as "H£"; first done.

      wp_bind (!_)%E.
      iInv "Hinv" as "(:inv_inner)".
      wp_load.
      destruct state as [waiters | v_].
      { iDestruct "Hstate" as "(:inv_state_unset)".
        iDestruct (lstate_unset₁_set with "Hlstate_unset₁ Hlstate_set") as %[].
      }
      iDestruct "Hstate" as "(:inv_state_set =1)".
      iDestruct (lstate_set_agree with "Hlstate_set Hlstate_set_1") as %<-. iClear "Hlstate_set_1".
      iSplitR "H£ HΦ". { iFrameSteps. }
      iSteps.
    Qed.

    Lemma ivar_3_wait_spec {t γ Ψ Ξ Ω waiter} ω :
      {{{
        ivar_3_inv t γ Ψ Ξ Ω ∗
        ▷ Ω #t waiter ω
      }}}
        ivar_3_wait #t waiter
      {{{ o,
        RET o : val;
        if o is Some v then
          £ 2 ∗
          ivar_3_result γ v ∗
          Ω #t waiter ω
        else
          ivar_3_waiter γ waiter ω
      }}}.
    Proof.
      iIntros "%Φ ((:inv) & Hwaiter) HΦ".
      iLöb as "HLöb".

      wp_rec credits:"H£". wp_pures.
      iDestruct (lc_weaken 2 with "H£") as "H£"; first done.

      wp_bind (!_)%E.
      iInv "Hinv" as "(:inv_inner)".
      wp_load.
      destruct state as [waiters | v].

      - iSplitR "Hwaiter H£ HΦ". { iFrameSteps. }
        iModIntro.

        wp_pures.

        wp_bind (CAS _ _ _).
        iInv "Hinv" as "(:inv_inner)".
        wp_cas as Hcas.

        + iSplitR "Hwaiter HΦ". { iFrameSteps. }
          iModIntro.

          wp_smart_apply ("HLöb" with "Hwaiter HΦ").

        + destruct state as [waiters' | v]; zoo_simplify.
          iDestruct "Hstate" as "(:inv_state_unset)".
          iMod (waiters_insert waiter with "Hwaiters_auth") as "(Hwaiters_auth & #Hwaiters_elem)".
          iDestruct (big_sepL2_cons_2' _ waiter ω with "[Hwaiter H£] Hwaiters") as "Hwaiters"; first iSteps.
          iSplitR "HΦ". { iExists (Unset (waiter :: waiters)). iFrameSteps. }
          iSpecialize ("HΦ" $! None).
          iSteps.

      - iDestruct "Hstate" as "(:inv_state_set)".
        iSplitR "H£ Hwaiter HΦ". { iFrameSteps. }
        iSpecialize ("HΦ" $! (Some v)).
        iSteps.
    Qed.

    Lemma ivar_3_set_spec t γ Ψ Ξ Ω v :
      {{{
        ivar_3_inv t γ Ψ Ξ Ω ∗
        ivar_3_producer γ ∗
        ▷ Ψ v ∗
        ▷ □ Ξ v
      }}}
        ivar_3_set #t v
      {{{ waiters ωs,
        RET lst_to_val waiters;
        ivar_3_result γ v ∗
        ivar_3_waiters γ waiters ωs ∗
        [∗ list] waiter; ω ∈ waiters; ωs, Ω #t waiter ω
      }}}.
    Proof.
      iIntros "%Φ ((:inv) & (:producer) & HΨ & #HΞ) HΦ".

      wp_rec. wp_pures.

      wp_bind (Xchg _ _).
      iInv "Hinv" as "(:inv_inner)".
      wp_xchg.
      destruct state; last first.
      { iDestruct "Hstate" as "(:inv_state_set =1)".
        iDestruct (lstate_unset₂_set with "Hlstate_unset₂ Hlstate_set_1") as %[].
      }
      iDestruct "Hstate" as "(:inv_state_unset)".
      iMod (lstate_update with "Hlstate_unset₁ Hlstate_unset₂") as "#Hlstate_set".
      iDestruct (consumer_produce with "Hconsumer_auth HΨ") as "Hconsumer_auth".
      iMod (waiters_auth_discard with "Hwaiters_auth") as "#Hwaiters_auth".
      iSplitR "Hwaiters HΦ". { iExists (Set_ v). iSteps. }
      iSteps.
    Qed.
  End ivar_3_G.

  #[global] Opaque ivar_3_inv.
  #[global] Opaque ivar_3_producer.
  #[global] Opaque ivar_3_consumer.
  #[global] Opaque ivar_3_result.
  #[global] Opaque ivar_3_waiter.
  #[global] Opaque ivar_3_waiters.
End base.

From zoo_std Require
  ivar_3__opaque.

Section ivar_3_G.
  Context `{ivar_3_G : Ivar3G Σ waiter_name}.

  Implicit Types 𝑡 : location.
  Implicit Types t : val.
  Implicit Types Ψ Χ Ξ : val → iProp Σ.
  Implicit Types Ω : val → val → waiter_name → iProp Σ.

  Definition ivar_3_inv t Ψ Ξ Ω : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.ivar_3_inv 𝑡 γ Ψ Ξ Ω.
  #[local] Instance : CustomIpatFormat "inv" :=
    " ( %𝑡{} &
        %γ{} &
        {%Heq{};->} &
        #Hmeta{_{}} &
        Hinv{_{}}
      )
    ".

  Definition ivar_3_producer t : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.ivar_3_producer γ.
  #[local] Instance : CustomIpatFormat "producer" :=
    " ( %𝑡{} &
        %γ{} &
        {%Heq{};->} &
        #Hmeta{_{}} &
        Hproducer{_{}}
      )
    ".

  Definition ivar_3_consumer t Χ : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.ivar_3_consumer γ Χ.
  #[local] Instance : CustomIpatFormat "consumer" :=
    " ( %𝑡{} &
        %γ{} &
        {%Heq{};->} &
        #Hmeta{_{}} &
        Hconsumer{_{}}
      )
    ".

  Definition ivar_3_result t v : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.ivar_3_result γ v.
  #[local] Instance : CustomIpatFormat "result" :=
    " ( %𝑡{} &
        %γ{} &
        {%Heq{};->} &
        #Hmeta{_{}} &
        Hresult{_{}}
      )
    ".
  Definition ivar_3_resolved t : iProp Σ :=
    ∃ v,
    ivar_3_result t v.

  Definition ivar_3_waiters t waiters ωs : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.ivar_3_waiters γ waiters ωs.
  #[local] Instance : CustomIpatFormat "waiters" :=
    " ( %𝑡{} &
        %γ{} &
        {%Heq{};->} &
        #Hmeta{_{}} &
        Hwaiters{_{}}
      )
    ".

  Definition ivar_3_waiter t waiter ω : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.ivar_3_waiter γ waiter ω.
  #[local] Instance : CustomIpatFormat "waiter" :=
    " ( %𝑡{} &
        %γ{} &
        {%Heq{};->} &
        #Hmeta{_{}} &
        Hwaiter{_{}}
      )
    ".

  #[global] Instance ivar_3_inv_contractive t n :
    Proper (
      (pointwise_relation _ $ dist_later n) ==>
      (pointwise_relation _ $ dist_later n) ==>
      (pointwise_relation _ $ pointwise_relation _ $ pointwise_relation _ $ dist_later n) ==>
      (≡{n}≡)
    ) (ivar_3_inv t).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance ivar_3_inv_proper t :
    Proper (
      (pointwise_relation _ (≡)) ==>
      (pointwise_relation _ (≡)) ==>
      (pointwise_relation _ $ pointwise_relation _ $ pointwise_relation _ (≡)) ==>
      (≡)
    ) (ivar_3_inv t).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance ivar_3_consumer_contractive t n :
    Proper (
      (pointwise_relation _ $ dist_later n) ==>
      (≡{n}≡)
    ) (ivar_3_consumer t).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance ivar_3_consumer_proper t :
    Proper (
      (pointwise_relation _ (≡)) ==>
      (≡)
    ) (ivar_3_consumer t).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance ivar_3_producer_timeless t :
    Timeless (ivar_3_producer t).
  Proof.
    apply _.
  Qed.
  #[global] Instance ivar_3_result_timeless t v :
    Timeless (ivar_3_result t v).
  Proof.
    apply _.
  Qed.
  #[global] Instance ivar_3_waiters_timeless t waiters ωs :
    Timeless (ivar_3_waiters t waiters ωs).
  Proof.
    apply _.
  Qed.
  #[global] Instance ivar_3_waiter_timeless t waiter ω :
    Timeless (ivar_3_waiter t waiter ω).
  Proof.
    apply _.
  Qed.

  #[global] Instance ivar_3_inv_persistent t Ψ Ξ Ω :
    Persistent (ivar_3_inv t Ψ Ξ Ω).
  Proof.
    apply _.
  Qed.
  #[global] Instance ivar_3_result_persistent t v :
    Persistent (ivar_3_result t v).
  Proof.
    apply _.
  Qed.
  #[global] Instance ivar_3_waiters_persistent t waiters ωs :
    Persistent (ivar_3_waiters t waiters ωs).
  Proof.
    apply _.
  Qed.
  #[global] Instance ivar_3_waiter_persistent t waiter ω :
    Persistent (ivar_3_waiter t waiter ω).
  Proof.
    apply _.
  Qed.

  Lemma ivar_3_producer_exclusive t :
    ivar_3_producer t -∗
    ivar_3_producer t -∗
    False.
  Proof.
    iIntros "(:producer =1) (:producer =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.ivar_3_producer_exclusive with "Hproducer_1 Hproducer_2").
  Qed.

  Lemma ivar_3_consumer_divide {t Ψ Ξ Ω Χ} Χs :
    ivar_3_inv t Ψ Ξ Ω -∗
    ivar_3_consumer t Χ -∗
    (∀ v, Χ v -∗ [∗ list] Χ ∈ Χs, Χ v) ={⊤}=∗
    [∗ list] Χ ∈ Χs, ivar_3_consumer t Χ.
  Proof.
    iIntros "(:inv =1) (:consumer =2) H". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iDestruct (base.ivar_3_consumer_divide with "Hinv_1 Hconsumer_2 H") as "H".
    iApply (big_sepL_impl with "H").
    iSteps.
  Qed.
  Lemma ivar_3_consumer_split {t Ψ Ξ Ω Χ} Χ1 Χ2 :
    ivar_3_inv t Ψ Ξ Ω -∗
    ivar_3_consumer t Χ -∗
    (∀ v, Χ v -∗ Χ1 v ∗ Χ2 v) ={⊤}=∗
      ivar_3_consumer t Χ1 ∗
      ivar_3_consumer t Χ2.
  Proof.
    iIntros "#Hinv Hconsumer H".
    iMod (ivar_3_consumer_divide [Χ1;Χ2] with "Hinv Hconsumer [H]") as "($ & $ & _)"; iSteps.
  Qed.

  Lemma ivar_3_result_agree t v1 v2 :
    ivar_3_result t v1 -∗
    ivar_3_result t v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    iIntros "(:result =1) (:result =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.ivar_3_result_agree with "Hresult_1 Hresult_2").
  Qed.

  Lemma ivar_3_producer_result t v :
    ivar_3_producer t -∗
    ivar_3_result t v -∗
    False.
  Proof.
    iIntros "(:producer =1) (:result =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.ivar_3_producer_result with "Hproducer_1 Hresult_2").
  Qed.

  Lemma ivar_3_inv_result t Ψ Ξ Ω v :
    ivar_3_inv t Ψ Ξ Ω -∗
    ivar_3_result t v ={⊤}=∗
    ▷ □ Ξ v.
  Proof.
    iIntros "(:inv =1) (:result =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %<-.
    iApply (base.ivar_3_inv_result with "Hinv_1 Hresult_2").
  Qed.
  Lemma ivar_3_inv_result' t Ψ Ξ Ω v :
    £ 1 -∗
    ivar_3_inv t Ψ Ξ Ω -∗
    ivar_3_result t v ={⊤}=∗
    □ Ξ v.
  Proof.
    iIntros "H£ Hinv Hresult".
    iMod (ivar_3_inv_result with "Hinv Hresult") as "HΞ".
    iApply (lc_fupd_elim_later with "H£ HΞ").
  Qed.
  Lemma ivar_3_inv_result_consumer t Ψ Ξ Ω v Χ :
    ivar_3_inv t Ψ Ξ Ω -∗
    ivar_3_result t v -∗
    ivar_3_consumer t Χ ={⊤}=∗
      ▷^2 Χ v ∗
      ▷ □ Ξ v.
  Proof.
    iIntros "(:inv =1) (:result =2) (:consumer =3)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iDestruct (meta_agree with "Hmeta_2 Hmeta_3") as %<-.
    iApply (base.ivar_3_inv_result_consumer with "Hinv_1 Hresult_2 Hconsumer_3").
  Qed.
  Lemma ivar_3_inv_result_consumer' t Ψ Ξ Ω v Χ :
    £ 2 -∗
    ivar_3_inv t Ψ Ξ Ω -∗
    ivar_3_result t v -∗
    ivar_3_consumer t Χ ={⊤}=∗
      Χ v ∗
      □ Ξ v.
  Proof.
    iIntros "(H£1 & H£2) Hinv Hresult Hconsumer".
    iMod (ivar_3_inv_result_consumer with "Hinv Hresult Hconsumer") as "H".
    rewrite -bi.later_sep.
    iMod (lc_fupd_elim_later with "H£1 H") as "(HΧ & $)".
    iApply (lc_fupd_elim_later with "H£2 HΧ").
  Qed.

  Lemma ivar_3_waiter_valid t waiters ωs waiter ω :
    ivar_3_waiters t waiters ωs -∗
    ivar_3_waiter t waiter ω -∗
      ∃ i,
      ⌜waiters !! i = Some waiter⌝ ∗
      ⌜ωs !! i = Some ω⌝.
  Proof.
    iIntros "(:waiters =1) (:waiter =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.ivar_3_waiter_valid with "Hwaiters_1 Hwaiter_2").
  Qed.

  Lemma ivar_3_create_spec Ψ Ξ Ω :
    {{{
      True
    }}}
      ivar_3_create ()
    {{{ t,
      RET t;
      ivar_3_inv t Ψ Ξ Ω ∗
      ivar_3_producer t ∗
      ivar_3_consumer t Ψ
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    iApply wp_fupd.
    wp_apply (base.ivar_3_create_spec with "[//]") as (𝑡 γ) "(Hmeta & Hinv & Hproducer & Hconsumer)".
    iMod (meta_set γ with "Hmeta") as "#Hmeta"; first done.
    iSteps.
  Qed.

  Lemma ivar_3_make_spec Ψ Ξ Ω v :
    {{{
      ▷ Ψ v ∗
      ▷ □ Ξ v
    }}}
      ivar_3_make v
    {{{ t,
      RET t;
      ivar_3_inv t Ψ Ξ Ω ∗
      ivar_3_consumer t Ψ ∗
      ivar_3_result t v ∗
      ivar_3_waiters t [] []
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #HΞ) HΦ".

    iApply wp_fupd.
    wp_apply (base.ivar_3_make_spec with "[$]") as (𝑡 γ) "(Hmeta & Hinv & Hproducer & Hconsumer)".
    iMod (meta_set γ with "Hmeta") as "#Hmeta"; first done.
    iSteps.
  Qed.

  Lemma ivar_3_is_set_spec t Ψ Ξ Ω :
    {{{
      ivar_3_inv t Ψ Ξ Ω
    }}}
      ivar_3_is_set t
    {{{ b,
      RET #b;
      if b then
        £ 2 ∗
        ivar_3_resolved t
      else
        True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_apply (base.ivar_3_is_set_spec with "[$]") as (b) "Hb".
    rewrite /ivar_3_resolved. destruct b; iSteps.
  Qed.
  Lemma ivar_3_is_set_spec_result t Ψ Ξ Ω v :
    {{{
      ivar_3_inv t Ψ Ξ Ω ∗
      ivar_3_result t v
    }}}
      ivar_3_is_set t
    {{{
      RET #true;
      £ 2
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:result =2)) HΦ". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp_apply (base.ivar_3_is_set_spec_result with "[$] HΦ").
  Qed.

  Lemma ivar_3_try_get_spec t Ψ Ξ Ω :
    {{{
      ivar_3_inv t Ψ Ξ Ω
    }}}
      ivar_3_try_get t
    {{{ o,
      RET o : val;
      if o is Some v then
        £ 2 ∗
        ivar_3_result t v
      else
        True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_apply (base.ivar_3_try_get_spec with "[$]") as (o) "Ho".
    iSpecialize ("HΦ" $! o).
    destruct o; iSteps.
  Qed.
  Lemma ivar_3_try_get_spec_result t Ψ Ξ Ω v :
    {{{
      ivar_3_inv t Ψ Ξ Ω ∗
      ivar_3_result t v
    }}}
      ivar_3_try_get t
    {{{
      RET Some v : val;
      £ 2
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:result =2)) HΦ". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp_apply (base.ivar_3_try_get_spec_result with "[$] HΦ").
  Qed.

  Lemma ivar_3_get_spec t Ψ Ξ Ω v :
    {{{
      ivar_3_inv t Ψ Ξ Ω ∗
      ivar_3_result t v
    }}}
      ivar_3_get t
    {{{
      RET v;
      £ 2
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:result =2)) HΦ". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp_apply (base.ivar_3_get_spec with "[$] HΦ").
  Qed.

  Lemma ivar_3_wait_spec {t Ψ Ξ Ω waiter} ω :
    {{{
      ivar_3_inv t Ψ Ξ Ω ∗
      ▷ Ω t waiter ω
    }}}
      ivar_3_wait t waiter
    {{{ o,
      RET o : val;
      if o is Some v then
        £ 2 ∗
        ivar_3_result t v ∗
        Ω t waiter ω
      else
        ivar_3_waiter t waiter ω
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & Hwaiter) HΦ".

    wp_apply (base.ivar_3_wait_spec with "[$]") as (o) "Ho".
    iSpecialize ("HΦ" $! o).
    destruct o; iSteps.
  Qed.

  Lemma ivar_3_set_spec t Ψ Ξ Ω v :
    {{{
      ivar_3_inv t Ψ Ξ Ω ∗
      ivar_3_producer t ∗
      ▷ Ψ v ∗
      ▷ □ Ξ v
    }}}
      ivar_3_set t v
    {{{ waiters ωs,
      RET lst_to_val waiters;
      ivar_3_result t v ∗
      ivar_3_waiters t waiters ωs ∗
      [∗ list] waiter; ω ∈ waiters; ωs, Ω t waiter ω
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:producer =2) & HΨ & HΞ) HΦ". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp_apply (base.ivar_3_set_spec with "[$]").
    iSteps.
  Qed.
End ivar_3_G.

#[global] Opaque ivar_3_inv.
#[global] Opaque ivar_3_producer.
#[global] Opaque ivar_3_consumer.
#[global] Opaque ivar_3_result.
#[global] Opaque ivar_3_waiter.
#[global] Opaque ivar_3_waiters.
