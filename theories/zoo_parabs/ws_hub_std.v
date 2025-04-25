From zoo Require Import
  prelude.
From zoo.common Require Import
  countable
  list.
From zoo.iris.bi Require Import
  big_op.
From zoo.iris.base_logic Require Import
  lib.twins.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  int
  option
  optional
  array
  random_round
  domain.
From zoo_parabs Require Export
  base
  ws_hub_std__code.
From zoo_parabs Require Import
  ws_hub_std__types
  ws_deques_public
  waiters.
From zoo Require Import
  options.

Implicit Types b yield killed : bool.
Implicit Types l : location.
Implicit Types v t until pred : val.
Implicit Types vs : gmultiset val.

Class WsHubStdG Σ `{zoo_G : !ZooG Σ} := {
  #[local] ws_hub_std_G_deques_G :: WsDequesPublicG Σ ;
  #[local] ws_hub_std_G_waiters_G :: WaitersG Σ ;
  #[local] ws_hub_std_G_model_G :: TwinsG Σ (leibnizO (gmultiset val)) ;
}.

Definition ws_hub_std_Σ := #[
  ws_deques_public_Σ ;
  waiters_Σ ;
  twins_Σ (leibnizO (gmultiset val))
].
#[global] Instance subG_ws_hub_std_Σ Σ `{zoo_G : !ZooG Σ} :
  subG ws_hub_std_Σ Σ →
  WsHubStdG Σ.
Proof.
  solve_inG.
Qed.

Section ws_hub_std_G.
  Context `{ws_hub_std_G : WsHubStdG Σ}.

  Record metadata := {
    metadata_size : nat ;
    metadata_deques : val ;
    metadata_rounds : val ;
    metadata_waiters : val ;
    metadata_model : gname ;
  }.
  Implicit Types γ : metadata.

  #[local] Instance metadata_eq_dec :
    EqDecision metadata.
  Proof.
    solve_decision.
  Qed.
  #[local] Instance metadata_countable :
    Countable metadata.
  Proof.
    solve_countable.
  Qed.

  #[local] Definition model₁' γ_model vs :=
    twins_twin1 γ_model (DfracOwn 1) vs.
  #[local] Definition model₁ γ vs :=
    model₁' γ.(metadata_model) vs.
  #[local] Definition model₂' γ_model vs :=
    twins_twin2 γ_model vs.
  #[local] Definition model₂ γ vs :=
    model₂' γ.(metadata_model) vs.

  #[local] Definition inv_inner l γ : iProp Σ :=
    ∃ vs vss killed,
    ⌜vs = foldr (λ vs_deques vs, list_to_set_disj vs_deques ⊎ vs) ∅ vss⌝ ∗
    l.[killed] ↦ #killed ∗
    ws_deques_public_model γ.(metadata_deques) vss ∗
    model₂ γ vs.
  #[local] Instance : CustomIpatFormat "inv_inner" :=
    "(
      %vs &
      %vss &
      %killed &
      >%Hvs &
      >Hl_killed &
      >Hdeques_model &
      >Hmodel₂
    )".
  Definition ws_hub_std_inv t ι sz : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    ⌜sz = γ.(metadata_size)⌝ ∗
    l.[deques] ↦□ γ.(metadata_deques) ∗
    l.[rounds] ↦□ γ.(metadata_rounds) ∗
    l.[waiters] ↦□ γ.(metadata_waiters) ∗
    ws_deques_public_inv γ.(metadata_deques) (ι.@"deques") γ.(metadata_size) ∗
    array_inv γ.(metadata_rounds) γ.(metadata_size) ∗
    waiters_inv γ.(metadata_waiters) ∗
    inv (ι.@"inv") (inv_inner l γ).
  #[local] Instance : CustomIpatFormat "inv" :=
    "(
      %l{} &
      %γ{} &
      {%Heq{}=->} &
      #Hmeta{} &
      -> &
      #Hl{}_deques &
      #Hl{}_rounds &
      #Hl{}_waiters &
      #Hdeques{}_inv &
      #Hrounds{}_inv &
      #Hwaiters{}_inv &
      #Hinv{}
    )".

  Definition ws_hub_std_model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    model₁ γ vs.
  #[local] Instance : CustomIpatFormat "model" :=
    "(
      %l_ &
      %γ_ &
      %Heq &
      Hmeta_ &
      Hmodel₁
    )".

  Definition ws_hub_std_owner t i status : iProp Σ :=
    ∃ l γ round n,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    ws_deques_public_owner γ.(metadata_deques) i status ∗
    array_slice γ.(metadata_rounds) i DfracDiscarded [round] ∗
    random_round_model' round (γ.(metadata_size) - 1) n.
  #[local] Instance : CustomIpatFormat "owner" :=
    "(
      %l{=_} &
      %γ{=_} &
      %round{} &
      %n{} &
      %Heq{} &
      Hmeta{=_} &
      Hdeques_owner{} &
      #Hrounds{} &
      Hround{}
    )".

  #[global] Instance ws_hub_std_model_timeless t vs :
    Timeless (ws_hub_std_model t vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance ws_hub_std_inv_persistent t ι sz :
    Persistent (ws_hub_std_inv t ι sz).
  Proof.
    apply _.
  Qed.

  #[local] Lemma model_alloc :
    ⊢ |==>
      ∃ γ_model,
      model₁' γ_model ∅ ∗
      model₂' γ_model ∅.
  Proof.
    apply twins_alloc'.
  Qed.
  #[local] Lemma model_agree γ vs1 vs2 :
    model₁ γ vs1 -∗
    model₂ γ vs2 -∗
    ⌜vs1 = vs2⌝.
  Proof.
    apply: twins_agree_L.
  Qed.
  #[local] Lemma model_update {γ vs1 vs2} vs :
    model₁ γ vs1 -∗
    model₂ γ vs2 ==∗
      model₁ γ vs ∗
      model₂ γ vs.
  Proof.
    apply twins_update'.
  Qed.

  Lemma ws_hub_std_inv_agree t ι sz1 sz2 :
    ws_hub_std_inv t ι sz1 -∗
    ws_hub_std_inv t ι sz2 -∗
    ⌜sz1 = sz2⌝.
  Proof.
    iIntros "(:inv =1) (:inv =2)". simplify.
    iDestruct (meta_agree with "Hmeta1 Hmeta2") as %<-.
    iSteps.
  Qed.

  Lemma ws_hub_std_owner_exclusive t i status1 status2 :
    ws_hub_std_owner t i status1 -∗
    ws_hub_std_owner t i status2 -∗
    False.
  Proof.
    iIntros "(:owner =1) (:owner =2)". simplify.
    iDestruct (meta_agree with "Hmeta1 Hmeta2") as %<-. iClear "Hmeta2".
    iApply (ws_deques_public_owner_exclusive with "Hdeques_owner1 Hdeques_owner2").
  Qed.

  Lemma ws_hub_std_create_spec ι sz :
    (0 ≤ sz)%Z →
    {{{
      True
    }}}
      ws_hub_std_create #sz
    {{{ t,
      RET t;
      ws_hub_std_inv t ι ₊sz ∗
      ws_hub_std_model t ∅ ∗
      [∗ list] i ∈ seq 0 ₊sz,
        ws_hub_std_owner t i Nonblocked
    }}}.
  Proof.
    iIntros "%Hsz %Φ _ HΦ".

    wp_rec.

    wp_apply (waiters_create_spec with "[//]") as (waiters) "#Hwaiters_inv".

    wp_smart_apply (array_unsafe_init_spec_disentangled (λ _ round, random_round_model' round (₊sz - 1) (₊sz - 1))) as (v_rounds rounds) "(%Hrounds & Hrounds_model & Hrounds)"; first done.
    { iIntros "!> %i %Hi".
      wp_smart_apply int_positive_part_spec.
      wp_apply (random_round_create_spec' with "[//]"); first lia.
      rewrite Nat2Z.id. assert (₊(sz - 1) = ₊sz - 1) as -> by lia.
      iSteps.
    }
    iDestruct (array_model_to_inv with "Hrounds_model") as "#Hrounds_inv".
    rewrite Hrounds.

    wp_smart_apply (ws_deques_public_create_spec with "[//]") as (deques) "(#Hdeques_inv & Hdeques_model & Hdeques_owner)"; first done.

    wp_block l as "Hmeta" "(Hl_deques & Hl_rounds & Hl_waiters & Hl_killed & _)".
    iMod (pointsto_persist with "Hl_deques") as "#Hl_deques".
    iMod (pointsto_persist with "Hl_rounds") as "#Hl_rounds".
    iMod (pointsto_persist with "Hl_waiters") as "#Hl_waiters".

    iMod model_alloc as "(%γ_model & Hmodel₁ & Hmodel₂)".

    pose γ := {|
      metadata_size := ₊sz ;
      metadata_deques := deques ;
      metadata_rounds := v_rounds ;
      metadata_waiters := waiters ;
      metadata_model := γ_model ;
    |}.

    iMod (meta_set γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitR "Hmodel₁ Hdeques_owner Hrounds_model Hrounds"; iSteps.
    - assert (∀ sz, foldr (λ vs_deques vs, list_to_set_disj vs_deques ⊎ vs) ∅ (replicate sz []) = ∅) as ->.
      { clear. induction sz as [| sz IH]; first done. rewrite /= left_id //. }
      iSteps.
    - iMod (array_model_persist with "Hrounds_model") as "Hrounds_model".
      iDestruct (array_model_atomize with "Hrounds_model") as "(_ & Hrounds_model)".
      iDestruct (big_sepL_sep_2 with "Hrounds_model Hrounds") as "Hrounds".
      iDestruct (big_sepL_seq_index_1 with "Hdeques_owner") as "Hdeques_owner"; first done.
      iDestruct (big_sepL_sep_2 with "Hdeques_owner Hrounds") as "H".
      iApply big_sepL_seq_index; first done.
      iApply (big_sepL_impl with "H").
      iSteps.
  Qed.

  Lemma ws_hub_std_size_spec t ι sz :
    {{{
      ws_hub_std_inv t ι sz
    }}}
      ws_hub_std_size t
    {{{
      RET #sz;
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_rec. wp_load.
    wp_apply (array_size_spec_inv with "Hrounds_inv HΦ").
  Qed.

  Lemma ws_hub_std_block_spec t ι sz i i_ :
    i = ⁺i_ →
    {{{
      ws_hub_std_inv t ι sz ∗
      ws_hub_std_owner t i_ Nonblocked
    }}}
      ws_hub_std_block t #i
    {{{
      RET ();
      ws_hub_std_owner t i_ Blocked
    }}}.
  Proof.
    iIntros (->) "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp_rec. wp_load.
    wp_apply (ws_deques_public_block_spec with "[$Hdeques_inv $Hdeques_owner]"); first done.
    iSteps.
  Qed.

  Lemma ws_hub_std_unblock_spec t ι sz i i_ :
    i = ⁺i_ →
    {{{
      ws_hub_std_inv t ι sz ∗
      ws_hub_std_owner t i_ Blocked
    }}}
      ws_hub_std_unblock t #i
    {{{
      RET ();
      ws_hub_std_owner t i_ Nonblocked
    }}}.
  Proof.
    iIntros (->) "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp_rec. wp_load.
    wp_apply (ws_deques_public_unblock_spec with "[$Hdeques_inv $Hdeques_owner]"); first done.
    iSteps.
  Qed.

  Lemma ws_hub_std_killed_spec t ι sz :
    {{{
      ws_hub_std_inv t ι sz
    }}}
      ws_hub_std_killed t
    {{{ killed,
      RET #killed;
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  #[local] Lemma ws_hub_std_notify_spec t ι sz :
    {{{
      ws_hub_std_inv t ι sz
    }}}
      ws_hub_std_notify t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_rec. wp_load.
    wp_apply (waiters_notify_spec with "Hwaiters_inv HΦ").
  Qed.

  #[local] Lemma ws_hub_std_notify_all_spec t ι sz :
    {{{
      ws_hub_std_inv t ι sz
    }}}
      ws_hub_std_notify_all t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_rec.
    wp_apply (ws_hub_std_size_spec) as "_"; first iSteps.
    wp_load.
    wp_apply (waiters_notify_many_spec with "Hwaiters_inv HΦ"); first lia.
  Qed.

  Lemma ws_hub_std_push_spec t ι sz i i_ v :
    i = ⁺i_ →
    <<<
      ws_hub_std_inv t ι sz ∗
      ws_hub_std_owner t i_ Nonblocked
    | ∀∀ vs,
      ws_hub_std_model t vs
    >>>
      ws_hub_std_push t #i v @ ↑ι
    <<<
      ws_hub_std_model t ({[+v+]} ⊎ vs)
    | RET ();
      ws_hub_std_owner t i_ Nonblocked
    >>>.
  Proof.
    iIntros (->) "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp_rec. wp_load.

    awp_apply (ws_deques_public_push_spec with "[$Hdeques_inv $Hdeques_owner]") without "Hround"; first done.
    iInv "Hinv" as "(:inv_inner)".
    iApply (aacc_aupd_commit with "HΦ"); first solve_ndisj. iIntros "%vs_ (:model)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
    iAaccIntro with "Hdeques_model".
    { iIntros "Hdeques_model !>".
      iSplitL "Hmodel₁"; first iSteps. iIntros "$ !>".
      iSteps.
    }
    iIntros "%vs' (%Hlookup & Hdeques_model)".
    iMod (model_update ({[+v+]} ⊎ vs) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iSplitL "Hmodel₁"; first iSteps. iIntros "!> HΦ !>".
    iSplitR "HΦ".
    { repeat iExists _. iFrame. iPureIntro.
      rewrite (foldr_insert_strong _ (flip (++))) //.
      { set_solver by lia. }
      { rewrite list_to_set_disj_app. multiset_solver. }
      set_solver.
    }
    iIntros "Hdeques_owner Hround {%}".

    wp_smart_apply ws_hub_std_notify_spec; iSteps.
  Qed.

  Lemma ws_hub_std_pop_spec t ι sz i i_ :
    i = ⁺i_ →
    <<<
      ws_hub_std_inv t ι sz ∗
      ws_hub_std_owner t i_ Nonblocked
    | ∀∀ vs,
      ws_hub_std_model t vs
    >>>
      ws_hub_std_pop t #i @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_std_model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_std_model t vs'
      end
    | RET o;
      ws_hub_std_owner t i_ Nonblocked
    >>>.
  Proof.
    iIntros (->) "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp_rec. wp_load.

    awp_smart_apply (ws_deques_public_pop_spec with "[$Hdeques_inv $Hdeques_owner]") without "Hround"; first done.
    iInv "Hinv" as "(:inv_inner)".
    iApply (aacc_aupd_commit with "HΦ"); first solve_ndisj. iIntros "%vs_ (:model)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
    iAaccIntro with "Hdeques_model".
    { iIntros "Hdeques_model !>".
      iSplitL "Hmodel₁"; first iSteps.
      iIntros "$". iSteps.
    }
    iIntros ([v |]) "Hdeques_model".

    - iDestruct "Hdeques_model" as "(%ws & %Hlookup & Hdeques_model)".
      set vs' := vs ∖ {[+v+]}.
      iMod (model_update vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iExists (Some v).
      iSplitL "Hmodel₁".
      { iExists vs'. iSteps. iPureIntro.
        apply gmultiset_disj_union_difference'.
        rewrite {}Hvs -(take_drop_middle vss i_ (ws ++ [v])) // foldr_app /=.
        rewrite foldr_comm_acc_strong; first multiset_solver.
        rewrite gmultiset_elem_of_disj_union list_to_set_disj_app.
        set_solver.
      }
      iIntros "!> HΦ !>".
      iSplitR "HΦ".
      { repeat iExists _. iFrame. iPureIntro.
        rewrite /vs' Hvs -{1}(take_drop_middle vss i_ (ws ++ [v])) // insert_take_drop.
        { eapply lookup_lt_Some. done. }
        rewrite !foldr_app /= foldr_comm_acc_strong; first multiset_solver.
        rewrite (foldr_comm_acc_strong _ _ _ (foldr _ _ _)); first multiset_solver.
        rewrite list_to_set_disj_app.
        multiset_solver.
      }
      iSteps.

    - iDestruct "Hdeques_model" as "(%Hlookup & Hdeques_model)".
      iExists None.
      iSplitL "Hmodel₁"; first iSteps.
      iIntros "!> HΦ !>".
      iSplitR "HΦ"; first iSteps.
      iSteps.
  Qed.

  #[local] Lemma ws_hub_std_try_steal_once_spec t ι sz i i_ :
    i = ⁺i_ →
    <<<
      ws_hub_std_inv t ι sz ∗
      ws_hub_std_owner t i_ Blocked
    | ∀∀ vs,
      ws_hub_std_model t vs
    >>>
      ws_hub_std_try_steal_once t #i @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_std_model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_std_model t vs'
      end
    | RET o;
      ws_hub_std_owner t i_ Blocked
    >>>.
  Proof.
    iIntros (->) "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp_rec. wp_load.
    wp_apply (array_unsafe_get_spec_cell with "Hrounds") as "_"; first lia.
    wp_smart_apply (random_round_reset_spec' with "Hround") as "Hround".
    wp_load.

    iDestruct (ws_deques_public_inv_owner with "Hdeques_inv Hdeques_owner") as %?.
    awp_apply (ws_deques_public_steal_as_spec with "[$Hdeques_inv $Hdeques_owner $Hround]"); [lia.. |].
    iInv "Hinv" as "(:inv_inner)".
    iApply (aacc_aupd_commit with "HΦ"); first solve_ndisj. iIntros "%vs_ (:model)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
    iAaccIntro with "Hdeques_model".
    { iIntros "Hdeques_model !>".
      iSplitL "Hmodel₁"; first iSteps.
      iIntros "$". iSteps.
    }
    iIntros ([v |]) "Hdeques_model".

    - iDestruct "Hdeques_model" as "(%j & %ws & %Hj & %Hlookup & Hdeques_model)".
      set vs' := vs ∖ {[+v+]}.
      iMod (model_update vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iExists (Some v).
      iSplitL "Hmodel₁".
      { iExists vs'. iSteps. iPureIntro.
        apply gmultiset_disj_union_difference'.
        rewrite {}Hvs -(take_drop_middle vss j (v :: ws)) // foldr_app /=.
        rewrite foldr_comm_acc_strong; first multiset_solver.
        set_solver.
      }
      iIntros "!> HΦ !>".
      iSplitR "HΦ".
      { repeat iExists _. iFrame. iPureIntro.
        rewrite /vs' Hvs -{1}(take_drop_middle vss j (v :: ws)) // insert_take_drop.
        { eapply lookup_lt_Some. done. }
        rewrite !foldr_app /= foldr_comm_acc_strong; first multiset_solver.
        rewrite (foldr_comm_acc_strong _ _ _ (foldr _ _ _)); multiset_solver.
      }
      iSteps.

    - iExists None.
      iSplitL "Hmodel₁"; first iSteps.
      iIntros "!> HΦ !>".
      iSplitR "HΦ"; first iSteps.
      iSteps.
  Qed.

  #[local] Lemma ws_hub_std_try_steal_spec P t ι sz i i_ yield max_round until :
    i = ⁺i_ →
    (0 ≤ max_round)%Z →
    <<<
      ws_hub_std_inv t ι sz ∗
      ws_hub_std_owner t i_ Blocked ∗
      □ WP until () {{ res,
        ∃ b,
        ⌜res = #b⌝ ∗
        if b then P else True
      }}
    | ∀∀ vs,
      ws_hub_std_model t vs
    >>>
      ws_hub_std_try_steal t #i #yield #max_round until @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | Nothing
      | Anything =>
          ws_hub_std_model t vs
      | Something v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_std_model t vs'
      end
    | RET o;
      ws_hub_std_owner t i_ Blocked ∗
      if o is Anything then P else True
    >>>.
  Proof.
    intros ->.
    iLöb as "HLöb" forall (max_round).

    iIntros "%Hmax_round %Φ ((:inv) & (:owner) & #Huntil) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp_rec. wp_pures.
    case_bool_decide as Hcase; wp_pures.

    - iMod "HΦ" as "(%vss & Hmodel & _ & HΦ)".
      iApply ("HΦ" $! Nothing with "Hmodel").
      iSteps.

    - awp_smart_apply (ws_hub_std_try_steal_once_spec with "[Hdeques_owner Hround]"); [done | iSteps |].
      iApply (aacc_aupd with "HΦ"); first done. iIntros "%vs Hmodel".
      iAaccIntro with "Hmodel"; first iSteps. iIntros ([v |]) "Hmodel !>".

      + iRight. iExists (Something v). iFrame.
        iIntros "HΦ !> Howner {%}".

        iSpecialize ("HΦ" with "[$Howner]").
        iSteps.

      + iLeft. iFrame.
        iIntros "HΦ !> Howner". clear- Hmax_round Hcase.

        wp_smart_apply (wp_wand with "Huntil") as (res) "(%b & -> & HP)".
        destruct b; wp_pures.

        * iMod "HΦ" as "(%vss & Hmodel & _ & HΦ)".
          iApply ("HΦ" $! Anything with "Hmodel [$Howner $HP]").

        * wp_bind (if: _ then _ else _)%E.
          wp_apply (wp_wand itype_unit) as (res) "->".
          { destruct yield; iSteps. }
          wp_smart_apply ("HLöb" with "[] [$Howner] HΦ"); iSteps.
  Qed.

  #[local] Lemma ws_hub_std_steal_until_0_spec P t ι sz i i_ pred :
    i = ⁺i_ →
    <<<
      ws_hub_std_inv t ι sz ∗
      ws_hub_std_owner t i_ Blocked ∗
      □ WP pred () {{ res,
        ∃ b,
        ⌜res = #b⌝ ∗
        if b then P else True
      }}
    | ∀∀ vs,
      ws_hub_std_model t vs
    >>>
      ws_hub_std_steal_until_0 t #i pred @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_std_model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_std_model t vs'
      end
    | RET o;
      ws_hub_std_owner t i_ Blocked ∗
      if o then True else P
    >>>.
  Proof.
    iIntros (->) "%Φ (#Hinv & Howner & #Hpred) HΦ".

    iLöb as "HLöb".

    wp_rec.

    awp_smart_apply (ws_hub_std_try_steal_once_spec with "[$Hinv $Howner]"); first done.
    iApply (aacc_aupd with "HΦ"); first done. iIntros "%vs Hmodel".
    iAaccIntro with "Hmodel"; first iSteps. iIntros ([v |]) "Hmodel !>".

    - iRight. iExists (Some v). iFrame.
      iIntros "HΦ !> Howner {%}".

      iStep.
      iSpecialize ("HΦ" with "[$Howner]").
      iSteps.

    - iLeft. iFrame.
      iIntros "HΦ !> Howner {%}".

      wp_smart_apply (wp_wand with "Hpred") as (res) "(%b & -> & HP)".
      destruct b; wp_pures.

      + iMod "HΦ" as "(%vss & Hmodel & _ & HΦ)".
        iApply ("HΦ" $! None with "Hmodel [$Howner $HP]").

      + wp_apply domain_yield_spec.
        wp_smart_apply ("HLöb" with "Howner HΦ").
  Qed.
  Lemma ws_hub_std_steal_until_1_spec P t ι sz i i_ max_round_noyield pred :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    <<<
      ws_hub_std_inv t ι sz ∗
      ws_hub_std_owner t i_ Blocked ∗
      □ WP pred () {{ res,
        ∃ b,
        ⌜res = #b⌝ ∗
        if b then P else True
      }}
    | ∀∀ vs,
      ws_hub_std_model t vs
    >>>
      ws_hub_std_steal_until_1 t #i #max_round_noyield pred @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_std_model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_std_model t vs'
      end
    | RET o;
      ws_hub_std_owner t i_ Blocked ∗
      if o then True else P
    >>>.
  Proof.
    iIntros (->) "%Hmax_round_noyield %Φ (#Hinv & Howner & #Hpred) HΦ".

    wp_rec.

    awp_smart_apply (ws_hub_std_try_steal_spec with "[$Hinv $Howner $Hpred]"); [done.. |].
    iApply (aacc_aupd with "HΦ"); first done. iIntros "%vs Hmodel".
    iAaccIntro with "Hmodel"; first iSteps. iIntros ([| | v]) "Hmodel !>".

    - iLeft. iFrame.
      iIntros "HΦ !> (Howner & _) {%}".

      wp_smart_apply (ws_hub_std_steal_until_0_spec with "[$Hinv $Howner $Hpred] HΦ"); first done.

    - iRight. iExists None. iFrame.
      iSteps.

    - iRight. iExists (Some v). iFrame.
      iIntros "HΦ !> Howner {%}".

      iSpecialize ("HΦ" with "Howner").
      iSteps.
  Qed.
  Lemma ws_hub_std_steal_until_spec P t ι sz i i_ max_round_noyield pred :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    <<<
      ws_hub_std_inv t ι sz ∗
      ws_hub_std_owner t i_ Nonblocked ∗
      □ WP pred () {{ res,
        ∃ b,
        ⌜res = #b⌝ ∗
        if b then P else True
      }}
    | ∀∀ vs,
      ws_hub_std_model t vs
    >>>
      ws_hub_std_steal_until t #i #max_round_noyield pred @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_std_model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_std_model t vs'
      end
    | RET o;
      ws_hub_std_owner t i_ Nonblocked ∗
      if o then True else P
    >>>.
  Proof.
    iIntros (->) "%Hmax_round_noyield %Φ (#Hinv & Howner & #Hpred) HΦ".

    wp_rec.
    wp_smart_apply (ws_hub_std_block_spec with "[$Hinv $Howner]") as "Howner"; first done.
    wp_smart_apply (ws_hub_std_steal_until_1_spec with "[$Hinv $Howner $Hpred]"); [done.. |].
    iApply (atomic_update_wand with "HΦ"). iIntros "_ %o HΦ (Howner & HP)".
    wp_smart_apply (ws_hub_std_unblock_spec with "[$Hinv $Howner]") as "Howner"; first done.
    wp_pures.
    iApply ("HΦ" with "[$Howner $HP]").
  Qed.

  #[local] Lemma ws_hub_std_steal_aux_spec P t ι i i_ sz max_round_noyield max_round_yield until :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub_std_inv t ι sz ∗
      ws_hub_std_owner t i_ Blocked ∗
      □ WP until () {{ res,
        ∃ b,
        ⌜res = #b⌝ ∗
        if b then P else True
      }}
    | ∀∀ vs,
      ws_hub_std_model t vs
    >>>
      ws_hub_std_steal_aux t #i #max_round_noyield #max_round_yield until @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | Nothing
      | Anything =>
          ws_hub_std_model t vs
      | Something v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_std_model t vs'
      end
    | RET o;
      ws_hub_std_owner t i_ Blocked ∗
      if o is Anything then P else True
    >>>.
  Proof.
    iIntros (->) "%Hmax_round_noyield %Hmax_round_yield %Φ (#Hinv & Howner & #Huntil) HΦ".

    wp_rec.

    awp_smart_apply (ws_hub_std_try_steal_spec with "[$Hinv $Howner $Huntil]"); [done.. |].
    iApply (aacc_aupd with "HΦ"); first done. iIntros "%vs Hmodel".
    iAaccIntro with "Hmodel"; first iSteps. iIntros ([| | v]) "Hmodel !>".

    - iLeft. iFrame.
      iIntros "HΦ !> (Howner & _)". clear- Hmax_round_yield.

      wp_smart_apply (ws_hub_std_try_steal_spec with "[$Hinv $Howner $Huntil] HΦ"); done.

    - iRight. iExists Anything. iFrame.
      iSteps.

    - iRight. iExists (Something v). iFrame.
      iIntros "HΦ !> Howner {%}".

      iSpecialize ("HΦ" with "Howner").
      iSteps.
  Qed.
  Lemma ws_hub_std_steal_0_spec t ι i i_ sz max_round_noyield max_round_yield :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub_std_inv t ι sz ∗
      ws_hub_std_owner t i_ Blocked
    | ∀∀ vs,
      ws_hub_std_model t vs
    >>>
      ws_hub_std_steal_0 t #i #max_round_noyield #max_round_yield @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_std_model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_std_model t vs'
      end
    | RET o;
      ws_hub_std_owner t i_ Blocked
    >>>.
  Proof.
    iIntros (->) "%Hmax_round_noyield %Hmax_round_yield %Φ (#Hinv & Howner) HΦ".

    iLöb as "HLöb".

    wp_rec.

    awp_smart_apply (ws_hub_std_steal_aux_spec True with "[$Hinv $Howner]"); [done.. | |].
    { iModIntro.
      wp_smart_apply (ws_hub_std_killed_spec with "Hinv") as (killed) "_".
      iSteps. destruct killed; iSteps.
    }
    iApply (aacc_aupd with "HΦ"); first done. iIntros "%vs Hmodel".
    iAaccIntro with "Hmodel"; first iSteps. iIntros ([| | v]) "Hmodel !>".

    - iLeft. iFrame.
      iIntros "HΦ !> (Howner & _) {%}".

      iDestruct "Hinv" as "(:inv)".

      wp_load.
      wp_smart_apply (waiters_prepare_wait_spec with "Hwaiters_inv") as (waiter) "Hwaiter".

      awp_smart_apply (ws_hub_std_try_steal_once_spec with "[$Howner]") without "Hwaiter"; [done.. | iSteps |].
      iApply (aacc_aupd with "HΦ"); first done. iIntros "%vs Hmodel".
      iAaccIntro with "Hmodel"; first iSteps. iIntros ([v |]) "Hmodel !>".

      + iDestruct "Hmodel" as "(%vs' & -> & Hmodel)".
        iRight. iExists (Some v).
        iSplitL "Hmodel". { iExists vs'. iFrameSteps. }
        iIntros "HΦ !> Howner Hwaiter {%}".

        wp_smart_apply (waiters_cancel_wait_spec with "[$Hwaiters_inv $Hwaiter]") as "_".
        wp_pures.
        iApply ("HΦ" with "Howner").

      + iLeft. iFrame.
        iIntros "HΦ !> Howner Hwaiter {%}".

        wp_smart_apply ws_hub_std_killed_spec as ([]) "_"; first iSteps.

        * wp_smart_apply (waiters_cancel_wait_spec with "[$Hwaiters_inv $Hwaiter]") as "_".
          wp_pures.
          iMod "HΦ" as "(%vss & Hmodel & _ & HΦ)".
          iApply ("HΦ" $! None with "Hmodel Howner").

        * wp_smart_apply (waiters_commit_wait_spec with "[$Hwaiters_inv $Hwaiter]") as "_".
          wp_smart_apply ("HLöb" with "Howner HΦ").

    - iRight. iExists None. iFrame.
      iSteps.

    - iDestruct "Hmodel" as "(%vs' & -> & Hmodel)".
      iRight. iExists (Some v).
      iSplitL "Hmodel". { iExists vs'. iFrameSteps. }
      iSteps.
  Qed.
  Lemma ws_hub_std_steal_spec t ι i i_ sz max_round_noyield max_round_yield :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub_std_inv t ι sz ∗
      ws_hub_std_owner t i_ Nonblocked
    | ∀∀ vs,
      ws_hub_std_model t vs
    >>>
      ws_hub_std_steal t #i #max_round_noyield #max_round_yield @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_std_model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_std_model t vs'
      end
    | RET o;
      ws_hub_std_owner t i_ Nonblocked
    >>>.
  Proof.
    iIntros (->) "%Hmax_round_noyield %Hmax_round_yield %Φ (#Hinv & Howner) HΦ".

    wp_rec.
    wp_smart_apply (ws_hub_std_block_spec with "[$Hinv $Howner]") as "Howner"; first done.
    wp_smart_apply (ws_hub_std_steal_0_spec with "[$Hinv $Howner]"); [done.. |].
    iApply (atomic_update_wand with "HΦ"). iIntros "_ %o HΦ Howner".
    wp_smart_apply (ws_hub_std_unblock_spec with "[$Hinv $Howner]") as "Howner"; first done.
    wp_pures.
    iApply ("HΦ" with "Howner").
  Qed.

  Lemma ws_hub_std_kill_spec t ι sz :
    {{{
      ws_hub_std_inv t ι sz
    }}}
      ws_hub_std_kill t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_rec. wp_pures.

    wp_bind (_ <-{killed} _)%E.
    iInv "Hinv" as "(:inv_inner)".
    wp_store.
    iSplitR "HΦ"; first iSteps.
    iIntros "!> {%}".

    wp_smart_apply ws_hub_std_notify_all_spec as "_"; first iSteps.
    iSteps.
  Qed.
End ws_hub_std_G.

#[global] Opaque ws_hub_std_inv.
#[global] Opaque ws_hub_std_model.
#[global] Opaque ws_hub_std_owner.

Section ws_hub_std_G.
  Context `{ws_hub_std_G : WsHubStdG Σ}.

  Lemma ws_hub_std_pop_steal_until_spec P t ι i i_ sz max_round_noyield pred :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    <<<
      ws_hub_std_inv t ι sz ∗
      ws_hub_std_owner t i_ Nonblocked ∗
      □ WP pred () {{ res,
        ∃ b,
        ⌜res = #b⌝ ∗
        if b then P else True
      }}
    | ∀∀ vs,
      ws_hub_std_model t vs
    >>>
      ws_hub_std_pop_steal_until t #i #max_round_noyield pred @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_std_model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_std_model t vs'
      end
    | RET o;
      ws_hub_std_owner t i_ Nonblocked ∗
      if o then True else P
    >>>.
  Proof.
    iIntros (->) "%Hmax_round_noyield %Φ (#Hinv & Howner & #Hpred) HΦ".

    wp_rec.

    awp_smart_apply (ws_hub_std_pop_spec with "[$Hinv $Howner]"); [done.. |].
    iApply (aacc_aupd with "HΦ"); first done. iIntros "%vs Hmodel".
    iAaccIntro with "Hmodel"; first iSteps. iIntros ([v |]) "Hmodel !>".

    - iRight. iExists (Some v). iFrame.
      iIntros "HΦ !> Howner {%}".

      iSpecialize ("HΦ" with "[$Howner]").
      iSteps.

    - iLeft. iFrame.
      iIntros "HΦ !> Howner". clear- Hmax_round_noyield.

      wp_smart_apply (ws_hub_std_steal_until_spec with "[$Hinv $Howner $Hpred] HΦ"); done.
  Qed.

  Lemma ws_hub_std_pop_steal_spec t ι i i_ sz max_round_noyield max_round_yield :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub_std_inv t ι sz ∗
      ws_hub_std_owner t i_ Nonblocked
    | ∀∀ vs,
      ws_hub_std_model t vs
    >>>
      ws_hub_std_pop_steal t #i #max_round_noyield #max_round_yield @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_std_model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_std_model t vs'
      end
    | RET o;
      ws_hub_std_owner t i_ Nonblocked
    >>>.
  Proof.
    iIntros (->) "%Hmax_round_noyield %Hmax_round_yield %Φ (#Hinv & Howner) HΦ".

    wp_rec.

    awp_smart_apply (ws_hub_std_pop_spec with "[$Hinv $Howner]"); [done.. |].
    iApply (aacc_aupd with "HΦ"); first done. iIntros "%vs Hmodel".
    iAaccIntro with "Hmodel"; first iSteps. iIntros ([v |]) "Hmodel !>".

    - iDestruct "Hmodel" as "(%vs' & -> & Hmodel)".
      iRight. iExists (Some v). iStep.
      iIntros "HΦ !> Howner {%}".

      iSpecialize ("HΦ" with "Howner").
      iSteps.

    - iLeft. iFrame.
      iIntros "HΦ !> Howner". clear- Hmax_round_noyield Hmax_round_yield.

      wp_smart_apply (ws_hub_std_steal_spec with "[$Hinv $Howner] HΦ"); done.
  Qed.
End ws_hub_std_G.

#[global] Opaque ws_hub_std_create.
#[global] Opaque ws_hub_std_size.
#[global] Opaque ws_hub_std_block.
#[global] Opaque ws_hub_std_unblock.
#[global] Opaque ws_hub_std_killed.
#[global] Opaque ws_hub_std_push.
#[global] Opaque ws_hub_std_pop.
#[global] Opaque ws_hub_std_steal_until.
#[global] Opaque ws_hub_std_steal.
#[global] Opaque ws_hub_std_kill.
#[global] Opaque ws_hub_std_pop_steal_until.
#[global] Opaque ws_hub_std_pop_steal.
