From iris.algebra Require Import
  list.

From zoo Require Import
  prelude.
From zoo.common Require Import
  countable
  relations
  list.
From zoo.iris.base_logic Require Import
  lib.twins
  lib.auth_twins
  lib.auth_nat_max
  lib.mono_list.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  option
  array.
From zoo_saturn Require Export
  base
  spsc_bqueue__code.
From zoo_saturn Require Import
  spsc_bqueue__types.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types i front front_cache back back_cache : nat.
Implicit Types l : location.
Implicit Types v w t : val.
Implicit Types vs ws hist : list val.

Inductive stability :=
  | Stable
  | Unstable.
Implicit Types stable : stability.

#[local] Instance stability_inhabited : Inhabited stability :=
  populate Stable.

Class SpscBqueueG Σ `{zoo_G : !ZooG Σ} := {
  #[local] spsc_bqueue_G_model_G :: AuthTwinsG Σ (leibnizO (list val)) suffix ;
  #[local] spsc_bqueue_G_history_G :: MonoListG Σ val ;
  #[local] spsc_bqueue_G_stability_G :: TwinsG Σ (leibnizO stability) ;
  #[local] spsc_bqueue_G_mono_nat_G :: AuthNatMaxG Σ ;
}.

Definition spsc_bqueue_Σ := #[
  auth_twins_Σ (leibnizO (list val)) suffix ;
  mono_list_Σ val ;
  twins_Σ (leibnizO stability) ;
  auth_nat_max_Σ
].
Lemma subG_spsc_bqueue_Σ Σ `{zoo_G : !ZooG Σ} :
  subG spsc_bqueue_Σ Σ →
  SpscBqueueG Σ.
Proof.
  solve_inG.
Qed.

Section spsc_bqueue_G.
  Context `{spsc_bqueue_G : SpscBqueueG Σ}.

  Record metadata := {
    metadata_capacity : nat ;
    metadata_data : val ;
    metadata_model : auth_twins_name ;
    metadata_history : gname ;
    metadata_producer : gname ;
    metadata_back : gname ;
    metadata_consumer : gname ;
    metadata_front : gname ;
  }.
  Implicit Types γ : metadata.

  #[local] Instance metadata_eq_dec : EqDecision metadata :=
    ltac:(solve_decision).
  #[local] Instance metadata_countable :
    Countable metadata.
  Proof.
    solve_countable.
  Qed.

  #[local] Definition model₁' γ_model vs :=
    auth_twins_twin1 (auth_twins_G := spsc_bqueue_G_model_G) _ γ_model vs.
  #[local] Definition model₁ γ :=
    model₁' γ.(metadata_model).
  #[local] Definition model₂' γ_model vs :=
    auth_twins_twin2 (auth_twins_G := spsc_bqueue_G_model_G) _ γ_model vs.
  #[local] Definition model₂ γ :=
    model₂' γ.(metadata_model).

  #[local] Definition history_auth' γ_history :=
    mono_list_auth γ_history (DfracOwn 1).
  #[local] Definition history_auth γ :=
    history_auth' γ.(metadata_history).
  #[local] Definition history_at γ :=
    mono_list_at γ.(metadata_history).

  #[local] Definition producer₁' γ_producer γ_back γ_model stable back ws : iProp Σ :=
    twins_twin1 γ_producer (DfracOwn 1) stable ∗
    auth_nat_max_auth γ_back (DfracOwn (1/2)) back ∗
    auth_twins_auth _ (auth_twins_G := spsc_bqueue_G_model_G) γ_model ws.
  #[local] Definition producer₁ γ :=
    producer₁' γ.(metadata_producer) γ.(metadata_back) γ.(metadata_model).
  #[local] Instance : CustomIpatFormat "producer₁" :=
    "(
      Hproducer₁ &
      Hback_auth₁ &
      Hmodel_auth
    )".
  #[local] Definition producer₂' γ_producer γ_back stable back : iProp Σ :=
    twins_twin2 γ_producer stable ∗
    auth_nat_max_auth γ_back (DfracOwn (1/2)) back.
  #[local] Definition producer₂ γ :=
    producer₂' γ.(metadata_producer) γ.(metadata_back).
  #[local] Instance : CustomIpatFormat "producer₂" :=
    "(
      Hproducer₂ &
      Hback_auth₂
    )".
  #[local] Definition back_lb γ :=
    auth_nat_max_lb γ.(metadata_back).

  #[local] Definition consumer₁' γ_consumer γ_front stable front : iProp Σ :=
    twins_twin1 γ_consumer (DfracOwn 1) stable ∗
    auth_nat_max_auth γ_front (DfracOwn (1/2)) front.
  #[local] Definition consumer₁ γ :=
    consumer₁' γ.(metadata_consumer) γ.(metadata_front).
  #[local] Instance : CustomIpatFormat "consumer₁" :=
    "(
      Hconsumer₁ &
      Hfront_auth₁
    )".
  #[local] Definition consumer₂' γ_consumer γ_front stable front : iProp Σ :=
    twins_twin2 γ_consumer stable ∗
    auth_nat_max_auth γ_front (DfracOwn (1/2)) front.
  #[local] Definition consumer₂ γ :=
    consumer₂' γ.(metadata_consumer) γ.(metadata_front).
  #[local] Instance : CustomIpatFormat "consumer₂" :=
    "(
      Hconsumer₂ &
      Hfront_auth₂
    )".
  #[local] Definition front_lb γ :=
    auth_nat_max_lb γ.(metadata_front).

  #[local] Definition inv_inner l γ : iProp Σ :=
    ∃ cstable front pstable back vs hist,
    ⌜back = (front + length vs)%nat⌝ ∗
    ⌜back ≤ front + γ.(metadata_capacity)⌝ ∗
    ⌜length hist = back⌝ ∗
    ⌜vs = drop front hist⌝ ∗
    l.[front] ↦ #front ∗
    consumer₂ γ cstable front ∗
    l.[back] ↦ #back ∗
    producer₂ γ pstable back ∗
    model₂ γ vs ∗
    history_auth γ hist ∗
    ( if cstable then
        array_cslice γ.(metadata_data) γ.(metadata_capacity) front (DfracOwn 1) ((λ v, ‘Some( v )%V) <$> take 1 vs)
      else
        True
    ) ∗
    array_cslice γ.(metadata_data) γ.(metadata_capacity) (S front) (DfracOwn 1) ((λ v, ‘Some( v )%V) <$> drop 1 vs) ∗
    ( if pstable then
        array_cslice γ.(metadata_data) γ.(metadata_capacity) back (DfracOwn 1) (if decide (back = front + γ.(metadata_capacity)) then [] else [§None%V])
      else
        True
    ) ∗
    array_cslice γ.(metadata_data) γ.(metadata_capacity) (S back) (DfracOwn 1) (replicate (γ.(metadata_capacity) - (back - front) - 1) §None%V).
  #[local] Instance : CustomIpatFormat "inv_inner" :=
    "(
      %cstable{} &
      %front{} &
      %pstable{} &
      %back{} &
      %vs{} &
      %hist{} &
      >%Hback{} &
      >%Hback{}_le &
      >%Hhist{}_len &
      >%Hvs{} &
      >Hl_front &
      >Hconsumer₂ &
      >Hl_back &
      >Hproducer₂ &
      >Hmodel₂ &
      >Hhistory_auth &
      >Hfront &
      >Hvs &
      >Hback &
      >Hextra
    )".
  Definition spsc_bqueue_inv t ι cap : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    ⌜cap = γ.(metadata_capacity)⌝ ∗
    meta l nroot γ ∗
    l.[data] ↦□ γ.(metadata_data) ∗
    array_inv γ.(metadata_data) γ.(metadata_capacity) ∗
    inv ι (inv_inner l γ).
  #[local] Instance : CustomIpatFormat "inv" :=
    "(
      %l &
      %γ &
      -> &
      -> &
      #Hmeta &
      #Hl_data &
      #Hdata_inv &
      #Hinv
    )".

  Definition spsc_bqueue_model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    model₁ γ vs.
  #[local] Instance : CustomIpatFormat "model" :=
    "(
      %l_ &
      %γ_ &
      %Heq &
      #Hmeta_ &
      Hmodel₁
    )".

  Definition spsc_bqueue_producer t ws : iProp Σ :=
    ∃ l γ front_cache back,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    l.[front_cache] ↦ #front_cache ∗
    producer₁ γ Stable back ws ∗
    front_lb γ front_cache.
  #[local] Instance : CustomIpatFormat "producer" :=
    "(
      %l{{};_} &
      %γ{{};_} &
      %front_cache &
      %back &
      {{}->;%Heq} &
      #Hmeta{{};_} &
      Hl_front_cache &
      Hproducer₁ &
      #Hfront_lb
    )".

  Definition spsc_bqueue_consumer t : iProp Σ :=
    ∃ l γ front back_cache,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    l.[back_cache] ↦ #back_cache ∗
    consumer₁ γ Stable front ∗
    back_lb γ back_cache.
  #[local] Instance : CustomIpatFormat "consumer" :=
    "(
      %l_ &
      %γ_ &
      %front &
      %back_cache &
      %Heq &
      #Hmeta_ &
      Hl_back_cache &
      Hconsumer₁ &
      #Hback_lb
    )".

  #[global] Instance spsc_bqueue_inv_persistent t ι cap :
    Persistent (spsc_bqueue_inv t ι cap).
  Proof.
    apply _.
  Qed.
  #[global] Instance spsc_bqueue_model_timeless t vs :
    Timeless (spsc_bqueue_model t vs).
  Proof.
    apply _.
  Qed.
  #[local] Instance producer₂_timeless γ stable back :
    Timeless (producer₂ γ stable back).
  Proof.
    apply _.
  Qed.
  #[global] Instance spsc_bqueue_producer_timeless t ws :
    Timeless (spsc_bqueue_producer t ws).
  Proof.
    apply _.
  Qed.
  #[local] Instance consumer₂_timeless γ stable front :
    Timeless (consumer₂ γ stable front).
  Proof.
    apply _.
  Qed.
  #[global] Instance spsc_bqueue_consumer_timeless t :
    Timeless (spsc_bqueue_consumer t).
  Proof.
    apply _.
  Qed.

  #[local] Lemma model_producer_alloc :
    ⊢ |==>
      ∃ γ_model γ_producer γ_back,
      model₁' γ_model [] ∗
      model₂' γ_model [] ∗
      producer₁' γ_producer γ_back γ_model Stable 0 [] ∗
      producer₂' γ_producer γ_back Stable 0.
  Proof.
    iMod (auth_twins_alloc (auth_twins_G := spsc_bqueue_G_model_G) _ []) as "(%γ_model & Hmodel_auth & Hmodel₁ & Hmodel₂)".
    iMod twins_alloc' as "(%γ_producer & Hproducer₁ & Hproducer₂)".
    iMod auth_nat_max_alloc as "(%γ_back & Hback_auth₁ & Hback_auth₂)".
    iSteps.
  Qed.
  #[local] Lemma model_valid γ stable back ws vs :
    producer₁ γ stable back ws -∗
    model₁ γ vs -∗
    ⌜vs `suffix_of` ws⌝.
  Proof.
    iIntros "(:producer₁) Hmodel₁".
    iDestruct (auth_twins_valid_1 with "Hmodel_auth Hmodel₁") as %H.
    rewrite preorder_rtc in H. iSteps.
  Qed.
  #[local] Lemma model_agree γ vs1 vs2 :
    model₁ γ vs1 -∗
    model₂ γ vs2 -∗
    ⌜vs1 = vs2⌝.
  Proof.
    iIntros "Hmodel₁ Hmodel₂".
    iDestruct (auth_twins_agree_L with "Hmodel₁ Hmodel₂") as %->.
    iSteps.
  Qed.
  #[local] Lemma model_push {γ stable back ws vs1 vs2} v :
    producer₁ γ stable back ws -∗
    model₁ γ vs1 -∗
    model₂ γ vs2 ==∗
      producer₁ γ stable back (vs1 ++ [v]) ∗
      model₁ γ (vs1 ++ [v]) ∗
      model₂ γ (vs1 ++ [v]).
  Proof.
    iIntros "(:producer₁) Hmodel₁ Hmodel₂".
    iMod (auth_twins_update_auth with "Hmodel_auth Hmodel₁ Hmodel₂") as "(Hmodel_auth & Hmodel₁ & Hmodel₂)".
    iSteps.
  Qed.
  #[local] Lemma model_pop γ v vs1 vs2 :
    model₁ γ (v :: vs1) -∗
    model₂ γ vs2 ==∗
      model₁ γ vs1 ∗
      model₂ γ vs1.
  Proof.
    apply: auth_twins_update_twins_L.
    rewrite preorder_rtc. solve_suffix.
  Qed.

  #[local] Lemma history_alloc :
    ⊢ |==>
      ∃ γ_history,
      history_auth' γ_history [].
  Proof.
    apply mono_list_alloc.
  Qed.
  #[local] Lemma history_at_get {γ hist} i v :
    hist !! i = Some v →
    history_auth γ hist ⊢
    history_at γ i v.
  Proof.
    apply mono_list_at_get.
  Qed.
  #[local] Lemma history_agree γ hist i v :
    history_auth γ hist -∗
    history_at γ i v -∗
    ⌜hist !! i = Some v⌝.
  Proof.
    apply mono_list_at_valid.
  Qed.
  #[local] Lemma history_update {γ hist} v :
    history_auth γ hist ⊢ |==>
    history_auth γ (hist ++ [v]).
  Proof.
    apply mono_list_update_snoc.
  Qed.

  #[local] Lemma producer_agree γ stable1 back1 ws stable2 back2 :
    producer₁ γ stable1 back1 ws -∗
    producer₂ γ stable2 back2 -∗
      ⌜stable1 = stable2⌝ ∗
      ⌜back1 = back2⌝.
  Proof.
    iIntros "(:producer₁) (:producer₂)".
    iDestruct (twins_agree_L with "Hproducer₁ Hproducer₂") as %<-.
    iDestruct (auth_nat_max_auth_agree with "Hback_auth₁ Hback_auth₂") as %<-.
    iSteps.
  Qed.
  #[local] Lemma producer_update_stability {γ stable1 back1 ws stable2 back2} stable :
    producer₁ γ stable1 back1 ws -∗
    producer₂ γ stable2 back2 ==∗
      producer₁ γ stable back1 ws ∗
      producer₂ γ stable back2.
  Proof.
    iIntros "(:producer₁) (:producer₂)".
    iMod (twins_update' with "Hproducer₁ Hproducer₂") as "(Hproducer₁ & Hproducer₂)".
    iSteps.
  Qed.
  #[local] Lemma producer_update_back {γ stable1 back1 ws stable2 back2} back :
    back1 ≤ back →
    producer₁ γ stable1 back1 ws -∗
    producer₂ γ stable2 back2 ==∗
      producer₁ γ stable1 back ws ∗
      producer₂ γ stable2 back.
  Proof.
    iIntros "% (:producer₁) (:producer₂)".
    iDestruct (auth_nat_max_auth_agree with "Hback_auth₁ Hback_auth₂") as %->.
    iCombine "Hback_auth₁ Hback_auth₂" as "Hback_auth".
    iMod (auth_nat_max_update with "Hback_auth") as "(Hback_auth₁ & Hback_auth₂)"; first done.
    iSteps.
  Qed.
  #[local] Lemma back_lb_get γ stable back :
    producer₂ γ stable back ⊢
    back_lb γ back.
  Proof.
    iIntros "(:producer₂)".
    iApply (auth_nat_max_lb_get with "Hback_auth₂").
  Qed.
  #[local] Lemma back_lb_valid γ stable back1 back2 :
    producer₂ γ stable back1 -∗
    back_lb γ back2 -∗
    ⌜back2 ≤ back1⌝.
  Proof.
    iIntros "(:producer₂) Hback_lb".
    iApply (auth_nat_max_lb_valid with "Hback_auth₂ Hback_lb").
  Qed.

  #[local] Lemma consumer_alloc :
    ⊢ |==>
      ∃ γ_consumer γ_front,
      consumer₁' γ_consumer γ_front Stable 0 ∗
      consumer₂' γ_consumer γ_front Stable 0.
  Proof.
    iMod twins_alloc' as "(%γ_consumer & Hconsumer₁ & Hconsumer₂)".
    iMod auth_nat_max_alloc as "(%γ_front & Hfront_auth₁ & Hfront_auth₂)".
    iSteps.
  Qed.
  #[local] Lemma consumer_agree γ stable1 front1 stable2 front2 :
    consumer₁ γ stable1 front1 -∗
    consumer₂ γ stable2 front2 -∗
      ⌜stable1 = stable2⌝ ∗
      ⌜front1 = front2⌝.
  Proof.
    iIntros "(:consumer₁) (:consumer₂)".
    iDestruct (twins_agree_L with "Hconsumer₁ Hconsumer₂") as %<-.
    iDestruct (auth_nat_max_auth_agree with "Hfront_auth₁ Hfront_auth₂") as %<-.
    iSteps.
  Qed.
  #[local] Lemma consumer_update_front {γ stable1 front1 stable2 front2} front :
    front1 ≤ front →
    consumer₁ γ stable1 front1 -∗
    consumer₂ γ stable2 front2 ==∗
      consumer₁ γ stable1 front ∗
      consumer₂ γ stable2 front.
  Proof.
    iIntros "% (:consumer₁) (:consumer₂)".
    iDestruct (auth_nat_max_auth_agree with "Hfront_auth₁ Hfront_auth₂") as %->.
    iCombine "Hfront_auth₁ Hfront_auth₂" as "Hfront_auth".
    iMod (auth_nat_max_update with "Hfront_auth") as "(Hauth_auth₁ & Hfront_auth₂)"; first done.
    iSteps.
  Qed.
  #[local] Lemma consumer_update_stability {γ stable1 front1 stable2 front2} stable :
    consumer₁ γ stable1 front1 -∗
    consumer₂ γ stable2 front2 ==∗
      consumer₁ γ stable front1 ∗
      consumer₂ γ stable front2.
  Proof.
    iIntros "(:consumer₁) (:consumer₂)".
    iMod (twins_update' with "Hconsumer₁ Hconsumer₂") as "(Hconsumer₁ & Hconsumer₂)".
    iSteps.
  Qed.
  #[local] Lemma front_lb_get γ stable front :
    consumer₂ γ stable front ⊢
    front_lb γ front.
  Proof.
    iIntros "(:consumer₂)".
    iApply (auth_nat_max_lb_get with "Hfront_auth₂").
  Qed.
  #[local] Lemma front_lb_valid γ stable front1 front2 :
    consumer₂ γ stable front1 -∗
    front_lb γ front2 -∗
    ⌜front2 ≤ front1⌝.
  Proof.
    iIntros "(:consumer₂) Hfront_lb".
    iApply (auth_nat_max_lb_valid with "Hfront_auth₂ Hfront_lb").
  Qed.

  Opaque producer₁'.
  Opaque producer₂'.
  Opaque consumer₁'.
  Opaque consumer₂'.

  Lemma spsc_bqueue_producer_exclusive t ws :
    spsc_bqueue_producer t ws -∗
    spsc_bqueue_producer t ws -∗
    False.
  Proof.
    iSteps.
  Qed.
  Lemma spsc_bqueue_model_valid t ws vs :
    spsc_bqueue_producer t ws -∗
    spsc_bqueue_model t vs -∗
    ⌜vs `suffix_of` ws⌝.
  Proof.
    iIntros "(:producer =) (:model)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iApply (model_valid with "Hproducer₁ Hmodel₁").
  Qed.

  Lemma spsc_bqueue_consumer_exclusive t :
    spsc_bqueue_consumer t -∗
    spsc_bqueue_consumer t -∗
    False.
  Proof.
    iSteps.
  Qed.

  #[local] Instance hint_array_cslice_nil t cap i dq :
    HINT ε₁ ✱ [- ; array_inv t cap] ⊫ [id]; array_cslice t cap i dq [] ✱ [emp].
  Proof.
    iSteps. rewrite array_cslice_nil. iSteps.
  Qed.

  Lemma spsc_bqueue_create_spec ι cap :
    (0 ≤ cap)%Z →
    {{{
      True
    }}}
      spsc_bqueue_create #cap
    {{{ t,
      RET t;
      spsc_bqueue_inv t ι ₊cap ∗
      spsc_bqueue_model t [] ∗
      spsc_bqueue_producer t [] ∗
      spsc_bqueue_consumer t
    }}}.
  Proof.
    iIntros "%Hcap %Φ _ HΦ".

    wp_rec.
    iApply wp_fupd.
    wp_apply (array_unsafe_make_spec with "[//]") as "%data Hdata_model"; first done.
    iDestruct (array_model_to_inv with "Hdata_model") as "#Hdata_inv". simpl_length.
    wp_block l as "Hmeta" "(Hl_data & Hl_front & Hl_front_cache & Hl_back & Hl_back_cache & _)".
    iMod (pointsto_persist with "Hl_data") as "#Hl_data".

    iMod model_producer_alloc as "(%γ_model & %γ_producer & %γ_back & Hmodel₁ & Hmodel₂ & Hproducer₁ & Hproducer₂)".
    iMod history_alloc as "(%γ_history & Hhistory_auth)".
    iMod consumer_alloc as "(%γ_consumer & %γ_front & Hconsumer₁ & Hconsumer₂)".

    pose γ := {|
      metadata_capacity := ₊cap ;
      metadata_data := data ;
      metadata_model := γ_model ;
      metadata_history := γ_history ;
      metadata_producer := γ_producer ;
      metadata_back := γ_back ;
      metadata_consumer := γ_consumer ;
      metadata_front := γ_front ;
    |}.
    iMod (meta_set γ with "Hmeta") as "#Hmeta"; first done.

    iDestruct (back_lb_get γ with "Hproducer₂") as "#Hback_lb".
    iDestruct (front_lb_get γ with "Hconsumer₂") as "#Hfront_lb".

    iApply "HΦ".
    iSplitL "Hdata_model Hl_front Hl_back Hmodel₂ Hhistory_auth Hproducer₂ Hconsumer₂"; last iSteps.
    iExists l, γ. iStep 5.
    iApply inv_alloc. iExists Stable, 0, Stable, 0, [], []. iStep 11.
    Z_to_nat cap. rewrite Nat2Z.id. destruct cap as [| cap]; first iSteps.
    iDestruct (array_model_to_cslice with "Hdata_model") as "Hdata_cslice".
    rewrite length_replicate -(take_drop 1 (replicate _ _)).
    iDestruct (array_cslice_app with "Hdata_cslice") as "(Hback & Hextra)".
    rewrite Nat.add_0_l take_replicate_add. iStep.
    rewrite Nat.sub_0_r. iSteps.
  Qed.

  #[local] Lemma front_spec l γ ι stable front :
    {{{
      inv ι (inv_inner l γ) ∗
      consumer₁ γ stable front
    }}}
      (#l).{front}
    {{{
      RET #front;
      consumer₁ γ stable front
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & Hconsumer₁) HΦ".

    iInv "Hinv" as "(:inv_inner =')".
    wp_load.
    iDestruct (consumer_agree with "Hconsumer₁ Hconsumer₂") as %(<- & <-).
    iSplitR "Hconsumer₁ HΦ". { iFrameSteps. }
    iSteps.
  Qed.

  #[local] Lemma back_spec l γ ι stable back ws :
    {{{
      inv ι (inv_inner l γ) ∗
      producer₁ γ stable back ws
    }}}
      (#l).{back}
    {{{
      RET #back;
      producer₁ γ stable back ws
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & Hproducer₁) HΦ".

    iInv "Hinv" as "(:inv_inner =')".
    wp_load.
    iDestruct (producer_agree with "Hproducer₁ Hproducer₂") as %(<- & <-).
    iSplitR "Hproducer₁ HΦ". { iFrameSteps. }
    iSteps.
  Qed.

  Lemma spsc_bqueue_size_spec_producer t ι cap ws :
    <<<
      spsc_bqueue_inv t ι cap ∗
      spsc_bqueue_producer t ws
    | ∀∀ vs,
      spsc_bqueue_model t vs
    >>>
      spsc_bqueue_size t @ ↑ι
    <<<
      spsc_bqueue_model t vs
    | RET #(length vs);
      spsc_bqueue_producer t ws
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:producer)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp_rec.

    wp_apply (back_spec with "[$Hinv $Hproducer₁]") as "Hproducer₁".
    wp_pures.

    wp_bind (_.{front})%E.
    iInv "Hinv" as "(:inv_inner =2)".
    wp_load.
    iDestruct (producer_agree with "Hproducer₁ Hproducer₂") as %(<- & <-).

    iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %<-.
    iMod ("HΦ" with "[$Hmodel₁]") as "HΦ"; first iSteps.

    iSplitR "Hl_front_cache Hproducer₁ HΦ". { iFrameSteps. }
    assert (⁺back - ⁺front2 = length vs)%Z as Hlen by lia.
    iModIntro. clear- Hlen.

    iSteps. rewrite Hlen. iSteps.
  Qed.
  Lemma spsc_bqueue_size_spec_consumer t ι cap :
    <<<
      spsc_bqueue_inv t ι cap ∗
      spsc_bqueue_consumer t
    | ∀∀ vs,
      spsc_bqueue_model t vs
    >>>
      spsc_bqueue_size t @ ↑ι
    <<<
      spsc_bqueue_model t vs
    | RET #(length vs);
      spsc_bqueue_consumer t
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:consumer)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp_rec.

    wp_bind (_.{back})%E.
    iInv "Hinv" as "(:inv_inner =1)".
    wp_load.
    iDestruct (consumer_agree with "Hconsumer₁ Hconsumer₂") as %(<- & <-).

    iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %<-.
    iMod ("HΦ" with "[$Hmodel₁]") as "HΦ"; first iSteps.

    iSplitR "Hl_back_cache Hconsumer₁ HΦ". { iFrameSteps. }
    assert (⁺back1 - ⁺front = length vs)%Z as Hlen by lia.
    iModIntro. clear- Hlen.

    wp_smart_apply (front_spec with "[$Hinv $Hconsumer₁]") as "Hconsumer₁".
    iSteps. rewrite Hlen. iSteps.
  Qed.

  Lemma spsc_bqueue_is_empty_spec_producer t ι cap ws :
    <<<
      spsc_bqueue_inv t ι cap ∗
      spsc_bqueue_producer t ws
    | ∀∀ vs,
      spsc_bqueue_model t vs
    >>>
      spsc_bqueue_is_empty t @ ↑ι
    <<<
      spsc_bqueue_model t vs
    | RET #(bool_decide (vs = []%list));
      spsc_bqueue_producer t ws
    >>>.
  Proof.
    iIntros "%Φ (#Hinv & Hproducer) HΦ".

    wp_rec.

    wp_apply (spsc_bqueue_size_spec_producer with "[$Hinv $Hproducer]").
    iApply (atomic_update_wand with "HΦ"). iIntros "%vs HΦ Hproducer".

    wp_pures.
    setoid_rewrite (bool_decide_ext _ (vs = [])) at 2; last first.
    { rewrite -length_zero_iff_nil. lia. }
    iApply ("HΦ" with "Hproducer").
  Qed.
  Lemma spsc_bqueue_is_empty_spec_consumer t ι cap :
    <<<
      spsc_bqueue_inv t ι cap ∗
      spsc_bqueue_consumer t
    | ∀∀ vs,
      spsc_bqueue_model t vs
    >>>
      spsc_bqueue_is_empty t @ ↑ι
    <<<
      spsc_bqueue_model t vs
    | RET #(bool_decide (vs = []%list));
      spsc_bqueue_consumer t
    >>>.
  Proof.
    iIntros "%Φ (#Hinv & Hconsumer) HΦ".

    wp_rec.

    wp_apply (spsc_bqueue_size_spec_consumer with "[$Hinv $Hconsumer]").
    iApply (atomic_update_wand with "HΦ"). iIntros "%vs HΦ Hconsumer".

    wp_pures.
    setoid_rewrite (bool_decide_ext _ (vs = [])) at 2; last first.
    { rewrite -length_zero_iff_nil. lia. }
    iApply ("HΦ" with "Hconsumer").
  Qed.

  #[local] Definition au_push l γ ι v Ψ : iProp Σ :=
    AU <{
      ∃∃ vs,
      spsc_bqueue_model #l vs
    }> @ ⊤ ∖ ↑ι, ∅ <{
      spsc_bqueue_model #l (if decide (length vs = γ.(metadata_capacity)) then vs else vs ++ [v]),
    COMM
      Ψ vs
    }>.
  #[local] Lemma spsc_bqueue_push_0_spec l ι γ front_cache stable back ws v Ψ :
    {{{
      meta l nroot γ ∗
      array_inv γ.(metadata_data) γ.(metadata_capacity) ∗
      inv ι (inv_inner l γ) ∗
      l.[front_cache] ↦ #front_cache ∗
      producer₁ γ stable back ws ∗
      front_lb γ front_cache ∗
      au_push l γ ι v Ψ
    }}}
      spsc_bqueue_push_0 #l γ.(metadata_data) #back
    {{{ b front_cache,
      RET #b;
      ⌜b = bool_decide (back < front_cache + γ.(metadata_capacity))⌝ ∗
      l.[front_cache] ↦ #front_cache ∗
      producer₁ γ stable back ws ∗
      front_lb γ front_cache ∗
      if b then
        au_push l γ ι v Ψ
      else
        ∃ vs,
        ⌜length vs = γ.(metadata_capacity)⌝ ∗
        Ψ vs
    }}}.
  Proof.
    iIntros "%Φ (#Hmeta & #Hdata_inv & #Hinv & Hl_front_cache & Hproducer₁ & #Hfront_lb & HΨ) HΦ".

    wp_rec.
    wp_smart_apply (array_size_spec_inv with "Hdata_inv") as "_".
    wp_load. wp_pures.
    case_bool_decide as Hbranch1; wp_pures.

    - iSpecialize ("HΦ" $! true front_cache). rewrite bool_decide_eq_true_2; first lia.
      iSteps.

    - wp_bind (_.{front})%E.
      iInv "Hinv" as "(:inv_inner =1)".
      wp_load.
      iDestruct (producer_agree with "Hproducer₁ Hproducer₂") as %(<- & <-).
      iClear "Hfront_lb". iDestruct (front_lb_get with "Hconsumer₂") as "#Hfront_lb".
      destruct (decide (back < front1 + γ.(metadata_capacity))) as [Hbranch2 | Hbranch2].

      + iSplitR "Hl_front_cache Hproducer₁ HΨ HΦ". { iFrameSteps. }
        iModIntro. clear- Hbranch2.

        wp_store. wp_pures.
        iApply ("HΦ" $! _ front1).
        rewrite !bool_decide_eq_true_2; [lia.. |]. iSteps.

      + assert (length vs1 = γ.(metadata_capacity)) as Hvs1_len by lia.

        iMod "HΨ" as "(%vs & (:model) & _ & HΨ)". injection Heq as <-.
        iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
        iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
        rewrite decide_True; [lia.. |].
        iMod ("HΨ" with "[Hmodel₁]") as "HΨ"; first iSteps.

        iSplitR "Hl_front_cache Hproducer₁ HΨ HΦ". { iFrameSteps. }
        iModIntro. clear- Hbranch2 Hvs1_len.

        wp_store. wp_pures.
        iApply ("HΦ" $! _ front1).
        rewrite !bool_decide_eq_false_2; [lia.. |]. iSteps.
  Qed.
  Lemma spsc_bqueue_push_spec t ι cap ws v :
    <<<
      spsc_bqueue_inv t ι cap ∗
      spsc_bqueue_producer t ws
    | ∀∀ vs,
      spsc_bqueue_model t vs
    >>>
      spsc_bqueue_push t v @ ↑ι
    <<<
      spsc_bqueue_model t (if decide (length vs = cap) then vs else vs ++ [v])
    | RET #(bool_decide (length vs = cap));
      spsc_bqueue_producer t (if decide (length vs = cap) then ws else vs ++ [v])
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:producer)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp_rec. wp_load.
    wp_smart_apply (back_spec with "[$Hinv $Hproducer₁]") as "Hproducer₁".
    iDestruct "Hfront_lb" as "-#Hfront_lb". wp_smart_apply (spsc_bqueue_push_0_spec with "[$]") as (? front_cache') "(-> & Hl_front_cache & Hproducer₁ & #Hfront_lb & HΦ)".
    case_bool_decide as Hbranch.

    - iApply fupd_wp.
      iInv "Hinv" as "(:inv_inner =2)".
      iDestruct (producer_agree with "Hproducer₁ Hproducer₂") as %(<- & <-).
      iDestruct (front_lb_valid with "Hconsumer₂ Hfront_lb") as %Hfront2.
      rewrite decide_False; first lia.
      iMod (producer_update_stability Unstable with "Hproducer₁ Hproducer₂") as "(Hproducer₁ & Hproducer₂)".
      iSplitR "Hl_front_cache Hproducer₁ Hback HΦ". { iFrameSteps. }
      iModIntro. clear- Hbranch. iModIntro.

      wp_smart_apply (array_unsafe_cset_spec_cell with "Hback") as "Hback_"; first done.
      wp_pures.

      wp_bind (_ <-{back} _)%E.
      iInv "Hinv" as "(:inv_inner =3)".
      wp_store.
      iDestruct (producer_agree with "Hproducer₁ Hproducer₂") as %(<- & <-).
      iDestruct (front_lb_valid with "Hconsumer₂ Hfront_lb") as %Hfront3_ge.
      iMod (producer_update_stability Stable with "Hproducer₁ Hproducer₂") as "(Hproducer₁ & Hproducer₂)".
      iMod (producer_update_back (S back) with "Hproducer₁ Hproducer₂") as "(Hproducer₁ & Hproducer₂)"; first lia.
      iMod (history_update v with "Hhistory_auth") as "Hhistory_auth".

      iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod (model_push v with "Hproducer₁ Hmodel₁ Hmodel₂") as "(Hproducer₁ & Hmodel₁ & Hmodel₂)".
      rewrite !decide_False; [lia.. |]. rewrite bool_decide_eq_false_2; first lia.
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.

      iSplitR "Hl_front_cache Hproducer₁ HΦ".
      { do 2 iModIntro. iExists _, front3, _, (S back), (vs3 ++ [v]), (hist3 ++ [v]). iFrame.
        simpl_length. iStep 3.
        iSplit. { rewrite Hvs3 drop_app_le //; first lia. }
        iStep.
        rewrite assoc. iSplitL "Hfront Hvs Hback_".
        - destruct vs3 as [| v' vs3]; iFrame.
          + assert (front3 = back) as -> by naive_solver lia.
            destruct cstable3; iSteps.
          + rewrite /= !drop_0 fmap_app.
            iApply (array_cslice_app_1 with "Hvs Hback_").
            simpl_length. naive_solver lia.
        - case_decide.
          + assert (γ.(metadata_capacity) - (S back - front3) - 1 = 0) as -> by lia.
            iSteps.
          + iDestruct (array_cslice_app_2 [§None%V] (replicate (γ.(metadata_capacity) - (S back - front3) - 1) §None%V) with "Hextra") as "($ & Hextra)".
            { rewrite /= -replicate_S. f_equal. lia. }
            rewrite Nat.add_1_r //.
      }
      iSteps.

    - iDestruct "HΦ" as "(%vs & %Hvs & HΦ)".
      rewrite decide_True // bool_decide_eq_true_2 //.
      iSteps.
  Qed.

  #[local] Definition au_pop l ι Ψ : iProp Σ :=
    AU <{
      ∃∃ vs,
      spsc_bqueue_model #l vs
    }> @ ⊤ ∖ ↑ι, ∅ <{
      spsc_bqueue_model #l (tail vs),
    COMM
      spsc_bqueue_consumer #l -∗
      Ψ (head vs : val)
    }>.
  #[local] Lemma spsc_bqueue_pop_0_spec l ι γ back_cache stable front Ψ :
    {{{
      meta l nroot γ ∗
      inv ι (inv_inner l γ) ∗
      l.[back_cache] ↦ #back_cache ∗
      consumer₁ γ stable front ∗
      back_lb γ back_cache ∗
      au_pop l ι Ψ
    }}}
      spsc_bqueue_pop_0 #l #front
    {{{ b back_cache,
      RET #b;
      ⌜b = bool_decide (front < back_cache)⌝ ∗
      l.[back_cache] ↦ #back_cache ∗
      consumer₁ γ stable front ∗
      back_lb γ back_cache ∗
      if b then
        au_pop l ι Ψ
      else
        spsc_bqueue_consumer #l -∗
        Ψ None
    }}}.
  Proof.
    iIntros "%Φ (#Hmeta & #Hinv & Hl_back_cache & Hconsumer₁ & #Hback_lb & HΨ) HΦ".

    wp_rec.
    wp_load. wp_pures.
    case_bool_decide as Hbranch1; wp_pures.

    - iSpecialize ("HΦ" $! true back_cache). rewrite bool_decide_eq_true_2; first lia.
      iSteps.

    - wp_bind (_.{back})%E.
      iInv "Hinv" as "(:inv_inner =1)".
      wp_load.
      iDestruct (consumer_agree with "Hconsumer₁ Hconsumer₂") as %(<- & <-).
      iClear "Hback_lb". iDestruct (back_lb_get with "Hproducer₂") as "#Hback_lb".
      destruct (decide (front < back1)) as [Hbranch2 | Hbranch2].

      + iSplitR "Hl_back_cache Hconsumer₁ HΨ HΦ". { iFrameSteps. }
        iModIntro. clear- Hbranch2.

        wp_store. wp_pures.
        iApply ("HΦ" $! _ back1).
        rewrite !bool_decide_eq_true_2; [lia.. |]. iSteps.

      + assert (front = back1) as <- by lia.

        iMod "HΨ" as "(%vs & (:model) & _ & HΨ)". injection Heq as <-.
        iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
        iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
        assert (length vs1 = 0) as ->%nil_length_inv by lia.
        iMod ("HΨ" with "[Hmodel₁]") as "HΨ"; first iSteps.

        iSplitR "Hl_back_cache Hconsumer₁ HΨ HΦ". { iFrameSteps. }
        iModIntro. clear- Hbranch2.

        wp_store. wp_pures.
        iApply ("HΦ" $! _ front).
        rewrite !bool_decide_eq_false_2; [lia.. |]. iSteps.
  Qed.
  Lemma spsc_bqueue_pop_spec t ι cap :
    <<<
      spsc_bqueue_inv t ι cap ∗
      spsc_bqueue_consumer t
    | ∀∀ vs,
      spsc_bqueue_model t vs
    >>>
      spsc_bqueue_pop t @ ↑ι
    <<<
      spsc_bqueue_model t (tail vs)
    | RET head vs;
      spsc_bqueue_consumer t
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & (:consumer)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp_rec.
    wp_smart_apply (front_spec with "[$Hinv $Hconsumer₁]") as "Hconsumer₁".
    iDestruct "Hback_lb" as "-#Hback_lb". wp_smart_apply (spsc_bqueue_pop_0_spec with "[$]") as (? back_cache') "(-> & Hl_back_cache & Hconsumer₁ & #Hback_lb & HΦ)".
    case_bool_decide as Hbranch; last iSteps.

    iApply fupd_wp.
    iInv "Hinv" as "(:inv_inner =2)".
    iDestruct (consumer_agree with "Hconsumer₁ Hconsumer₂") as %(<- & <-).
    iDestruct (back_lb_valid with "Hproducer₂ Hback_lb") as %Hback2_ge.
    destruct vs2 as [| v vs2]; first naive_solver lia.
    iDestruct (history_at_get front v with "Hhistory_auth") as "#Hhistory_at".
    { rewrite -(take_drop front hist2) -Hvs2 lookup_app_r length_take; first lia.
      rewrite Nat.min_l; first lia.
      rewrite Nat.sub_diag //.
    }
    iMod (consumer_update_stability Unstable with "Hconsumer₁ Hconsumer₂") as "(Hconsumer₁ & Hconsumer₂)".
    iSplitR "Hl_back_cache Hconsumer₁ Hfront HΦ". { iFrameSteps. }
    iModIntro. clear- Hbranch. iModIntro.

    wp_load.
    wp_smart_apply (array_unsafe_cget_spec_cell with "Hfront") as "Hfront"; first done.
    wp_smart_apply (array_unsafe_cset_spec_cell with "Hfront") as "Hfront_"; first done.
    wp_pures.

    wp_bind (_ <-{front} _)%E.
    iInv "Hinv" as "(:inv_inner =3)".
    wp_store.
    iDestruct (consumer_agree with "Hconsumer₁ Hconsumer₂") as %(<- & <-).
    iDestruct (back_lb_valid with "Hproducer₂ Hback_lb") as %Hback2.
    destruct vs3 as [| _v vs3]; first naive_solver lia.
    iDestruct (history_agree with "Hhistory_auth Hhistory_at") as %Hhist3_lookup.
    assert (_v = v) as ->.
    { move: Hhist3_lookup.
      rewrite -(take_drop front hist3) -Hvs3 lookup_app_r length_take; first lia.
      rewrite Nat.min_l; first lia.
      rewrite Nat.sub_diag. naive_solver.
    }
    rewrite /= drop_0.
    iMod (consumer_update_stability Stable with "Hconsumer₁ Hconsumer₂") as "(Hconsumer₁ & Hconsumer₂)".
    iMod (consumer_update_front (S front) with "Hconsumer₁ Hconsumer₂") as "(Hconsumer₁ & Hconsumer₂)"; first lia.

    iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
    iMod (model_pop with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.

    iSplitR "Hl_back_cache Hconsumer₁ HΦ".
    { do 2 iModIntro. iExists _, (S front), _, back3, vs3, hist3. iFrame. simpl in *.
      iStep 3.
      iSplit. { erewrite drop_S in Hvs3 => //. naive_solver. }
      iStep.
      rewrite assoc. iSplitL "Hvs".
      - rewrite -{1}(take_drop 1 vs3) fmap_app -array_cslice_app. simpl_length.
        destruct vs3.
        2: rewrite Nat.add_1_r.
        all: destruct pstable3; iSteps.
      - iDestruct (array_cslice_shift with "Hfront_") as "Hfront_".
        case_decide as Hcase.
        + rewrite -Hcase decide_False; first lia.
          assert (γ.(metadata_capacity) - (back3 - S front) - 1 = 0) as -> by lia.
          destruct pstable3; iSteps.
        + rewrite decide_False; first lia. iFrame.
          iDestruct (array_cslice_app_1 with "Hextra Hfront_") as "Hextra".
          { simpl_length. lia. }
          rewrite -replicate_S_end.
          assert (S (γ.(metadata_capacity) - (back3 - front) - 1) = γ.(metadata_capacity) - (back3 - S front) - 1) as -> by lia.
          iSteps.
    }
    iSteps.
  Qed.
End spsc_bqueue_G.

From zoo_saturn Require
  spsc_bqueue__opaque.

#[global] Opaque spsc_bqueue_inv.
#[global] Opaque spsc_bqueue_model.
#[global] Opaque spsc_bqueue_producer.
#[global] Opaque spsc_bqueue_consumer.
