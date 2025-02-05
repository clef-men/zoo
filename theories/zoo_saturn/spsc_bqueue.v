From iris.algebra Require Import
  list.

From zoo Require Import
  prelude.
From zoo.common Require Import
  countable
  relations
  list.
From zoo.iris.base_logic Require Import
  lib.excl
  lib.twins
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
Implicit Types vs hist : list val.

Class SpscBqueueG Σ `{zoo_G : !ZooG Σ} := {
  #[local] spsc_bqueue_G_model_G :: TwinsG Σ (listO val_O) ;
  #[local] spsc_bqueue_G_history_G :: MonoListG Σ val ;
  #[local] spsc_bqueue_G_ctl_G :: AuthNatMaxG Σ ;
  #[local] spsc_bqueue_G_region_G :: ExclG Σ unitO ;
}.

Definition spsc_bqueue_Σ := #[
  twins_Σ (listO val_O) ;
  mono_list_Σ val ;
  auth_nat_max_Σ ;
  excl_Σ unitO
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
    metadata_data : val ;
    metadata_model : gname ;
    metadata_history : gname ;
    metadata_producer_ctl : gname ;
    metadata_producer_region : gname ;
    metadata_consumer_ctl : gname ;
    metadata_consumer_region : gname ;
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
    twins_twin2 γ_model vs.
  #[local] Definition model₁ γ vs :=
    model₁' γ.(metadata_model) vs.
  #[local] Definition model₂' γ_model vs :=
    twins_twin1 γ_model (DfracOwn 1) vs.
  #[local] Definition model₂ γ vs :=
    model₂' γ.(metadata_model) vs.

  #[local] Definition history_auth' γ_history hist :=
    mono_list_auth γ_history (DfracOwn 1) hist.
  #[local] Definition history_auth γ hist :=
    history_auth' γ.(metadata_history) hist.
  #[local] Definition history_at γ i v :=
    mono_list_at γ.(metadata_history) i v.

  #[local] Definition producer_ctl₁' γ_producer_ctl back :=
    auth_nat_max_auth γ_producer_ctl (DfracOwn (1/2)) back.
  #[local] Definition producer_ctl₁ γ back :=
    producer_ctl₁' γ.(metadata_producer_ctl) back.
  #[local] Definition producer_ctl₂' γ_producer_ctl back :=
    auth_nat_max_auth γ_producer_ctl (DfracOwn (1/2)) back.
  #[local] Definition producer_ctl₂ γ back :=
    producer_ctl₂' γ.(metadata_producer_ctl) back.
  #[local] Definition back_lb γ back :=
    auth_nat_max_lb γ.(metadata_producer_ctl) back.

  #[local] Definition producer_region' γ_producer_region :=
    excl γ_producer_region ().
  #[local] Definition producer_region γ :=
    producer_region' γ.(metadata_producer_region).

  #[local] Definition consumer_ctl₁' γ_consumer_ctl front :=
    auth_nat_max_auth γ_consumer_ctl (DfracOwn (1/2)) front.
  #[local] Definition consumer_ctl₁ γ front :=
    consumer_ctl₁' γ.(metadata_consumer_ctl) front.
  #[local] Definition consumer_ctl₂' γ_consumer_ctl front :=
    auth_nat_max_auth γ_consumer_ctl (DfracOwn (1/2)) front.
  #[local] Definition consumer_ctl₂ γ front :=
    consumer_ctl₂' γ.(metadata_consumer_ctl) front.
  #[local] Definition front_lb γ front :=
    auth_nat_max_lb γ.(metadata_consumer_ctl) front.

  #[local] Definition consumer_region' γ_consumer_region :=
    excl γ_consumer_region ().
  #[local] Definition consumer_region γ :=
    consumer_region' γ.(metadata_consumer_region).

  #[local] Definition inv_inner l γ cap : iProp Σ :=
    ∃ front back vs hist,
    ⌜back = (front + length vs)%nat⌝ ∗
    ⌜back ≤ front + cap⌝ ∗
    ⌜length hist = back⌝ ∗
    ⌜vs = drop front hist⌝ ∗
    l.[front] ↦ #front ∗
    consumer_ctl₂ γ front ∗
    l.[back] ↦ #back ∗
    producer_ctl₂ γ back ∗
    model₂ γ vs ∗
    history_auth γ hist ∗
    ( array_cslice γ.(metadata_data) cap front (DfracOwn 1) ((λ v, ‘Some( v )%V) <$> take 1 vs)
    ∨ consumer_region γ
    ) ∗
    array_cslice γ.(metadata_data) cap (S front) (DfracOwn 1) ((λ v, ‘Some( v )%V) <$> drop 1 vs) ∗
    ( array_cslice γ.(metadata_data) cap back (DfracOwn 1) (if decide (back = front + cap) then [] else [§None%V])
    ∨ producer_region γ
    ) ∗
    array_cslice γ.(metadata_data) cap (S back) (DfracOwn 1) (replicate (cap - (back - front) - 1) §None%V).
  #[local] Instance : CustomIpatFormat "inv_inner" :=
    "(
      %front{} &
      %back{} &
      %vs{} &
      %hist{} &
      >%Hback{} &
      >%Hback{}_le &
      >%Hhist{}_len &
      >%Hvs{} &
      >Hl_front &
      >Hconsumer_ctl₂ &
      >Hl_back &
      >Hproducer_ctl₂ &
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
    meta l nroot γ ∗
    l.[data] ↦□ γ.(metadata_data) ∗
    inv ι (inv_inner l γ cap).
  #[local] Instance : CustomIpatFormat "inv" :=
    "(
      %l &
      %γ &
      -> &
      #Hmeta &
      #Hl_data &
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

  Definition spsc_bqueue_producer t : iProp Σ :=
    ∃ l γ front_cache back,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    l.[front_cache] ↦ #front_cache ∗
    producer_ctl₁ γ back ∗
    producer_region γ ∗
    front_lb γ front_cache.
  #[local] Instance : CustomIpatFormat "producer" :=
    "(
      %l_ &
      %γ_ &
      %front_cache &
      %back &
      %Heq &
      #Hmeta_ &
      Hl_front_cache &
      Hproducer_ctl₁ &
      Hproducer_region &
      #Hfront_lb
    )".

  Definition spsc_bqueue_consumer t : iProp Σ :=
    ∃ l γ front back_cache,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    l.[back_cache] ↦ #back_cache ∗
    consumer_ctl₁ γ front ∗
    consumer_region γ ∗
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
      Hconsumer_ctl₁ &
      Hconsumer_region &
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
  #[global] Instance spsc_bqueue_producer_timeless t :
    Timeless (spsc_bqueue_producer t).
  Proof.
    apply _.
  Qed.
  #[global] Instance spsc_bqueue_consumer_timeless t :
    Timeless (spsc_bqueue_consumer t).
  Proof.
    apply _.
  Qed.

  #[local] Lemma model_alloc :
    ⊢ |==>
      ∃ γ_model,
      model₁' γ_model [] ∗
      model₂' γ_model [].
  Proof.
    iMod (twins_alloc' (twins_G := spsc_bqueue_G_model_G) []) as "(%γ_model & Hmodel₁ & Hmodel₂)".
    iSteps.
  Qed.
  #[local] Lemma model_agree γ model1 model2 :
    model₁ γ model1 -∗
    model₂ γ model2 -∗
    ⌜model1 = model2⌝.
  Proof.
    iIntros "Hmodel₁ Hmodel₂".
    iDestruct (twins_agree_L with "Hmodel₂ Hmodel₁") as %->.
    iSteps.
  Qed.
  #[local] Lemma model_update {γ model1 model2} model :
    model₁ γ model1 -∗
    model₂ γ model2 ==∗
      model₁ γ model ∗
      model₂ γ model.
  Proof.
    iIntros "Hmodel₁ Hmodel₂".
    iMod (twins_update' with "Hmodel₂ Hmodel₁") as "(Hmodel₂ & Hmodel₁)".
    iSteps.
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

  #[local] Lemma producer_ctl_alloc :
    ⊢ |==>
      ∃ γ_producer_ctl,
      producer_ctl₁' γ_producer_ctl 0 ∗
      producer_ctl₂' γ_producer_ctl 0.
  Proof.
    iMod auth_nat_max_alloc as "(%γ_producer_ctl & Hproducer_ctl₁ & Hproducer_ctl₂)".
    iSteps.
  Qed.
  #[local] Lemma producer_ctl_agree γ back1 back2 :
    producer_ctl₁ γ back1 -∗
    producer_ctl₂ γ back2 -∗
    ⌜back1 = back2⌝.
  Proof.
    apply auth_nat_max_auth_agree.
  Qed.
  #[local] Lemma producer_ctl_update {γ back1 back2} back :
    back1 ≤ back →
    producer_ctl₁ γ back1 -∗
    producer_ctl₂ γ back2 ==∗
      producer_ctl₁ γ back ∗
      producer_ctl₂ γ back.
  Proof.
    iIntros "%Hle Hproducer_ctl₁ Hproducer_ctl₂".
    iDestruct (auth_nat_max_auth_agree with "Hproducer_ctl₁ Hproducer_ctl₂") as %->.
    iCombine "Hproducer_ctl₁ Hproducer_ctl₂" as "Hproducer_ctl".
    iMod (auth_nat_max_update with "Hproducer_ctl") as "($ & $)"; done.
  Qed.
  #[local] Lemma back_lb_get γ back :
    producer_ctl₂ γ back ⊢
    back_lb γ back.
  Proof.
    apply auth_nat_max_lb_get.
  Qed.
  #[local] Lemma back_lb_valid γ back1 back2 :
    producer_ctl₂ γ back1 -∗
    back_lb γ back2 -∗
    ⌜back2 ≤ back1⌝.
  Proof.
    apply auth_nat_max_lb_valid.
  Qed.

  #[local] Lemma producer_region_alloc :
    ⊢ |==>
      ∃ γ_producer_region,
      producer_region' γ_producer_region.
  Proof.
    apply excl_alloc.
  Qed.
  #[local] Lemma producer_region_exclusive γ :
    producer_region γ -∗
    producer_region γ -∗
    False.
  Proof.
    apply excl_exclusive.
  Qed.

  #[local] Lemma consumer_ctl_alloc :
    ⊢ |==>
      ∃ γ_consumer_ctl,
      consumer_ctl₁' γ_consumer_ctl 0 ∗
      consumer_ctl₂' γ_consumer_ctl 0.
  Proof.
    iMod auth_nat_max_alloc as "(%γ_consumer_ctl & Hconsumer_ctl₁ & Hconsumer_ctl₂)".
    iSteps.
  Qed.
  #[local] Lemma consumer_ctl_agree γ front1 front2 :
    consumer_ctl₁ γ front1 -∗
    consumer_ctl₂ γ front2 -∗
    ⌜front1 = front2⌝.
  Proof.
    apply auth_nat_max_auth_agree.
  Qed.
  #[local] Lemma consumer_ctl_update {γ front1 front2} front :
    front1 ≤ front →
    consumer_ctl₁ γ front1 -∗
    consumer_ctl₂ γ front2 ==∗
      consumer_ctl₁ γ front ∗
      consumer_ctl₂ γ front.
  Proof.
    iIntros "%Hle Hconsumer_ctl₁ Hconsumer_ctl₂".
    iDestruct (auth_nat_max_auth_agree with "Hconsumer_ctl₁ Hconsumer_ctl₂") as %->.
    iCombine "Hconsumer_ctl₁ Hconsumer_ctl₂" as "Hconsumer_ctl".
    iMod (auth_nat_max_update with "Hconsumer_ctl") as "($ & $)"; done.
  Qed.
  #[local] Lemma front_lb_get γ front :
    consumer_ctl₂ γ front ⊢
    front_lb γ front.
  Proof.
    apply auth_nat_max_lb_get.
  Qed.
  #[local] Lemma front_lb_valid γ front1 front2 :
    consumer_ctl₂ γ front1 -∗
    front_lb γ front2 -∗
    ⌜front2 ≤ front1⌝.
  Proof.
    iIntros "Hconsumer_ctl₁ Hfront_lb".
    iApply (auth_nat_max_lb_valid with "Hconsumer_ctl₁ Hfront_lb").
  Qed.

  #[local] Lemma consumer_region_alloc :
    ⊢ |==>
      ∃ γ_consumer_region,
      consumer_region' γ_consumer_region.
  Proof.
    apply excl_alloc.
  Qed.
  #[local] Lemma consumer_region_exclusive γ :
    consumer_region γ -∗
    consumer_region γ -∗
    False.
  Proof.
    apply excl_exclusive.
  Qed.

  Lemma spsc_bqueue_producer_exclusive t :
    spsc_bqueue_producer t -∗
    spsc_bqueue_producer t -∗
    False.
  Proof.
    iSteps.
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
      spsc_bqueue_producer t ∗
      spsc_bqueue_consumer t
    }}}.
  Proof.
    iIntros "%Hcap %Φ _ HΦ".

    wp_rec.
    iApply wp_fupd.
    wp_apply (array_unsafe_make_spec with "[//]") as "%data Hdata_model"; first done.
    wp_block l as "Hmeta" "(Hl_data & Hl_front & Hl_front_cache & Hl_back & Hl_back_cache & _)".
    iMod (pointsto_persist with "Hl_data") as "#Hl_data".

    iMod model_alloc as "(%γ_model & Hmodel₁ & Hmodel₂)".
    iMod history_alloc as "(%γ_history & Hhistory_auth)".
    iMod producer_ctl_alloc as "(%γ_producer_ctl & Hproducer_ctl₁ & Hproducer_ctl₂)".
    iMod producer_region_alloc as "(%γ_producer_region & Hproducer_region)".
    iMod consumer_ctl_alloc as "(%γ_consumer_ctl & Hconsumer_ctl₁ & Hconsumer_ctl₂)".
    iMod consumer_region_alloc as "(%γ_consumer_region & Hconsumer_region)".

    pose γ := {|
      metadata_data := data ;
      metadata_model := γ_model ;
      metadata_history := γ_history ;
      metadata_producer_ctl := γ_producer_ctl ;
      metadata_producer_region := γ_producer_region ;
      metadata_consumer_ctl := γ_consumer_ctl ;
      metadata_consumer_region := γ_consumer_region ;
    |}.
    iMod (meta_set _ _ γ with "Hmeta") as "#Hmeta"; first done.

    iDestruct (back_lb_get γ with "Hproducer_ctl₂") as "#Hback_lb".
    iDestruct (front_lb_get γ with "Hconsumer_ctl₂") as "#Hfront_lb".

    iApply "HΦ".
    iSplitL "Hdata_model Hl_front Hl_back Hmodel₂ Hhistory_auth Hproducer_ctl₂ Hconsumer_ctl₂"; last iSteps.
    iStep 3. iApply inv_alloc. iExists 0, 0, [], []. iStep 7.
    iDestruct (array_model_to_inv with "Hdata_model") as "#Hdata_size". rewrite length_replicate.
    iStep 4.
    Z_to_nat cap. rewrite Nat2Z.id. destruct cap as [| cap]; first iSteps.
    iDestruct (array_model_to_cslice with "Hdata_model") as "Hdata_cslice".
    rewrite length_replicate -(take_drop 1 (replicate _ _)).
    iDestruct (array_cslice_app with "Hdata_cslice") as "(Hback & Hextra)".
    rewrite Nat.add_0_l take_replicate_add. iStep.
    rewrite Nat.sub_0_r. iSteps.
  Qed.

  #[local] Definition spsc_bqueue_push_au l ι cap v Φ : iProp Σ :=
    AU <{
      ∃∃ vs,
      spsc_bqueue_model #l vs
    }> @ ⊤ ∖ ↑ι, ∅ <{
      spsc_bqueue_model #l (if decide (length vs = cap) then vs else vs ++ [v]),
    COMM
      spsc_bqueue_producer #l -∗
      Φ #(bool_decide (length vs = cap))
    }>.
  #[local] Lemma spsc_bqueue_push_0_spec l ι γ cap front_cache back v Ψ :
    {{{
      meta l nroot γ ∗
      inv ι (inv_inner l γ cap) ∗
      array_inv γ.(metadata_data) cap ∗
      l.[front_cache] ↦ #front_cache ∗
      producer_ctl₁ γ back ∗
      front_lb γ front_cache ∗
      spsc_bqueue_push_au l ι cap v Ψ
    }}}
      spsc_bqueue_push_0 #l γ.(metadata_data) #back
    {{{ b front_cache',
      RET #b;
      ⌜b = bool_decide (back < front_cache' + cap)⌝ ∗
      l.[front_cache] ↦ #front_cache' ∗
      producer_ctl₁ γ back ∗
      front_lb γ front_cache' ∗
      if b then
        spsc_bqueue_push_au l ι cap v Ψ
      else
        spsc_bqueue_producer #l -∗
        Ψ #true
    }}}.
  Proof.
    iIntros "%Φ (#Hmeta & #Hinv & #Hdata_inv & Hl_front_cache & Hproducer_ctl₁ & #Hfront_lb & HΨ) HΦ".

    wp_rec.
    wp_smart_apply (array_size_spec_inv with "Hdata_inv") as "_".
    wp_load. wp_pures.
    case_bool_decide as Hbranch1; wp_pures.

    - iSpecialize ("HΦ" $! true front_cache). rewrite bool_decide_eq_true_2; first lia.
      iSteps.

    - wp_bind (_.{front})%E.
      iInv "Hinv" as "(:inv_inner =1)".
      wp_load.
      iDestruct (producer_ctl_agree with "Hproducer_ctl₁ Hproducer_ctl₂") as %<-.
      iClear "Hfront_lb". iDestruct (front_lb_get with "Hconsumer_ctl₂") as "#Hfront_lb".
      destruct (decide (back < front1 + cap)) as [Hbranch2 | Hbranch2].

      + iSplitR "Hl_front_cache Hproducer_ctl₁ HΨ HΦ". { iFrameSteps. }
        iModIntro. clear- Hbranch2.

        wp_store. wp_pures.
        iApply ("HΦ" $! _ front1).
        rewrite !bool_decide_eq_true_2; [lia.. |]. iSteps.

      + iMod "HΨ" as "(%vs & (:model) & _ & HΨ)". injection Heq as <-.
        iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
        iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
        rewrite decide_True; [lia.. |]. rewrite bool_decide_eq_true_2; first lia.
        iMod ("HΨ" with "[Hmodel₁]") as "HΨ"; first iSteps.

        iSplitR "Hl_front_cache Hproducer_ctl₁ HΨ HΦ". { iFrameSteps. }
        iModIntro. clear- Hbranch2.

        wp_store. wp_pures.
        iApply ("HΦ" $! _ front1).
        rewrite !bool_decide_eq_false_2; [lia.. |]. iSteps.
  Qed.
  Lemma spsc_bqueue_push_spec t ι cap v :
    <<<
      spsc_bqueue_inv t ι cap ∗
      spsc_bqueue_producer t
    | ∀∀ vs,
      spsc_bqueue_model t vs
    >>>
      spsc_bqueue_push t v @ ↑ι
    <<<
      spsc_bqueue_model t (if decide (length vs = cap) then vs else vs ++ [v])
    | RET #(bool_decide (length vs = cap));
      spsc_bqueue_producer t
    >>>.
  Proof.
    iIntros "!> %Φ ((:inv) & (:producer)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp_rec. wp_load. wp_pures.

    wp_bind (_.{back})%E.
    iInv "Hinv" as "(:inv_inner =1)".
    wp_load.
    iDestruct (producer_ctl_agree with "Hproducer_ctl₁ Hproducer_ctl₂") as %<-.
    iDestruct (array_cslice_to_inv with "Hvs") as "#Hdata_inv".
    iSplitR "Hl_front_cache Hproducer_ctl₁ Hproducer_region HΦ". { iFrameSteps. }
    iModIntro. clear.

    iDestruct "Hfront_lb" as "-#Hfront_lb". wp_smart_apply (spsc_bqueue_push_0_spec with "[$]") as (? front_cache') "(-> & Hl_front_cache & Hproducer_ctl₁ & #Hfront_lb & HΦ)".
    case_bool_decide as Hbranch; last iSteps.

    iApply fupd_wp.
    iInv "Hinv" as "(:inv_inner =2)".
    iDestruct (producer_ctl_agree with "Hproducer_ctl₁ Hproducer_ctl₂") as %<-.
    iDestruct "Hback" as "[Hback_ | Hproducer_region_]"; last first.
    { iDestruct (producer_region_exclusive with "Hproducer_region Hproducer_region_") as %[]. }
    iDestruct (front_lb_valid with "Hconsumer_ctl₂ Hfront_lb") as %Hfront2.
    rewrite decide_False; first lia.
    iSplitR "Hl_front_cache Hproducer_ctl₁ Hback_ HΦ". { iFrameSteps. }
    iModIntro. clear- Hbranch. iModIntro.

    wp_smart_apply (array_unsafe_cset_spec with "Hback_") as "Hback_"; first done.
    wp_pures.

    wp_bind (_ <-{back} _)%E.
    iInv "Hinv" as "(:inv_inner =3)".
    wp_store.
    iDestruct (producer_ctl_agree with "Hproducer_ctl₁ Hproducer_ctl₂") as %<-.
    iDestruct (front_lb_valid with "Hconsumer_ctl₂ Hfront_lb") as %Hfront3_ge.
    iDestruct "Hback" as "[Hback | Hproducer_region]".
    { rewrite decide_False; first lia.
      iDestruct (array_cslice_exclusive with "Hback Hback_") as %[]; [simpl; lia | done].
    }
    iMod (producer_ctl_update (S back) with "Hproducer_ctl₁ Hproducer_ctl₂") as "(Hproducer_ctl₁ & Hproducer_ctl₂)"; first lia.
    iMod (history_update v with "Hhistory_auth") as "Hhistory_auth".

    iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
    iMod (model_update (vs3 ++ [v]) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    rewrite decide_False; first lia.
    iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
    rewrite bool_decide_eq_false_2; first lia.

    iSplitR "Hl_front_cache Hproducer_ctl₁ Hproducer_region HΦ".
    { do 2 iModIntro. iExists front3, (S back), (vs3 ++ [v]), (hist3 ++ [v]). iFrame.
      rewrite !length_app. iStep 3.
      iSplit. { rewrite Hvs3 drop_app_le //; first lia. }
      iSplitL "Hl_back"; first iSteps.
      rewrite assoc. iSplitL "Hfront Hvs Hback_".
      - destruct vs3 as [| v' vs3].
        + assert (front3 = back) as -> by naive_solver lia. iSteps.
        + iFrame. rewrite /= !drop_0 fmap_app.
          iApply (array_cslice_app_1 with "Hvs Hback_").
          rewrite length_fmap. naive_solver lia.
      - case_decide.
        + assert (cap - (S back - front3) - 1 = 0) as -> by lia. iSteps.
        + iDestruct (array_cslice_app_2 [§None%V] (replicate (cap - (S back - front3) - 1) §None%V) with "Hextra") as "(Hback & Hextra)".
          { rewrite /= -replicate_S. f_equal. lia. }
          rewrite Nat.add_1_r. iSteps.
    }
    iSteps.
  Qed.

  #[local] Definition spsc_bqueue_pop_au l ι Φ : iProp Σ :=
    AU <{
      ∃∃ vs,
      spsc_bqueue_model #l vs
    }> @ ⊤ ∖ ↑ι, ∅ <{
      spsc_bqueue_model #l (tail vs),
    COMM
      spsc_bqueue_consumer #l -∗
      Φ (head vs : val)
    }>.
  #[local] Lemma spsc_bqueue_pop_0_spec l ι γ cap front back_cache Ψ :
    {{{
      meta l nroot γ ∗
      inv ι (inv_inner l γ cap) ∗
      l.[back_cache] ↦ #back_cache ∗
      consumer_ctl₁ γ front ∗
      back_lb γ back_cache ∗
      spsc_bqueue_pop_au l ι Ψ
    }}}
      spsc_bqueue_pop_0 #l #front
    {{{ b back_cache',
      RET #b;
      ⌜b = bool_decide (front < back_cache')⌝ ∗
      l.[back_cache] ↦ #back_cache' ∗
      consumer_ctl₁ γ front ∗
      back_lb γ back_cache' ∗
      if b then
        spsc_bqueue_pop_au l ι Ψ
      else
        spsc_bqueue_consumer #l -∗
        Ψ None
    }}}.
  Proof.
    iIntros "%Φ (#Hmeta & #Hinv & Hl_back_cache & Hconsumer_ctl₁ & #Hback_lb & HΨ) HΦ".

    wp_rec.
    wp_load. wp_pures.
    case_bool_decide as Hbranch1; wp_pures.

    - iSpecialize ("HΦ" $! true back_cache). rewrite bool_decide_eq_true_2; first lia.
      iSteps.

    - wp_bind (_.{back})%E.
      iInv "Hinv" as "(:inv_inner =1)".
      wp_load.
      iDestruct (consumer_ctl_agree with "Hconsumer_ctl₁ Hconsumer_ctl₂") as %<-.
      iClear "Hback_lb". iDestruct (back_lb_get with "Hproducer_ctl₂") as "#Hback_lb".
      destruct (decide (front < back1)) as [Hbranch2 | Hbranch2].

      + iSplitR "Hl_back_cache Hconsumer_ctl₁ HΨ HΦ". { iFrameSteps. }
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

        iSplitR "Hl_back_cache Hconsumer_ctl₁ HΨ HΦ". { iFrameSteps. }
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
    iIntros "!> %Φ ((:inv) & (:consumer)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp_rec. wp_pures.

    wp_bind (_.{front})%E.
    iInv "Hinv" as "(:inv_inner =1)".
    wp_load.
    iDestruct (consumer_ctl_agree with "Hconsumer_ctl₁ Hconsumer_ctl₂") as %<-.
    iDestruct (array_cslice_to_inv with "Hvs") as "#Hdata_inv".
    iSplitR "Hl_back_cache Hconsumer_ctl₁ Hconsumer_region HΦ". { iFrameSteps. }
    iModIntro. clear.

    iDestruct "Hback_lb" as "-#Hback_lb". wp_smart_apply (spsc_bqueue_pop_0_spec with "[$]") as (? back_cache') "(-> & Hl_back_cache & Hconsumer_ctl₁ & #Hback_lb & HΦ)".
    case_bool_decide as Hbranch; last iSteps.

    iApply fupd_wp.
    iInv "Hinv" as "(:inv_inner =2)".
    iDestruct (consumer_ctl_agree with "Hconsumer_ctl₁ Hconsumer_ctl₂") as %<-.
    iDestruct (back_lb_valid with "Hproducer_ctl₂ Hback_lb") as %Hback2_ge.
    destruct vs2 as [| v vs2]; first naive_solver lia.
    iDestruct "Hfront" as "[Hfront_ | Hconsumer_region_]"; last first.
    { iDestruct (consumer_region_exclusive with "Hconsumer_region Hconsumer_region_") as %[]. }
    iDestruct (history_at_get front v with "Hhistory_auth") as "#Hhistory_at".
    { rewrite -(take_drop front hist2) -Hvs2 lookup_app_r length_take; first lia.
      rewrite Nat.min_l; first lia.
      rewrite Nat.sub_diag //.
    }
    iSplitR "Hl_back_cache Hconsumer_ctl₁ Hfront_ HΦ". { iFrameSteps. }
    iModIntro. clear- Hbranch. iModIntro.

    wp_load.
    wp_smart_apply (array_unsafe_cget_spec with "Hfront_") as "Hfront_"; first done.
    wp_smart_apply (array_unsafe_cset_spec with "Hfront_") as "Hfront_"; first done.
    wp_pures.

    wp_bind (_ <-{front} _)%E.
    iInv "Hinv" as "(:inv_inner =3)".
    wp_store.
    iDestruct (consumer_ctl_agree with "Hconsumer_ctl₁ Hconsumer_ctl₂") as %<-.
    iDestruct (back_lb_valid with "Hproducer_ctl₂ Hback_lb") as %Hback2.
    destruct vs3 as [| _v vs3]; first naive_solver lia.
    iDestruct (history_agree with "Hhistory_auth Hhistory_at") as %Hhist3_lookup.
    assert (_v = v) as ->.
    { move: Hhist3_lookup.
      rewrite -(take_drop front hist3) -Hvs3 lookup_app_r length_take; first lia.
      rewrite Nat.min_l; first lia.
      rewrite Nat.sub_diag. naive_solver.
    }
    rewrite /= drop_0.
    iDestruct "Hfront" as "[Hfront | Hconsumer_region]".
    { iDestruct (array_cslice_exclusive with "Hfront Hfront_") as %[]; [simpl; lia | done]. }
    iMod (consumer_ctl_update (S front) with "Hconsumer_ctl₁ Hconsumer_ctl₂") as "(Hconsumer_ctl₁ & Hconsumer_ctl₂)"; first lia.

    iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
    iMod (model_update vs3 with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.

    iSplitR "Hl_back_cache Hconsumer_ctl₁ Hconsumer_region HΦ".
    { do 2 iModIntro. iExists (S front), back3, vs3, hist3. iFrame. simpl in *.
      iStep 3.
      iSplit. { erewrite drop_S in Hvs3 => //. naive_solver. }
      iStep.
      rewrite assoc. iSplitL "Hvs".
      - rewrite -{1}(take_drop 1 vs3) fmap_app -array_cslice_app length_fmap length_take.
        destruct vs3; last rewrite Nat.add_1_r; iSteps.
      - iDestruct (array_cslice_shift with "Hfront_") as "Hfront".
        case_decide as Hcase.
        + rewrite -Hcase decide_False; first lia.
          assert (cap - (back3 - S front) - 1 = 0) as -> by lia.
          iSteps.
        + rewrite decide_False; first lia.
          iFrame.
          iDestruct (array_cslice_app_1 with "Hextra Hfront") as "Hextra".
          { rewrite length_replicate. lia. }
          rewrite -replicate_S_end.
          assert (S (cap - (back3 - front) - 1) = cap - (back3 - S front) - 1) as -> by lia.
          iSteps.
    }
    iSteps.
  Qed.
End spsc_bqueue_G.

#[global] Opaque spsc_bqueue_create.
#[global] Opaque spsc_bqueue_push.
#[global] Opaque spsc_bqueue_pop.

#[global] Opaque spsc_bqueue_inv.
#[global] Opaque spsc_bqueue_model.
#[global] Opaque spsc_bqueue_producer.
#[global] Opaque spsc_bqueue_consumer.
