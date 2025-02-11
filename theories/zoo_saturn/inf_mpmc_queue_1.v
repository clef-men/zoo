From zoo Require Import
  prelude.
From zoo.common Require Import
  countable
  function.
From zoo.iris.bi Require Import
  big_op.
From zoo.iris.base_logic Require Import
  lib.twins
  lib.mono_list
  lib.saved_pred
  lib.oneshot.
From zoo.language Require Import
  notations.
From zoo.program_logic Require Import
  typed_prophet.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  option
  optional
  inf_array
  int.
From zoo_saturn Require Export
  base
  inf_mpmc_queue_1__code.
From zoo_saturn Require Import
  inf_mpmc_queue_1__types.
From zoo Require Import
  options.

Implicit Types front back : nat.
Implicit Types l : location.
Implicit Types t v : val.
Implicit Types vs hist : list val.
Implicit Types slot : optional val.
Implicit Types slots : nat → optional val.
Implicit Types η : gname.
Implicit Types ηs : list gname.

#[local] Program Definition prophet := {|
  typed_strong_prophet1_type :=
    nat ;
  typed_strong_prophet1_of_val v _ :=
    match v with
    | ValInt i =>
        Some (Z.to_nat i)
    | _ =>
        None
    end ;
  typed_strong_prophet1_to_val i :=
    (#i, ()%V) ;
|}.
Solve Obligations of prophet with
  try done.
Next Obligation.
  intros i v _ [= -> ->]. rewrite /= Nat2Z.id //.
Qed.

Class InfMpmcQueue1G Σ `{zoo_G : !ZooG Σ} := {
  #[local] inf_mpmc_queue_1_G_inf_array_G :: InfArrayG Σ ;
  #[local] inf_mpmc_queue_1_G_model_G :: TwinsG Σ (leibnizO (list val)) ;
  #[local] inf_mpmc_queue_1_G_history_G :: MonoListG Σ val ;
  #[local] inf_mpmc_queue_1_G_consumers_list_G :: MonoListG Σ gname ;
  #[local] inf_mpmc_queue_1_G_consumers_pred_G :: SavedPredG Σ val ;
  #[local] inf_mpmc_queue_1_G_tokens_list_G :: MonoListG Σ gname ;
  #[local] inf_mpmc_queue_1_G_tokens_state_G :: OneshotG Σ () () ;
}.

Definition inf_mpmc_queue_1_Σ := #[
  inf_array_Σ ;
  twins_Σ (leibnizO (list val)) ;
  mono_list_Σ val ;
  mono_list_Σ gname ;
  saved_pred_Σ val ;
  mono_list_Σ gname ;
  oneshot_Σ unit unit
].
#[global] Instance subG_inf_mpmc_queue_1_Σ Σ `{zoo_G : !ZooG Σ} :
  subG inf_mpmc_queue_1_Σ Σ →
  InfMpmcQueue1G Σ.
Proof.
  solve_inG.
Qed.

Section inf_mpmc_queue_1_G.
  Context `{inf_mpmc_queue_1_G : InfMpmcQueue1G Σ}.

  Implicit Types Ψ : val → iProp Σ.

  Record metadata := {
    metadata_data : val ;
    metadata_model : gname ;
    metadata_history : gname ;
    metadata_consumers : gname ;
    metadata_tokens : gname ;
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
    twins_twin1 γ_model (DfracOwn 1) vs.
  #[local] Definition model₁ γ :=
    model₁' γ.(metadata_model).
  #[local] Definition model₂' γ_model vs :=
    twins_twin2 γ_model vs.
  #[local] Definition model₂ γ :=
    model₂' γ.(metadata_model).

  #[local] Definition history_auth' γ_history hist :=
    mono_list_auth γ_history (DfracOwn 1) hist.
  #[local] Definition history_auth γ :=
    history_auth' γ.(metadata_history).
  #[local] Definition history_at γ i v :=
    mono_list_at γ.(metadata_history) i v.

  #[local] Definition consumers_auth' γ_consumers i : iProp Σ :=
    ∃ ηs,
    mono_list_auth γ_consumers (DfracOwn 1) ηs ∗
    ⌜length ηs = i⌝.
  #[local] Definition consumers_auth γ i :=
    consumers_auth' γ.(metadata_consumers) i.
  #[local] Instance : CustomIpatFormat "consumers_auth" :=
    "(
      %ηs{} &
      Hauth{} &
      %Hηs{}
    )".
  #[local] Definition consumers_at γ i Ψ : iProp Σ :=
    ∃ η,
    mono_list_at γ.(metadata_consumers) i η ∗
    saved_pred η Ψ.
  #[local] Instance : CustomIpatFormat "consumers_at" :=
    "(
      %η{} &
      Hat{} &
      HΨ{}
    )".
  #[local] Definition consumers_lb γ i : iProp Σ :=
    ∃ ηs,
    ⌜length ηs = i⌝ ∗
    mono_list_lb γ.(metadata_consumers) ηs.
  #[local] Instance : CustomIpatFormat "consumers_lb" :=
    "(
      %ηs{} &
      %Hηs{} &
      Hlb{}
    )".

  #[local] Definition tokens_auth' γ_tokens i : iProp Σ :=
    ∃ ηs,
    mono_list_auth γ_tokens (DfracOwn 1) ηs ∗
    ⌜length ηs = i⌝.
  #[local] Definition tokens_auth γ i :=
    tokens_auth' γ.(metadata_tokens) i.
  #[local] Instance : CustomIpatFormat "tokens_auth" :=
    "(
      %ηs{} &
      Hauth{} &
      %Hηs{}
    )".
  #[local] Definition tokens_pending γ i : iProp Σ :=
    ∃ η,
    mono_list_at γ.(metadata_tokens) i η ∗
    oneshot_pending η (DfracOwn 1) ().
  #[local] Instance : CustomIpatFormat "tokens_pending" :=
    "(
      %η{} &
      Hat{} &
      Hpending{}
    )".
  #[local] Definition tokens_done γ i : iProp Σ :=
    ∃ η,
    mono_list_at γ.(metadata_tokens) i η ∗
    oneshot_shot η ().
  #[local] Instance : CustomIpatFormat "tokens_done" :=
    "(
      %η{} &
      Hat{} &
      Hshot{}
    )".

  #[local] Definition consumer_au γ ι Ψ : iProp Σ :=
    AU <{
      ∃∃ vs,
      model₁ γ vs
    }> @ ⊤ ∖ ↑ι, ∅ <{
      ∀∀ v vs',
      ⌜vs = v :: vs'⌝ ∗
      model₁ γ vs'
    , COMM
      Ψ v
    }>.

  #[local] Definition slot_model γ i slot : iProp Σ :=
    match slot with
    | Something v =>
        history_at γ i v
    | Anything =>
        tokens_done γ i
    | Nothing =>
        True
    end.
  #[local] Definition inv_inner l γ ι : iProp Σ :=
    ∃ front back hist slots,
    l.[front] ↦ #front ∗
    l.[back] ↦ #back ∗
    inf_array_model γ.(metadata_data) (optional_to_val ∘ slots) ∗
    history_auth γ hist ∗
    ⌜length hist = back⌝ ∗
    model₂ γ (drop front hist) ∗
    consumers_auth γ front ∗
    tokens_auth γ (front `max` back) ∗
    ( [∗ list] i ∈ seq 0 back,
        tokens_pending γ i
      ∨ ∃ Ψ,
        consumers_at γ i Ψ ∗
        ( tokens_done γ i
        ∨ ∃ v,
          history_at γ i v ∗
          Ψ v
        )
    ) ∗
    ( [∗ list] i ∈ seq back (front - back),
      ∃ Ψ,
      consumers_at γ i Ψ ∗
      consumer_au γ ι Ψ
    ) ∗
    (∀ i, slot_model γ i (slots i)).
  #[local] Instance : CustomIpatFormat "inv_inner" :=
    "(
      %front{} &
      %back{} &
      %hist{} &
      %slots{} &
      Hl_front &
      Hl_back &
      >Hdata_model &
      >Hhistory_auth &
      >%Hhist{} &
      Hmodel₂ &
      Hconsumers_auth &
      Htokens_auth &
      Hpast &
      Hwaiters &
      Hslots
    )".
  Definition inv' l γ ι : iProp Σ :=
    meta l nroot γ ∗
    l.[data] ↦□ γ.(metadata_data) ∗
    inf_array_inv γ.(metadata_data) ∗
    inv ι (inv_inner l γ ι).
  #[local] Instance : CustomIpatFormat "inv'" :=
    "(
      #Hmeta &
      #Hl_data &
      #Hdata_inv &
      #Hinv
    )".
  Definition inf_mpmc_queue_1_inv t ι : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    inv' l γ ι.
  #[local] Instance : CustomIpatFormat "inv" :=
    "(
      %l &
      %γ &
      -> &
      (:inv')
    )".

  Definition inf_mpmc_queue_1_model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    model₁ γ vs.
  #[local] Instance : CustomIpatFormat "model" :=
    "(
      %_l &
      %_γ &
      %Heq &
      _Hmeta &
      Hmodel₁
    )".

  #[local] Instance tokens_pending_timeless γ i :
    Timeless (tokens_pending γ i).
  Proof.
    apply _.
  Qed.
  #[local] Instance tokens_done_timeless γ i :
    Timeless (tokens_done γ i).
  Proof.
    apply _.
  Qed.
  #[local] Instance slot_model_timeless γ i slot :
    Timeless (slot_model γ i slot).
  Proof.
    rewrite /slot_model. apply _.
  Qed.
  #[global] Instance inf_mpmc_queue_1_model_timeless t vs :
    Timeless (inf_mpmc_queue_1_model t vs).
  Proof.
    apply _.
  Qed.
  #[local] Instance consumers_at_persistent γ i Ψ :
    Persistent (consumers_at γ i Ψ).
  Proof.
    apply _.
  Qed.
  #[local] Instance consumers_lb_persistent γ i :
    Persistent (consumers_lb γ i).
  Proof.
    apply _.
  Qed.
  #[local] Instance tokens_done_persistent γ i :
    Persistent (tokens_done γ i).
  Proof.
    apply _.
  Qed.
  #[local] Instance slot_model_persistent γ i slot :
    Persistent (slot_model γ i slot).
  Proof.
    rewrite /slot_model. apply _.
  Qed.
  #[global] Instance inf_mpmc_queue_1_inv_persistent t ι :
    Persistent (inf_mpmc_queue_1_inv t ι).
  Proof.
    apply _.
  Qed.

  #[local] Lemma model_alloc :
    ⊢ |==>
      ∃ γ_model,
      model₁' γ_model [] ∗
      model₂' γ_model [].
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

  #[local] Lemma history_alloc :
    ⊢ |==>
      ∃ γ_history,
      history_auth' γ_history [].
  Proof.
    apply mono_list_alloc.
  Qed.
  #[local] Lemma history_at_valid γ hist i v :
    history_auth γ hist -∗
    history_at γ i v -∗
    ⌜hist !! i = Some v⌝.
  Proof.
    apply mono_list_at_valid.
  Qed.
  #[local] Lemma history_at_agree γ i v1 v2 :
    history_at γ i v1 -∗
    history_at γ i v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    apply mono_list_at_agree.
  Qed.
  #[local] Lemma history_at_get {γ hist} i v :
    hist !! i = Some v →
    history_auth γ hist ⊢
    history_at γ i v.
  Proof.
    apply mono_list_at_get.
  Qed.
  #[local] Lemma history_update {γ hist} v :
    history_auth γ hist ⊢ |==>
      history_auth γ (hist ++ [v]) ∗
      history_at γ (length hist) v.
  Proof.
    iIntros "Hhistory_auth".
    iMod (mono_list_update_snoc v with "Hhistory_auth") as "Hhistory_auth".
    iDestruct (mono_list_at_get with "Hhistory_auth") as "#Hhistory_at".
    { rewrite list_lookup_middle //. }
    iSteps.
  Qed.

  #[local] Lemma consumers_alloc :
    ⊢ |==>
      ∃ γ_consumers,
      consumers_auth' γ_consumers 0.
  Proof.
    iMod mono_list_alloc as "(%γ_consumers & Hauth)".
    iExists _, []. iSteps.
  Qed.
  #[local] Lemma consumers_at_valid γ i j Ψ :
    consumers_auth γ i -∗
    consumers_at γ j Ψ -∗
    ⌜j < i⌝.
  Proof.
    iIntros "(:consumers_auth) (:consumers_at)".
    iDestruct (mono_list_at_valid with "Hauth Hat") as %?Hj%lookup_lt_Some.
    iSteps.
  Qed.
  #[local] Lemma consumers_at_agree γ i Ψ1 Ψ2 v :
    consumers_at γ i Ψ1 -∗
    ▷ consumers_at γ i Ψ2 -∗
    ▷ Ψ2 v -∗
    ▷^2 Ψ1 v.
  Proof.
    iIntros "(:consumers_at =1) (:consumers_at =2) HΨ !>".
    iDestruct (mono_list_at_agree with "Hat1 Hat2") as %<-.
    iDestruct (saved_pred_agree v with "HΨ1 HΨ2") as "Heq".
    iModIntro. iRewrite "Heq". iSteps.
  Qed.
  #[local] Lemma consumers_lb_valid γ i j :
    consumers_auth γ i -∗
    consumers_lb γ j -∗
    ⌜j ≤ i⌝.
  Proof.
    iIntros "(:consumers_auth =1) (:consumers_lb =2)".
    iDestruct (mono_list_lb_valid with "Hauth1 Hlb2") as %?%prefix_length.
    iSteps.
  Qed.
  #[local] Lemma consumers_update {γ i} Ψ :
    consumers_auth γ i ⊢ |==>
      consumers_auth γ (S i) ∗
      consumers_at γ i Ψ.
  Proof.
    iIntros "(:consumers_auth)".
    iMod (saved_pred_alloc Ψ) as "(%η & HΨ)".
    iMod (mono_list_update_snoc with "Hauth") as "Hauth".
    iDestruct (mono_list_at_get with "Hauth") as "#Hat".
    { rewrite list_lookup_middle //. }
    iFrame. rewrite length_app. iSteps.
  Qed.
  #[local] Lemma consumers_lb_get γ i :
    consumers_auth γ i ⊢
    consumers_lb γ i.
  Proof.
    iIntros "(:consumers_auth)".
    iDestruct (mono_list_lb_get with "Hauth") as "Hlb".
    iSteps.
  Qed.

  #[local] Lemma tokens_alloc :
    ⊢ |==>
      ∃ γ_tokens,
      tokens_auth' γ_tokens 0.
  Proof.
    iMod mono_list_alloc as "(%γ_tokens & Hauth)".
    iExists _, []. iSteps.
  Qed.
  #[local] Lemma tokens_pending_exclusive γ i :
    tokens_pending γ i -∗
    tokens_pending γ i -∗
    False.
  Proof.
    iIntros "(:tokens_pending =1) (:tokens_pending =2)".
    iDestruct (mono_list_at_agree with "Hat1 Hat2") as %<-.
    iApply (oneshot_pending_exclusive with "Hpending1 Hpending2").
  Qed.
  #[local] Lemma tokens_pending_done γ i :
    tokens_pending γ i -∗
    tokens_done γ i -∗
    False.
  Proof.
    iIntros "(:tokens_pending =1) (:tokens_done =2)".
    iDestruct (mono_list_at_agree with "Hat1 Hat2") as %<-.
    iApply (oneshot_pending_shot with "Hpending1 Hshot2").
  Qed.
  #[local] Lemma tokens_update {γ} i :
    tokens_auth γ i ⊢ |==>
      tokens_auth γ (S i) ∗
      tokens_pending γ i.
  Proof.
    iIntros "(:tokens_auth)".
    iMod oneshot_alloc as "(%η & Hpending)".
    iMod (mono_list_update_snoc with "Hauth") as "Hauth".
    iDestruct (mono_list_at_get with "Hauth") as "#Hat".
    { rewrite list_lookup_middle //. }
    iFrame. rewrite length_app. iSteps.
  Qed.
  #[local] Lemma tokens_pending_update γ i :
    tokens_pending γ i ⊢ |==>
    tokens_done γ i.
  Proof.
    iIntros "(:tokens_pending)".
    iMod (oneshot_update_shot with "Hpending") as "Hshot".
    iSteps.
  Qed.

  Opaque consumers_auth'.
  Opaque consumers_at.
  Opaque consumers_lb.
  Opaque tokens_auth'.
  Opaque tokens_pending.
  Opaque tokens_done.

  Lemma inf_mpmc_queue_1_create_spec ι :
    {{{
      True
    }}}
      inf_mpmc_queue_1_create ()
    {{{ t,
      RET t;
      inf_mpmc_queue_1_inv t ι ∗
      inf_mpmc_queue_1_model t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_rec.
    wp_apply (inf_array_create_spec with "[//]") as (data) "(#Hdata_inv & Hdata_model)".
    wp_block l as "Hmeta" "(Hl_data & Hl_front & Hl_back & _)".
    iMod (pointsto_persist with "Hl_data") as "#Hl_data".

    iMod model_alloc as "(%γ_model & Hmodel₁ & Hmodel₂)".
    iMod history_alloc as "(%γ_history & Hhistory_auth)".
    iMod consumers_alloc as "(%γ_consumers & Hconsumers_auth)".
    iMod tokens_alloc as "(%γ_tokens & Htokens_auth)".

    pose γ := {|
      metadata_data := data ;
      metadata_model := γ_model ;
      metadata_history := γ_history ;
      metadata_consumers := γ_consumers ;
      metadata_tokens := γ_tokens ;
    |}.
    iMod (meta_set _ _ γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitR "Hmodel₁"; last iSteps.
    iSteps. iExists (λ _, Nothing). iSteps.
  Qed.

  Lemma inf_mpmc_queue_1_size_spec t ι :
    <<<
      inf_mpmc_queue_1_inv t ι
    | ∀∀ vs,
      inf_mpmc_queue_1_model t vs
    >>>
      inf_mpmc_queue_1_size t @ ↑ι
    <<<
      inf_mpmc_queue_1_model t vs
    | RET #(length vs);
      True
    >>>.
  Proof.
    iIntros "!> %Φ (:inv) HΦ".

    iLöb as "HLöb".

    wp_rec.

    wp_bind (_.{front})%E.
    iInv "Hinv" as "(:inv_inner =1)".
    wp_load.
    iDestruct (consumers_lb_get with "Hconsumers_auth") as "#Hconsumers_lb1".
    iSplitR "HΦ"; first iSteps.
    iModIntro. clear.

    wp_smart_apply (typed_strong_prophet1_wp_proph prophet with "[//]") as (pid proph) "Hproph".
    wp_pures.

    wp_bind (_.{back})%E.
    iInv "Hinv" as "(:inv_inner =2)".
    wp_load.
    destruct (decide (proph = front1)) as [-> | Hproph].

    - destruct (decide (front2 = front1)) as [-> | ?].

      + iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
        iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
        iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
        iMod ("HΦ" with "[Hmodel₁] [//]") as "HΦ"; first iSteps.

        iSplitR "Hproph HΦ"; first iSteps.
        iModIntro. clear- Hhist2.

        wp_smart_apply (typed_strong_prophet1_wp_resolve with "Hproph"); first done.
        iInv "Hinv" as "(:inv_inner =3)".
        wp_load.
        iSplitR "HΦ"; first iSteps.

        iSteps.
        iApply int_positive_part_spec .
        rewrite length_drop Hhist2 Z2Nat.inj_sub; first lia.
        rewrite !Nat2Z.id //.

      + iDestruct (consumers_lb_valid with "Hconsumers_auth Hconsumers_lb1") as %?.
        iDestruct (consumers_lb_get with "Hconsumers_auth") as "#Hconsumers_lb2".
        iSplitR "Hproph HΦ"; first iSteps.
        iModIntro.

        wp_smart_apply (typed_strong_prophet1_wp_resolve with "Hproph"); first done.
        iInv "Hinv" as "(:inv_inner =3)".
        wp_load.
        iDestruct (consumers_lb_valid with "Hconsumers_auth Hconsumers_lb2") as %?.
        iSplitR "HΦ"; first iSteps.
        iSteps.

    - iSplitR "Hproph HΦ"; first iSteps.
      iModIntro. clear- Hproph.

      wp_smart_apply (typed_strong_prophet1_wp_resolve with "Hproph"); first done.
      iInv "Hinv" as "(:inv_inner =3)".
      wp_load.
      iSplitR "HΦ"; first iSteps.
      iSteps.
  Qed.

  Lemma inf_mpmc_queue_1_is_empty_spec t ι :
    <<<
      inf_mpmc_queue_1_inv t ι
    | ∀∀ vs,
      inf_mpmc_queue_1_model t vs
    >>>
      inf_mpmc_queue_1_is_empty t @ ↑ι
    <<<
      inf_mpmc_queue_1_model t vs
    | RET #(bool_decide (vs = []%list));
      True
    >>>.
  Proof.
    iIntros "!> %Φ #Hinv HΦ".

    wp_rec.

    awp_apply (inf_mpmc_queue_1_size_spec with "Hinv").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs Hmodel".
    iAaccIntro with "Hmodel"; iSteps.
    destruct vs; iSteps.
  Qed.

  Lemma inf_mpmc_queue_1_push_spec t ι v :
    <<<
      inf_mpmc_queue_1_inv t ι
    | ∀∀ vs,
      inf_mpmc_queue_1_model t vs
    >>>
      inf_mpmc_queue_1_push t v @ ↑ι
    <<<
      inf_mpmc_queue_1_model t (vs ++ [v])
    | RET ();
      True
    >>>.
  Proof.
    iIntros "!> %Φ (:inv) HΦ".

    wp_rec. wp_pures.

    wp_bind (FAA _ _).
    wp_apply (wp_wand _ _
      ( λ res,
        ∃ back,
        ⌜res = #back⌝ ∗
        history_at γ back v ∗
        Φ ()%V
      )%I
      with "[HΦ]"
    ) as (res) "(%back & -> & #Hhistory_at & HΦ)".
    { iInv "Hinv" as "(:inv_inner =1)".
      wp_faa.

      iMod (history_update v with "Hhistory_auth") as "(History_auth & #Hhistory_at)".
      iEval (rewrite Hhist1) in "Hhistory_at".

      iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %Hvs.
      iMod (model_update (vs ++ [v]) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "[Hmodel₁] [//]") as "$"; first iSteps.

      destruct (decide (front1 ≤ back1)) as [Hback1 | Hback1].

      - rewrite Nat.max_r //.

        iMod (tokens_update with "Htokens_auth") as "(Htokens_auth & Htokens_at)".
        iDestruct (big_sepL_seq_snoc_2 with "Hpast [$Htokens_at]") as "Hpast".

        iSplitL.
        { iExists front1, (S back1). iFrame.
          rewrite length_app /=.
          rewrite Hvs drop_app_le; first lia.
          rewrite Nat.max_r; first lia.
          assert (front1 - S back1 = 0) as -> by lia.
          iSteps.
        }
        iSteps.

      - rewrite Nat.max_l; first lia.
        rewrite (nil_length_inv vs).
        { rewrite Hvs length_drop. lia. }
        assert (front1 - back1 = S (front1 - S back1)) as ->; first lia.
        destruct (Nat.lt_exists_pred 0 (front1 - back1)) as (δ & ? & _); first lia.
        iDestruct (big_sepL_seq_cons_1 with "Hwaiters") as "((%Ψ & #Hconsumers_at & HΨ) & Hwaiters)".

        iMod "HΨ" as "(% & Hmodel₁ & _ & HΨ)".
        iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
        iMod (model_update [] with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
        iMod ("HΨ" with "[$Hmodel₁ //]") as "HΨ".

        iDestruct (big_sepL_seq_snoc_2 with "Hpast [HΨ]") as "Hpast"; first iSteps.

        iSplitL.
        { iFrame.
          rewrite skipn_all2 length_app /=; first lia.
          rewrite Nat.max_l; first lia.
          iSteps.
        }
        iSteps.
    }

    wp_load.

    awp_apply (inf_array_set_spec with "Hdata_inv") without "HΦ"; first lia.
    iInv "Hinv" as "(:inv_inner =2)".
    iAaccIntro with "Hdata_model"; first auto with iFrame. iIntros "Hdata_model !>".
    iSplitL.
    { repeat iExists _.
      rewrite Nat2Z.id -(fn_compose_insert _ _ _ (Something v)).
      iSteps.
      rewrite function.fn_lookup_insert.
      case_decide; first subst; iSteps.
    }
    iSteps.
  Qed.

  #[local] Lemma inf_mpmc_queue_1_pop_0_spec l γ ι front Ψ :
    {{{
      inv' l γ ι ∗
      consumers_at γ front Ψ ∗
      tokens_pending γ front
    }}}
      inf_mpmc_queue_1_pop_0 #l #front
    {{{ v,
      RET v;
      Ψ v
    }}}.
  Proof.
    iIntros "%Φ ((:inv') & #Hconsumers_at & Htokens_pending) HΦ".

    iLöb as "HLöb".

    wp_rec credit:"H£". wp_load.

    awp_apply (inf_array_get_spec with "Hdata_inv") without "Htokens_pending H£ HΦ"; first lia.
    iInv "Hinv" as "(:inv_inner =1)".
    iAaccIntro with "Hdata_model"; first auto with iFrame. iIntros "Hdata_model".
    iAssert (▷ slot_model γ front (slots1 front))%I with "[Hslots]" as "#>Hslot"; first iSteps.
    iSplitL; first iSteps.
    iIntros "!> _ (Htokens_pending & H£ & HΦ) {%}".

    rewrite Nat2Z.id /=. destruct (slots1 front) as [| | v].

    - iStep 7. iModIntro.
      wp_apply ("HLöb" with "Htokens_pending HΦ").

    - iDestruct (tokens_pending_done with "Htokens_pending Hslot") as %[].

    - wp_load.

      awp_apply (inf_array_set_spec with "Hdata_inv") without "H£"; first lia.
      iInv "Hinv" as "(:inv_inner =2)".
      iAaccIntro with "Hdata_model"; first auto with iFrame. iIntros "Hdata_model".
      iDestruct (history_at_valid with "Hhistory_auth Hslot") as %Hhist2_lookup.
      opose proof* lookup_lt_Some as Hfront; first done.
      iDestruct (big_sepL_seq_lookup_acc' front with "Hpast") as "([>Htokens_pending_ | (%Ψ_ & Hconsumers_at_ & [>Htokens_done | (%v_ & >Hhistory_at & HΨ)])] & Hpast)"; first lia.
      { iDestruct (tokens_pending_exclusive with "Htokens_pending Htokens_pending_") as %[]. }
      { iDestruct (tokens_pending_done with "Htokens_pending Htokens_done") as %[]. }
      iDestruct (history_at_agree with "Hslot Hhistory_at") as %<-.
      iDestruct (consumers_at_agree with "Hconsumers_at Hconsumers_at_ HΨ") as "HΨ".
      iMod (tokens_pending_update with "Htokens_pending") as "#Htokens_done".
      iDestruct ("Hpast" with "[]") as "Hpast"; first iSteps.
      iSplitR "HΨ HΦ".
      { rewrite Nat2Z.id -(fn_compose_insert _ _ _ Anything).
        iFrameSteps.
        rewrite function.fn_lookup_insert.
        case_decide; first subst; iSteps.
      }
      iIntros "!> _ H£ {%}".

      iMod (lc_fupd_elim_later with "H£ HΨ") as "HΨ".
      iSteps.
  Qed.
  Lemma inf_mpmc_queue_1_pop_spec t ι :
    <<<
      inf_mpmc_queue_1_inv t ι
    | ∀∀ vs,
      inf_mpmc_queue_1_model t vs
    >>>
      inf_mpmc_queue_1_pop t @ ↑ι
    <<<
      ∃∃ v vs',
      ⌜vs = v :: vs'⌝ ∗
      inf_mpmc_queue_1_model t vs'
    | RET v;
      True
    >>>.
  Proof.
    iIntros "!> %Φ (:inv) HΦ".

    wp_rec. wp_pures.

    wp_bind (FAA _ _).
    wp_apply (wp_wand _ _
      ( λ res,
        ∃ front,
        ⌜res = #front⌝ ∗
        consumers_at γ front Φ ∗
        tokens_pending γ front
      )%I
      with "[HΦ]"
    ) as (res) "(%front & -> & Hconsumers_at & Htokens_pending)".
    { iInv "Hinv" as "(:inv_inner)".
      wp_faa.
      destruct (decide (front < back)) as [Hfront1 | Hfront1].

      - rewrite Nat.max_r; first lia.
        destruct (lookup_lt_is_Some_2 hist front) as (v & Hhist_lookup); first lia.
        erewrite drop_S; last done.

        iDestruct (history_at_get with "Hhistory_auth") as "#Hhistory_at"; first done.
        iDestruct (big_sepL_seq_lookup_acc front with "Hpast") as "([$ | (%Ψ & Hconsumers_at & _)] & Hpast)"; first lia; last first.
        { iDestruct (consumers_at_valid with "Hconsumers_auth Hconsumers_at") as %?. lia. }
        iMod (consumers_update Φ with "Hconsumers_auth") as "(Hconsumers_auth & #Hconsumers_at)".

        iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
        iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
        iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
        iMod (model_update (drop (S front) hist) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
        iMod ("HΦ" with "[Hmodel₁] [//]") as "HΦ"; first iSteps.

        iSplitL.
        { iFrameSteps.
          rewrite Nat.max_r //.
          assert (S front - back = 0) as -> by lia.
          iSteps.
        }
        iSteps.

      - rewrite Nat.max_l; first lia.

        iMod (consumers_update Φ with "Hconsumers_auth") as "(Hconsumers_auth & #Hconsumers_at)".
        iMod (tokens_update with "Htokens_auth") as "(Htokens_auth & $)".
        iDestruct (big_sepL_seq_snoc_2 with "Hwaiters [HΦ]") as "Hwaiters".
        { rewrite -Nat.le_add_sub; first lia.
          iSteps. rewrite /consumer_au. iAuIntro.
          iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model)". injection Heq as <-.
          iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
          iAaccIntro with "Hmodel₁"; iSteps.
        }
        rewrite -Nat.sub_succ_l; first lia.

        iSplitL.
        { iFrameSteps.
          rewrite !skipn_all2; [lia.. |].
          rewrite Nat.max_l; first lia.
          iSteps.
        }
        iSteps.
    }

    wp_smart_apply (inf_mpmc_queue_1_pop_0_spec with "[$Hconsumers_at $Htokens_pending]"); iSteps.
  Qed.
End inf_mpmc_queue_1_G.

#[global] Opaque inf_mpmc_queue_1_create.
#[global] Opaque inf_mpmc_queue_1_size.
#[global] Opaque inf_mpmc_queue_1_is_empty.
#[global] Opaque inf_mpmc_queue_1_push.
#[global] Opaque inf_mpmc_queue_1_pop.

#[global] Opaque inf_mpmc_queue_1_inv.
#[global] Opaque inf_mpmc_queue_1_model.
