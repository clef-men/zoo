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
  prophet_nat.
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
Implicit Types v : val.
Implicit Types vs hist : list val.
Implicit Types slot : optional val.
Implicit Types slots : nat → optional val.
Implicit Types η : gname.
Implicit Types ηs : list gname.

Class InfMpmcQueue1G Σ `{zoo_G : !ZooG Σ} :=
  { #[local] inf_mpmc_queue_1_G_inf_array_G :: InfArrayG Σ
  ; #[local] inf_mpmc_queue_1_G_model_G :: TwinsG Σ (leibnizO (list val))
  ; #[local] inf_mpmc_queue_1_G_history_G :: MonoListG Σ val
  ; #[local] inf_mpmc_queue_1_G_consumer_G :: SavedPredG Σ val
  ; #[local] inf_mpmc_queue_1_G_consumers_G :: MonoListG Σ gname
  ; #[local] inf_mpmc_queue_1_G_token_G :: OneshotG Σ () ()
  ; #[local] inf_mpmc_queue_1_G_tokens_G :: MonoListG Σ gname
  }.

Definition inf_mpmc_queue_1_Σ := #[
  inf_array_Σ ;
  twins_Σ (leibnizO (list val)) ;
  mono_list_Σ val ;
  saved_pred_Σ val ;
  mono_list_Σ gname ;
  oneshot_Σ () () ;
  mono_list_Σ gname
].
#[global] Instance subG_inf_mpmc_queue_1_Σ Σ `{zoo_G : !ZooG Σ} :
  subG inf_mpmc_queue_1_Σ Σ →
  InfMpmcQueue1G Σ.
Proof.
  solve_inG.
Qed.

Module base.
  Section inf_mpmc_queue_1_G.
    Context `{inf_mpmc_queue_1_G : InfMpmcQueue1G Σ}.

    Implicit Types t : location.
    Implicit Types Ψ : val → iProp Σ.

    Record inf_mpmc_queue_1_name :=
      { inf_mpmc_queue_1_name_data : val
      ; inf_mpmc_queue_1_name_inv : namespace
      ; inf_mpmc_queue_1_name_model : gname
      ; inf_mpmc_queue_1_name_history : gname
      ; inf_mpmc_queue_1_name_consumers : gname
      ; inf_mpmc_queue_1_name_tokens : gname
      }.
    Implicit Types γ : inf_mpmc_queue_1_name.

    #[global] Instance inf_mpmc_queue_1_name_eq_dec : EqDecision inf_mpmc_queue_1_name :=
      ltac:(solve_decision).
    #[global] Instance inf_mpmc_queue_1_name_countable :
      Countable inf_mpmc_queue_1_name.
    Proof.
      solve_countable.
    Qed.

    #[local] Definition model₁' γ_model vs :=
      twins_twin1 γ_model (DfracOwn 1) vs.
    #[local] Definition model₁ γ :=
      model₁' γ.(inf_mpmc_queue_1_name_model).
    #[local] Definition model₂' γ_model vs :=
      twins_twin2 γ_model vs.
    #[local] Definition model₂ γ :=
      model₂' γ.(inf_mpmc_queue_1_name_model).

    #[local] Definition history_auth' γ_history hist :=
      mono_list_auth γ_history (DfracOwn 1) hist.
    #[local] Definition history_auth γ :=
      history_auth' γ.(inf_mpmc_queue_1_name_history).
    #[local] Definition history_at γ i v :=
      mono_list_at γ.(inf_mpmc_queue_1_name_history) i v.

    #[local] Definition consumers_auth' γ_consumers i : iProp Σ :=
      ∃ ηs,
      mono_list_auth γ_consumers (DfracOwn 1) ηs ∗
      ⌜length ηs = i⌝.
    #[local] Definition consumers_auth γ i :=
      consumers_auth' γ.(inf_mpmc_queue_1_name_consumers) i.
    #[local] Instance : CustomIpat "consumers_auth" :=
      " ( %ηs{}
        & Hauth{}
        & %Hηs{}
        )
      ".
    #[local] Definition consumers_at γ i Ψ : iProp Σ :=
      ∃ η,
      mono_list_at γ.(inf_mpmc_queue_1_name_consumers) i η ∗
      saved_pred η Ψ.
    #[local] Instance : CustomIpat "consumers_at" :=
      " ( %η{}
        & Hat{}
        & HΨ{}
        )
      ".
    #[local] Definition consumers_lb γ i : iProp Σ :=
      ∃ ηs,
      ⌜length ηs = i⌝ ∗
      mono_list_lb γ.(inf_mpmc_queue_1_name_consumers) ηs.
    #[local] Instance : CustomIpat "consumers_lb" :=
      " ( %ηs{}
        & %Hηs{}
        & Hlb{}
        )
      ".

    #[local] Definition tokens_auth' γ_tokens i : iProp Σ :=
      ∃ ηs,
      mono_list_auth γ_tokens (DfracOwn 1) ηs ∗
      ⌜length ηs = i⌝.
    #[local] Definition tokens_auth γ i :=
      tokens_auth' γ.(inf_mpmc_queue_1_name_tokens) i.
    #[local] Instance : CustomIpat "tokens_auth" :=
      " ( %ηs{}
        & Hauth{}
        & %Hηs{}
        )
      ".
    #[local] Definition tokens_pending γ i : iProp Σ :=
      ∃ η,
      mono_list_at γ.(inf_mpmc_queue_1_name_tokens) i η ∗
      oneshot_pending η (DfracOwn 1) ().
    #[local] Instance : CustomIpat "tokens_pending" :=
      " ( %η{}
        & Hat{}
        & Hpending{}
        )
      ".
    #[local] Definition tokens_done γ i : iProp Σ :=
      ∃ η,
      mono_list_at γ.(inf_mpmc_queue_1_name_tokens) i η ∗
      oneshot_shot η ().
    #[local] Instance : CustomIpat "tokens_done" :=
      " ( %η{}
        & Hat{}
        & Hshot{}
        )
      ".

    #[local] Definition consumer_au γ Ψ : iProp Σ :=
      AU <{
        ∃∃ vs,
        model₁ γ vs
      }> @ ⊤ ∖ ↑γ.(inf_mpmc_queue_1_name_inv), ∅ <{
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
    #[local] Definition inv_inner t γ : iProp Σ :=
      ∃ front back hist slots,
      t.[front] ↦ #front ∗
      t.[back] ↦ #back ∗
      inf_array_model γ.(inf_mpmc_queue_1_name_data) (optional_to_val ∘ slots) ∗
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
        consumer_au γ Ψ
      ) ∗
      (∀ i, slot_model γ i (slots i)).
    #[local] Instance : CustomIpat "inv_inner" :=
      " ( %front{}
        & %back{}
        & %hist{}
        & %slots{}
        & Ht_front
        & Ht_back
        & >Hdata_model
        & >Hhistory_auth
        & >%Hhist{}
        & Hmodel₂
        & Hconsumers_auth
        & Htokens_auth
        & Hpast
        & Hwaiters
        & Hslots
        )
      ".
    Definition inv' t γ : iProp Σ :=
      t.[data] ↦□ γ.(inf_mpmc_queue_1_name_data) ∗
      inf_array_inv γ.(inf_mpmc_queue_1_name_data) ∗
      inv γ.(inf_mpmc_queue_1_name_inv) (inv_inner t γ).
    #[local] Instance : CustomIpat "inv'" :=
      " ( #Ht_data
        & #Hdata_inv
        & #Hinv
        )
      ".
    Definition inf_mpmc_queue_1_inv t γ ι : iProp Σ :=
      ⌜ι = γ.(inf_mpmc_queue_1_name_inv)⌝ ∗
      inv' t γ.
    #[local] Instance : CustomIpat "inv" :=
      " ( ->
        & (:inv')
        )
      ".

    Definition inf_mpmc_queue_1_model :=
      model₁.
    #[local] Instance : CustomIpat "model" :=
      " Hmodel₁{_{}}
      ".

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
    #[global] Instance inf_mpmc_queue_1_model_timeless γ vs :
      Timeless (inf_mpmc_queue_1_model γ vs).
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
    #[global] Instance inf_mpmc_queue_1_inv_persistent t γ ι :
      Persistent (inf_mpmc_queue_1_inv t γ ι).
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
    #[local] Lemma model₁_exclusive γ vs1 vs2 :
      model₁ γ vs1 -∗
      model₁ γ vs2 -∗
      False.
    Proof.
      apply twins_twin1_exclusive.
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
      apply twins_update.
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
    #[local] Lemma consumers_lb_get γ i :
      consumers_auth γ i ⊢
      consumers_lb γ i.
    Proof.
      iIntros "(:consumers_auth)".
      iDestruct (mono_list_lb_get with "Hauth") as "Hlb".
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
      iFrame. simpl_length. iSteps.
    Qed.
    Opaque consumers_auth'.
    Opaque consumers_at.
    Opaque consumers_lb.

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
      iFrame. simpl_length. iSteps.
    Qed.
    #[local] Lemma tokens_pending_update γ i :
      tokens_pending γ i ⊢ |==>
      tokens_done γ i.
    Proof.
      iIntros "(:tokens_pending)".
      iMod (oneshot_update_shot with "Hpending") as "Hshot".
      iSteps.
    Qed.
    Opaque tokens_auth'.
    Opaque tokens_pending.
    Opaque tokens_done.

    Lemma inf_mpmc_queue_1_model_exclusive γ vs1 vs2 :
      inf_mpmc_queue_1_model γ vs1 -∗
      inf_mpmc_queue_1_model γ vs2 -∗
      False.
    Proof.
      iIntros "(:model =1) (:model =2)".
      iApply (model₁_exclusive with "Hmodel₁_1 Hmodel₁_2").
    Qed.

    Lemma inf_mpmc_queue_1_create𑁒spec ι :
      {{{
        True
      }}}
        inf_mpmc_queue_1_create ()
      {{{
        t γ
      , RET #t;
        meta_token t ⊤ ∗
        inf_mpmc_queue_1_inv t γ ι ∗
        inf_mpmc_queue_1_model γ []
      }}}.
    Proof.
      iIntros "%Φ _ HΦ".

      wp_rec.
      wp_apply (inf_array_create𑁒spec with "[//]") as (data) "(#Hdata_inv & Hdata_model)".
      wp_block t as "Hmeta" "(Ht_data & Ht_front & Ht_back & _)".
      iMod (pointsto_persist with "Ht_data") as "#Ht_data".

      iMod model_alloc as "(%γ_model & Hmodel₁ & Hmodel₂)".
      iMod history_alloc as "(%γ_history & Hhistory_auth)".
      iMod consumers_alloc as "(%γ_consumers & Hconsumers_auth)".
      iMod tokens_alloc as "(%γ_tokens & Htokens_auth)".

      pose γ := {|
        inf_mpmc_queue_1_name_data := data ;
        inf_mpmc_queue_1_name_inv := ι ;
        inf_mpmc_queue_1_name_model := γ_model ;
        inf_mpmc_queue_1_name_history := γ_history ;
        inf_mpmc_queue_1_name_consumers := γ_consumers ;
        inf_mpmc_queue_1_name_tokens := γ_tokens ;
      |}.

      iApply ("HΦ" $! t γ).
      iFrameSteps. iExists (λ _, Nothing). iSteps.
    Qed.

    Lemma inf_mpmc_queue_1_size𑁒spec t γ ι :
      <<<
        inf_mpmc_queue_1_inv t γ ι
      | ∀∀ vs,
        inf_mpmc_queue_1_model γ vs
      >>>
        inf_mpmc_queue_1_size #t @ ↑ι
      <<<
        inf_mpmc_queue_1_model γ vs
      | RET #(length vs);
        True
      >>>.
    Proof.
      iIntros "%Φ (:inv) HΦ".

      iLöb as "HLöb".

      wp_rec.

      wp_bind (_.{front})%E.
      iInv "Hinv" as "(:inv_inner =1)".
      wp_load.
      iDestruct (consumers_lb_get with "Hconsumers_auth") as "#Hconsumers_lb1".
      iSplitR "HΦ". { iFrameSteps. }
      iIntros "!> {%}".

      wp_apply+ (prophet_typed_1_wp_proph prophet_nat_1 with "[//]") as (pid proph) "Hproph".
      wp_pures.

      wp_bind (_.{back})%E.
      iInv "Hinv" as "(:inv_inner =2)".
      wp_load.
      destruct_decide (proph = front1) as -> | Hproph.

      - destruct_decide (front2 = front1) as -> | ?.

        + iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
          iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
          iMod ("HΦ" with "Hmodel₁ [//]") as "HΦ".

          iSplitR "Hproph HΦ". { iFrameSteps. }
          iIntros "!> {%- Hhist2}".

          wp_pures.

          wp_bind (_.{front})%E.
          iInv "Hinv" as "(:inv_inner =3)".
          wp_load.
          iSplitR "Hproph HΦ". { iFrameSteps. }
          iIntros "!> {%- Hhist2}".

          wp_apply+ (prophet_typed_1_wp_resolve with "Hproph"); [done.. |].
          iSteps.
          rewrite length_drop Hhist2 Z2Nat.inj_sub; first lia.
          rewrite !Nat2Z.id //.

        + iDestruct (consumers_lb_valid with "Hconsumers_auth Hconsumers_lb1") as %?.
          iDestruct (consumers_lb_get with "Hconsumers_auth") as "#Hconsumers_lb2".
          iSplitR "Hproph HΦ". { iFrameSteps. }
          iModIntro.

          wp_pures.

          wp_bind (_.{front})%E.
          iInv "Hinv" as "(:inv_inner =3)".
          wp_load.
          iDestruct (consumers_lb_valid with "Hconsumers_auth Hconsumers_lb2") as %?.
          iSplitR "Hproph HΦ". { iFrameSteps. }
          iModIntro.

          wp_apply+ (prophet_typed_1_wp_resolve with "Hproph"); [done.. |].
          iSteps.

      - iSplitR "Hproph HΦ". { iFrameSteps. }
        iIntros "!> {%- Hproph}".

        wp_pures.

        wp_bind (_.{front})%E.
        iInv "Hinv" as "(:inv_inner =3)".
        wp_load.
        iSplitR "Hproph HΦ". { iFrameSteps. }
        iIntros "!> {%- Hproph}".

        wp_apply+ (prophet_typed_1_wp_resolve with "Hproph"); [done.. |].
        iSteps.
    Qed.

    Lemma inf_mpmc_queue_1_is_empty𑁒spec t γ ι :
      <<<
        inf_mpmc_queue_1_inv t γ ι
      | ∀∀ vs,
        inf_mpmc_queue_1_model γ vs
      >>>
        inf_mpmc_queue_1_is_empty #t @ ↑ι
      <<<
        inf_mpmc_queue_1_model γ vs
      | RET #(bool_decide (vs = []%list));
        True
      >>>.
    Proof.
      iIntros "%Φ #Hinv HΦ".

      wp_rec.

      awp_apply (inf_mpmc_queue_1_size𑁒spec with "Hinv").
      iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs Hmodel".
      iAaccIntro with "Hmodel"; iSteps.
      destruct vs; iSteps.
    Qed.

    Lemma inf_mpmc_queue_1_push𑁒spec t γ ι v :
      <<<
        inf_mpmc_queue_1_inv t γ ι
      | ∀∀ vs,
        inf_mpmc_queue_1_model γ vs
      >>>
        inf_mpmc_queue_1_push #t v @ ↑ι
      <<<
        inf_mpmc_queue_1_model γ (vs ++ [v])
      | RET ();
        True
      >>>.
    Proof.
      iIntros "%Φ (:inv) HΦ".

      wp_rec. wp_pures.

      wp_bind (FAA _ _).
      wp_apply (wp_wand (λ res,
        ∃ back,
        ⌜res = #back⌝ ∗
        history_at γ back v ∗
        Φ ()%V
      )%I with "[HΦ]") as (res) "(%back & -> & #Hhistory_at & HΦ)".
      { iInv "Hinv" as "(:inv_inner =1)".
        wp_faa.

        iMod (history_update v with "Hhistory_auth") as "(History_auth & #Hhistory_at)".
        iEval (rewrite Hhist1) in "Hhistory_at".

        iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
        iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %Hvs.
        iMod (model_update (vs ++ [v]) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
        iMod ("HΦ" with "Hmodel₁ [//]") as "$".

        destruct_decide (front1 ≤ back1) as Hback1.

        - rewrite Nat.max_r //.

          iMod (tokens_update with "Htokens_auth") as "(Htokens_auth & Htokens_at)".
          iDestruct (big_sepL_seq_snoc_2 with "Hpast [$Htokens_at]") as "Hpast".

          iSplitL.
          { iExists front1, (S back1). iFrame.
            simpl_length.
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

      awp_apply (inf_array_set𑁒spec with "Hdata_inv") without "HΦ"; first lia.
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

    #[local] Lemma inf_mpmc_queue_1_pop_0𑁒spec t γ front Ψ :
      {{{
        inv' t γ ∗
        consumers_at γ front Ψ ∗
        tokens_pending γ front
      }}}
        inf_mpmc_queue_1_pop_0 #t #front
      {{{
        v
      , RET v;
        Ψ v
      }}}.
    Proof.
      iIntros "%Φ ((:inv') & #Hconsumers_at & Htokens_pending) HΦ".

      iLöb as "HLöb".

      wp_rec credit:"H£". wp_load.

      awp_apply (inf_array_get𑁒spec with "Hdata_inv") without "Htokens_pending H£ HΦ"; first lia.
      iInv "Hinv" as "(:inv_inner =1)".
      iAaccIntro with "Hdata_model"; first auto with iFrame. iIntros "Hdata_model".
      iAssert (▷ slot_model γ front (slots1 front))%I with "[Hslots]" as "#>Hslot"; first iSteps.
      iSplitL. { iFrameSteps. }
      iIntros "!> _ (Htokens_pending & H£ & HΦ) {%}".

      rewrite Nat2Z.id /=. destruct (slots1 front) as [| | v].

      - iStep 8.
        wp_apply ("HLöb" with "Htokens_pending HΦ").

      - iDestruct (tokens_pending_done with "Htokens_pending Hslot") as %[].

      - wp_load.

        awp_apply (inf_array_set𑁒spec with "Hdata_inv") without "H£"; first lia.
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
    Lemma inf_mpmc_queue_1_pop𑁒spec t γ ι :
      <<<
        inf_mpmc_queue_1_inv t γ ι
      | ∀∀ vs,
        inf_mpmc_queue_1_model γ vs
      >>>
        inf_mpmc_queue_1_pop #t @ ↑ι
      <<<
        ∃∃ v vs',
        ⌜vs = v :: vs'⌝ ∗
        inf_mpmc_queue_1_model γ vs'
      | RET v;
        True
      >>>.
    Proof.
      iIntros "%Φ (:inv) HΦ".

      wp_rec. wp_pures.

      wp_bind (FAA _ _).
      wp_apply (wp_wand (λ res,
        ∃ front,
        ⌜res = #front⌝ ∗
        consumers_at γ front Φ ∗
        tokens_pending γ front
      )%I with "[HΦ]") as (res) "(%front & -> & Hconsumers_at & Htokens_pending)".
      { iInv "Hinv" as "(:inv_inner)".
        wp_faa.
        destruct_decide (front < back) as Hfront1.

        - rewrite Nat.max_r; first lia.
          destruct (lookup_lt_is_Some_2 hist front) as (v & Hhist_lookup); first lia.
          erewrite drop_S; last done.

          iDestruct (history_at_get with "Hhistory_auth") as "#Hhistory_at"; first done.
          iDestruct (big_sepL_seq_lookup_acc front with "Hpast") as "([$ | (%Ψ & Hconsumers_at & _)] & Hpast)"; first lia; last first.
          { iDestruct (consumers_at_valid with "Hconsumers_auth Hconsumers_at") as %?. lia. }
          iMod (consumers_update Φ with "Hconsumers_auth") as "(Hconsumers_auth & #Hconsumers_at)".

          iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
          iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
          iMod (model_update (drop (S front) hist) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
          iMod ("HΦ" with "[$Hmodel₁ //] [//]") as "HΦ".

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
            iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model)".
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

      wp_apply+ (inf_mpmc_queue_1_pop_0𑁒spec with "[$Hconsumers_at $Htokens_pending]"); iSteps.
    Qed.
  End inf_mpmc_queue_1_G.

  #[global] Opaque inf_mpmc_queue_1_inv.
  #[global] Opaque inf_mpmc_queue_1_model.
End base.

From zoo_saturn Require
  inf_mpmc_queue_1__opaque.

Section inf_mpmc_queue_1_G.
  Context `{inf_mpmc_queue_1_G : InfMpmcQueue1G Σ}.

  Implicit Types 𝑡 : location.
  Implicit Types t : val.

  Definition inf_mpmc_queue_1_inv t ι : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.inf_mpmc_queue_1_inv 𝑡 γ ι.
  #[local] Instance : CustomIpat "inv" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hinv{_{}}
      )
    ".

  Definition inf_mpmc_queue_1_model t vs : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.inf_mpmc_queue_1_model γ vs.
  #[local] Instance : CustomIpat "model" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & Hmeta{_{}}
      & Hmodel{_{}}
      )
    ".

  #[global] Instance inf_mpmc_queue_1_model_timeless t vs :
    Timeless (inf_mpmc_queue_1_model t vs).
  Proof.
    apply _.
  Qed.

  #[global] Instance inf_mpmc_queue_1_inv_persistent t ι :
    Persistent (inf_mpmc_queue_1_inv t ι).
  Proof.
    apply _.
  Qed.

  Lemma inf_mpmc_queue_1_model_exclusive t vs1 vs2 :
    inf_mpmc_queue_1_model t vs1 -∗
    inf_mpmc_queue_1_model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.inf_mpmc_queue_1_model_exclusive with "Hmodel_1 Hmodel_2").
  Qed.

  Lemma inf_mpmc_queue_1_create𑁒spec ι :
    {{{
      True
    }}}
      inf_mpmc_queue_1_create ()
    {{{
      t
    , RET t;
      inf_mpmc_queue_1_inv t ι ∗
      inf_mpmc_queue_1_model t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    iApply wp_fupd.
    wp_apply (base.inf_mpmc_queue_1_create𑁒spec with "[//]") as (𝑡 γ) "(Hmeta & Hinv & Hmodel)".
    iMod (meta_set γ with "Hmeta"); first done.
    iSteps.
  Qed.

  Lemma inf_mpmc_queue_1_size𑁒spec t ι :
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
    iIntros "%Φ (:inv) HΦ".

    awp_apply (base.inf_mpmc_queue_1_size𑁒spec with "[$]").
    { iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta_agree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma inf_mpmc_queue_1_is_empty𑁒spec t ι :
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
    iIntros "%Φ (:inv) HΦ".

    awp_apply (base.inf_mpmc_queue_1_is_empty𑁒spec with "[$]").
    { iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta_agree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma inf_mpmc_queue_1_push𑁒spec t ι v :
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
    iIntros "%Φ (:inv) HΦ".

    awp_apply (base.inf_mpmc_queue_1_push𑁒spec with "[$]").
    { iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta_agree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma inf_mpmc_queue_1_pop𑁒spec t ι :
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
    iIntros "%Φ (:inv) HΦ".

    awp_apply (base.inf_mpmc_queue_1_pop𑁒spec with "[$]").
    { iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta_agree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.
End inf_mpmc_queue_1_G.

#[global] Opaque inf_mpmc_queue_1_inv.
#[global] Opaque inf_mpmc_queue_1_model.
