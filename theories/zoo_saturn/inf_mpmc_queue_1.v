From zoo Require Import
  prelude.
From zoo.common Require Import
  countable
  function.
From zoo.iris.base_logic Require Import
  lib.twins
  lib.mono_list
  lib.saved_pred
  lib.oneshot.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  option
  optional
  inf_array.
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
Implicit Types slots : nat → optional val.
Implicit Types η : gname.
Implicit Types ηs : list gname.

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
  #[local] Definition consumers_at γ i Ψ : iProp Σ :=
    ∃ η,
    mono_list_at γ.(metadata_consumers) i η ∗
    saved_pred η Ψ.

  #[local] Definition tokens_auth' γ_tokens i : iProp Σ :=
    ∃ ηs,
    mono_list_auth γ_tokens (DfracOwn 1) ηs ∗
    ⌜length ηs = i⌝.
  #[local] Definition tokens_auth γ i :=
    tokens_auth' γ.(metadata_tokens) i.
  #[local] Definition tokens_pending γ i : iProp Σ :=
    ∃ η,
    mono_list_at γ.(metadata_tokens) i η ∗
    oneshot_pending η (DfracOwn 1) ().
  #[local] Definition tokens_done γ i : iProp Σ :=
    ∃ η,
    mono_list_at γ.(metadata_tokens) i η ∗
    oneshot_shot η ().

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
      ∨ ∃ Ψ v,
        consumers_at γ i Ψ ∗
        history_at γ i v ∗
        Ψ v
    ) ∗
    ( [∗ list] i ∈ seq back (front - back),
      ∃ Ψ,
      consumers_at γ i Ψ ∗
      consumer_au γ ι Ψ
    ) ∗
    ( ∀ i,
      match slots i with
      | Something v =>
          history_at γ i v
      | Anything =>
          tokens_done γ i
      | Nothing =>
          True
      end
    ).
  #[local] Instance : CustomIpatFormat "inv_inner" :=
    "(
      %front{} &
      %back{} &
      %hist{} &
      %slots{} &
      Hl_front &
      Hl_back &
      >Hdata_model &
      Hhistory_auth &
      >%Hhist{} &
      Hmodel₂ &
      Hconsumers_auth &
      Htokens_auth &
      Hpast &
      Hwaiters &
      Hslots
    )".
  Definition inf_mpmc_queue_1_inv t ι : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    l.[data] ↦□ γ.(metadata_data) ∗
    inf_array_inv γ.(metadata_data) ∗
    inv ι (inv_inner l γ ι).
  #[local] Instance : CustomIpatFormat "inv" :=
    "(
      %l &
      %γ &
      -> &
      #Hmeta &
      #Hl_data &
      #Hdata_inv &
      #Hinv
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
  #[global] Instance inf_mpmc_queue_1_inv_persistent t ι :
    Persistent (inf_mpmc_queue_1_inv t ι).
  Proof.
    apply _.
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

  #[local] Lemma tokens_update {γ} i :
    tokens_auth γ i ⊢ |==>
      tokens_auth γ (S i) ∗
      tokens_pending γ i.
  Proof.
    iIntros "(%ηs & Hauth & %Hηs)".
    iMod oneshot_alloc as "(%η & Hpending)".
    iMod (mono_list_update_snoc with "Hauth") as "Hauth".
    iDestruct (mono_list_at_get with "Hauth") as "#Hat".
    { rewrite list_lookup_middle //. }
    iFrame. rewrite length_app. iSteps.
  Qed.

  Opaque consumers_auth'.
  Opaque consumers_at.
  Opaque tokens_auth'.
  Opaque tokens_pending.
  Opaque tokens_done.

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
        iDestruct (big_sepL_snoc with "[$Hpast $Htokens_at]") as "Hpast".
        rewrite -seq_S.

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
        rewrite -cons_seq. iDestruct "Hwaiters" as "((%Ψ & #Hconsumers_at & HΨ) & Hwaiters)".

        iMod "HΨ" as "(% & Hmodel₁ & _ & HΨ)".
        iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
        iMod (model_update [] with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
        iMod ("HΨ" with "[$Hmodel₁ //]") as "HΨ".

        iDestruct (big_sepL_snoc with "[$Hpast HΨ]") as "Hpast"; first iSteps.
        rewrite -seq_S.

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
    iAaccIntro with "Hdata_model".
    { iIntros. iFrame. done. }
    iIntros "Hdata_model !>".
    iSplitL.
    { repeat iExists _.
      rewrite Nat2Z.id -(fn_compose_insert _ _ _ (Something v)).
      iSteps.
      rewrite function.fn_lookup_insert.
      case_decide; first subst; iSteps.
    }
    iSteps.
  Qed.
End inf_mpmc_queue_1_G.

#[global] Opaque inf_mpmc_queue_1_create.
#[global] Opaque inf_mpmc_queue_1_size.
#[global] Opaque inf_mpmc_queue_1_is_empty.
#[global] Opaque inf_mpmc_queue_1_push.
#[global] Opaque inf_mpmc_queue_1_pop.

#[global] Opaque inf_mpmc_queue_1_inv.
#[global] Opaque inf_mpmc_queue_1_model.
