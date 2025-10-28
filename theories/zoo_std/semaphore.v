From stdpp Require Import
  finite.

From zoo Require Import
  prelude.
From zoo.common Require Import
  countable.
From zoo.iris.bi Require Import
  big_op.
From zoo.iris.base_logic Require Import
  lib.excl.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
  base
  semaphore__code.
From zoo_std Require Import
  semaphore__types
  condition.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types cnt : nat.
Implicit Types l : location.
Implicit Types t : val.

Class SemaphoreG Σ `{zoo_G : !ZooG Σ} := {
  #[local] semaphore_G_mutex_G :: MutexG Σ ;
  #[local] semaphore_G_tokens_G :: ExclG Σ unitO ;
}.

Definition semaphore_Σ := #[
  mutex_Σ ;
  excl_Σ unitO
].
#[global] Instance subG_semaphore_Σ Σ `{zoo_G : !ZooG Σ} :
  subG semaphore_Σ Σ →
  SemaphoreG Σ.
Proof.
  solve_inG.
Qed.

Section semaphore_G.
  Context `{semaphore_G : SemaphoreG Σ}.

  Implicit Types P : iProp Σ.

  Record metadata := {
    metadata_mutex : val ;
    metadata_condition : val ;
    metadata_tokens : list gname ;
  }.
  Implicit Types γ : metadata.
  Implicit Types γ_tokens : list gname.

  #[local] Instance metadata_eq_dec : EqDecision metadata :=
    ltac:(solve_decision).
  #[local] Instance metadata_countable :
    Countable metadata.
  Proof.
    solve_countable.
  Qed.

  #[local] Definition tokens_auth' γ_tokens cap : iProp Σ :=
    ⌜length γ_tokens = cap⌝.
  #[local] Definition tokens_auth γ :=
    tokens_auth' γ.(metadata_tokens).
  #[local] Instance : CustomIpatFormat "tokens_auth" :=
    "%Htokens".
  #[local] Definition tokens_frag' γ_tokens : iProp Σ :=
    ∃ i η,
    ⌜γ_tokens !! i = Some η⌝ ∗
    excl η ().
  #[local] Definition tokens_frag γ :=
    tokens_frag' γ.(metadata_tokens).
  #[local] Instance : CustomIpatFormat "tokens_frag" :=
    " ( %i &
        %η &
        %Htokens_lookup &
        Hexcl
      )
    ".

  #[local] Definition inv_inner l γ P : iProp Σ :=
    ∃ cnt,
    l.[count] ↦ #cnt ∗
    [∗ list] _ ∈ seq 0 (S cnt),
      tokens_frag γ ∗
      P.
  #[local] Instance : CustomIpatFormat "inv_inner" :=
    " ( %cnt &
        Hl_count &
        H
      )
    ".
  Definition semaphore_inv t cap P : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    l.[mutex] ↦□ γ.(metadata_mutex) ∗
    mutex_inv γ.(metadata_mutex) (inv_inner l γ P) ∗
    l.[condition] ↦□ γ.(metadata_condition) ∗
    condition_inv γ.(metadata_condition) ∗
    tokens_auth γ cap.
  #[local] Instance : CustomIpatFormat "inv" :=
    " ( %l &
        %γ &
        -> &
        #Hmeta &
        #Hl_mutex &
        #Hmutex_inv &
        #Hl_condition &
        #Hcondition_inv &
        #Htokens_auth
      )
    ".

  Definition semaphore_locked t : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    tokens_frag γ.
  #[local] Instance : CustomIpatFormat "locked" :=
    " ( %l_ &
        %γ_ &
        %Heq &
        #Hmeta_ &
        Htokens_frag
      )
    ".

  #[global] Instance semaphore_inv_contractive t cap :
    Contractive (semaphore_inv t cap).
  Proof.
    rewrite /semaphore_inv /inv_inner.
    solve_contractive.
  Qed.
  #[global] Instance semaphore_inv_ne t cap :
    NonExpansive (semaphore_inv t cap).
  Proof.
    apply _.
  Qed.
  #[global] Instance semaphore_inv_proper t cap :
    Proper ((≡) ==> (≡)) (semaphore_inv t cap).
  Proof.
    apply _.
  Qed.

  #[global] Instance semaphore_locked_timeless t :
    Timeless (semaphore_locked t).
  Proof.
    apply _.
  Qed.

  #[local] Instance tokens_auth_persistent γ cap :
    Persistent (tokens_auth γ cap).
  Proof.
    apply _.
  Qed.
  #[global] Instance semaphore_inv_persistent t cap P :
    Persistent (semaphore_inv t cap P).
  Proof.
    apply _.
  Qed.

  #[local] Lemma tokens_alloc cap :
    ⊢ |==>
      ∃ γ_tokens,
      tokens_auth' γ_tokens cap ∗
      [∗ list] _ ∈ seq 0 cap, tokens_frag' γ_tokens.
  Proof.
    iAssert (
      [∗ list] _ ∈ seq 0 cap,
        |==>
        ∃ η,
        excl (excl_G := semaphore_G_tokens_G) η ()
    )%I as "-#H".
    { iApply big_sepL_intro. iIntros "!> % % _".
      iApply excl_alloc.
    }
    iMod (big_sepL_bupd with "H") as "H".
    iDestruct (big_sepL_exists with "H") as "(%ηs & %Hηs & H)". simpl_length in Hηs.
    iDestruct (big_sepL2_retract_r with "H") as "(_ & H)".
    iDestruct (big_sepL_retract_index with "H") as "H".
    iSteps.
  Qed.
  #[local] Lemma tokens_frags_valid γ cap n :
    tokens_auth γ cap -∗
    ([∗ list] _ ∈ seq 0 n, tokens_frag γ) -∗
    ⌜n ≤ cap⌝.
  Proof.
    rewrite Nat.le_ngt.
    iIntros "(:tokens_auth) Htokens_frags %Hn".
    iDestruct (big_sepL_seq_exists with "Htokens_frags") as "(%is & %His & Htokens_frags)".
    iDestruct (big_sepL_exists with "Htokens_frags") as "(%ηs & %Hηs & Htokens_frags)".
    iAssert ⌜ηs ⊆ γ.(metadata_tokens)⌝%I as %(i1 & i2 & η & ? & Htokens_lookup_1 & Htokens_lookup_2)%list_pigeonhole; last lia.
    { iIntros (η Hηs_elem).
      iDestruct (big_sepL2_elem_of_r' with "Htokens_frags") as "(%i & %His_elem & %Htokens_lookup & _)"; first done.
      rewrite elem_of_list_lookup. iSteps.
    }
    iDestruct (big_sepL2_delete'_r i1 with "Htokens_frags") as "(%j1 & _ & (_ & Hexcl_1) & Htokens_frags)"; first done.
    iDestruct (big_sepL2_delete'_r i2 with "Htokens_frags") as "(%j2 & _ & H & Htokens_frags)"; first done.
    iDestruct ("H" with "[%]") as "(_ & Hexcl_2)"; first lia.
    iApply (excl_exclusive with "Hexcl_1 Hexcl_2").
  Qed.

  Opaque tokens_auth.
  Opaque tokens_frag.

  Lemma semaphore_create_spec {cap} P :
    (0 < cap)%Z →
    {{{
      [∗ list] _ ∈ seq 0 ₊cap, P
    }}}
      semaphore_create #cap
    {{{ t,
      RET t;
      semaphore_inv t ₊cap P
    }}}.
  Proof.
    iIntros "%Hcap %Φ HPs HΦ".

    wp_rec.
    wp_smart_apply (condition_create_spec with "[//]") as (cond) "#Hcondition_inv".
    wp_apply (mutex_create_spec_init with "[//]") as (mtx) "Hmutex_init".
    wp_block l as "Hmeta" "(Hl_mutex & Hl_condition & Hl_count & _)".
    iMod (pointsto_persist with "Hl_mutex") as "#Hl_mutex".
    iMod (pointsto_persist with "Hl_condition") as "#Hl_condition".

    iMod tokens_alloc as "(%γ_tokens & Htokens_auth & Htokens_frags)".

    pose γ := {|
      metadata_mutex := mtx ;
      metadata_condition := cond ;
      metadata_tokens := γ_tokens ;
    |}.
    iMod (meta_set γ with "Hmeta") as "#Hmeta"; first done.

    replace ₊cap with (S ₊(cap - 1)) by lia.
    iMod (mutex_init_to_inv (inv_inner l γ P) with "Hmutex_init [Hl_count Htokens_frags HPs]") as "#Hmutex_inv".
    { iDestruct (big_sepL_sep_2 with "Htokens_frags HPs") as "H".
      iFrameSteps.
    }
    iSteps.
  Qed.

  Lemma semaphore_try_lock_spec t cap P :
    {{{
      semaphore_inv t cap P
    }}}
      semaphore_try_lock t
    {{{ b,
      RET #b;
      if b then
        semaphore_locked t ∗
        P
      else
        True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_rec. wp_load.

    wp_apply (mutex_protect_spec (λ v,
      ∃ b,
      ⌜v = #b⌝ ∗
      if b then
        tokens_frag γ ∗
        P
      else
        True
    )%I with "[$Hmutex_inv]") as (res) "(%b & -> & H)".
    { iIntros "Hmutex_locked (:inv_inner)".
      wp_load. wp_pures.
      case_bool_decide; last iSteps.
      wp_store.
      rewrite seq_S. iDestruct (big_sepL_snoc with "H") as "(H & Htokens_frag & HP)".
      iStep 5. iSplitR "Htokens_frag HP"; last iSteps.
      replace cnt with (S ₊(⁺cnt - 1)) by lia.
      iFrameSteps.
    }

    destruct b; iSteps.
  Qed.

  Lemma semaphore_lock_spec t cap P :
    {{{
      semaphore_inv t cap P
    }}}
      semaphore_lock t
    {{{
      RET ();
      semaphore_locked t ∗
      P
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_rec. wp_load.

    wp_apply (mutex_protect_spec (λ v,
      ⌜v = ()%V⌝ ∗
      tokens_frag γ ∗
      P
    )%I with "[$Hmutex_inv]"); last iSteps.
    iIntros "Hmutex_locked Hinv_inner".
    do 2 wp_load.
    wp_apply (condition_wait_until_spec' (λ b,
      if b then
        ∃ cnt,
        ⌜0 < cnt⌝ ∗
        l.[count] ↦ #cnt ∗
        [∗ list] _ ∈ seq 0 (S cnt),
          tokens_frag γ ∗
          P
      else
        True
    )%I with "[$Hcondition_inv $Hmutex_inv $Hmutex_locked $Hinv_inner]") as "(Hmutex_locked & (%cnt & %Hcnt & Hl_count & H))".
    { iIntros "!> Hmutex_locked (:inv_inner) _".
      wp_load. wp_pures.
      case_bool_decide; iStepFrameSteps.
    }
    wp_load. wp_store.
    rewrite seq_S. iDestruct (big_sepL_snoc with "H") as "(H & Htokens_frag & HP)".
    iFrame "Hmutex_locked". iSplitR "Htokens_frag HP"; last iSteps.
    replace (⁺cnt - 1)%Z with ⁺(cnt - 1) by lia.
    replace cnt with (S (cnt - 1)) at 2 by lia.
    iSteps.
  Qed.

  Lemma semaphore_unlock_spec t cap P :
    {{{
      semaphore_inv t cap P ∗
      semaphore_locked t ∗
      P
    }}}
      semaphore_unlock t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & (:locked) & HP) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp_rec. wp_load.

    wp_apply (mutex_protect_spec (λ v,
      ⌜v = ()%V⌝
    )%I with "[$Hmutex_inv Htokens_frag HP]"); last iSteps.
    iIntros "Hmutex_locked (:inv_inner)".
    wp_load. wp_store.
    iDestruct (big_sepL_snoc_2 (S cnt) with "H [$]") as "H".
    rewrite -seq_S. iFrameSteps.
  Qed.
End semaphore_G.

From zoo_std Require
  semaphore__opaque.

#[global] Opaque semaphore_inv.
#[global] Opaque semaphore_locked.
