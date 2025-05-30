From zoo Require Import
  prelude.
From zoo.common Require Import
  countable.
From zoo.iris.bi Require Import
  big_op.
From zoo.iris.base_logic Require Import
  lib.twins
  lib.excl.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  option
  domain.
From zoo_saturn Require Import
  mpmc_queue_1.
From zoo_parabs Require Export
  base
  ws_hub_fifo__code.
From zoo_parabs Require Import
  ws_hub_fifo__types
  waiters.
From zoo Require Import
  options.

Implicit Types b yield killed : bool.
Implicit Types l : location.
Implicit Types v t until pred : val.
Implicit Types ws : list val.
Implicit Types vs : gmultiset val.
Implicit Types status : status.

Class WsHubFifoG Σ `{zoo_G : !ZooG Σ} := {
  #[local] ws_hub_fifo_G_queue_G :: MpmcQueue1G Σ ;
  #[local] ws_hub_fifo_G_waiters_G :: WaitersG Σ ;
  #[local] ws_hub_fifo_G_model_G :: TwinsG Σ (leibnizO (gmultiset val)) ;
  #[local] ws_hub_fifo_G_owner_G :: ExclG Σ unitO ;
}.

Definition ws_hub_fifo_Σ := #[
  mpmc_queue_1_Σ ;
  waiters_Σ ;
  twins_Σ (leibnizO (gmultiset val)) ;
  excl_Σ unitO
].
#[global] Instance subG_ws_hub_fifo_Σ Σ `{zoo_G : !ZooG Σ} :
  subG ws_hub_fifo_Σ Σ →
  WsHubFifoG Σ.
Proof.
  solve_inG.
Qed.

Section ws_hub_fifo_G.
  Context `{ws_hub_fifo_G : WsHubFifoG Σ}.

  Record metadata := {
    metadata_queue : val ;
    metadata_waiters : val ;
    metadata_model : gname ;
    metadata_owners : list gname ;
  }.
  Implicit Types γ : metadata.
  Implicit Types γ_owners : list gname.

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
  #[local] Definition model₂ γ vs :=
    model₂' γ.(metadata_model) vs.

  #[local] Definition owner' γ_owners i : iProp Σ :=
    ∃ γ_owner,
    ⌜γ_owners !! i = Some γ_owner⌝ ∗
    excl γ_owner ().
  #[local] Definition owner γ i :=
    owner' γ.(metadata_owners) i.
  #[local] Instance : CustomIpatFormat "owner_" :=
    "(
      %γ_owner{} &
      %Hlookup{} &
      Howner{}
    )".

  #[local] Definition ws_hub_fifo_inv_inner l γ : iProp Σ :=
    ∃ ws killed,
    l.[killed] ↦ #killed ∗
    mpmc_queue_1_model γ.(metadata_queue) ws ∗
    model₂ γ (list_to_set_disj ws).
  #[local] Instance : CustomIpatFormat "inv_inner" :=
    "(
      %ws &
      %killed &
      >Hl_killed &
      >Hqueue_model &
      >Hmodel₂
    )".
  Definition ws_hub_fifo_inv t ι (sz : nat) : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    l.[size] ↦□ #sz ∗
    l.[queue] ↦□ γ.(metadata_queue) ∗
    l.[waiters] ↦□ γ.(metadata_waiters) ∗
    mpmc_queue_1_inv γ.(metadata_queue) (ι.@"queue") ∗
    waiters_inv γ.(metadata_waiters) ∗
    inv (ι.@"inv") (ws_hub_fifo_inv_inner l γ).
  #[local] Instance : CustomIpatFormat "inv" :=
    "(
      %l{} &
      %γ{} &
      {%Heq{};->} &
      #Hmeta{} &
      #Hl{}_size &
      #Hl{}_queue &
      #Hl{}_waiters &
      #Hqueue{}_inv &
      #Hwaiters{}_inv &
      #Hinv{}
    )".

  Definition ws_hub_fifo_model t vs : iProp Σ :=
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

  Definition ws_hub_fifo_owner t i status : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    owner γ i.
  #[local] Instance : CustomIpatFormat "owner" :=
    "(
      %l{;_} &
      %γ{;_} &
      %Heq{} &
      #Hmeta{;_} &
      Howner{}
    )".

  #[global] Instance ws_hub_fifo_model_timeless t vs :
    Timeless (ws_hub_fifo_model t vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance ws_hub_fifo_inv_persistent t ι sz :
    Persistent (ws_hub_fifo_inv t ι sz).
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

  #[local] Lemma owner_alloc sz :
    ⊢ |==>
      ∃ γ_owners,
      [∗ list] i ∈ seq 0 sz,
        owner' γ_owners i.
  Proof.
    iAssert (
      [∗ list] _ ∈ seq 0 sz,
        |==>
        ∃ γ_owner,
        excl (excl_G := ws_hub_fifo_G_owner_G) γ_owner ()
    )%I as "-#H".
    { iApply big_sepL_intro. iIntros "!> % % _".
      iApply excl_alloc.
    }
    iMod (big_sepL_bupd with "H") as "H".
    iDestruct (big_sepL_exists with "H") as "(%γ_owners & _ & H)".
    iDestruct (big_sepL2_retract_r with "H") as "(_ & H)".
    iDestruct (big_sepL_seq_index_2 with "H") as "H".
    { simpl_length. }
    iSteps.
  Qed.
  #[local] Lemma owner_exclusive γ i :
    owner γ i -∗
    owner γ i -∗
    False.
  Proof.
    iIntros "(:owner_ =1) (:owner_ =2)". simplify.
    iApply (excl_exclusive with "Howner1 Howner2").
  Qed.

  Opaque owner'.

  Lemma ws_hub_fifo_inv_agree t ι sz1 sz2 :
    ws_hub_fifo_inv t ι sz1 -∗
    ws_hub_fifo_inv t ι sz2 -∗
    ⌜sz1 = sz2⌝.
  Proof.
    iIntros "(:inv =1) (:inv =2)". simplify.
    iDestruct (pointsto_agree with "Hl1_size Hl2_size") as %[=].
    iSteps.
  Qed.

  Lemma ws_hub_fifo_owner_exclusive t i status1 status2 :
    ws_hub_fifo_owner t i status1 -∗
    ws_hub_fifo_owner t i status2 -∗
    False.
  Proof.
    iIntros "(:owner =1) (:owner =2)". simplify.
    iDestruct (meta_agree with "Hmeta1 Hmeta2") as %->.
    iApply (owner_exclusive with "Howner1 Howner2").
  Qed.

  Lemma ws_hub_fifo_create_spec ι sz :
    (0 ≤ sz)%Z →
    {{{
      True
    }}}
      ws_hub_fifo_create #sz
    {{{ t,
      RET t;
      ws_hub_fifo_inv t ι ₊sz ∗
      ws_hub_fifo_model t ∅ ∗
      [∗ list] i ∈ seq 0 ₊sz,
        ws_hub_fifo_owner t i Nonblocked
    }}}.
  Proof.
    iIntros "%Hsz %Φ _ HΦ".

    wp_rec.
    wp_apply (waiters_create_spec with "[//]") as (waiters) "#Hwaiters_inv".
    wp_apply (mpmc_queue_1_create_spec with "[//]") as (queue) "(#Hqueue_inv & Hqueue_model)".
    wp_block l as "Hmeta" "(Hl_size & Hl_queue & Hl_waiters & Hl_killed & _)".
    iMod (pointsto_persist with "Hl_size") as "#Hl_size".
    iMod (pointsto_persist with "Hl_queue") as "#Hl_queue".
    iMod (pointsto_persist with "Hl_waiters") as "#Hl_waiters".

    iMod model_alloc as "(%γ_model & Hmodel₁ & Hmodel₂)".
    iMod owner_alloc as "(%γ_owners & Howners)".

    pose γ := {|
      metadata_queue := queue ;
      metadata_waiters := waiters ;
      metadata_model := γ_model ;
      metadata_owners := γ_owners ;
    |}.
    iMod (meta_set γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitR "Hmodel₁ Howners"; first iSteps.
    iSteps.
    iApply (big_sepL_impl with "Howners"). iSteps.
  Qed.

  Lemma ws_hub_fifo_size_spec t ι sz :
    {{{
      ws_hub_fifo_inv t ι sz
    }}}
      ws_hub_fifo_size t
    {{{
      RET #sz;
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma ws_hub_fifo_block_spec t ι sz i i_ :
    i = ⁺i_ →
    {{{
      ws_hub_fifo_inv t ι sz ∗
      ws_hub_fifo_owner t i_ Nonblocked
    }}}
      ws_hub_fifo_block t #i
    {{{
      RET ();
      ws_hub_fifo_owner t i_ Blocked
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma ws_hub_fifo_unblock_spec t ι sz i i_ :
    i = ⁺i_ →
    {{{
      ws_hub_fifo_inv t ι sz ∗
      ws_hub_fifo_owner t i_ Blocked
    }}}
      ws_hub_fifo_unblock t #i
    {{{
      RET ();
      ws_hub_fifo_owner t i_ Nonblocked
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma ws_hub_fifo_killed_spec t ι sz :
    {{{
      ws_hub_fifo_inv t ι sz
    }}}
      ws_hub_fifo_killed t
    {{{ killed,
      RET #killed;
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  #[local] Lemma ws_hub_fifo_notify_spec t ι sz :
    {{{
      ws_hub_fifo_inv t ι sz
    }}}
      ws_hub_fifo_notify t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_rec. wp_load.
    wp_apply (waiters_notify_spec with "Hwaiters_inv HΦ").
  Qed.

  #[local] Lemma ws_hub_fifo_notify_all_spec t ι sz :
    {{{
      ws_hub_fifo_inv t ι sz
    }}}
      ws_hub_fifo_notify_all t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_rec.
    wp_apply (ws_hub_fifo_size_spec) as "_"; first iSteps.
    wp_load.
    wp_apply (waiters_notify_many_spec with "Hwaiters_inv HΦ"); first lia.
  Qed.

  Lemma ws_hub_fifo_push_spec t ι sz i i_ v :
    i = ⁺i_ →
    <<<
      ws_hub_fifo_inv t ι sz ∗
      ws_hub_fifo_owner t i_ Nonblocked
    | ∀∀ vs,
      ws_hub_fifo_model t vs
    >>>
      ws_hub_fifo_push t #i v @ ↑ι
    <<<
      ws_hub_fifo_model t ({[+v+]} ⊎ vs)
    | RET ();
      ws_hub_fifo_owner t i_ Nonblocked
    >>>.
  Proof.
    iIntros (->) "%Φ ((:inv) & Howner) HΦ".

    wp_rec. wp_load.

    awp_apply (mpmc_queue_1_push_spec with "Hqueue_inv") without "Howner".
    iInv "Hinv" as "(:inv_inner)".
    iApply (aacc_aupd_commit with "HΦ"); first solve_ndisj. iIntros "%vs (:model)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
    iAaccIntro with "Hqueue_model"; first iSteps. iIntros "Hqueue_model".
    iMod (model_update (list_to_set_disj $ ws ++ [v]) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iSplitL "Hmodel₁".
    { rewrite list_to_set_disj_app list_to_set_disj_cons right_id comm. iSteps. }
    iIntros "!> HΦ !>".
    iSplitR "HΦ"; first iSteps.
    iIntros "_ Howner {%}".

    wp_smart_apply ws_hub_fifo_notify_spec as "_"; first iSteps.
    iApply ("HΦ" with "Howner").
  Qed.

  Lemma ws_hub_fifo_pop'_spec t ι sz :
    <<<
      ws_hub_fifo_inv t ι sz
    | ∀∀ vs,
      ws_hub_fifo_model t vs
    >>>
      ws_hub_fifo_pop' t @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_fifo_model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_fifo_model t vs'
      end
    | RET o;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_rec. wp_load.

    awp_smart_apply (mpmc_queue_1_pop_spec with "Hqueue_inv").
    iInv "Hinv" as "(:inv_inner)".
    iApply (aacc_aupd_commit with "HΦ"); first solve_ndisj. iIntros "%vs (:model)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
    iAaccIntro with "Hqueue_model"; first iSteps. iIntros "Hqueue_model".
    iExists (head ws).
    destruct ws as [| w ws]; first iSteps.
    iMod (model_update (list_to_set_disj ws) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iSteps.
  Qed.
  Lemma ws_hub_fifo_pop_spec t ι sz i i_ :
    i = ⁺i_ →
    <<<
      ws_hub_fifo_inv t ι sz ∗
      ws_hub_fifo_owner t i_ Nonblocked
    | ∀∀ vs,
      ws_hub_fifo_model t vs
    >>>
      ws_hub_fifo_pop t #i @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_fifo_model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_fifo_model t vs'
      end
    | RET o;
      ws_hub_fifo_owner t i_ Nonblocked
    >>>.
  Proof.
    iIntros (->) "%Φ (Hinv & Howner) HΦ".

    wp_rec.
    wp_smart_apply (ws_hub_fifo_pop'_spec with "Hinv").
    iApply (atomic_update_wand with "HΦ"). iIntros "%vs %o HΦ _".
    iApply ("HΦ" with "Howner").
  Qed.

  Lemma ws_hub_fifo_steal_until_0_spec P t ι sz pred :
    <<<
      ws_hub_fifo_inv t ι sz ∗
      □ WP pred () {{ res,
        ∃ b,
        ⌜res = #b⌝ ∗
        if b then P else True
      }}
    | ∀∀ vs,
      ws_hub_fifo_model t vs
    >>>
      ws_hub_fifo_steal_until_0 t pred @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_fifo_model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_fifo_model t vs'
      end
    | RET o;
      if o then True else P
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & #Hpred) HΦ".
    iLöb as "HLöb".

    wp_rec.
    wp_smart_apply (wp_wand with "Hpred") as (res) "(%b & -> & HP)".
    destruct b.

    - iApply fupd_wp.
      iMod "HΦ" as "(%vs & Hmodel & _ & HΦ)".
      iMod ("HΦ" $! None with "Hmodel") as "HΦ".
      iSteps.

    - wp_smart_apply domain_yield_spec.
      awp_smart_apply ws_hub_fifo_pop'_spec; first iSteps.
      iApply (aacc_aupd with "HΦ"); first done. iIntros "%vs Hmodel".
      iAaccIntro with "Hmodel"; first iSteps. iIntros ([v |]) "Hmodel".

      + iRight. iExists (Some v). iFrameSteps.

      + iLeft. iFrameSteps.
  Qed.
  Lemma ws_hub_fifo_steal_until_spec P t ι i i_ sz max_round_noyield pred :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    <<<
      ws_hub_fifo_inv t ι sz ∗
      ws_hub_fifo_owner t i_ Nonblocked ∗
      □ WP pred () {{ res,
        ∃ b,
        ⌜res = #b⌝ ∗
        if b then P else True
      }}
    | ∀∀ vs,
      ws_hub_fifo_model t vs
    >>>
      ws_hub_fifo_steal_until t #i #max_round_noyield pred @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_fifo_model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_fifo_model t vs'
      end
    | RET o;
      ws_hub_fifo_owner t i_ Nonblocked ∗
      if o then True else P
    >>>.
  Proof.
    iIntros (-> Hmax_round_noyield) "%Φ (#Hinv & Howner & #Hpred) HΦ".

    wp_rec.
    wp_smart_apply (ws_hub_fifo_steal_until_0_spec with "[$Hinv $Hpred]").
    iApply (atomic_update_wand with "HΦ"). iIntros "%vs %o HΦ HP".
    iApply ("HΦ" with "[$Howner $HP]").
  Qed.

  Lemma ws_hub_fifo_steal_0_spec t ι sz :
    <<<
      ws_hub_fifo_inv t ι sz
    | ∀∀ vs,
      ws_hub_fifo_model t vs
    >>>
      ws_hub_fifo_steal_0 t @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_fifo_model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_fifo_model t vs'
      end
    | RET o;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".
    iLöb as "HLöb".

    wp_rec. wp_load.
    wp_smart_apply (waiters_prepare_wait_spec with "Hwaiters_inv") as (waiter) "Hwaiter".
    wp_smart_apply ws_hub_fifo_killed_spec as ([]) "_"; first iSteps.

    - wp_smart_apply (waiters_cancel_wait_spec with "[$Hwaiters_inv $Hwaiter]") as "_".

      iApply fupd_wp.
      iMod "HΦ" as "(%vs & Hmodel & _ & HΦ)".
      iMod ("HΦ" $! None with "Hmodel") as "HΦ".
      iSteps.

    - wp_load.
      wp_smart_apply (mpmc_queue_1_is_empty_spec' with "Hqueue_inv") as (b) "_".

      wp_bind (if: _ then _ else _)%E.
      wp_apply (wp_wand itype_unit with "[Hwaiter]") as (res) "->".
      { destruct b; wp_pures.
        1: wp_apply (waiters_commit_wait_spec with "[$Hwaiters_inv $Hwaiter]").
        2: wp_apply (waiters_cancel_wait_spec with "[$Hwaiters_inv $Hwaiter]").
        all: iSteps.
      }

      awp_smart_apply ws_hub_fifo_pop'_spec; first iSteps.
      iApply (aacc_aupd with "HΦ"); first done. iIntros "%vs Hmodel".
      iAaccIntro with "Hmodel"; first iSteps. iIntros ([v |]) "Hmodel".

      + iRight. iExists (Some v). iFrameSteps.

      + iLeft. iFrameSteps.
  Qed.
  Lemma ws_hub_fifo_steal_spec t ι i i_ sz max_round_noyield max_round_yield :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub_fifo_inv t ι sz ∗
      ws_hub_fifo_owner t i_ Nonblocked
    | ∀∀ vs,
      ws_hub_fifo_model t vs
    >>>
      ws_hub_fifo_steal t #i #max_round_noyield #max_round_yield @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_fifo_model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_fifo_model t vs'
      end
    | RET o;
      ws_hub_fifo_owner t i_ Nonblocked
    >>>.
  Proof.
    iIntros (-> Hmax_round_noyield Hmax_round_yield) "%Φ (#Hinv & Howner) HΦ".

    wp_rec.
    wp_smart_apply (ws_hub_fifo_steal_0_spec with "Hinv").
    iApply (atomic_update_wand with "HΦ"). iIntros "%vs %o HΦ HP".
    iApply ("HΦ" with "[$Howner $HP]").
  Qed.

  Lemma ws_hub_fifo_kill_spec t ι sz :
    {{{
      ws_hub_fifo_inv t ι sz
    }}}
      ws_hub_fifo_kill t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_rec.

    wp_bind (_ <-{killed} _)%E.
    iInv "Hinv" as "(:inv_inner)".
    wp_store.
    iSplitR "HΦ"; first iSteps.
    iIntros "!> {%}".

    wp_smart_apply ws_hub_fifo_notify_all_spec as "_"; first iSteps.
    iSteps.
  Qed.
End ws_hub_fifo_G.

#[global] Opaque ws_hub_fifo_inv.
#[global] Opaque ws_hub_fifo_model.
#[global] Opaque ws_hub_fifo_owner.

Section ws_hub_fifo_G.
  Context `{ws_hub_fifo_G : WsHubFifoG Σ}.

  Lemma ws_hub_fifo_pop_steal_until_spec P t ι i i_ sz max_round_noyield pred :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    <<<
      ws_hub_fifo_inv t ι sz ∗
      ws_hub_fifo_owner t i_ Nonblocked ∗
      □ WP pred () {{ res,
        ∃ b,
        ⌜res = #b⌝ ∗
        if b then P else True
      }}
    | ∀∀ vs,
      ws_hub_fifo_model t vs
    >>>
      ws_hub_fifo_pop_steal_until t #i #max_round_noyield pred @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_fifo_model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_fifo_model t vs'
      end
    | RET o;
      ws_hub_fifo_owner t i_ Nonblocked ∗
      if o then True else P
    >>>.
  Proof.
    iIntros (->) "%Hmax_round_noyield %Φ (#Hinv & Howner & #Hpred) HΦ".

    wp_rec.

    awp_smart_apply (ws_hub_fifo_pop_spec with "[$Hinv $Howner]"); [done.. |].
    iApply (aacc_aupd with "HΦ"); first done. iIntros "%vs Hmodel".
    iAaccIntro with "Hmodel"; first iSteps. iIntros ([v |]) "Hmodel !>".

    - iRight. iExists (Some v). iFrame.
      iIntros "HΦ !> Howner {%}".

      iSpecialize ("HΦ" with "[$Howner]").
      iSteps.

    - iLeft. iFrame.
      iIntros "HΦ !> Howner". clear- Hmax_round_noyield.

      wp_smart_apply (ws_hub_fifo_steal_until_spec with "[$Hinv $Howner $Hpred] HΦ"); done.
  Qed.

  Lemma ws_hub_fifo_pop_steal_spec t ι i i_ sz max_round_noyield max_round_yield :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub_fifo_inv t ι sz ∗
      ws_hub_fifo_owner t i_ Nonblocked
    | ∀∀ vs,
      ws_hub_fifo_model t vs
    >>>
      ws_hub_fifo_pop_steal t #i #max_round_noyield #max_round_yield @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_fifo_model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_fifo_model t vs'
      end
    | RET o;
      ws_hub_fifo_owner t i_ Nonblocked
    >>>.
  Proof.
    iIntros (->) "%Hmax_round_noyield %Hmax_round_yield %Φ (#Hinv & Howner) HΦ".

    wp_rec.

    awp_smart_apply (ws_hub_fifo_pop_spec with "[$Hinv $Howner]"); [done.. |].
    iApply (aacc_aupd with "HΦ"); first done. iIntros "%vs Hmodel".
    iAaccIntro with "Hmodel"; first iSteps. iIntros ([v |]) "Hmodel !>".

    - iDestruct "Hmodel" as "(%vs' & -> & Hmodel)".
      iRight. iExists (Some v). iStep.
      iIntros "HΦ !> Howner {%}".

      iSpecialize ("HΦ" with "Howner").
      iSteps.

    - iLeft. iFrame.
      iIntros "HΦ !> Howner". clear- Hmax_round_noyield Hmax_round_yield.

      wp_smart_apply (ws_hub_fifo_steal_spec with "[$Hinv $Howner] HΦ"); done.
  Qed.
End ws_hub_fifo_G.

#[global] Opaque ws_hub_fifo_create.
#[global] Opaque ws_hub_fifo_size.
#[global] Opaque ws_hub_fifo_block.
#[global] Opaque ws_hub_fifo_unblock.
#[global] Opaque ws_hub_fifo_killed.
#[global] Opaque ws_hub_fifo_push.
#[global] Opaque ws_hub_fifo_pop.
#[global] Opaque ws_hub_fifo_steal_until.
#[global] Opaque ws_hub_fifo_steal.
#[global] Opaque ws_hub_fifo_kill.
#[global] Opaque ws_hub_fifo_pop_steal_until.
#[global] Opaque ws_hub_fifo_pop_steal.
