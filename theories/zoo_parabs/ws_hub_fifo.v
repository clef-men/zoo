From zoo Require Import
  prelude.
From zoo.common Require Import
  countable.
From zoo.iris.bi Require Import
  big_op.
From zoo.iris.base_logic Require Import
  lib.excl
  lib.ghost_list.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  option.
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

Implicit Types b closed : bool.
Implicit Types num_active : Z.
Implicit Types 𝑡 : location.
Implicit Types v t notification notify pred : val.
Implicit Types ws : list val.
Implicit Types vs : gmultiset val.
Implicit Types status : status.
Implicit Types empty : emptiness.
Implicit Types emptys : list emptiness.

Class WsHubFifoG Σ `{zoo_G : !ZooG Σ} :=
  { #[local] ws_hub_fifo_G_queue_G :: MpmcQueue1G Σ
  ; #[local] ws_hub_fifo_G_waiters_G :: WaitersG Σ
  ; #[local] ws_hub_fifo_G_owner_G :: ExclG Σ unitO
  ; #[local] ws_hub_fifo_G_emptiness_G :: GhostListG Σ emptiness
  }.

Definition ws_hub_fifo_Σ :=
  #[mpmc_queue_1_Σ
  ; waiters_Σ
  ; excl_Σ unitO
  ; ghost_list_Σ emptiness
  ].
#[global] Instance subG_ws_hub_fifo_Σ Σ `{zoo_G : !ZooG Σ} :
  subG ws_hub_fifo_Σ Σ →
  WsHubFifoG Σ.
Proof.
  solve_inG.
Qed.

#[local] Definition consistent vs ws :=
  vs = list_to_set_disj ws.

#[local] Lemma consistent_nil_inv vs :
  consistent vs [] →
  vs = ∅.
Proof.
  done.
Qed.
#[local] Lemma consistent_push {vs ws} v :
  consistent vs ws →
  consistent ({[+v+]} ⊎ vs) (ws ++ [v]).
Proof.
  intros ->.
  rewrite /consistent.
  rewrite list_to_set_disj_app list_to_set_disj_cons right_id (comm (⊎)) //.
Qed.
#[local] Lemma consistent_pop vs v ws :
  consistent vs (v :: ws) →
    ∃ vs',
    vs = {[+v+]} ⊎ vs' ∧
    consistent vs' ws.
Proof.
  naive_solver.
Qed.

Opaque consistent.

Section ws_hub_fifo_G.
  Context `{ws_hub_fifo_G : WsHubFifoG Σ}.

  Implicit Types P P_notification P_pred Q Q_pred : iProp Σ.

  Record metadata :=
    { metadata_size : nat
    ; metadata_queue : val
    ; metadata_waiters : val
    ; metadata_owners : list gname
    ; metadata_emptiness : gname
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

  #[local] Definition owner' γ_owners sz i : iProp Σ :=
    ∃ γ_owner,
    ⌜γ_owners !! i = Some γ_owner⌝ ∗
    ⌜length γ_owners = sz⌝ ∗
    excl γ_owner ().
  #[local] Definition owner γ i :=
    owner' γ.(metadata_owners) γ.(metadata_size) i.
  #[local] Instance : CustomIpat "owner_" :=
    " ( %γ_owner{}
      & %Hlookup{}
      & %Hlength{_{}}
      & Howner{}
      )
    ".

  #[local] Definition emptiness_auth' γ_emptiness sz vs : iProp Σ :=
    ∃ emptys,
    ghost_list_auth γ_emptiness emptys ∗
    ⌜length emptys = sz⌝ ∗
    ⌜ vs = ∅
    ∨ ∃ i,
      emptys !! i = Some Nonempty
    ⌝.
  #[local] Definition emptiness_auth γ :=
    emptiness_auth' γ.(metadata_emptiness) γ.(metadata_size).
  #[local] Instance : CustomIpat "emptiness_auth" :=
    " ( %emptys
      & Hauth
      & %Hemptys
      & %Hemptiness
      )
    ".
  #[local] Definition emptiness_at' γ_emptiness i :=
    ghost_list_at γ_emptiness i (DfracOwn 1).
  #[local] Definition emptiness_at γ :=
    emptiness_at' γ.(metadata_emptiness).

  #[local] Definition inv_inner 𝑡 : iProp Σ :=
    ∃ num_active,
    𝑡.[num_active] ↦ #num_active.
  #[local] Instance : CustomIpat "inv_inner" :=
    " ( %num_active
      & H𝑡_num_active
      )
    ".
  Definition ws_hub_fifo_inv t ι (sz : nat) : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    ⌜sz = γ.(metadata_size)⌝ ∗
    meta 𝑡 nroot γ ∗
    𝑡.[size] ↦□ #γ.(metadata_size) ∗
    𝑡.[queue] ↦□ γ.(metadata_queue) ∗
    𝑡.[waiters] ↦□ γ.(metadata_waiters) ∗
    mpmc_queue_1_inv γ.(metadata_queue) ι ∗
    waiters_inv γ.(metadata_waiters) sz ∗
    inv nroot (inv_inner 𝑡).
  #[local] Instance : CustomIpat "inv" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & ->
      & #Hmeta{}
      & #H𝑡{}_size
      & #H𝑡{}_queue
      & #H𝑡{}_waiters
      & #Hqueue{}_inv
      & #Hwaiters{}_inv
      & #Hinv{}
      )
    ".

  Definition ws_hub_fifo_model t vs : iProp Σ :=
    ∃ 𝑡 γ ws,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    mpmc_queue_1_model γ.(metadata_queue) ws ∗
    ⌜consistent vs ws⌝ ∗
    emptiness_auth γ vs.
  #[local] Instance : CustomIpat "model" :=
    " ( %l_
      & %γ_
      & %ws
      & %Heq
      & Hmeta_
      & Hqueue_model
      & %Hconsistent
      & Hemptiness_auth
      )
    ".

  Definition ws_hub_fifo_owner t i status empty : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    owner γ i ∗
    emptiness_at γ i empty.
  #[local] Instance : CustomIpat "owner" :=
    " ( %𝑡{;_}
      & %γ{;_}
      & %Heq{}
      & #Hmeta_{}
      & Howner{_{}}
      & Hemptiness_at{_{}}
      )
    ".

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

  #[local] Lemma owner_alloc sz :
    ⊢ |==>
      ∃ γ_owners,
      [∗ list] i ∈ seq 0 sz,
        owner' γ_owners sz i.
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
    iDestruct (big_sepL_exists with "H") as "(%γ_owners & %Hlength & H)".
    iDestruct (big_sepL2_intro (λ _ _ _, ⌜length γ_owners = sz⌝)%I (seq 0 sz) γ_owners with "[%]") as "Hlength". 1: done.
    { simpl_length in Hlength. naive_solver. }
    iDestruct (big_sepL2_sep_2 with "Hlength H") as "H".
    iDestruct (big_sepL2_retract_r with "H") as "(_ & H)".
    iDestruct (big_sepL_seq_index_2 with "H") as "H".
    { simpl_length. }
    iSteps.
  Qed.
  #[local] Lemma owner_valid γ i :
    owner γ i ⊢
    ⌜i < γ.(metadata_size)⌝.
  Proof.
    iIntros "(:owner_)". iPureIntro.
    rewrite -Hlength. eapply lookup_lt_Some => //.
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

  #[local] Lemma emptiness_alloc sz :
    ⊢ |==>
      ∃ γ_emptiness,
      emptiness_auth' γ_emptiness sz ∅ ∗
      [∗ list] i ∈ seq 0 sz,
        emptiness_at' γ_emptiness i Empty.
  Proof.
    iMod ghost_list_alloc as "(%γ_emptiness & $ & Hats)".
    iDestruct (big_sepL_replicate_1 with "Hats") as "$".
    iSteps. iPureIntro. simpl_length.
  Qed.
  #[local] Lemma emptiness_at_valid γ vs i empty :
    emptiness_auth γ vs -∗
    emptiness_at γ i empty -∗
    ⌜i < γ.(metadata_size)⌝.
  Proof.
    iIntros "(:emptiness_auth) Hat".
    iDestruct (ghost_list_lookup with "Hauth Hat") as %Hi%lookup_lt_Some.
    iSteps.
  Qed.
  #[local] Lemma emptiness_empty γ vs :
    emptiness_auth γ vs -∗
    ( [∗ list] i ∈ seq 0 γ.(metadata_size),
      emptiness_at γ i Empty
    ) -∗
    ⌜vs = ∅⌝.
  Proof.
    iIntros "(:emptiness_auth) Hats".
    destruct Hemptiness as [-> | (i & Hlookup)]; first iSteps.
    iDestruct (big_sepL_lookup with "Hats") as "Hat".
    { apply lookup_lt_Some in Hlookup.
      rewrite lookup_seq -Hemptys /=. eauto.
    }
    iDestruct (ghost_list_lookup with "Hauth Hat") as %?. congruence.
  Qed.
  #[local] Lemma emptiness_update_auth γ v vs :
    emptiness_auth γ ({[+v+]} ⊎ vs) ⊢
    emptiness_auth γ vs.
  Proof.
    iIntros "(:emptiness_auth)".
    destruct Hemptiness as [? | (i & Hlookup)]; last iSteps.
    exfalso. multiset_solver.
  Qed.
  #[local] Lemma emptiness_update_Nonempty {γ vs i empty} vs' :
    emptiness_auth γ vs -∗
    emptiness_at γ i empty ==∗
      emptiness_auth γ vs' ∗
      emptiness_at γ i Nonempty.
  Proof.
    iIntros "(:emptiness_auth) Hat".
    iDestruct (ghost_list_lookup with "Hauth Hat") as %Hi%lookup_lt_Some.
    iMod (ghost_list_update_at Nonempty with "Hauth Hat") as "($ & $)".
    iPureIntro. split.
    - simpl_length.
    - right. exists i. apply list_lookup_insert_eq. done.
  Qed.
  #[local] Lemma emptiness_update_Empty γ i empty :
    emptiness_auth γ ∅ -∗
    emptiness_at γ i empty ==∗
      emptiness_auth γ ∅ ∗
      emptiness_at γ i Empty.
  Proof.
    iIntros "(:emptiness_auth) Hat".
    iMod (ghost_list_update_at Empty with "Hauth Hat") as "($ & $)".
    iSteps. simpl_length.
  Qed.

  Opaque emptiness_auth'.

  Lemma ws_hub_fifo_inv_agree t ι sz1 sz2 :
    ws_hub_fifo_inv t ι sz1 -∗
    ws_hub_fifo_inv t ι sz2 -∗
    ⌜sz1 = sz2⌝.
  Proof.
    iIntros "(:inv =1) (:inv =2)". simplify.
    iDestruct (pointsto_agree with "H𝑡1_size H𝑡2_size") as %[=].
    iSteps.
  Qed.

  Lemma ws_hub_fifo_owner_exclusive t i status1 empty1 status2 empty2 :
    ws_hub_fifo_owner t i status1 empty1 -∗
    ws_hub_fifo_owner t i status2 empty2 -∗
    False.
  Proof.
    iIntros "(:owner =1) (:owner =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (owner_exclusive with "Howner_1 Howner_2").
  Qed.

  Lemma ws_hub_fifo_inv_owner t ι sz i status empty :
    ws_hub_fifo_inv t ι sz -∗
    ws_hub_fifo_owner t i status empty -∗
    ⌜i < sz⌝.
  Proof.
    iIntros "(:inv) (:owner)". simplify.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-.
    iApply (owner_valid with "Howner").
  Qed.

  Lemma ws_hub_fifo_model_empty t ι sz vs :
    ws_hub_fifo_inv t ι sz -∗
    ws_hub_fifo_model t vs -∗
    ( [∗ list] i ∈ seq 0 sz,
      ∃ status,
      ws_hub_fifo_owner t i status Empty
    ) -∗
    ⌜vs = ∅⌝.
  Proof.
    iIntros "(:inv) (:model) Howners". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iApply (emptiness_empty with "Hemptiness_auth").
    iApply (big_sepL_seq_impl with "Howners"). iIntros "!> %i %Hi (%status & (:owner)) /=". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iSteps.
  Qed.

  Lemma ws_hub_fifo_create𑁒spec ι sz :
    (0 ≤ sz)%Z →
    {{{
      True
    }}}
      ws_hub_fifo_create #sz
    {{{
      t
    , RET t;
      ws_hub_fifo_inv t ι ₊sz ∗
      ws_hub_fifo_model t ∅ ∗
      [∗ list] i ∈ seq 0 ₊sz,
        ws_hub_fifo_owner t i Nonblocked Empty
    }}}.
  Proof.
    iIntros "%Hsz %Φ _ HΦ".

    wp_rec.
    wp_apply+ (waiters_create𑁒spec with "[//]") as (waiters) "#Hwaiters_inv". 1: done.
    wp_apply (mpmc_queue_1_create𑁒spec with "[//]") as (queue) "(#Hqueue_inv & Hqueue_model)".
    wp_block 𝑡 as "Hmeta" "(H𝑡_size & H𝑡_queue & H𝑡_waiters & H𝑡_num_active & _)".
    iMod (pointsto_persist with "H𝑡_size") as "#H𝑡_size".
    iMod (pointsto_persist with "H𝑡_queue") as "#H𝑡_queue".
    iMod (pointsto_persist with "H𝑡_waiters") as "#H𝑡_waiters".

    iMod owner_alloc as "(%γ_owners & Howners)".
    iMod (emptiness_alloc ₊sz) as "(%γ_emptiness & Hemptiness_auth & Hemptiness_ats)".

    pose γ :=
      {|metadata_size := ₊sz
      ; metadata_queue := queue
      ; metadata_waiters := waiters
      ; metadata_owners := γ_owners
      ; metadata_emptiness := γ_emptiness
      |}.

    iMod (meta_set γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitL "H𝑡_num_active".
    { iExists 𝑡, γ. iSteps. }
    iSplitL "Hqueue_model Hemptiness_auth".
    { iSteps. }
    iDestruct (big_sepL_sep_2 with "Howners Hemptiness_ats") as "Howners".
    iApply (big_sepL_seq_impl with "Howners").
    iSteps.
  Qed.

  Lemma ws_hub_fifo_size𑁒spec t ι sz :
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

  #[local] Lemma ws_hub_fifo_begin_inactive𑁒spec t ι sz :
    {{{
      ws_hub_fifo_inv t ι sz
    }}}
      ws_hub_fifo_begin_inactive t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  #[local] Lemma ws_hub_fifo_end_inactive𑁒spec t ι sz :
    {{{
      ws_hub_fifo_inv t ι sz
    }}}
      ws_hub_fifo_end_inactive t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma ws_hub_fifo_block𑁒spec t ι sz i i_ empty :
    i = ⁺i_ →
    {{{
      ws_hub_fifo_inv t ι sz ∗
      ws_hub_fifo_owner t i_ Nonblocked empty
    }}}
      ws_hub_fifo_block t #i
    {{{
      RET ();
      ws_hub_fifo_owner t i_ Blocked empty
    }}}.
  Proof.
    iIntros (->) "%Φ (#Hinv & Howner) HΦ".

    wp_rec.
    wp_apply+ (ws_hub_fifo_begin_inactive𑁒spec with "Hinv") as "_".
    iApply ("HΦ" with "Howner").
  Qed.

  Lemma ws_hub_fifo_unblock𑁒spec t ι sz i i_ empty :
    i = ⁺i_ →
    {{{
      ws_hub_fifo_inv t ι sz ∗
      ws_hub_fifo_owner t i_ Blocked empty
    }}}
      ws_hub_fifo_unblock t #i
    {{{
      RET ();
      ws_hub_fifo_owner t i_ Nonblocked empty
    }}}.
  Proof.
    iIntros (->) "%Φ (#Hinv & Howner) HΦ".

    wp_rec.
    wp_apply+ (ws_hub_fifo_end_inactive𑁒spec with "Hinv") as "_".
    iApply ("HΦ" with "Howner").
  Qed.

  Lemma ws_hub_fifo_closed𑁒spec t ι sz :
    {{{
      ws_hub_fifo_inv t ι sz
    }}}
      ws_hub_fifo_closed t
    {{{
      closed
    , RET #closed;
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  #[local] Lemma ws_hub_fifo_notify𑁒spec t ι sz :
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
    wp_apply (waiters_notify_one𑁒spec with "Hwaiters_inv HΦ").
  Qed.

  #[local] Lemma ws_hub_fifo_notify_all𑁒spec t ι sz :
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

    wp_rec. wp_load.
    wp_apply (waiters_notify_all𑁒spec with "Hwaiters_inv HΦ").
  Qed.

  Lemma ws_hub_fifo_push𑁒spec t ι sz i i_ empty v :
    i = ⁺i_ →
    <<<
      ws_hub_fifo_inv t ι sz ∗
      ws_hub_fifo_owner t i_ Nonblocked empty
    | ∀∀ vs,
      ws_hub_fifo_model t vs
    >>>
      ws_hub_fifo_push t #i v @ ↑ι
    <<<
      ws_hub_fifo_model t ({[+v+]} ⊎ vs)
    | RET ();
      ws_hub_fifo_owner t i_ Nonblocked Nonempty
    >>>.
  Proof.
    iIntros (->) "%Φ ((:inv) & (:owner)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    iApply (wp_frame_wand with "Howner").

    wp_rec. wp_load.

    awp_apply (mpmc_queue_1_push𑁒spec with "Hqueue_inv").
    iApply (aacc_aupd_commit with "HΦ"); first solve_ndisj. iIntros "%vs (:model)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iAaccIntro with "Hqueue_model"; first iSteps. iIntros "Hqueue_model".
    iMod (emptiness_update_Nonempty ({[+v+]} ⊎ vs) with "Hemptiness_auth Hemptiness_at") as "(Hemptiness_auth & Hemptiness_at)".
    iSplitL "Hqueue_model Hemptiness_auth".
    { iFrameSteps. iPureIntro. apply consistent_push. done. }
    iIntros "!> HΦ !> _ {%}".

    wp_apply+ ws_hub_fifo_notify𑁒spec as "_"; first iSteps.
    iSteps.
  Qed.

  #[local] Lemma ws_hub_fifo_pop'𑁒spec_aux (owner : option (nat * emptiness)) t ι sz :
    <<<
      ws_hub_fifo_inv t ι sz ∗
      match owner with
      | None =>
          True
      | Some (i, empty) =>
          ws_hub_fifo_owner t i Nonblocked empty
      end
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
      match owner with
      | None =>
          True
      | Some (i, empty) =>
          ws_hub_fifo_owner t i Nonblocked (if o then empty else Empty)
      end
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & Howner) HΦ".

    wp_rec. wp_load.

    awp_apply+ (mpmc_queue_1_pop𑁒spec with "Hqueue_inv").
    iApply (aacc_aupd_commit with "HΦ"); first solve_ndisj. iIntros "%vs (:model)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iAaccIntro with "Hqueue_model"; first iSteps. iIntros "Hqueue_model".
    iExists (head ws).
    destruct ws as [| w ws].

    - apply consistent_nil_inv in Hconsistent as ->.

      iAssert (
        emptiness_auth γ ∅ ∗
        match owner with
        | None =>
            True
        | Some (i, empty) =>
            ws_hub_fifo_owner #𝑡 i Nonblocked Empty
        end
      )%I with "[> Hemptiness_auth Howner]" as "(Hemptiness_auth & Howner)".
      { destruct owner as [(i, empty) |]; last iSteps.
        iDestruct "Howner" as "(:owner)". injection Heq as <-.
        iDestruct (meta_agree with "Hmeta Hmeta_") as %<-.
        iMod (emptiness_update_Empty with "Hemptiness_auth Hemptiness_at") as "($ & $)".
        iFrameSteps.
      }

      iSteps.

    - apply consistent_pop in Hconsistent as (vs' & -> & Hconsistent).
      iDestruct (emptiness_update_auth with "Hemptiness_auth") as "Hemptiness_auth".
      iSteps.
  Qed.
  #[local] Lemma ws_hub_fifo_pop'𑁒spec t ι sz :
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
    iIntros "%Φ Hinv HΦ".

    wp_apply (ws_hub_fifo_pop'𑁒spec_aux None with "[$Hinv] HΦ").
  Qed.
  #[local] Lemma ws_hub_fifo_pop'𑁒spec_owner t ι sz i empty :
    <<<
      ws_hub_fifo_inv t ι sz ∗
      ws_hub_fifo_owner t i Nonblocked empty
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
      ws_hub_fifo_owner t i Nonblocked (if o then empty else Empty)
    >>>.
  Proof.
    iIntros "%Φ (#Hinv & Howner) HΦ".

    wp_apply (ws_hub_fifo_pop'𑁒spec_aux (Some (i, empty)) with "[$Hinv $Howner] HΦ").
  Qed.

  Lemma ws_hub_fifo_pop𑁒spec t ι sz i i_ empty :
    i = ⁺i_ →
    <<<
      ws_hub_fifo_inv t ι sz ∗
      ws_hub_fifo_owner t i_ Nonblocked empty
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
      ws_hub_fifo_owner t i_ Nonblocked (if o then empty else Empty)
    >>>.
  Proof.
    iIntros (->) "%Φ (#Hinv & Howner) HΦ".

    wp_rec.
    wp_apply+ (ws_hub_fifo_pop'𑁒spec_owner with "[$Hinv $Howner] HΦ").
  Qed.

  #[local] Lemma ws_hub_fifo_steal_aux𑁒spec P_notification P_pred Q_pred t ι (sz : nat) i notification pred :
    (0 ≤ i < sz)%Z →
    <<<
      ws_hub_fifo_inv t ι sz ∗
      P_notification ∗
      ( ∀ notify,
        P_notification -∗
        WP notify () {{ itype_unit }} -∗
        WP notification notify {{ res,
          ⌜res = ()%V⌝ ∗
          P_notification
        }}
      ) ∗
      P_pred ∗
      □ (
        P_pred -∗
        WP pred () {{ res,
          ∃ b,
          ⌜res = #b⌝ ∗
          if b then Q_pred else P_pred
        }}
      )
    | ∀∀ vs,
      ws_hub_fifo_model t vs
    >>>
      ws_hub_fifo_steal_aux t #i notification pred @ ↑ι
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
      P_notification ∗
      if o then P_pred else Q_pred
    >>>.
  Proof.
    iIntros "%Hi %Φ ((:inv) & HP_notification & Hnotification & HP_pred & #Hpred) HΦ".

    iLöb as "HLöb" forall (notification).

    wp_rec. wp_load.
    wp_apply (waiters_prepare_wait𑁒spec with "Hwaiters_inv") as "_". 1: done.
    wp_apply+ (wp_wand with "(Hnotification HP_notification [])") as (res) "(-> & HP_notification)".
    { wp_load.
      wp_apply (waiters_notify𑁒spec with "Hwaiters_inv") => //.
    }
    wp_apply+ (wp_wand with "(Hpred HP_pred)") as (res) "(%b & -> & Hb)".
    destruct b; wp_pures.

    - wp_load.
      wp_apply (waiters_cancel_wait𑁒spec with "Hwaiters_inv") as (b) "_". 1: done.

      wp_bind (if: _ then _ else _)%E.
      wp_apply (wp_wand itype_unit) as (res) "->".
      { destruct b; wp_pures. 1: iSteps.
        wp_load.
        wp_apply (waiters_notify_one𑁒spec with "Hwaiters_inv") => //.
      }

      iApply fupd_wp.
      iMod "HΦ" as "(%vs & Hmodel & _ & HΦ)".
      iMod ("HΦ" $! None with "Hmodel") as "HΦ".
      iSteps.

    - awp_apply+ ws_hub_fifo_pop'𑁒spec. 1: iSteps.
      iApply (aacc_aupd with "HΦ"). 1: done. iIntros "%vs Hmodel".
      iAaccIntro with "Hmodel". 1: iSteps. iIntros ([v |]) "Hmodel".

      + iRight. iExists (Some v). iFrame. iIntros "!> HΦ !> _".
        wp_load.
        wp_apply (waiters_cancel_wait𑁒spec with "Hwaiters_inv"). 1: done.
        iSteps.

      + iLeft. iFrame. iIntros "!> HΦ !> _".
        wp_load.
        wp_apply (waiters_commit_wait𑁒spec with "Hwaiters_inv") as "_". 1: done.
        wp_apply+ ("HLöb" with "HP_notification [] Hb HΦ"). 1: iSteps.
  Qed.

  Lemma ws_hub_fifo_steal_until𑁒spec P_notification P_pred Q_pred t ι sz i i_ empty max_round_noyield max_round_yield notification pred :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub_fifo_inv t ι sz ∗
      ws_hub_fifo_owner t i_ Nonblocked empty ∗
      P_notification ∗
      ( ∀ notify,
        P_notification -∗
        WP notify () {{ itype_unit }} -∗
        WP notification notify {{ res,
          ⌜res = ()%V⌝ ∗
          P_notification
        }}
      ) ∗
      P_pred ∗
      □ (
        P_pred -∗
        WP pred () {{ res,
          ∃ b,
          ⌜res = #b⌝ ∗
          if b then Q_pred else P_pred
        }}
      )
    | ∀∀ vs,
      ws_hub_fifo_model t vs
    >>>
      ws_hub_fifo_steal_until t #i #max_round_noyield #max_round_yield notification pred @ ↑ι
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
      ws_hub_fifo_owner t i_ Nonblocked empty ∗
      P_notification ∗
      if o then P_pred else Q_pred
    >>>.
  Proof.
    iIntros (-> _ _) "%Φ (#Hinv & Howner & HP_notification & Hnotification & HP_pred & #Hpred) HΦ".
    iDestruct (ws_hub_fifo_inv_owner with "Hinv Howner") as %Hi.

    wp_rec.

    wp_apply+ (ws_hub_fifo_steal_aux𑁒spec P_notification P_pred Q_pred with "[$Hinv $HP_notification $Hnotification $HP_pred $Hpred]"). 1: lia.
    iApply (atomic_update_wand with "HΦ"). iIntros "%vs %o HΦ H".

    iApply ("HΦ" with "[$Howner $H]").
  Qed.

  Lemma ws_hub_fifo_steal𑁒spec t ι sz i i_ empty max_round_noyield max_round_yield :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub_fifo_inv t ι sz ∗
      ws_hub_fifo_owner t i_ Nonblocked empty
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
      ws_hub_fifo_owner t i_ (if o then Nonblocked else Blocked) empty
    >>>.
  Proof.
    iIntros (-> _ _) "%Φ (#Hinv & Howner) HΦ".
    iDestruct (ws_hub_fifo_inv_owner with "Hinv Howner") as %Hi.

    wp_rec.
    wp_apply+ (ws_hub_fifo_begin_inactive𑁒spec with "Hinv") as "_".

    wp_apply+ (ws_hub_fifo_steal_aux𑁒spec True True True with "[$Hinv]"). 1: lia.
    { iStep. iSplit. 1: iSteps. iStep 3.
      wp_apply+ (ws_hub_fifo_closed𑁒spec with "Hinv") as ([]) "_".
      all: iSteps.
    }
    iApply (atomic_update_wand with "HΦ"). iIntros "%vs %o HΦ _".

    wp_pures.

    wp_bind (Match _ _ _ _).
    wp_apply (wp_wand itype_unit) as (res) "->".
    { destruct o as [v |]; wp_pures.
      - wp_apply (ws_hub_fifo_end_inactive𑁒spec with "Hinv") => //.
      - wp_apply (ws_hub_fifo_notify_all𑁒spec with "Hinv") => //.
    }

    wp_pures.

    iApply ("HΦ" with "Howner").
  Qed.

  Lemma ws_hub_fifo_close𑁒spec t ι sz :
    {{{
      ws_hub_fifo_inv t ι sz
    }}}
      ws_hub_fifo_close t
    {{{
      RET ();
      True
    }}}.
  Proof.
    apply ws_hub_fifo_begin_inactive𑁒spec.
  Qed.
End ws_hub_fifo_G.

#[global] Opaque ws_hub_fifo_inv.
#[global] Opaque ws_hub_fifo_model.
#[global] Opaque ws_hub_fifo_owner.

Section ws_hub_fifo_G.
  Context `{ws_hub_fifo_G : WsHubFifoG Σ}.

  Implicit Types P P_notification P_pred Q Q_pred : iProp Σ.

  Lemma ws_hub_fifo_pop_steal_until𑁒spec P_notification P_pred Q_pred t ι sz i i_ empty max_round_noyield max_round_yield notification pred :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub_fifo_inv t ι sz ∗
      ws_hub_fifo_owner t i_ Nonblocked empty ∗
      P_notification ∗
      ( ∀ notify,
        P_notification -∗
        WP notify () {{ itype_unit }} -∗
        WP notification notify {{ res,
          ⌜res = ()%V⌝ ∗
          P_notification
        }}
      ) ∗
      P_pred ∗
      □ (
        P_pred -∗
        WP pred () {{ res,
          ∃ b,
          ⌜res = #b⌝ ∗
          if b then Q_pred else P_pred
        }}
      )
    | ∀∀ vs,
      ws_hub_fifo_model t vs
    >>>
      ws_hub_fifo_pop_steal_until t #i #max_round_noyield #max_round_yield notification pred @ ↑ι
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
    | empty,
      RET o;
      ws_hub_fifo_owner t i_ Nonblocked empty ∗
      P_notification ∗
      if o then P_pred else Q_pred
    >>>.
  Proof.
    iIntros (-> Hmax_round_noyield Hmax_round_yield) "%Φ (#Hinv & Howner & HP_notification & Hnotification & HP_pred & #Hpred) HΦ".

    wp_rec.
    wp_apply+ (wp_wand with "(Hpred HP_pred)") as (res) "(%b & -> & Hb)".
    destruct b; wp_pures.

    - iMod "HΦ" as "(%vs & Hmodel & _ & HΦ)".
      iMod ("HΦ" $! None with "Hmodel") as "HΦ".
      iSteps.

    - awp_apply+ (ws_hub_fifo_pop𑁒spec with "[$Hinv $Howner]"). 1: done.
      iApply (aacc_aupd with "HΦ"). 1: done. iIntros "%vs Hmodel".
      iAaccIntro with "Hmodel". 1: iFrameSteps. iIntros ([v |]) "Hmodel !>".

      + iRight. iExists (Some v). iFrameSteps.

      + iLeft. iFrame. iIntros "HΦ !> Howner {%- Hmax_round_noyield Hmax_round_yield}".

        wp_apply+ (ws_hub_fifo_steal_until𑁒spec P_notification P_pred Q_pred with "[$Hinv $Howner $HP_notification $Hnotification $Hb $Hpred]"). 1-3: done.
        iApply (atomic_update_wand with "HΦ").
        iSteps.
  Qed.

  Lemma ws_hub_fifo_pop_steal𑁒spec t ι sz i i_ empty max_round_noyield max_round_yield :
    i = ⁺i_ →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub_fifo_inv t ι sz ∗
      ws_hub_fifo_owner t i_ Nonblocked empty
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
    | empty,
      RET o;
      ws_hub_fifo_owner t i_ (if o then Nonblocked else Blocked) empty ∗
      if o then
        True
      else
        ⌜empty = Empty⌝
    >>>.
  Proof.
    iIntros (->) "%Hmax_round_noyield %Hmax_round_yield %Φ (#Hinv & Howner) HΦ".

    wp_rec.

    awp_apply+ (ws_hub_fifo_pop𑁒spec with "[$Hinv $Howner]"); [done.. |].
    iApply (aacc_aupd with "HΦ"); first done. iIntros "%vs Hmodel".
    iAaccIntro with "Hmodel"; first iSteps. iIntros ([v |]) "Hmodel !>".

    - iDestruct "Hmodel" as "(%vs' & -> & Hmodel)".
      iRight. iExists (Some v). iSteps.

    - iLeft. iFrame. iIntros "HΦ !> Howner {%- Hmax_round_noyield Hmax_round_yield}".

      wp_apply+ (ws_hub_fifo_steal𑁒spec with "[$Hinv $Howner]"); [done.. |].
      iApply (atomic_update_wand with "HΦ"). iIntros "%vs %o HΦ Howner".
      iApply ("HΦ" with "[$Howner]").
      destruct o; iFrameSteps.
  Qed.
End ws_hub_fifo_G.

From zoo_parabs Require
  ws_hub_fifo__opaque.
