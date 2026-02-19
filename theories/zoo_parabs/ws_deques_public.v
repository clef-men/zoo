From zoo Require Import
  prelude.
From zoo.iris.bi Require Import
  big_op.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  option
  array
  random_round.
From zoo_saturn Require Import
  ws_deque_2.
From zoo_parabs Require Export
  base
  ws_deques_public__code.
From zoo Require Import
  options.

Implicit Types v t queue round : val.
Implicit Types vs ws queues : list val.
Implicit Types vss : list (list val).
Implicit Types status : status.

Class WsDequesPublicG Σ `{zoo_G : !ZooG Σ} := {
  #[local] ws_deques_public_G_ws_deque_G :: WsDeque2G Σ ;
}.

Definition ws_deques_public_Σ := #[
  ws_deque_2_Σ
].
#[global] Instance subG_ws_deques_public_Σ Σ `{zoo_G : !ZooG Σ} :
  subG ws_deques_public_Σ Σ →
  WsDequesPublicG Σ.
Proof.
  solve_inG.
Qed.

Section ws_deques_public_G.
  Context `{ws_deques_public_G : WsDequesPublicG Σ}.

  Definition ws_deques_public_inv t ι sz : iProp Σ :=
    ∃ queues,
    ⌜sz = length queues⌝ ∗
    array_model t DfracDiscarded queues ∗
    [∗ list] queue ∈ queues,
      ws_deque_2_inv queue ι.
  #[local] Instance : CustomIpat "inv" :=
    " ( %queues{} &
        %Hqueues{}_length &
        #Hqueues{} &
        #Hqueues{}_inv
      )
    ".

  Definition ws_deques_public_model t vss : iProp Σ :=
    ∃ queues,
    array_model t DfracDiscarded queues ∗
    [∗ list] i ↦ queue; vs ∈ queues; vss,
      ws_deque_2_model queue vs.
  #[local] Instance : CustomIpat "model" :=
    " ( %queues{;_} &
        Hqueues{;_} &
        Hqueues{}_model
      )
    ".

  Definition ws_deques_public_owner t i status ws : iProp Σ :=
    ∃ queues queue,
    ⌜queues !! i = Some queue⌝ ∗
    array_model t DfracDiscarded queues ∗
    ws_deque_2_owner queue ws.
  #[local] Instance : CustomIpat "owner" :=
    " ( %queues{;_} &
        %queue{} &
        %Hqueues{}_lookup &
        Hqueues{;_} &
        Hqueue{}_owner
      )
    ".

  #[global] Instance ws_deques_public_model_timeless t vss :
    Timeless (ws_deques_public_model t vss).
  Proof.
    apply _.
  Qed.

  #[global] Instance ws_deques_public_inv_persistent t ι sz :
    Persistent (ws_deques_public_inv t ι sz).
  Proof.
    apply _.
  Qed.

  Lemma ws_deques_public_inv_agree t ι1 sz1 ι2 sz2 :
    ws_deques_public_inv t ι1 sz1 -∗
    ws_deques_public_inv t ι2 sz2 -∗
    ⌜sz1 = sz2⌝.
  Proof.
    iIntros "(:inv =1) (:inv =2)".
    iDestruct (array_model_agree with "Hqueues1 Hqueues2") as %<-.
    iSteps.
  Qed.

  Lemma ws_deques_public_owner_exclusive t i status1 ws1 status2 ws2 :
    ws_deques_public_owner t i status1 ws1 -∗
    ws_deques_public_owner t i status2 ws2 -∗
    False.
  Proof.
    iIntros "(:owner =1) (:owner =2)".
    iDestruct (array_model_agree with "Hqueues1 Hqueues2") as %<-. iClear "Hqueues2".
    simplify.
    iApply (ws_deque_2_owner_exclusive with "Hqueue1_owner Hqueue2_owner").
  Qed.

  Lemma ws_deques_public_inv_model t ι sz vss :
    ws_deques_public_inv t ι sz -∗
    ws_deques_public_model t vss -∗
    ⌜length vss = sz⌝.
  Proof.
    iIntros "(:inv) (:model)".
    iDestruct (big_sepL2_length with "Hqueues_model") as %<-.
    iDestruct (array_model_agree with "Hqueues Hqueues_") as %<-.
    iSteps.
  Qed.
  Lemma ws_deques_public_inv_owner t ι sz i status ws :
    ws_deques_public_inv t ι sz -∗
    ws_deques_public_owner t i status ws -∗
    ⌜i < sz⌝.
  Proof.
    iIntros "(:inv) (:owner)".
    iDestruct (array_model_agree with "Hqueues Hqueues_") as %<-. iClear "Hqueues_".
    iPureIntro. rewrite Hqueues_length. eapply lookup_lt_Some. done.
  Qed.

  Lemma ws_deques_public_model_owner t vss i status ws :
    ws_deques_public_model t vss -∗
    ws_deques_public_owner t i status ws -∗
      ∃ vs,
      ⌜vss !! i = Some vs⌝ ∗
      ⌜vs `suffix_of` ws⌝.
  Proof.
    iIntros "(:model =1) (:owner =2)".
    iDestruct (array_model_agree with "Hqueues1 Hqueues2") as %<-. iClear "Hqueues2".
    iDestruct (big_sepL2_lookup_l with "Hqueues1_model") as "(%vs & $ & Hqueue2_model)"; first done.
    iApply (ws_deque_2_owner_model with "Hqueue2_owner Hqueue2_model").
  Qed.

  Lemma ws_deques_public_create_spec ι sz :
    (0 ≤ sz)%Z →
    {{{
      True
    }}}
      ws_deques_public_create #sz
    {{{ t,
      RET t;
      ws_deques_public_inv t ι ₊sz ∗
      ws_deques_public_model t (replicate ₊sz []) ∗
      [∗ list] i ∈ seq 0 ₊sz,
        ws_deques_public_owner t i Nonblocked []
    }}}.
  Proof.
    iIntros "%Hsz %Φ _ HΦ".

    wp_rec.

    pose (Ψ t (_ : nat) queues := (
      ( [∗ list] queue ∈ queues,
        ws_deque_2_inv queue ι
      ) ∗
      ( [∗ list] queue ∈ queues,
        ws_deque_2_model queue []
      ) ∗
      ( [∗ list] queue ∈ queues,
        ws_deque_2_owner queue []
      )
    )%I).
    iApply wp_fupd.
    wp_smart_apply (array_unsafe_init_spec Ψ) as (t queues) "(%Hqueues_length & Hqueues & (Hinv & Hmodel & Howner))"; first done.
    { iSplit; iSteps.
      wp_apply (ws_deque_2_create_spec with "[//]").
      rewrite /Ψ. setoid_rewrite big_sepL_snoc. iSteps.
    }
    iMod (array_model_persist with "Hqueues") as "#Hqueues".

    iApply "HΦ". iSplitL "Hinv"; last iSplitL "Hmodel".
    - iExists queues. iSteps.
    - iExists queues. rewrite big_sepL2_replicate_r //. iSteps.
    - rewrite big_sepL_seq_index //.
      iApply (big_sepL_impl with "Howner").
      iSteps.
  Qed.

  Lemma ws_deques_public_size_spec t ι sz :
    {{{
      ws_deques_public_inv t ι sz
    }}}
      ws_deques_public_size t
    {{{
      RET #sz;
      True
    }}}.
  Proof.
    iSteps.
    wp_apply array_size_spec; iSteps.
  Qed.

  Lemma ws_deques_public_block_spec t ι sz i i_ ws :
    i = ⁺i_ →
    {{{
      ws_deques_public_inv t ι sz ∗
      ws_deques_public_owner t i_ Nonblocked ws
    }}}
      ws_deques_public_block t #i
    {{{
      RET ();
      ws_deques_public_owner t i_ Blocked ws
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma ws_deques_public_unblock_spec t ι sz i i_ ws :
    i = ⁺i_ →
    {{{
      ws_deques_public_inv t ι sz ∗
      ws_deques_public_owner t i_ Blocked ws
    }}}
      ws_deques_public_unblock t #i
    {{{
      RET ();
      ws_deques_public_owner t i_ Nonblocked ws
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma ws_deques_public_push_spec t ι sz i i_ ws v :
    i = ⁺i_ →
    <<<
      ws_deques_public_inv t ι sz ∗
      ws_deques_public_owner t i_ Nonblocked ws
    | ∀∀ vss,
      ws_deques_public_model t vss
    >>>
      ws_deques_public_push t #i v @ ↑ι
    <<<
      ∃∃ vs,
      ⌜vss !! i_ = Some vs⌝ ∗
      ⌜vs `suffix_of` ws⌝ ∗
      ws_deques_public_model t (<[i_ := vs ++ [v]]> vss)
    | RET ();
      ws_deques_public_owner t i_ Nonblocked (vs ++ [v])
    >>>.
  Proof.
    iIntros (->) "%Φ ((:inv) & (:owner)) HΦ".
    iDestruct (array_model_agree with "Hqueues Hqueues_") as %<-. iClear "Hqueues_".

    wp_rec.
    wp_smart_apply (array_unsafe_get_spec with "Hqueues") as "_"; [lia | done | lia |].

    iDestruct (big_sepL_lookup with "Hqueues_inv") as "Hqueue_inv"; first done.
    awp_smart_apply (ws_deque_2_push_spec with "[$Hqueue_inv $Hqueue_owner]").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vss (:model)".
    iDestruct (array_model_agree with "Hqueues Hqueues_") as %<-. iClear "Hqueues_".
    iDestruct (big_sepL2_lookup_Some_l with "Hqueues_model") as %(vs & Hvss_lookup); first done.
    iDestruct (big_sepL2_insert_acc with "Hqueues_model") as "(Hqueue_model & Hqueues_model)"; [done.. |].
    iAaccIntro with "Hqueue_model".

    - iIntros "Hqueue_model".
      iDestruct ("Hqueues_model" with "Hqueue_model") as "Hqueues_model".
      rewrite !list_insert_id //. iSteps.

    - iIntros "(%Hsuffix & Hqueue_model)".
      iDestruct ("Hqueues_model" with "Hqueue_model") as "Hqueues_model".
      rewrite list_insert_id //. iSteps.
  Qed.

  Lemma ws_deques_public_pop_spec t ι sz i i_ ws :
    i = ⁺i_ →
    <<<
      ws_deques_public_inv t ι sz ∗
      ws_deques_public_owner t i_ Nonblocked ws
    | ∀∀ vss,
      ws_deques_public_model t vss
    >>>
      ws_deques_public_pop t #i @ ↑ι
    <<<
      ∃∃ o ws',
      match o with
      | None =>
          ⌜vss !! i_ = Some []⌝ ∗
          ⌜ws' = []⌝ ∗
          ws_deques_public_model t vss
      | Some v =>
          ∃ vs,
          ⌜vss !! i_ = Some (vs ++ [v])⌝ ∗
          ⌜vs ++ [v] `suffix_of` ws⌝ ∗
          ⌜ws' = vs⌝ ∗
          ws_deques_public_model t (<[i_ := vs]> vss)
      end
    | RET o;
      ws_deques_public_owner t i_ Nonblocked ws'
    >>>.
  Proof.
    iIntros (->) "%Φ ((:inv) & (:owner)) HΦ".
    iDestruct (array_model_agree with "Hqueues Hqueues_") as %<-. iClear "Hqueues_".

    wp_rec.
    wp_smart_apply (array_unsafe_get_spec with "Hqueues") as "_"; [lia | done | lia |].

    iDestruct (big_sepL_lookup with "Hqueues_inv") as "Hqueue_inv"; first done.
    awp_smart_apply (ws_deque_2_pop_spec with "[$Hqueue_inv $Hqueue_owner]").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vss (:model)".
    iDestruct (array_model_agree with "Hqueues Hqueues_") as %<-. iClear "Hqueues_".
    iDestruct (big_sepL2_lookup_Some_l with "Hqueues_model") as %(vs & Hvss_lookup); first done.
    iDestruct (big_sepL2_insert_acc with "Hqueues_model") as "(Hqueue_model & Hqueues_model)"; [done.. |].
    iAaccIntro with "Hqueue_model".

    - iIntros "Hqueue_model".
      iDestruct ("Hqueues_model" with "Hqueue_model") as "Hqueues_model".
      rewrite !list_insert_id //. iSteps.

    - iIntros "%o %ws' (%Hsuffix & Hqueue_model)".
      iExists o, ws'. iSplitL; last iSteps.
      destruct o as [v |].

      + iDestruct "Hqueue_model" as "(%vs' & -> & -> & Hqueue_model)".
        iDestruct ("Hqueues_model" with "Hqueue_model") as "Hqueues_model".
        rewrite list_insert_id //. iSteps.

      + iDestruct "Hqueue_model" as "(-> & -> & Hqueue_model)".
        iDestruct ("Hqueues_model" with "Hqueue_model") as "Hqueues_model".
        rewrite !list_insert_id //. iSteps.
  Qed.

  Lemma ws_deques_public_steal_to_spec t ι (sz : nat) i i_ ws j :
    i = ⁺i_ →
    (0 ≤ j < sz)%Z →
    <<<
      ws_deques_public_inv t ι sz ∗
      ws_deques_public_owner t i_ Blocked ws
    | ∀∀ vss,
      ws_deques_public_model t vss
    >>>
      ws_deques_public_steal_to t #i #j @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_deques_public_model t vss
      | Some v =>
          ∃ vs,
          ⌜vss !! ₊j = Some (v :: vs)⌝ ∗
          ws_deques_public_model t (<[₊j := vs]> vss)
      end
    | RET o;
      ws_deques_public_owner t i_ Blocked ws
    >>>.
  Proof.
    iIntros (-> Hj) "%Φ ((:inv) & Howner) HΦ".

    wp_rec.
    destruct (lookup_lt_is_Some_2 queues ₊j) as (queue & Hqueue_lookup); first lia.
    wp_smart_apply (array_unsafe_get_spec with "Hqueues") as "_"; [lia | done.. |].

    iDestruct (big_sepL_lookup with "Hqueues_inv") as "#Hqueue_inv"; first done.
    awp_smart_apply (ws_deque_2_steal_spec with "Hqueue_inv") without "Howner".
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vss (:model)".
    iDestruct (array_model_agree with "Hqueues Hqueues_") as %<-. iClear "Hqueues_".
    iDestruct (big_sepL2_lookup_Some_l with "Hqueues_model") as %(vs & Hvss_lookup); first done.
    iDestruct (big_sepL2_insert_acc with "Hqueues_model") as "(Hqueue_model & Hqueues_model)"; [done.. |].
    iAaccIntro with "Hqueue_model".

    - iIntros "Hqueue_model".
      iDestruct ("Hqueues_model" with "Hqueue_model") as "Hqueues_model".
      rewrite !list_insert_id //. iSteps.

    - iIntros "Hqueue_model !>". destruct vs as [| v vs].

      + iExists None. iSplitL; last iSteps.
        iDestruct ("Hqueues_model" with "Hqueue_model") as "Hqueues_model".
        rewrite !list_insert_id //. iSteps.

      + iExists (Some v). iSplitL; last iSteps.
        iDestruct ("Hqueues_model" with "Hqueue_model") as "Hqueues_model".
        rewrite list_insert_id //. iSteps.
  Qed.
End ws_deques_public_G.

#[global] Opaque ws_deques_public_inv.
#[global] Opaque ws_deques_public_model.
#[global] Opaque ws_deques_public_owner.

Section ws_deques_public_G.
  Context `{ws_deques_public_G : WsDequesPublicG Σ}.

  #[local] Lemma ws_deques_public_steal_as_0_spec t ι (sz : nat) i i_ ws round (n : nat) :
    i = ⁺i_ →
    <<<
      ws_deques_public_inv t ι sz ∗
      ws_deques_public_owner t i_ Blocked ws ∗
      random_round_model' round (sz - 1) n
    | ∀∀ vss,
      ws_deques_public_model t vss
    >>>
      ws_deques_public_steal_as_0 t #sz #i round #n @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_deques_public_model t vss
      | Some v =>
          ∃ j vs,
          ⌜₊i ≠ j⌝ ∗
          ⌜vss !! j = Some (v :: vs)⌝ ∗
          ws_deques_public_model t (<[j := vs]> vss)
      end
    | RET o;
      ∃ n,
      ws_deques_public_owner t i_ Blocked ws ∗
      random_round_model' round (sz - 1) n
    >>>.
  Proof.
    iIntros (->) "%Φ (#Hinv & Howner & Hround) HΦ".
    iDestruct (ws_deques_public_inv_owner with "Hinv Howner") as %Hi.

    iLöb as "HLöb" forall (n).

    wp_rec. wp_pures.
    case_bool_decide as Hcase; wp_pures.

    - iMod "HΦ" as "(%vss & Hmodel & _ & HΦ)".
      iApply ("HΦ" $! None with "Hmodel [$Howner Hround]"); first iSteps.

    - wp_apply (random_round_next_spec' with "Hround") as (j) "(%Hj & Hround)"; first lia.
      wp_pures.
      rewrite Nat2Z.id.
      pose k := (i_ + 1 + j) `mod` sz.
      assert ((i_ + 1 + j) `rem` sz = k)%Z as ->.
      { rewrite Z.rem_mod_nonneg; lia. }
      awp_smart_apply (ws_deques_public_steal_to_spec with "[$Hinv $Howner]") without "Hround"; [done | lia |].
      iApply (aacc_aupd with "HΦ"); first done. iIntros "%vss Hmodel".
      iAaccIntro with "Hmodel"; first iSteps. iIntros ([ v |]).

      + rewrite Nat2Z.id.
        iSteps as (vs Hlookup) "Hmodel". iExists (Some v). iSteps. iExists k. iSteps. iPureIntro.
        clear Hlookup. rewrite {}/k.
        destruct_decide (i_ + 1 + j < sz).
        * rewrite Nat.mod_small //. lia.
        * assert (i_ + 1 + j < sz * 2) as ?%Nat.div_lt_upper_bound by lia; last lia.
          assert ((i_ + 1 + j) `div` sz = 1) by lia.
          lia.

      + iSteps as "HΦ Howner Hround".
        assert (n - 1 = (n - 1)%nat)%Z as -> by lia.
        iSteps.
  Qed.
  Lemma ws_deques_public_steal_as_spec t ι sz i i_ ws round :
    i = ⁺i_ →
    0 < sz →
    <<<
      ws_deques_public_inv t ι sz ∗
      ws_deques_public_owner t i_ Blocked ws ∗
      random_round_model' round (sz - 1) (sz - 1)
    | ∀∀ vss,
      ws_deques_public_model t vss
    >>>
      ws_deques_public_steal_as t #i round @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_deques_public_model t vss
      | Some v =>
          ∃ j vs,
          ⌜₊i ≠ j⌝ ∗
          ⌜vss !! j = Some (v :: vs)⌝ ∗
          ws_deques_public_model t (<[j := vs]> vss)
      end
    | RET o;
      ∃ n,
      ws_deques_public_owner t i_ Blocked ws ∗
      random_round_model' round (sz - 1) n
    >>>.
  Proof.
    iIntros (->) "%Hsz %Φ (#Hinv & Hround) HΦ".

    wp_rec.
    wp_smart_apply (ws_deques_public_size_spec with "Hinv") as "_".
    wp_pures.
    assert (sz - 1 = (sz - 1)%nat)%Z as -> by lia.
    wp_apply (ws_deques_public_steal_as_0_spec with "[$Hinv $Hround] HΦ"); first done.
  Qed.
End ws_deques_public_G.

From zoo_parabs Require
  ws_deques_public__opaque.
