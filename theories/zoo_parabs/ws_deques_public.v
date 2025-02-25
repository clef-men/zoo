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
  inf_ws_deque_2.
From zoo_parabs Require Export
  base
  ws_deques_public__code.
From zoo Require Import
  options.

Implicit Types v t deque round : val.
Implicit Types vs deques : list val.
Implicit Types vss : list (list val).

Class WsDequesPublicG Σ `{zoo_G : !ZooG Σ} := {
  #[local] ws_deques_public_G_ws_deque_G :: InfWsDeque2G Σ ;
}.

Definition ws_deques_public_Σ := #[
  inf_ws_deque_2_Σ
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
    ∃ deques,
    ⌜sz = length deques⌝ ∗
    array_model t DfracDiscarded deques ∗
    [∗ list] deque ∈ deques,
      inf_ws_deque_2_inv deque ι.

  Definition ws_deques_public_model t vss : iProp Σ :=
    ∃ deques,
    array_model t DfracDiscarded deques ∗
    [∗ list] i ↦ deque; vs ∈ deques; vss,
      inf_ws_deque_2_model deque vs.

  Definition ws_deques_public_owner t i : iProp Σ :=
    ∃ deques deque,
    ⌜deques !! i = Some deque⌝ ∗
    array_model t DfracDiscarded deques ∗
    inf_ws_deque_2_owner deque.

  #[global] Instance ws_deques_public_model_timeless t vss :
    Timeless (ws_deques_public_model t vss).
  Proof.
    apply _.
  Qed.
  #[global] Instance ws_deques_public_owner_timeless t i :
    Timeless (ws_deques_public_owner t i).
  Proof.
    apply _.
  Qed.
  #[global] Instance ws_deques_public_inv_persistent t ι sz :
    Persistent (ws_deques_public_inv t ι sz).
  Proof.
    apply _.
  Qed.

  Lemma ws_deques_public_owner_valid t ι sz i :
    ws_deques_public_inv t ι sz -∗
    ws_deques_public_owner t i -∗
    ⌜i < sz⌝.
  Proof.
    iIntros "(%deques & %Hdeques_length & #Hdeques & #Hdeques_inv) (%_deques & %deque & %Hdeques_lookup & _Hdeques & Hdeque_owner)".
    iDestruct (array_model_agree with "Hdeques _Hdeques") as %<-. iClear "_Hdeques".
    iPureIntro. rewrite Hdeques_length. eapply lookup_lt_Some. done.
  Qed.
  Lemma ws_deques_public_owner_exclusive t i :
    ws_deques_public_owner t i -∗
    ws_deques_public_owner t i -∗
    False.
  Proof.
    iIntros "(%deques & %deque & %Hlookup & #Hdeques & Hdeque_owner) (%_deques & %_deque & %_Hlookup & _Hdeques & _Hdeque_owner)".
    iDestruct (array_model_agree with "Hdeques _Hdeques") as %<-. iClear "_Hdeques".
    simplify.
    iApply (inf_ws_deque_2_owner_exclusive with "Hdeque_owner _Hdeque_owner").
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
        ws_deques_public_owner t i
    }}}.
  Proof.
    iIntros "%Hsz %Φ _ HΦ".
    wp_rec.
    pose (Ψ (_ : nat) deques := (
      ( [∗ list] deque ∈ deques,
        inf_ws_deque_2_inv deque ι
      ) ∗
      ( [∗ list] deque ∈ deques,
        inf_ws_deque_2_model deque []
      ) ∗
      ( [∗ list] deque ∈ deques,
        inf_ws_deque_2_owner deque
      )
    )%I).
    iApply wp_fupd.
    wp_smart_apply (array_unsafe_init_spec Ψ) as (t deques) "(%Hdeques_length & Hdeques & (Hinv & Hmodel & Howner))"; first done.
    { iSteps.
      wp_apply (inf_ws_deque_2_create_spec with "[//]").
      rewrite /Ψ. setoid_rewrite big_sepL_snoc. iSteps.
    }
    iMod (array_model_persist with "Hdeques") as "#Hdeques".
    iApply "HΦ". iSplitL "Hinv"; last iSplitL "Hmodel".
    - iExists deques. iSteps.
    - iExists deques. rewrite big_sepL2_replicate_r //. iSteps.
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

  Lemma ws_deques_public_push_spec t ι sz i i_ v :
    i = ⁺i_ →
    <<<
      ws_deques_public_inv t ι sz ∗
      ws_deques_public_owner t i_
    | ∀∀ vss,
      ws_deques_public_model t vss
    >>>
      ws_deques_public_push t #i v @ ↑ι
    <<<
      ∃∃ vs,
      ⌜vss !! i_ = Some vs⌝ ∗
      ws_deques_public_model t (<[i_ := vs ++ [v]]> vss)
    | RET ();
      ws_deques_public_owner t i_
    >>>.
  Proof.
    iIntros (->) "%Φ ((%deques & %Hdeques_length & #Hdeques & #Hdeques_inv) & (%_deques & %deque & %Hdeques_lookup & _Hdeques & Hdeque_owner)) HΦ".
    iDestruct (array_model_agree with "Hdeques _Hdeques") as %<-. iClear "_Hdeques".
    wp_rec.
    wp_smart_apply (array_unsafe_get_spec with "Hdeques") as "_"; [lia | done | lia |].
    iDestruct (big_sepL_lookup with "Hdeques_inv") as "Hdeque_inv"; first done.
    awp_smart_apply (inf_ws_deque_2_push_spec with "[$Hdeque_inv $Hdeque_owner]").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vss (%_deques & _Hdeques & Hdeques_model)".
    iDestruct (array_model_agree with "Hdeques _Hdeques") as %<-. iClear "_Hdeques".
    iDestruct (big_sepL2_lookup_Some_l with "Hdeques_model") as %(vs & Hvss_lookup); first done.
    iDestruct (big_sepL2_insert_acc with "Hdeques_model") as "(Hdeque_model & Hdeques_model)"; [done.. |].
    iAaccIntro with "Hdeque_model".
    - iIntros "Hdeque_model".
      iDestruct ("Hdeques_model" with "Hdeque_model") as "Hdeques_model".
      rewrite !list_insert_id //. iSteps.
    - iIntros "Hdeque_model". iExists vs. iSplitL; last iSteps.
      iDestruct ("Hdeques_model" with "Hdeque_model") as "Hdeques_model".
      rewrite list_insert_id //. iSteps.
  Qed.

  Lemma ws_deques_public_pop_spec t ι sz i i_ :
    i = ⁺i_ →
    <<<
      ws_deques_public_inv t ι sz ∗
      ws_deques_public_owner t i_
    | ∀∀ vss,
      ws_deques_public_model t vss
    >>>
      ws_deques_public_pop t #i @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ⌜vss !! i_ = Some []⌝ ∗
          ws_deques_public_model t vss
      | Some v =>
          ∃ vs,
          ⌜vss !! i_ = Some (vs ++ [v])⌝ ∗
          ws_deques_public_model t (<[i_ := vs]> vss)
      end
    | RET o;
      ws_deques_public_owner t i_
    >>>.
  Proof.
    iIntros (->) "%Φ ((%deques & %Hdeques_length & #Hdeques & #Hdeques_inv) & (%_deques & %deque & %Hdeques_lookup & _Hdeques & Hdeque_owner)) HΦ".
    iDestruct (array_model_agree with "Hdeques _Hdeques") as %<-. iClear "_Hdeques".
    wp_rec.
    wp_smart_apply (array_unsafe_get_spec with "Hdeques") as "_"; [lia | done | lia |].
    iDestruct (big_sepL_lookup with "Hdeques_inv") as "Hdeque_inv"; first done.
    awp_smart_apply (inf_ws_deque_2_pop_spec with "[$Hdeque_inv $Hdeque_owner]").
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vss (%_deques & _Hdeques & Hdeques_model)".
    iDestruct (array_model_agree with "Hdeques _Hdeques") as %<-. iClear "_Hdeques".
    iDestruct (big_sepL2_lookup_Some_l with "Hdeques_model") as %(vs & Hvss_lookup); first done.
    iDestruct (big_sepL2_insert_acc with "Hdeques_model") as "(Hdeque_model & Hdeques_model)"; [done.. |].
    iAaccIntro with "Hdeque_model".
    - iIntros "Hdeque_model".
      iDestruct ("Hdeques_model" with "Hdeque_model") as "Hdeques_model".
      rewrite !list_insert_id //. iSteps.
    - iIntros "%o Hdeque_model". iExists o. iSplitL; last iSteps. destruct o as [v |].
      + iDestruct "Hdeque_model" as "(%vs' & -> & Hdeque_model)".
        iDestruct ("Hdeques_model" with "Hdeque_model") as "Hdeques_model".
        rewrite list_insert_id //. iSteps.
      + iDestruct "Hdeque_model" as "(-> & Hdeque_model)".
        iDestruct ("Hdeques_model" with "Hdeque_model") as "Hdeques_model".
        rewrite !list_insert_id //. iSteps.
  Qed.

  Lemma ws_deques_public_steal_to_spec t ι (sz : nat) i i_ j :
    i = ⁺i_ →
    (0 ≤ j < sz)%Z →
    <<<
      ws_deques_public_inv t ι sz ∗
      ws_deques_public_owner t i_
    | ∀∀ vss,
      ws_deques_public_model t vss
    >>>
      ws_deques_public_steal_to t #i #j @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ⌜vss !! ₊j = Some []⌝ ∗
          ws_deques_public_model t vss
      | Some v =>
          ∃ vs,
          ⌜vss !! ₊j = Some (v :: vs)⌝ ∗
          ws_deques_public_model t (<[₊j := vs]> vss)
      end
    | RET o;
      ws_deques_public_owner t i_
    >>>.
  Proof.
    iIntros (-> Hj) "%Φ ((%deques & %Hdeques_length & #Hdeques & #Hdeques_inv) & Howner) HΦ".
    wp_rec.
    destruct (lookup_lt_is_Some_2 deques ₊j) as (deque & Hdeque_lookup); first lia.
    wp_smart_apply (array_unsafe_get_spec with "Hdeques") as "_"; [lia | done.. |].
    iDestruct (big_sepL_lookup with "Hdeques_inv") as "#Hdeque_inv"; first done.
    awp_smart_apply (inf_ws_deque_2_steal_spec with "Hdeque_inv") without "Howner".
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vss (%_deques & _Hdeques & Hdeques_model)".
    iDestruct (array_model_agree with "Hdeques _Hdeques") as %<-. iClear "_Hdeques".
    iDestruct (big_sepL2_lookup_Some_l with "Hdeques_model") as %(vs & Hvss_lookup); first done.
    iDestruct (big_sepL2_insert_acc with "Hdeques_model") as "(Hdeque_model & Hdeques_model)"; [done.. |].
    iAaccIntro with "Hdeque_model".
    - iIntros "Hdeque_model".
      iDestruct ("Hdeques_model" with "Hdeque_model") as "Hdeques_model".
      rewrite !list_insert_id //. iSteps.
    - iIntros "Hdeque_model !>". destruct vs as [| v vs].
      + iExists None. iSplitL; last iSteps.
        iDestruct ("Hdeques_model" with "Hdeque_model") as "Hdeques_model".
        rewrite !list_insert_id //. iSteps.
      + iExists (Some v). iSplitL; last iSteps.
        iDestruct ("Hdeques_model" with "Hdeque_model") as "Hdeques_model".
        rewrite list_insert_id //. iSteps.
  Qed.
End ws_deques_public_G.

#[global] Opaque ws_deques_public_inv.
#[global] Opaque ws_deques_public_model.
#[global] Opaque ws_deques_public_owner.

Section ws_deques_public_G.
  Context `{ws_deques_public_G : WsDequesPublicG Σ}.

  #[local] Lemma ws_deques_public_steal_as_0_spec t ι (sz : nat) i i_ round (n : nat) :
    i = ⁺i_ →
    <<<
      ws_deques_public_inv t ι sz ∗
      ws_deques_public_owner t i_ ∗
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
      ws_deques_public_owner t i_ ∗
      random_round_model' round (sz - 1) n
    >>>.
  Proof.
    iIntros (->) "%Φ (#Hinv & Howner & Hround) HΦ".
    iDestruct (ws_deques_public_owner_valid with "Hinv Howner") as %Hi.
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
        destruct (decide (i_ + 1 + j < sz)).
        * rewrite Nat.mod_small //. lia.
        * assert (i_ + 1 + j < sz * 2) as ?%Nat.div_lt_upper_bound by lia; last lia.
          assert ((i_ + 1 + j) `div` sz = 1) by lia.
          lia.
      + iSteps as (_) "HΦ Howner Hround".
        assert (n - 1 = (n - 1)%nat)%Z as -> by lia.
        iSteps.
  Qed.
  Lemma ws_deques_public_steal_as_spec t ι sz i i_ round :
    i = ⁺i_ →
    0 < sz →
    <<<
      ws_deques_public_inv t ι sz ∗
      ws_deques_public_owner t i_ ∗
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
      ws_deques_public_owner t i_ ∗
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

#[global] Opaque ws_deques_public_create.
#[global] Opaque ws_deques_public_size.
#[global] Opaque ws_deques_public_push.
#[global] Opaque ws_deques_public_pop.
#[global] Opaque ws_deques_public_steal_to.
#[global] Opaque ws_deques_public_steal_as.
