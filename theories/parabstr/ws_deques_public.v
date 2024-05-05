From zebre Require Import
  prelude.
From zebre.iris.bi Require Import
  big_op.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Import
  opt
  array.
From zebre.saturn Require Import
  inf_ws_deque.
From zebre.parabstr Require Export
  ws_deques.
From zebre Require Import
  options.

Implicit Types v t deque : val.
Implicit Types vs deques : list val.
Implicit Types vss : list (list val).

Definition ws_deques_public_create : val :=
  λ: "sz",
    array_init "sz" (λ: <>, inf_ws_deque_create ()).

Definition ws_deques_public_size : val :=
  array_size.

Definition ws_deques_public_push : val :=
  λ: "t" "i" "v",
    inf_ws_deque_push (array_unsafe_get "t" "i") "v".

Definition ws_deques_public_pop : val :=
  λ: "t" "i",
    inf_ws_deque_pop (array_unsafe_get "t" "i").

Definition ws_deques_public_steal_to : val :=
  λ: "t" "i",
    inf_ws_deque_steal (array_unsafe_get "t" "i").

Class WsDequesPublicG Σ `{zebre_G : !ZebreG Σ} := {
  #[local] ws_deques_public_G_ws_deque_G :: InfWsDequeG Σ ;
}.

Definition ws_deques_public_Σ := #[
  inf_ws_deque_Σ
].
#[global] Instance subG_ws_deques_public_Σ Σ `{zebre_G : !ZebreG Σ} :
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
      inf_ws_deque_inv deque ι.

  Definition ws_deques_public_model t vss : iProp Σ :=
    ∃ deques,
    array_model t DfracDiscarded deques ∗
    [∗ list] i ↦ deque; vs ∈ deques; vss,
      inf_ws_deque_model deque vs.

  Definition ws_deques_public_owner t i : iProp Σ :=
    ∃ deques deque,
    ⌜deques !! i = Some deque⌝ ∗
    array_model t DfracDiscarded deques ∗
    inf_ws_deque_owner deque.

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
    iApply (inf_ws_deque_owner_exclusive with "Hdeque_owner _Hdeque_owner").
  Qed.

  Lemma ws_deques_public_create_spec ι sz :
    let sz' := Z.to_nat sz in
    (0 ≤ sz)%Z →
    {{{ True }}}
      ws_deques_public_create #sz
    {{{ t,
      RET t;
      ws_deques_public_inv t ι sz' ∗
      ws_deques_public_model t (replicate sz' []) ∗
      [∗ list] i ∈ seq 0 sz',
        ws_deques_public_owner t i
    }}}.
  Proof.
    iIntros "%sz' %Hsz %Φ _ HΦ".
    wp_rec.
    pose (Ψ (_ : nat) deques := (
      ( [∗ list] deque ∈ deques,
        inf_ws_deque_inv deque ι
      ) ∗
      ( [∗ list] deque ∈ deques,
        inf_ws_deque_model deque []
      ) ∗
      ( [∗ list] deque ∈ deques,
        inf_ws_deque_owner deque
      )
    )%I).
    iApply wp_fupd.
    wp_smart_apply (array_init_spec Ψ) as (t deques) "(%Hdeques_length & Hdeques & (Hinv & Hmodel & Howner))"; first done.
    { iSteps. iModIntro.
      wp_apply (inf_ws_deque_create_spec with "[//]").
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
      RET #sz; True
    }}}.
  Proof.
    iSteps.
    wp_apply array_size_spec; iSteps.
  Qed.

  Lemma ws_deques_public_push_spec t ι sz i i_ v :
    i = Z.of_nat i_ →
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
    iIntros (->) "!> %Φ ((%deques & %Hdeques_length & #Hdeques & #Hdeques_inv) & (%_deques & %deque & %Hdeques_lookup & _Hdeques & Hdeque_owner)) HΦ".
    iDestruct (array_model_agree with "Hdeques _Hdeques") as %<-. iClear "_Hdeques".
    wp_rec.
    wp_smart_apply (array_unsafe_get_spec with "Hdeques") as "_"; [lia | done | lia |].
    iDestruct (big_sepL_lookup with "Hdeques_inv") as "Hdeque_inv"; first done.
    awp_apply (inf_ws_deque_push_spec with "[$Hdeque_inv $Hdeque_owner]").
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
    i = Z.of_nat i_ →
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
    iIntros (->) "!> %Φ ((%deques & %Hdeques_length & #Hdeques & #Hdeques_inv) & (%_deques & %deque & %Hdeques_lookup & _Hdeques & Hdeque_owner)) HΦ".
    iDestruct (array_model_agree with "Hdeques _Hdeques") as %<-. iClear "_Hdeques".
    wp_rec.
    wp_smart_apply (array_unsafe_get_spec with "Hdeques") as "_"; [lia | done | lia |].
    iDestruct (big_sepL_lookup with "Hdeques_inv") as "Hdeque_inv"; first done.
    awp_apply (inf_ws_deque_pop_spec with "[$Hdeque_inv $Hdeque_owner]").
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

  Lemma ws_deques_public_steal_to_spec t ι (sz : nat) i :
    let i_ := Z.to_nat i in
    (0 ≤ i < sz)%Z →
    <<<
      ws_deques_public_inv t ι sz
    | ∀∀ vss,
      ws_deques_public_model t vss
    >>>
      ws_deques_public_steal_to t #i @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ⌜vss !! i_ = Some []⌝ ∗
          ws_deques_public_model t vss
      | Some v =>
          ∃ vs,
          ⌜vss !! i_ = Some (v :: vs)⌝ ∗
          ws_deques_public_model t (<[i_ := vs]> vss)
      end
    | RET o; True
    >>>.
  Proof.
    iIntros "%i_ %Hi !> %Φ (%deques & %Hdeques_length & #Hdeques & #Hdeques_inv) HΦ".
    wp_rec.
    destruct (lookup_lt_is_Some_2 deques i_) as (deque & Hdeque_lookup); first lia.
    wp_smart_apply (array_unsafe_get_spec with "Hdeques") as "_"; [lia | done.. |].
    iDestruct (big_sepL_lookup with "Hdeques_inv") as "#Hdeque_inv"; first done.
    awp_apply (inf_ws_deque_steal_spec with "Hdeque_inv").
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

  Definition ws_deques_public :=
    Build_ws_deques
      ws_deques_public_owner_valid
      ws_deques_public_owner_exclusive
      ws_deques_public_create_spec
      ws_deques_public_size_spec
      ws_deques_public_push_spec
      ws_deques_public_pop_spec
      ws_deques_public_steal_to_spec.
End ws_deques_public_G.

#[global] Opaque ws_deques_public_create.
#[global] Opaque ws_deques_public_size.
#[global] Opaque ws_deques_public_push.
#[global] Opaque ws_deques_public_pop.
#[global] Opaque ws_deques_public_steal_to.

#[global] Opaque ws_deques_public_inv.
#[global] Opaque ws_deques_public_model.
#[global] Opaque ws_deques_public_owner.
