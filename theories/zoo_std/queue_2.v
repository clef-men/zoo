Require Import zoo.prelude.
Require Import zoo.language.notations.
Require Import zoo.diaframe.
Require Export zoo_std.base.
Require Export zoo_std.queue_2__code.
Require Import zoo_std.option.
Require Import zoo_std.chain.
Require Import zoo_std.queue_2__types.
Require Import zoo.options.

Implicit Types l : location.
Implicit Types t v front back : val.
Implicit Types vs : list val.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition queue_2_model t vs : iProp Σ :=
    ∃ l front back,
    ⌜t = #l⌝ ∗
    l.[front] ↦ front ∗
    l.[back] ↦ back ∗
    chain_model (Some §Node) front vs back ∗
    chain_model (Some §Node) back [()%V] ().
  #[local] Instance : CustomIpat "model" :=
    " ( %l
      & %front
      & %back
      & ->
      & Hl_front
      & Hl_back
      & Hfront
      & Hback
      )
    ".

  #[global] Instance queue_2_model_timeless t vs :
    Timeless (queue_2_model t vs).
  Proof.
    apply _.
  Qed.

  Lemma queue_2٠create𑁒spec :
    {{{
      True
    }}}
      queue_2٠create ()
    {{{
      t
    , RET t;
      queue_2_model t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    wp_apply (chain٠block𑁒spec (Some _)) as (back) "Hback_model".
    { iApply chain_model_nil. iSteps. }
    wp_block l as "(Hfront & Hback & _)".
    iApply "HΦ". iExists l, back, back. iFrameSteps.
    iApply chain_model_nil_1.
  Qed.

  Lemma queue_2٠is_empty𑁒spec t vs :
    {{{
      queue_2_model t vs
    }}}
      queue_2٠is_empty t
    {{{
      RET #(bool_decide (vs = []%list));
      queue_2_model t vs
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".
    wp_rec. do 2 wp_load.
    destruct vs as [| v vs].
    - iDestruct (chain_model_nil with "Hfront") as %->.
      wp_equal as ? | _.
      { iDestruct (chain_physically_distinct' with "Hback") as %[]; naive_solver. }
      iSteps.
    - wp_apply (wp_equal_chain with "Hfront Hback") as "Hfront Hback"; [naive_solver lia.. |].
      iSplit; first iSteps. iIntros "->".
      iDestruct (chain_model_exclusive with "Hback Hfront") as %[]; naive_solver lia.
  Qed.

  Lemma queue_2٠push𑁒spec t vs v :
    {{{
      queue_2_model t vs
    }}}
      queue_2٠push t v
    {{{
      RET ();
      queue_2_model t (vs ++ [v])
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".
    wp_rec.
    wp_apply+ (chain٠block𑁒spec (Some _)) as (back') "Hback'".
    { iApply chain_model_nil. iSteps. }
    iDestruct (chain_model_tag with "Hback'") as "#(%back'_ & -> & Hback'_header)"; first done. wp_match.
    wp_load.
    iDestruct (chain_model_tag with "Hback") as "#(%back_ & -> & Hback_header)"; first done. wp_match.
    wp_apply+ (chain٠set_next𑁒spec with "Hback") as (?) "(Hback & _)".
    wp_apply+ (chain٠set_data𑁒spec with "Hback") as "Hback".
    iDestruct (chain_model_app_2 with "Hfront Hback") as "Hfront".
    iSteps.
  Qed.

  Lemma queue_2٠pop𑁒spec t vs :
    {{{
      queue_2_model t vs
    }}}
      queue_2٠pop t
    {{{
      RET head vs;
      queue_2_model t (tail vs)
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".
    wp_rec. wp_load.

    iAssert (
      ∃ front_ : location,
      ⌜front = #front_⌝ ∗
      front_ ↦ₕ Header §Node 2
    )%I as "(%front_ & -> & #Hfront_header)".
    { iDestruct (chain_model_app_2 with "Hfront Hback") as "Hfront".
      iApply (chain_model_tag with "Hfront").
      { simpl_length/=. lia. }
    }

    wp_match.
    destruct vs as [| v1 vs].
    - iDestruct (chain_model_nil with "Hfront") as %->.
      wp_apply (chain٠next𑁒spec_singleton with "Hback") as "Hback".
      iSteps.
    - wp_apply (chain٠next𑁒spec with "Hfront") as (front') "(Hfront & Hfront')".
      destruct vs as [| v2 vs].
      + iDestruct (chain_model_nil with "Hfront'") as %->.
        iDestruct (chain_model_tag with "Hback") as "#(%back_ & -> & Hback_header)"; first done. wp_match.
        wp_store.
        wp_apply+ (chain٠data𑁒spec with "Hfront") as "Hfront".
        iSteps.
      + iDestruct (chain_model_tag with "Hfront'") as "#(%front'_ & -> & Hfront'_header)"; first done. wp_match.
        wp_store.
        wp_apply+ (chain٠data𑁒spec with "Hfront") as "Hfront".
        iSteps.
  Qed.
End zoo_G.

Require zoo_std.queue_2__opaque.

#[global] Opaque queue_2_model.
