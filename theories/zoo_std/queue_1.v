Require Import zoo.prelude.
Require Import zoo.base.
Require Export zoo_std.queue_1__code.
Require Import zoo_std.option.
Require Import zoo_std.chain.
Require Import zoo_std.queue_1__types.
Require Import zoo.options.

Implicit Types l : location.
Implicit Types t v front back : val.
Implicit Types vs : list val.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition queue_1_model t vs : iProp Σ :=
    ∃ l front back,
    ⌜t = #l⌝ ∗
    l.[front] ↦ front ∗
    l.[back] ↦ back ∗
    chain_model None front vs back ∗
    chain_model None back [()%V] ().
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

  #[global] Instance queue_1_model_timeless t vs :
    Timeless (queue_1_model t vs).
  Proof.
    apply _.
  Qed.

  Lemma queue_1٠create𑁒spec :
    {{{
      True
    }}}
      queue_1٠create ()
    {{{
      t
    , RET t;
      queue_1_model t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    wp_apply (chain٠block𑁒spec None) as (back) "Hback_model".
    { iApply chain_model_nil. iSteps. }
    wp_block l as "(Hfront & Hback & _)".
    iApply "HΦ". iExists l, back, back. iFrameSteps.
    iApply chain_model_nil_1.
  Qed.

  Lemma queue_1٠is_empty𑁒spec t vs :
    {{{
      queue_1_model t vs
    }}}
      queue_1٠is_empty t
    {{{
      RET #(bool_decide (vs = []%list));
      queue_1_model t vs
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

  Lemma queue_1٠push𑁒spec t vs v :
    {{{
      queue_1_model t vs
    }}}
      queue_1٠push t v
    {{{
      RET ();
      queue_1_model t (vs ++ [v])
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".
    wp_rec.
    wp_load.
    wp_apply+ (chain٠block𑁒spec None) as (back') "Hback'".
    { iApply chain_model_nil. iSteps. }
    wp_apply+ (chain٠set_next𑁒spec with "Hback") as (?) "(Hback & _)".
    wp_apply+ (chain٠set_data𑁒spec with "Hback") as "Hback".
    iDestruct (chain_model_app_2 with "Hfront Hback") as "Hfront".
    iSteps.
  Qed.

  Lemma queue_1٠pop𑁒spec t vs :
    {{{
      queue_1_model t vs
    }}}
      queue_1٠pop t
    {{{
      RET head vs;
      queue_1_model t (tail vs)
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp_rec.
    wp_apply (queue_1٠is_empty𑁒spec with "Hmodel") as "(:model)".
    destruct vs as [| v vs]; first iSteps.
    wp_load.
    wp_apply+ (chain٠next𑁒spec with "Hfront") as (front') "(Hfront & Hfront')".
    wp_store.
    wp_apply+ (chain٠data𑁒spec with "Hfront") as "Hfront".
    iSteps.
  Qed.
End zoo_G.

Require zoo_std.queue_1__opaque.

#[global] Opaque queue_1_model.
