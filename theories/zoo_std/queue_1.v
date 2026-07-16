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

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Definition queue_1۰model t vs : iProp Σ :=
    ∃ l front back,
    ⌜t = #l⌝ ∗
    l.[front] ↦ front ∗
    l.[back] ↦ back ∗
    chain۰model None front vs back ∗
    chain۰model None back [()%V] ().
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

  #[global] Instance queue_1۰model𑁒timeless t vs :
    Timeless (queue_1۰model t vs).
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
      queue_1۰model t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp۰rec.
    wp۰apply (chain٠block𑁒spec None) as (back) "Hback_model".
    { iApply chain۰model𑁒nil. iSteps. }
    wp۰block l as "(Hfront & Hback & _)".
    iApply "HΦ". iExists l, back, back. iFrameSteps.
    iApply chain۰model𑁒nil₁.
  Qed.

  Lemma queue_1٠is_empty𑁒spec t vs :
    {{{
      queue_1۰model t vs
    }}}
      queue_1٠is_empty t
    {{{
      RET #(bool_decide (vs = []%list));
      queue_1۰model t vs
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".
    wp۰rec. do 2 wp۰load.
    destruct vs as [| v vs].
    - iDestruct (chain۰model𑁒nil with "Hfront") as %->.
      wp۰equal as ? | _.
      { iDestruct (chain𑁒physically𑁒distinct' with "Hback") as %[]; naive_solver. }
      iSteps.
    - wp۰apply (wp𑁒equal𑁒chain with "Hfront Hback") as "Hfront Hback"; [naive_solver lia.. |].
      iSplit; first iSteps. iIntros "->".
      iDestruct (chain۰model𑁒exclusive with "Hback Hfront") as %[]; naive_solver lia.
  Qed.

  Lemma queue_1٠push𑁒spec t vs v :
    {{{
      queue_1۰model t vs
    }}}
      queue_1٠push t v
    {{{
      RET ();
      queue_1۰model t (vs ++ [v])
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".
    wp۰rec.
    wp۰load.
    wp۰apply+ (chain٠block𑁒spec None) as (back') "Hback'".
    { iApply chain۰model𑁒nil. iSteps. }
    wp۰apply+ (chain٠set_next𑁒spec with "Hback") as (?) "(Hback & _)".
    wp۰apply+ (chain٠set_data𑁒spec with "Hback") as "Hback".
    iDestruct (chain۰model𑁒app₂ with "Hfront Hback") as "Hfront".
    iSteps.
  Qed.

  Lemma queue_1٠pop𑁒spec t vs :
    {{{
      queue_1۰model t vs
    }}}
      queue_1٠pop t
    {{{
      RET head vs;
      queue_1۰model t (tail vs)
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp۰rec.
    wp۰apply (queue_1٠is_empty𑁒spec with "Hmodel") as "(:model)".
    destruct vs as [| v vs]; first iSteps.
    wp۰load.
    wp۰apply+ (chain٠next𑁒spec with "Hfront") as (front') "(Hfront & Hfront')".
    wp۰store.
    wp۰apply+ (chain٠data𑁒spec with "Hfront") as "Hfront".
    iSteps.
  Qed.
End zoo۰G.

Require zoo_std.queue_1__opaque.

#[global] Opaque queue_1۰model.
