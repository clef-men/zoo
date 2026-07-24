Require Import zoo.prelude.
Require Import zoo.base.
Require Export zoo_std.queue_2__code.
Require Import zoo_std.option.
Require Import zoo_std.chain.
Require Import zoo_std.queue_2__types.
Require Import zoo.options.

Implicit Type l : location.
Implicit Type t v front back : val.
Implicit Type vs : list val.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Definition queue_2۰model t vs : iProp Σ :=
    ∃ l front back,
    ⌜t = #l⌝ ∗
    l.[front] ↦ front ∗
    l.[back] ↦ back ∗
    chain۰model (Some §Node) front vs back ∗
    chain۰model (Some §Node) back [()%V] ().
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

  #[global] Instance queue_2۰model𑁒timeless t vs :
    Timeless (queue_2۰model t vs).
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
      queue_2۰model t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp۰rec.
    wp۰apply (chain٠block𑁒spec (Some _)) as (back) "Hback_model".
    { iApply chain۰model𑁒nil. iSteps. }
    wp۰block l as "(Hfront & Hback & _)".
    iApply "HΦ". iExists l, back, back. iFrameSteps.
    iApply chain۰model𑁒nil₁.
  Qed.

  Lemma queue_2٠is_empty𑁒spec t vs :
    {{{
      queue_2۰model t vs
    }}}
      queue_2٠is_empty t
    {{{
      RET #(bool_decide (vs = []%list));
      queue_2۰model t vs
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

  Lemma queue_2٠push𑁒spec t vs v :
    {{{
      queue_2۰model t vs
    }}}
      queue_2٠push t v
    {{{
      RET ();
      queue_2۰model t (vs ++ [v])
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".
    wp۰rec.
    wp۰apply+ (chain٠block𑁒spec (Some _)) as (back') "Hback'".
    { iApply chain۰model𑁒nil. iSteps. }
    iDestruct (chain۰model𑁒tag with "Hback'") as "#(%back'_ & -> & Hback'_header)"; first done. wp۰match.
    wp۰load.
    iDestruct (chain۰model𑁒tag with "Hback") as "#(%back_ & -> & Hback_header)"; first done. wp۰match.
    wp۰apply+ (chain٠set_next𑁒spec with "Hback") as (?) "(Hback & _)".
    wp۰apply+ (chain٠set_data𑁒spec with "Hback") as "Hback".
    iDestruct (chain۰model𑁒app₂ with "Hfront Hback") as "Hfront".
    iSteps.
  Qed.

  Lemma queue_2٠pop𑁒spec t vs :
    {{{
      queue_2۰model t vs
    }}}
      queue_2٠pop t
    {{{
      RET head vs;
      queue_2۰model t (tail vs)
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".
    wp۰rec. wp۰load.

    iAssert (
      ∃ front_ : location,
      ⌜front = #front_⌝ ∗
      front_ ↦ₕ Header §Node 2
    )%I as "(%front_ & -> & #Hfront_header)".
    { iDestruct (chain۰model𑁒app₂ with "Hfront Hback") as "Hfront".
      iApply (chain۰model𑁒tag with "Hfront").
      { simpl_length/=. lia. }
    }

    wp۰match.
    destruct vs as [| v1 vs].
    - iDestruct (chain۰model𑁒nil with "Hfront") as %->.
      wp۰apply (chain٠next𑁒spec𑁒singleton with "Hback") as "Hback".
      iSteps.
    - wp۰apply (chain٠next𑁒spec with "Hfront") as (front') "(Hfront & Hfront')".
      destruct vs as [| v2 vs].
      + iDestruct (chain۰model𑁒nil with "Hfront'") as %->.
        iDestruct (chain۰model𑁒tag with "Hback") as "#(%back_ & -> & Hback_header)"; first done. wp۰match.
        wp۰store.
        wp۰apply+ (chain٠data𑁒spec with "Hfront") as "Hfront".
        iSteps.
      + iDestruct (chain۰model𑁒tag with "Hfront'") as "#(%front'_ & -> & Hfront'_header)"; first done. wp۰match.
        wp۰store.
        wp۰apply+ (chain٠data𑁒spec with "Hfront") as "Hfront".
        iSteps.
  Qed.
End zoo۰G.

Require zoo_std.queue_2__opaque.

#[global] Opaque queue_2۰model.
