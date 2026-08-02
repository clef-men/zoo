Require Import zoo.prelude.
Require Import zoo.base.
Require Import zoo_std.option.
Require Import zoo_std.chain.
Require Export zoo_std.queue_2__code.
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

  #[global] Instance queue_2۰modelｰtimeless t vs :
    Timeless (queue_2۰model t vs).
  Proof.
    apply _.
  Qed.

  Lemma queue_2٠createｰspec :
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
    wp۰apply (chain٠blockｰspec (Some _)) as (back) "Hback_model".
    { iApply chain۰modelｰnil. iSteps. }
    wp۰block l as "(Hfront & Hback & _)".
    iApply "HΦ". iExists l, back, back. iFrameSteps.
    iApply chain۰modelｰnil₁.
  Qed.

  Lemma queue_2٠is_emptyｰspec t vs :
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
    - iDestruct (chain۰modelｰnil with "Hfront") as %->.
      wp۰equal as ? | _.
      { iDestruct (chainｰphysicallyｰdistinct' with "Hback") as %[]; naive_solver. }
      iSteps.
    - wp۰apply (wpｰequalｰchain with "Hfront Hback") as "Hfront Hback"; [naive_solver lia.. |].
      iSplit; first iSteps. iIntros "->".
      iDestruct (chain۰modelｰexclusive with "Hback Hfront") as %[]; naive_solver lia.
  Qed.

  Lemma queue_2٠pushｰspec t vs v :
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
    wp۰apply+ (chain٠blockｰspec (Some _)) as (back') "Hback'".
    { iApply chain۰modelｰnil. iSteps. }
    iDestruct (chain۰modelｰtag with "Hback'") as "#(%back'_ & -> & Hback'_header)"; first done. wp۰match.
    wp۰load.
    iDestruct (chain۰modelｰtag with "Hback") as "#(%back_ & -> & Hback_header)"; first done. wp۰match.
    wp۰apply+ (chain٠set_nextｰspec with "Hback") as (?) "(Hback & _)".
    wp۰apply+ (chain٠set_dataｰspec with "Hback") as "Hback".
    iDestruct (chain۰modelｰapp₂ with "Hfront Hback") as "Hfront".
    iSteps.
  Qed.

  Lemma queue_2٠popｰspec t vs :
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
    { iDestruct (chain۰modelｰapp₂ with "Hfront Hback") as "Hfront".
      iApply (chain۰modelｰtag with "Hfront").
      { simpl_length/=. lia. }
    }

    wp۰match.
    destruct vs as [| v1 vs].
    - iDestruct (chain۰modelｰnil with "Hfront") as %->.
      wp۰apply (chain٠nextｰspecｰsingleton with "Hback") as "Hback".
      iSteps.
    - wp۰apply (chain٠nextｰspec with "Hfront") as (front') "(Hfront & Hfront')".
      destruct vs as [| v2 vs].
      + iDestruct (chain۰modelｰnil with "Hfront'") as %->.
        iDestruct (chain۰modelｰtag with "Hback") as "#(%back_ & -> & Hback_header)"; first done. wp۰match.
        wp۰store.
        wp۰apply+ (chain٠dataｰspec with "Hfront") as "Hfront".
        iSteps.
      + iDestruct (chain۰modelｰtag with "Hfront'") as "#(%front'_ & -> & Hfront'_header)"; first done. wp۰match.
        wp۰store.
        wp۰apply+ (chain٠dataｰspec with "Hfront") as "Hfront".
        iSteps.
  Qed.
End zoo۰G.

Require zoo_std.queue_2__opaque.

#[global] Opaque queue_2۰model.
