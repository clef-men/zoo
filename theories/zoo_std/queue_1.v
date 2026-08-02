Require Import zoo.prelude.
Require Import zoo.base.
Require Import zoo_std.option.
Require Export zoo_std.queue_1__code.
Require Import zoo_std.queue_1__types.
Require Import zoo.options.

Implicit Type l : location.
Implicit Type t v front back : val.
Implicit Type vs : list val.

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

  #[global] Instance queue_1۰modelｰtimeless t vs :
    Timeless (queue_1۰model t vs).
  Proof.
    apply _.
  Qed.

  Lemma queue_1٠createｰspec :
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
    wp۰apply (chain٠blockｰspec None) as (back) "Hback_model".
    { iApply chain۰modelｰnil. iSteps. }
    wp۰block l as "(Hfront & Hback & _)".
    iApply "HΦ". iExists l, back, back. iFrameSteps.
    iApply chain۰modelｰnil₁.
  Qed.

  Lemma queue_1٠is_emptyｰspec t vs :
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
    - iDestruct (chain۰modelｰnil with "Hfront") as %->.
      wp۰equal as ? | _.
      { iDestruct (chainｰphysicallyｰdistinct' with "Hback") as %[]; naive_solver. }
      iSteps.
    - wp۰apply (wpｰequalｰchain with "Hfront Hback") as "Hfront Hback"; [naive_solver lia.. |].
      iSplit; first iSteps. iIntros "->".
      iDestruct (chain۰modelｰexclusive with "Hback Hfront") as %[]; naive_solver lia.
  Qed.

  Lemma queue_1٠pushｰspec t vs v :
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
    wp۰apply+ (chain٠blockｰspec None) as (back') "Hback'".
    { iApply chain۰modelｰnil. iSteps. }
    wp۰apply+ (chain٠set_nextｰspec with "Hback") as (?) "(Hback & _)".
    wp۰apply+ (chain٠set_dataｰspec with "Hback") as "Hback".
    iDestruct (chain۰modelｰapp₂ with "Hfront Hback") as "Hfront".
    iSteps.
  Qed.

  Lemma queue_1٠popｰspec t vs :
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
    wp۰apply (queue_1٠is_emptyｰspec with "Hmodel") as "(:model)".
    destruct vs as [| v vs]; first iSteps.
    wp۰load.
    wp۰apply+ (chain٠nextｰspec with "Hfront") as (front') "(Hfront & Hfront')".
    wp۰store.
    wp۰apply+ (chain٠dataｰspec with "Hfront") as "Hfront".
    iSteps.
  Qed.
End zoo۰G.

Require zoo_std.queue_1__opaque.

#[global] Opaque queue_1۰model.
