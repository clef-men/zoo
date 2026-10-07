Require Import zoo.prelude.
Require Import zoo.iris.base_logic.lib.twins.
Require Import zoo.base.
Require Import zoo_std.option.
Require Export zoo_saturn.stack_mpmc_1__code.
Require Import zoo_saturn.stack_mpmc_1__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type 𝑡 : location.
Implicit Type v t backoff : val.
Implicit Type vs : list val.

Zoo global :=
  { model : twins (leibnizO (list val))
  }.

Section stack_mpmc_1۰G.
  Context `{stack_mpmc_1۰G : StackMpmc1G Σ}.

  #[local] Definition metadata :=
    gname.
  Implicit Type γ : metadata.

  #[local] Definition model₁ γ vs :=
    twins۰twin₁ γ (DfracOwn 1) vs.
  #[local] Definition model₂ γ vs :=
    twins۰twin₂ γ vs.

  #[local] Definition inv۰inner 𝑡 γ : iProp Σ :=
    ∃ vs,
    𝑡 ↦ᵣ glist۰to_val vs ∗
    model₂ γ vs.
  #[local] Instance : CustomIpat "inv۰inner" :=
    " ( %vs{}
      & Ht
      & Hmodel₂
      )
    ".
  Please Definition stack_mpmc_1۰inv t ι : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    inv ι (inv۰inner 𝑡 γ).
  #[local] Instance : CustomIpat "inv" :=
    " ( %𝑡
      & %γ
      & ->
      & #Hmeta
      & #Hinv
      )
    ".

  Please Definition stack_mpmc_1۰model t vs : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    model₁ γ vs.
  #[local] Instance : CustomIpat "model" :=
    " ( %𝑡{;_}
      & %γ{;_}
      & %Heq{}
      & Hmeta_{}
      & Hmodel₁{_{}}
      )
    ".

  #[global] Instance stack_mpmc_1۰modelｰtimeless t vs :
    Timeless (stack_mpmc_1۰model t vs).
  Proof.
    apply _.
  Qed.

  #[global] Instance stack_mpmc_1۰invｰpersistent t ι :
    Persistent (stack_mpmc_1۰inv t ι).
  Proof.
    apply _.
  Qed.

  #[local] Lemma modelｰalloc :
    ⊢ |==>
      ∃ γ,
      model₁ γ [] ∗
      model₂ γ [].
  Proof.
    apply twinsｰalloc'.
  Qed.
  #[local] Lemma model₁ｰexclusive γ vs1 vs2 :
    model₁ γ vs1 -∗
    model₁ γ vs2 -∗
    False.
  Proof.
    apply twins۰twin₁ｰexclusive.
  Qed.
  #[local] Lemma modelｰagree γ vs1 vs2 :
    model₁ γ vs1 -∗
    model₂ γ vs2 -∗
    ⌜vs1 = vs2⌝.
  Proof.
    apply: twinsｰagreeｰL.
  Qed.
  #[local] Lemma modelｰupdate {γ vs1 vs2} vs :
    model₁ γ vs1 -∗
    model₂ γ vs2 ==∗
      model₁ γ vs ∗
      model₂ γ vs.
  Proof.
    apply twinsｰupdate.
  Qed.

  Lemma stack_mpmc_1۰modelｰexclusive t vs1 vs2 :
    stack_mpmc_1۰model t vs1 -∗
    stack_mpmc_1۰model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simp.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->.
    iApply (model₁ｰexclusive with "Hmodel₁_1 Hmodel₁_2").
  Qed.

  Lemma stack_mpmc_1٠createｰspec ι :
    {{{
      True
    }}}
      stack_mpmc_1٠create ()
    {{{
      t
    , RET t;
      stack_mpmc_1۰inv t ι ∗
      stack_mpmc_1۰model t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp۰rec.
    wp۰ref 𝑡 as "Hmeta" "Ht".

    iMod modelｰalloc as "(%γ & Hmodel₁ & Hmodel₂)".

    iMod (metaｰset γ with "Hmeta") as "#Hmeta". 1: done.

    iApply "HΦ".
    iSplitR "Hmodel₁". 2: iFrameSteps.
    iStep 2.
    iApply inv_alloc.
    iFrame.
  Qed.

  Lemma stack_mpmc_1٠try_pushｰspec t ι v :
    <<<
      stack_mpmc_1۰inv t ι
    | ∀∀ vs,
      stack_mpmc_1۰model t vs
    >>>
      stack_mpmc_1٠try_push t v
      @ ↑ι
    <<<
      ∃∃ b,
      stack_mpmc_1۰model t (if b then v :: vs else vs)
    | RET #b;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec. wp۰pures.

    wp۰bind (!_)%E.
    iInv "Hinv" as "(:inv۰inner =1)".
    wp۰load.
    iSplitR "HΦ". { iFrameSteps. }
    iModIntro.

    wp۰pures.

    wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
    iInv "Hinv" as "(:inv۰inner =2)".
    wp۰cas as _ | ->%(inj _).

    - iMod "HΦ" as "(%vs & Hmodel & _ & HΦ)".
      iMod ("HΦ" $! false with "Hmodel") as "HΦ".

      iSplitR "HΦ". { iFrameSteps. }
      iSteps.

    - iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
      iMod (modelｰupdate (v :: vs1) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" $! true with "[$Hmodel₁]") as "HΦ". 1: iSteps.

      iSplitR "HΦ". { iExists (v :: vs1). iFrameSteps. }
      iSteps.
  Qed.

  #[local] Lemma stack_mpmc_1٠push₁ｰspec t ι v backoff :
    <<<
      stack_mpmc_1۰inv t ι ∗
      backoff۰model backoff
    | ∀∀ vs,
      stack_mpmc_1۰model t vs
    >>>
      stack_mpmc_1٠push₁ t v backoff
      @ ↑ι
    <<<
      stack_mpmc_1۰model t (v :: vs)
    | RET ();
      True
    >>>.
  Proof.
    iIntros "%Φ (#Hinv & Hbackoff) HΦ".

    iLöb as "HLöb" forall (backoff).

    wp۰rec.

    awp۰apply+ (stack_mpmc_1٠try_pushｰspec with "Hinv").
    iApply (aaccｰaupd with "HΦ"). 1: done. iIntros "%vs Hmodel".
    iAaccIntro with "Hmodel". 1: iSteps. iIntros ([]) "Hmodel !>".

    - iRight. iFrameSteps.

    - iLeft. iFrameSteps.
  Qed.

  Lemma stack_mpmc_1٠pushｰspec t ι v :
    <<<
      stack_mpmc_1۰inv t ι
    | ∀∀ vs,
      stack_mpmc_1۰model t vs
    >>>
      stack_mpmc_1٠push t v
      @ ↑ι
    <<<
      stack_mpmc_1۰model t (v :: vs)
    | RET ();
      True
    >>>.
  Proof.
    iIntros "%Φ Hinv HΦ".

    wp۰rec.
    wp۰apply+ (stack_mpmc_1٠push₁ｰspec with "[$Hinv] HΦ"). 1: iSteps.
  Qed.

  Lemma stack_mpmc_1٠try_popｰspec t ι :
    <<<
      stack_mpmc_1۰inv t ι
    | ∀∀ vs,
      stack_mpmc_1۰model t vs
    >>>
      stack_mpmc_1٠try_pop t
      @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | Nothing =>
          ⌜vs = []⌝ ∗
          stack_mpmc_1۰model t []
      | Something v =>
          ∃ vs',
          ⌜vs = v :: vs'⌝ ∗
          stack_mpmc_1۰model t vs'
      | Anything =>
          stack_mpmc_1۰model t vs
      end
    | RET o;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec.

    wp۰bind (!_)%E.
    iInv "Hinv" as "(:inv۰inner =1)".
    wp۰load.
    destruct vs1 as [| v vs1].

    - iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
      iMod ("HΦ" $! Nothing with "[$Hmodel₁]") as "HΦ". 1: iSteps.

      iSplitR "HΦ". { iExists []. iFrameSteps. }
      iSteps.

    - iSplitR "HΦ". { iExists (v :: vs1). iFrameSteps. }
      iModIntro.

      wp۰pures.

      wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
      iInv "Hinv" as "(:inv۰inner =2)".
      wp۰cas as _ | Hcas.

      + iMod "HΦ" as "(%vs & Hmodel & _ & HΦ)".
        iMod ("HΦ" $! Anything with "Hmodel") as "HΦ".

        iSplitR "HΦ". { iFrameSteps. }
        iSteps.

      + destruct vs2. 1: done. apply (inj glist۰to_val _ (_ :: _)) in Hcas as [= -> ->].

        iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
        iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
        iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
        iMod (modelｰupdate vs1 with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
        iMod ("HΦ" $! (Something v) with "[$Hmodel₁]") as "HΦ". 1: iSteps.
        iSplitR "HΦ". { iFrameSteps. }
        iSteps.
  Qed.

  #[local] Lemma stack_mpmc_1٠pop₁ｰspec t ι backoff :
    <<<
      stack_mpmc_1۰inv t ι ∗
      backoff۰model backoff
    | ∀∀ vs,
      stack_mpmc_1۰model t vs
    >>>
      stack_mpmc_1٠pop₁ t backoff
      @ ↑ι
    <<<
      stack_mpmc_1۰model t (tail vs)
    | RET head vs;
      True
    >>>.
  Proof.
    iIntros "%Φ (#Hinv & Hbackoff) HΦ".

    iLöb as "HLöb" forall (backoff).

    wp۰rec.

    awp۰apply+ (stack_mpmc_1٠try_popｰspec with "Hinv").
    iApply (aaccｰaupd with "HΦ"). 1: done. iIntros "%vs Hmodel".
    iAaccIntro with "Hmodel". 1: iSteps. iIntros ([| | v]) "Hmodel !>".

    - iDestruct "Hmodel" as "(-> & Hmodel)".
      iRight. iFrameSteps.

    - iLeft. iFrameSteps.

    - iDestruct "Hmodel" as "(%vs' & -> & Hmodel)".
      iRight. iFrameSteps.
  Qed.

  Lemma stack_mpmc_1٠popｰspec t ι :
    <<<
      stack_mpmc_1۰inv t ι
    | ∀∀ vs,
      stack_mpmc_1۰model t vs
    >>>
      stack_mpmc_1٠pop t
      @ ↑ι
    <<<
      stack_mpmc_1۰model t (tail vs)
    | RET head vs;
      True
    >>>.
  Proof.
    iIntros "%Φ Hinv HΦ".

    wp۰rec.
    wp۰apply (stack_mpmc_1٠pop₁ｰspec with "[$Hinv] HΦ"). 1: iSteps.
  Qed.

  Lemma stack_mpmc_1٠snapshotｰspec t ι :
    <<<
      stack_mpmc_1۰inv t ι
    | ∀∀ vs,
      stack_mpmc_1۰model t vs
    >>>
      stack_mpmc_1٠snapshot t
      @ ↑ι
    <<<
      stack_mpmc_1۰model t vs
    | RET glist۰to_val vs;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec.

    iInv "Hinv" as "(:inv۰inner)".
    wp۰load.
    iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
    iMod ("HΦ" with "[$Hmodel₁]") as "HΦ". 1: iSteps.
    iSteps.
  Qed.
End stack_mpmc_1۰G.

Require zoo_saturn.stack_mpmc_1__opaque.

Please opacify.
