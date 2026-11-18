Require Import zoo.prelude.
Require Import zoo.iris.base_logic.lib.saved_pred.
Require Import zoo.iris.base_logic.lib.twins.
Require Import zoo.base.
Require Import zoo_std.option.
Require Export zoo_saturn.stack_mpmc_3__code.
Require Import zoo_saturn.stack_mpmc_3__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type v backoff : val.
Implicit Type vs : list val.
Implicit Type η μ : gname.

Zoo name :=
  { #stack : val
  ; #channel : val
  ; inv : namespace
  ; model : gname
  }.

Zoo global :=
  { stack : stack_mpmc_1
  ; channel : channel_sync_2 gname gname
  ; model : twins (leibnizO (list val))
  ; saved_pred : saved_pred val
  }.

Section stack_mpmc_3۰G.
  Context `{stack_mpmc_3۰G : StackMpmc3G Σ}.

  Implicit Type Ψ Χ : val → iProp Σ.

  #[local] Definition model₁' γ_model vs :=
    twins۰twin₁ γ_model (DfracOwn 1) vs.
  #[local] Definition model₁ γ vs :=
    model₁' γ.(stack_mpmc_3۰name۰model) vs.
  #[local] Definition model₂' γ_model vs :=
    twins۰twin₂ γ_model vs.
  #[local] Definition model₂ γ vs :=
    model₂' γ.(stack_mpmc_3۰name۰model) vs.

  #[local] Definition push۰pre γ v η : iProp Σ :=
    ∃ Ψ,
    saved_pred η Ψ ∗
    AU <{
      ∃∃ vs,
      model₁ γ vs
    }> @ ⊤ ∖ ↑γ.(stack_mpmc_3۰name۰inv), ∅ <{
      ∀∀ b,
      model₁ γ (if b then v :: vs else vs)
    , COMM
      True -∗ Ψ #b
    }>.
  #[local] Instance : CustomIpat "push۰pre" :=
    " ( %Ψ
      & #Hη{!;}
      & HΨ
      )
    ".
  #[local] Definition push۰post v η μ : iProp Σ :=
    ∃ Ψ,
    saved_pred η Ψ ∗
    Ψ true%V.
  #[local] Instance : CustomIpat "push۰post" :=
    " ( %Ψ
      & #Hη!
      & HΨ
      )
    ".

  #[local] Definition pop۰pre γ μ : iProp Σ :=
    ∃ Χ,
    saved_pred μ Χ ∗
    AU <{
      ∃∃ vs,
      model₁ γ vs
    }> @ ⊤ ∖ ↑γ.(stack_mpmc_3۰name۰inv), ∅ <{
      ∀∀ o,
      match o with
      | Nothing =>
          ⌜vs = []⌝ ∗
          model₁ γ []
      | Something v =>
          ∃ vs',
          ⌜vs = v :: vs'⌝ ∗
          model₁ γ vs'
      | Anything =>
          model₁ γ vs
      end
    , COMM
      True -∗ Χ o
    }>.
  #[local] Instance : CustomIpat "pop۰pre" :=
    " ( %Χ
      & #Hμ{!;}
      & HΧ
      )
    ".
  #[local] Definition pop۰post v η μ : iProp Σ :=
    ∃ Χ,
    saved_pred μ Χ ∗
    Χ (Something v).
  #[local] Instance : CustomIpat "pop۰post" :=
    " ( %Χ
      & #Hμ!
      & HΧ
      )
    ".

  #[local] Definition inv۰inner γ : iProp Σ :=
    ∃ vs,
    model₂ γ vs ∗
    stack_mpmc_1۰model γ.(stack_mpmc_3۰name۰stack) vs.
  #[local] Instance : CustomIpat "inv۰inner" :=
    " ( %vs{}
      & >Hmodel₂
      & >Hstack۰model
      )
    ".
  #[local] Definition inv' γ : iProp Σ :=
    stack_mpmc_1۰inv γ.(stack_mpmc_3۰name۰stack) (γ.(stack_mpmc_3۰name۰inv).@"stack") ∗
    channel_sync_2۰inv γ.(stack_mpmc_3۰name۰channel) (γ.(stack_mpmc_3۰name۰inv).@"channel") (push۰pre γ) (pop۰pre γ) push۰post pop۰post ∗
    inv (γ.(stack_mpmc_3۰name۰inv).@"inv") (inv۰inner γ).
  #[local] Instance : CustomIpat "inv'" :=
    " ( #Hstack۰inv
      & #Hchannel۰inv
      & #Hinv
      )
    ".
  Please Definition stack_mpmc_3۰inv γ ι : iProp Σ :=
    ⌜ι = γ.(stack_mpmc_3۰name۰inv)⌝ ∗
    inv' γ.
  #[local] Instance : CustomIpat "inv" :=
    " ( ->
      & (:inv')
      )
    ".

  Please Definition stack_mpmc_3۰model :=
    model₁.
  #[local] Instance : CustomIpat "model" :=
    " Hmodel₁{_{}}
    ".

  Zoo derive Timeless for stack_mpmc_3۰model.

  Zoo derive Persistent for stack_mpmc_3۰inv.

  #[local] Lemma modelｰalloc :
    ⊢ |==>
      ∃ γ_model,
      model₁' γ_model [] ∗
      model₂' γ_model [].
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

  Lemma stack_mpmc_3۰modelｰexclusive γ vs1 vs2 :
    stack_mpmc_3۰model γ vs1 -∗
    stack_mpmc_3۰model γ vs2 -∗
    False.
  Proof.
    apply model₁ｰexclusive.
  Qed.

  Lemma stack_mpmc_3٠createｰspec ι :
    {{{
      True
    }}}
      stack_mpmc_3٠create ()
    {{{
      γ
    , RET γ;
      stack_mpmc_3۰inv γ ι ∗
      stack_mpmc_3۰model γ []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp۰rec.
    wp۰apply (channel_sync_2٠createｰspecｰinit with "[//]") as (channel) "Hchannel۰init". 1: done.
    wp۰apply (stack_mpmc_1٠createｰspec with "[//]") as (stack) "(#Hstack۰inv & Hstack۰model)".
    wp۰pures.

    iMod modelｰalloc as "(%γ_model & Hmodel₁ & Hmodel₂)".

    pose γ :=
      {|stack_mpmc_3۰name۰stack := stack
      ; stack_mpmc_3۰name۰channel := channel
      ; stack_mpmc_3۰name۰inv := ι
      ; stack_mpmc_3۰name۰model := γ_model
      |}.

    iMod (inv_alloc (ι.@"inv") _ (inv۰inner γ) with "[$]") as "#Hinv".

    iMod (channel_sync_2۰initｰtoｰinv (ι.@"channel") (push۰pre γ) (pop۰pre γ) push۰post pop۰post with "Hchannel۰init []") as "#Hchannel۰inv".
    { iIntros "!> !> %v %η %μ (:push۰pre) (:pop۰pre)".

      iInv "Hinv" as "(:inv۰inner)".

      iMod "HΨ" as "(%vs_ & Hmodel₁ & _ & HΨ)".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
      iMod (modelｰupdate (v :: vs) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΨ" $! true with "Hmodel₁") as "HΨ".

      iMod "HΧ" as "(%vs_ & Hmodel₁ & _ & HΧ)".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
      iMod (modelｰupdate vs with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΧ" $! (Something v) with "[$Hmodel₁ //]") as "HΧ".

      iSplitR "HΨ HΧ". { iFrameSteps. }
      iSteps.
    }

    iApply ("HΦ" $! γ).
    iFrameSteps.
  Qed.

  Lemma stack_mpmc_3٠try_pushｰspec γ ι v :
    <<<
      stack_mpmc_3۰inv γ ι
    | ∀∀ vs,
      stack_mpmc_3۰model γ vs
    >>>
      stack_mpmc_3٠try_push γ v
      @ ↑ι
    <<<
      ∃∃ b,
      stack_mpmc_3۰model γ (if b then v :: vs else vs)
    | RET #b;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec credit:"H£".
    awp۰apply+ (stack_mpmc_1٠try_pushｰspec with "Hstack۰inv").
    iInv "Hinv" as "(:inv۰inner)".
    iApply (aaccｰaupd with "HΦ"). 1: solve_ndisj. iIntros "%vs_ (:model)".
    iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
    iAaccIntro with "Hstack۰model". 1: iSteps. iIntros ([]) "Hstack۰model".

    - iRight. iExists true.
      iMod (modelｰupdate (v :: vs) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iFrameSteps.

    - iLeft. iFrame. iIntros "!> HΦ !>".
      iSplitR "H£ HΦ". { iFrame. }
      iIntros "_ {%}".

      iApply wpｰfupd.
      iMod (saved_predｰalloc Φ) as "(%η & #Hη)".
      wp۰apply+ (channel_sync_2٠sendｰspec η with "[$Hchannel۰inv $Hη $HΦ]") as ([]) "HΦ".

      + iDestruct "HΦ" as "(%μ & (:push۰post))".
        iDestruct (saved_predｰagree true%V with "Hη Hη!") as "-#Heq".
        iMod (lc_fupd_elim_later with "H£ Heq") as "Heq".
        iRewrite "Heq" => //.

      + iDestruct "HΦ" as "(:push۰pre !)".
        iDestruct (saved_predｰagree false%V with "Hη Hη!") as "-#Heq".
        iMod (lc_fupd_elim_later with "H£ Heq") as "Heq".
        iRewrite "Heq".

        iMod "HΨ" as "(%vs & Hmodel & _ & HΦ)".
        iMod ("HΦ" $! false with "Hmodel") as "HΦ".

        iSteps.
  Qed.

  #[local] Lemma stack_mpmc_3٠push₁ｰspec γ ι v backoff :
    <<<
      stack_mpmc_3۰inv γ ι ∗
      backoff۰model backoff
    | ∀∀ vs,
      stack_mpmc_3۰model γ vs
    >>>
      stack_mpmc_3٠push₁ γ v backoff
      @ ↑ι
    <<<
      stack_mpmc_3۰model γ (v :: vs)
    | RET ();
      True
    >>>.
  Proof.
    iIntros "%Φ (#Hinv & Hbackoff) HΦ".

    iLöb as "HLöb" forall (backoff).

    wp۰rec.

    awp۰apply+ (stack_mpmc_3٠try_pushｰspec with "Hinv").
    iApply (aaccｰaupd with "HΦ"). 1: done. iIntros "%vs Hmodel".
    iAaccIntro with "Hmodel". 1: iSteps. iIntros ([]) "Hmodel !>".

    - iRight. iFrameSteps.

    - iLeft. iFrameSteps.
  Qed.

  Lemma stack_mpmc_3٠pushｰspec γ ι v :
    <<<
      stack_mpmc_3۰inv γ ι
    | ∀∀ vs,
      stack_mpmc_3۰model γ vs
    >>>
      stack_mpmc_3٠push γ v
      @ ↑ι
    <<<
      stack_mpmc_3۰model γ (v :: vs)
    | RET ();
      True
    >>>.
  Proof.
    iIntros "%Φ Hinv HΦ".

    wp۰rec.
    wp۰apply+ (stack_mpmc_3٠push₁ｰspec with "[$Hinv] HΦ"). 1: iSteps.
  Qed.

  Lemma stack_mpmc_3٠try_popｰspec γ ι :
    <<<
      stack_mpmc_3۰inv γ ι
    | ∀∀ vs,
      stack_mpmc_3۰model γ vs
    >>>
      stack_mpmc_3٠try_pop γ
      @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | Nothing =>
          ⌜vs = []⌝ ∗
          stack_mpmc_3۰model γ []
      | Something v =>
          ∃ vs',
          ⌜vs = v :: vs'⌝ ∗
          stack_mpmc_3۰model γ vs'
      | Anything =>
          stack_mpmc_3۰model γ vs
      end
    | RET o;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec credit:"H£".
    awp۰apply+ (stack_mpmc_1٠try_popｰspec with "Hstack۰inv").
    iInv "Hinv" as "(:inv۰inner)".
    iApply (aaccｰaupd with "HΦ"). 1: solve_ndisj. iIntros "%vs_ (:model)".
    iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
    iAaccIntro with "Hstack۰model". 1: iSteps. iIntros ([| | v]).

    - iIntros "(-> & Hstack۰model)".
      iRight. iExists Nothing.
      iFrameSteps.

    - iIntros "Hstack۰model".
      iLeft. iFrame. iIntros "!> HΦ !>".
      iSplitR "H£ HΦ". { iFrame. }
      iIntros "_ {%}".

      iApply wpｰfupd.
      iMod (saved_predｰalloc Φ) as "(%μ & #Hμ)".
      wp۰apply+ (channel_sync_2٠recvｰspec μ with "[$Hchannel۰inv $Hμ $HΦ]") as ([v |]) "HΦ".
      all: wp۰pures.

      + iDestruct "HΦ" as "(%η & (:pop۰post))".
        iDestruct (saved_predｰagree ltac۰simpl:(Something v : val) with "Hμ Hμ!") as "-#Heq".
        iMod (lc_fupd_elim_later with "H£ Heq") as "Heq".
        iRewrite "Heq" => //.

      + iDestruct "HΦ" as "(:pop۰pre !)".
        iDestruct (saved_predｰagree ltac۰simpl:(Anything : val) with "Hμ Hμ!") as "-#Heq".
        iMod (lc_fupd_elim_later with "H£ Heq") as "Heq".
        iRewrite "Heq".

        iMod "HΧ" as "(%vs & Hmodel & _ & HΦ)".
        iMod ("HΦ" $! Anything with "Hmodel") as "HΦ".

        iSteps.

    - iIntros "(%vs' & -> & Hstack۰model)".
      iRight. iExists (Something v).
      iMod (modelｰupdate vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iFrameSteps.
  Qed.

  #[local] Lemma stack_mpmc_3٠pop₁ｰspec γ ι backoff :
    <<<
      stack_mpmc_3۰inv γ ι ∗
      backoff۰model backoff
    | ∀∀ vs,
      stack_mpmc_3۰model γ vs
    >>>
      stack_mpmc_3٠pop₁ γ backoff
      @ ↑ι
    <<<
      stack_mpmc_3۰model γ (tail vs)
    | RET head vs;
      True
    >>>.
  Proof.
    iIntros "%Φ (#Hinv & Hbackoff) HΦ".

    iLöb as "HLöb" forall (backoff).

    wp۰rec.

    awp۰apply+ (stack_mpmc_3٠try_popｰspec with "Hinv").
    iApply (aaccｰaupd with "HΦ"). 1: done. iIntros "%vs Hmodel".
    iAaccIntro with "Hmodel". 1: iSteps. iIntros ([| | v]) "Hmodel !>".

    - iDestruct "Hmodel" as "(-> & Hmodel)".
      iRight. iFrameSteps.

    - iLeft. iFrameSteps.

    - iDestruct "Hmodel" as "(%vs' & -> & Hmodel)".
      iRight. iFrameSteps.
  Qed.

  Lemma stack_mpmc_3٠popｰspec γ ι :
    <<<
      stack_mpmc_3۰inv γ ι
    | ∀∀ vs,
      stack_mpmc_3۰model γ vs
    >>>
      stack_mpmc_3٠pop γ
      @ ↑ι
    <<<
      stack_mpmc_3۰model γ (tail vs)
    | RET head vs;
      True
    >>>.
  Proof.
    iIntros "%Φ Hinv HΦ".

    wp۰rec.
    wp۰apply (stack_mpmc_3٠pop₁ｰspec with "[$Hinv] HΦ"). 1: iSteps.
  Qed.
End stack_mpmc_3۰G.

Require zoo_saturn.stack_mpmc_3__opaque.

Please opacify.
