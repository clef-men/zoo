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

Zoo global :=
  { stack : stack_mpmc_1
  ; channel : channel_sync_2 gname gname
  ; model : twins (leibnizO (list val))
  ; saved_pred : saved_pred val
  }.

Module base.
  Section stack_mpmc_3۰G.
    Context `{stack_mpmc_3۰G : StackMpmc3G Σ}.

    Implicit Type t : location.
    Implicit Type Ψ Χ : val → iProp Σ.

    Record stack_mpmc_3۰name :=
      { stack_mpmc_3۰name۰stack : val
      ; stack_mpmc_3۰name۰channel : val
      ; stack_mpmc_3۰name۰model : gname
      }.
    Implicit Type γ : stack_mpmc_3۰name.

    Please derive EqDecision for stack_mpmc_3۰name.
    Please derive Countable for stack_mpmc_3۰name.

    #[local] Definition model₁' γ_model vs :=
      twins۰twin₁ γ_model (DfracOwn 1) vs.
    #[local] Definition model₁ γ vs :=
      model₁' γ.(stack_mpmc_3۰name۰model) vs.
    #[local] Definition model₂' γ_model vs :=
      twins۰twin₂ γ_model vs.
    #[local] Definition model₂ γ vs :=
      model₂' γ.(stack_mpmc_3۰name۰model) vs.

    #[local] Definition push۰pre γ ι v η : iProp Σ :=
      ∃ Ψ,
      saved_pred η Ψ ∗
      AU <{
        ∃∃ vs,
        model₁ γ vs
      }> @ ⊤ ∖ ↑ι, ∅ <{
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

    #[local] Definition pop۰pre γ ι μ : iProp Σ :=
      ∃ Χ,
      saved_pred μ Χ ∗
      AU <{
        ∃∃ vs,
        model₁ γ vs
      }> @ ⊤ ∖ ↑ι, ∅ <{
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
    Please Definition stack_mpmc_3۰inv t γ ι : iProp Σ :=
      t.[stack] ↦□ γ.(stack_mpmc_3۰name۰stack) ∗
      stack_mpmc_1۰inv γ.(stack_mpmc_3۰name۰stack) (ι.@"stack") ∗
      t.[channel] ↦□ γ.(stack_mpmc_3۰name۰channel) ∗
      channel_sync_2۰inv γ.(stack_mpmc_3۰name۰channel) (ι.@"channel") (push۰pre γ ι) (pop۰pre γ ι) push۰post pop۰post ∗
      inv (ι.@"inv") (inv۰inner γ).
    #[local] Instance : CustomIpat "inv" :=
      " ( #Ht۰stack
        & #Hstack۰inv
        & #Ht۰channel
        & #Hchannel۰inv
        & #Hinv
        )
      ".

    Please Definition stack_mpmc_3۰model :=
      model₁.
    #[local] Instance : CustomIpat "model" :=
      " Hmodel₁{_{}}
      ".

    #[global] Instance stack_mpmc_3۰modelｰtimeless γ vs :
      Timeless (stack_mpmc_3۰model γ vs).
    Proof.
      apply _.
    Qed.

    #[global] Instance stack_mpmc_3۰invｰpersistent t γ ι :
      Persistent (stack_mpmc_3۰inv t γ ι).
    Proof.
      apply _.
    Qed.

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
        t γ
      , RET #t;
        meta_token t ⊤ ∗
        stack_mpmc_3۰inv t γ ι ∗
        stack_mpmc_3۰model γ []
      }}}.
    Proof.
      iIntros "%Φ _ HΦ".

      wp۰rec.
      wp۰apply (channel_sync_2٠createｰspecｰinit with "[//]") as (channel) "Hchannel۰init". 1: done.
      wp۰apply (stack_mpmc_1٠createｰspec with "[//]") as (stack) "(#Hstack۰inv & Hstack۰model)".
      wp۰block t as "Hmeta" "#Ht۰stack #Ht۰channel".

      iMod modelｰalloc as "(%γ_model & Hmodel₁ & Hmodel₂)".

      pose γ :=
        {|stack_mpmc_3۰name۰stack := stack
        ; stack_mpmc_3۰name۰channel := channel
        ; stack_mpmc_3۰name۰model := γ_model
        |}.

      iMod (inv_alloc (ι.@"inv") _ (inv۰inner γ) with "[$]") as "#Hinv".

      iMod (channel_sync_2۰initｰtoｰinv (ι.@"channel") (push۰pre γ ι) (pop۰pre γ ι) push۰post pop۰post with "Hchannel۰init []") as "#Hchannel۰inv".
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

      iApply ("HΦ" $! t γ).
      iFrameSteps.
    Qed.

    Lemma stack_mpmc_3٠try_pushｰspec t γ ι v :
      <<<
        stack_mpmc_3۰inv t γ ι
      | ∀∀ vs,
        stack_mpmc_3۰model γ vs
      >>>
        stack_mpmc_3٠try_push #t v
        @ ↑ι
      <<<
        ∃∃ b,
        stack_mpmc_3۰model γ (if b then v :: vs else vs)
      | RET #b;
        True
      >>>.
    Proof.
      iIntros "%Φ (:inv) HΦ".

      wp۰rec credit:"H£". wp۰load.

      awp۰apply (stack_mpmc_1٠try_pushｰspec with "Hstack۰inv").
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

        wp۰load.

        iApply wpｰfupd.
        iMod (saved_predｰalloc Φ) as "(%η & #Hη)".
        wp۰apply (channel_sync_2٠sendｰspec η with "[$Hchannel۰inv $Hη $HΦ]") as ([]) "HΦ".

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

    #[local] Lemma stack_mpmc_3٠push₁ｰspec t γ ι v backoff :
      <<<
        stack_mpmc_3۰inv t γ ι ∗
        backoff۰model backoff
      | ∀∀ vs,
        stack_mpmc_3۰model γ vs
      >>>
        stack_mpmc_3٠push₁ #t v backoff
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

    Lemma stack_mpmc_3٠pushｰspec t γ ι v :
      <<<
        stack_mpmc_3۰inv t γ ι
      | ∀∀ vs,
        stack_mpmc_3۰model γ vs
      >>>
        stack_mpmc_3٠push #t v
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

    Lemma stack_mpmc_3٠try_popｰspec t γ ι :
      <<<
        stack_mpmc_3۰inv t γ ι
      | ∀∀ vs,
        stack_mpmc_3۰model γ vs
      >>>
        stack_mpmc_3٠try_pop #t
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

      wp۰rec credit:"H£". wp۰load.

      awp۰apply (stack_mpmc_1٠try_popｰspec with "Hstack۰inv").
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

        wp۰load.

        iApply wpｰfupd.
        iMod (saved_predｰalloc Φ) as "(%μ & #Hμ)".
        wp۰apply (channel_sync_2٠recvｰspec μ with "[$Hchannel۰inv $Hμ $HΦ]") as ([v |]) "HΦ".
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

    #[local] Lemma stack_mpmc_3٠pop₁ｰspec t γ ι backoff :
      <<<
        stack_mpmc_3۰inv t γ ι ∗
        backoff۰model backoff
      | ∀∀ vs,
        stack_mpmc_3۰model γ vs
      >>>
        stack_mpmc_3٠pop₁ #t backoff
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

    Lemma stack_mpmc_3٠popｰspec t γ ι :
      <<<
        stack_mpmc_3۰inv t γ ι
      | ∀∀ vs,
        stack_mpmc_3۰model γ vs
      >>>
        stack_mpmc_3٠pop #t
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

  Please opacify.
End base.

Require zoo_saturn.stack_mpmc_3__opaque.

Section stack_mpmc_3۰G.
  Context `{stack_mpmc_3۰G : StackMpmc3G Σ}.

  Implicit Type 𝑡 : location.
  Implicit Type t : val.
  Implicit Type Ψ Χ : val → iProp Σ.

  Please Definition stack_mpmc_3۰inv t ι : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.stack_mpmc_3۰inv 𝑡 γ ι.
  #[local] Instance : CustomIpat "inv" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hinv{_{}}
      )
    ".

  Please Definition stack_mpmc_3۰model t vs : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.stack_mpmc_3۰model γ vs.
  #[local] Instance : CustomIpat "model" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hmodel{_{}}
      )
    ".

  #[global] Instance stack_mpmc_3۰modelｰtimeless t vs :
    Timeless (stack_mpmc_3۰model t vs).
  Proof.
    apply _.
  Qed.

  #[global] Instance stack_mpmc_3۰invｰpersistent t ι :
    Persistent (stack_mpmc_3۰inv t ι).
  Proof.
    apply _.
  Qed.

  Lemma stack_mpmc_3۰modelｰexclusive t vs1 vs2 :
    stack_mpmc_3۰model t vs1 -∗
    stack_mpmc_3۰model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simp.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.stack_mpmc_3۰modelｰexclusive with "Hmodel_1 Hmodel_2").
  Qed.

  Lemma stack_mpmc_3٠createｰspec ι :
    {{{
      True
    }}}
      stack_mpmc_3٠create ()
    {{{
      t
    , RET t;
      stack_mpmc_3۰inv t ι ∗
      stack_mpmc_3۰model t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    iApply wpｰfupd.
    wp۰apply (base.stack_mpmc_3٠createｰspec with "[//]") as (𝑡 γ) "(Hmeta & Hinv & Hmodel)".
    iMod (metaｰset γ with "Hmeta"). 1: done.
    iSteps.
  Qed.

  Lemma stack_mpmc_3٠try_pushｰspec t ι v :
    <<<
      stack_mpmc_3۰inv t ι
    | ∀∀ vs,
      stack_mpmc_3۰model t vs
    >>>
      stack_mpmc_3٠try_push t v
      @ ↑ι
    <<<
      ∃∃ b,
      stack_mpmc_3۰model t (if b then v :: vs else vs)
    | RET #b;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    awp۰apply (base.stack_mpmc_3٠try_pushｰspec with "[$]").
    { iApply (aaccｰaupdｰcommit with "HΦ"). 1: done. iIntros "%vs (:model =1)". simp.
      iDestruct (metaｰagree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma stack_mpmc_3٠pushｰspec t ι v :
    <<<
      stack_mpmc_3۰inv t ι
    | ∀∀ vs,
      stack_mpmc_3۰model t vs
    >>>
      stack_mpmc_3٠push t v
      @ ↑ι
    <<<
      stack_mpmc_3۰model t (v :: vs)
    | RET ();
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    awp۰apply (base.stack_mpmc_3٠pushｰspec with "[$]").
    { iApply (aaccｰaupdｰcommit with "HΦ"). 1: done. iIntros "%vs (:model =1)". simp.
      iDestruct (metaｰagree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma stack_mpmc_3٠try_popｰspec t ι :
    <<<
      stack_mpmc_3۰inv t ι
    | ∀∀ vs,
      stack_mpmc_3۰model t vs
    >>>
      stack_mpmc_3٠try_pop t
      @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | Nothing =>
          ⌜vs = []⌝ ∗
          stack_mpmc_3۰model t []
      | Something v =>
          ∃ vs',
          ⌜vs = v :: vs'⌝ ∗
          stack_mpmc_3۰model t vs'
      | Anything =>
          stack_mpmc_3۰model t vs
      end
    | RET o;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    awp۰apply (base.stack_mpmc_3٠try_popｰspec with "[$]").
    { iApply (aaccｰaupdｰcommit with "HΦ"). 1: done. iIntros "%vs (:model =1)". simp.
      iDestruct (metaｰagree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_1". 1: iSteps. iIntros (o) "Hmodel !>".
      iExists o. iSplitL. 2: iSteps.
      destruct o; iDecompose "Hmodel"; iSteps.
    }
  Qed.

  Lemma stack_mpmc_3٠popｰspec t ι :
    <<<
      stack_mpmc_3۰inv t ι
    | ∀∀ vs,
      stack_mpmc_3۰model t vs
    >>>
      stack_mpmc_3٠pop t
      @ ↑ι
    <<<
      stack_mpmc_3۰model t (tail vs)
    | RET head vs;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    awp۰apply (base.stack_mpmc_3٠popｰspec with "[$]").
    { iApply (aaccｰaupdｰcommit with "HΦ"). 1: done. iIntros "%vs (:model =1)". simp.
      iDestruct (metaｰagree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.
End stack_mpmc_3۰G.

Please opacify.
