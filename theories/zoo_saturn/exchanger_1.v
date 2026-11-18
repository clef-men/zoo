Require Import zoo.prelude.
Require Import zoo.iris.base_logic.lib.twins.
Require Import zoo.base.
Require Import zoo_std.option.
Require Export zoo_saturn.exchanger_1__code.
Require Import zoo_saturn.exchanger_1__types.
Require Import zoo.options.

Implicit Type v 𝑣 : val.
Implicit Type o : option val.

Zoo name :=
  { self : location
  ; token : gname
  }.

Zoo global X :=
  { token : twins (leibnizO (val * X))
  }.

Section exchanger_1۰G.
  Context `{exchanger_1۰G : Exchanger1G Σ X}.
  Context `{!Inhabited X}.

  Implicit Type x 𝑥 : X.
  Implicit Type Ψ : val → X → iProp Σ.
  Implicit Type Χ : val → X → val → X → iProp Σ.

  Definition exchanger_1۰valid ι Ψ Χ : iProp Σ :=
    ▷ □
      ∀ v1 x1 v2 x2,
      Ψ v1 x1 -∗
      Ψ v2 x2 ={⊤ ∖ ↑ι}=∗
        Χ v1 x1 v2 x2 ∗
        Χ v2 x2 v1 x1.

  Variant state :=
    | Null
    | Offer v x
    | Accept v x 𝑣 𝑥.
  Implicit Type state : state.

  #[local] Please derive Inhabited for state.

  Coercion state۰to_val state : val :=
    match state with
    | Null =>
        §Null
    | Offer v _ =>
        ‘Offer[ v ]
    | Accept _ _ 𝑣 _ =>
        ‘Accept[ 𝑣 ]
    end.

  #[local] Definition token₁' γ_token v x :=
    twins۰twin₁ γ_token Own (v, x).
  #[local] Definition token₁ γ v x :=
    token₁' γ.(exchanger_1۰name۰token) v x.
  #[local] Definition token₂' γ_token v x :=
    twins۰twin₂ γ_token (v, x).
  #[local] Definition token₂ γ v x :=
    token₂' γ.(exchanger_1۰name۰token) v x.
  #[local] Definition token γ : iProp Σ :=
    ∃ v x,
    token₁ γ v x ∗
    token₂ γ v x.
  #[local] Instance : CustomIpat "token" :=
    " ( %{v}
      & %{x}
      & Htoken₁
      & Htoken₂{{!}_}
      )
    ".

  Please Definition exchanger_1۰init γ : iProp Σ :=
    γ.(exchanger_1۰name۰self) ↦ᵣ §Null ∗
    token γ.
  #[local] Instance : CustomIpat "init" :=
    " ( Ht
      & Htoken
      )
    ".

  #[local] Definition inv۰state۰null γ :=
    token γ.
  #[local] Instance : CustomIpat "inv۰state۰null" :=
    " (:token)
    ".
  #[local] Definition inv۰state۰offer γ Ψ v x : iProp Σ :=
    token₁ γ v x ∗
    Ψ v x.
  #[local] Instance : CustomIpat "inv۰state۰offer" :=
    " ( Htoken₁
      & HΨ{:{v}}
      )
    ".
  #[local] Definition inv۰state۰accept γ Χ v x 𝑣 𝑥 : iProp Σ :=
    token₁ γ v x ∗
    Χ v x 𝑣 𝑥.
  #[local] Instance : CustomIpat "inv۰state۰accept" :=
    " ( Htoken₁
      & HΧ
      )
    ".
  #[local] Definition inv۰state γ Ψ Χ state :=
    match state with
    | Null =>
        inv۰state۰null γ
    | Offer v x =>
        inv۰state۰offer γ Ψ v x
    | Accept v x 𝑣 𝑥 =>
        inv۰state۰accept γ Χ v x 𝑣 𝑥
    end.

  #[local] Definition inv۰inner γ Ψ Χ : iProp Σ :=
    ∃ state,
    γ.(exchanger_1۰name۰self) ↦ᵣ state ∗
    inv۰state γ Ψ Χ state.
  #[local] Instance : CustomIpat "inv۰inner" :=
    " ( %state
      & Ht
      & Hstate
      )
    ".
  Please Definition exchanger_1۰inv γ ι Ψ Χ : iProp Σ :=
    exchanger_1۰valid ι Ψ Χ ∗
    inv ι (inv۰inner γ Ψ Χ).
  #[local] Instance : CustomIpat "inv" :=
    " ( #Hvalid
      & #Hinv
      )
    ".

  #[global] Instance exchanger_1۰invｰcontractive γ ι n :
    Proper (
      (pointwise_relation _ $ pointwise_relation _ $ dist_later n) ==>
      (pointwise_relation _ $ pointwise_relation _ $ pointwise_relation _ $ pointwise_relation _ $ dist_later n) ==>
      (≡{n}≡)
    ) (exchanger_1۰inv γ ι).
  Proof.
    rewrite /exchanger_1۰inv /exchanger_1۰valid /inv۰inner /inv۰state /inv۰state۰offer /inv۰state۰accept.
    solve_contractive.
  Qed.
  #[global] Instance exchanger_1۰invｰproper γ ι :
    Proper (
      (pointwise_relation _ $ pointwise_relation _ (≡)) ==>
      (pointwise_relation _ $ pointwise_relation _ $ pointwise_relation _ $ pointwise_relation _ (≡)) ==>
      (≡)
    ) (exchanger_1۰inv γ ι).
  Proof.
    rewrite /exchanger_1۰inv /exchanger_1۰valid /inv۰inner /inv۰state /inv۰state۰offer /inv۰state۰accept.
    solve_proper.
  Qed.

  Zoo derive Timeless for exchanger_1۰init.

  Zoo derive Persistent for exchanger_1۰inv.

  #[local] Lemma tokenｰalloc :
    ⊢ |==>
      ∃ γ_token,
      token₁' γ_token inhabitant inhabitant ∗
      token₂' γ_token inhabitant inhabitant.
  Proof.
    apply twinsｰalloc'.
  Qed.
  #[local] Lemma token₁ｰexclusive γ v1 x1 v2 x2 :
    token₂ γ v1 x1 -∗
    token₂ γ v2 x2 -∗
    False.
  Proof.
    apply twins۰twin₂ｰexclusive.
  Qed.
  #[local] Lemma tokenｰagree γ v1 x1 v2 x2 :
    token₁ γ v1 x1 -∗
    token₂ γ v2 x2 -∗
      ⌜v1 = v2⌝ ∧
      ⌜x1 = x2⌝.
  Proof.
    iIntros "Htwin₁ Htwin₂".
    iDestruct (twinsｰagreeｰL with "Htwin₁ Htwin₂") as %[= -> ->] => //.
  Qed.
  #[local] Lemma tokenｰupdate {γ v1 x1 v2 x2} v x :
    token₁ γ v1 x1 -∗
    token₂ γ v2 x2 ==∗
      token₁ γ v x ∗
      token₂ γ v x.
  Proof.
    apply twinsｰupdate.
  Qed.

  Lemma exchanger_1۰initｰexclusive γ :
    exchanger_1۰init γ -∗
    exchanger_1۰init γ -∗
    False.
  Proof.
    iSteps.
  Qed.
  Lemma exchanger_1۰initｰtoｰinv {γ} ι Ψ Χ E :
    exchanger_1۰init γ -∗
    exchanger_1۰valid ι Ψ Χ ={E}=∗
    exchanger_1۰inv γ ι Ψ Χ.
  Proof.
    iIntros "(:init) Hvalid".
    iFrame.
    iApply inv_alloc.
    iExists Null. iFrame.
  Qed.

  Lemma exchanger_1٠createｰspecｰinit :
    {{{
      True
    }}}
      exchanger_1٠create ()
    {{{
      γ
    , RET γ;
      exchanger_1۰init γ
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp۰rec.
    wp۰ref t as "Ht".

    iMod tokenｰalloc as "(%γ۰token & Htoken₁ & Htoken₂)".

    pose γ :=
      {|exchanger_1۰name۰self := t
      ; exchanger_1۰name۰token := γ۰token
      |}.

    iApply ("HΦ" $! γ).
    iFrameSteps.
  Qed.
  Lemma exchanger_1٠createｰspec ι Ψ Χ :
    {{{
      exchanger_1۰valid ι Ψ Χ
    }}}
      exchanger_1٠create ()
    {{{
      γ
    , RET γ;
      exchanger_1۰inv γ ι Ψ Χ
    }}}.
  Proof.
    iIntros "%Φ Hvalid HΦ".

    iApply wpｰfupd.
    wp۰apply (exchanger_1٠createｰspecｰinit with "[//]") as (γ) "Hinit".
    iMod (exchanger_1۰initｰtoｰinv with "Hinit Hvalid") as "Hinv".
    iSteps.
  Qed.

  #[local] Lemma exchanger_1٠exchangeｰspecｰaux γ ι Ψ Χ v x :
    ⊢ {{{
        exchanger_1۰inv γ ι Ψ Χ ∗
        Ψ v x
      }}}
        exchanger_1٠exchange γ v
      {{{
        o
      , RET o;
        if o is Some 𝑣 then
          ∃ 𝑥,
          Χ v x 𝑣 𝑥
        else
          Ψ v x
      }}}
    ∧ {{{
        exchanger_1۰inv γ ι Ψ Χ ∗
        Ψ v x
      }}}
        exchanger_1٠exchange_aux γ v
      {{{
        o
      , RET o;
        if o is Some 𝑣 then
          ∃ 𝑥,
          Χ v x 𝑣 𝑥
        else
          Ψ v x
      }}}.
  Proof.
    iLöb as "HLöb".
    iDestruct "HLöb" as "(IHexchange & IHexchange_aux)".
    iSplit.

    { iClear "IHexchange".
      iIntros "!> %Φ ((:inv) & HΨ:v) HΦ".

      wp۰rec. wp۰pures.

      wp۰bind (!_)%E.
      iInv "Hinv" as "(:inv۰inner)".
      wp۰load.
      iSplitR "HΨ:v HΦ". { iFrameSteps. }
      iModIntro.

      destruct state as [| 𝑣 𝑥 | v' x' 𝑣 𝑥]; wp۰pures.

      - wp۰apply ("IHexchange_aux" with "[$] HΦ").

      - wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
        iInv "Hinv" as "(:inv۰inner)".
        wp۰cas.

        + iSplitR "HΨ:v HΦ". { iFrameSteps. }
          iModIntro.

          wp۰pures.

          iApply ("HΦ" $! None with "HΨ:v").

        + destruct state as [| 𝑣_ 𝑥_ |]; zoo۰simp.
          iDestruct "Hstate" as "(:inv۰state۰offer v=𝑣)".
          iMod ("Hvalid" with "HΨ:v HΨ:𝑣") as "(HΧ:v & HΧ:𝑣)".
          iSplitR "HΧ:v HΦ". { iExists (Accept _ _ v x). iFrameSteps. }
          iModIntro.

          wp۰pures.

          iApply ("HΦ" $! (Some 𝑣) with "[$HΧ:v]").

      - iApply ("HΦ" $! None with "HΨ:v").
    }

    { iClear "IHexchange_aux".
      iIntros "!> %Φ ((:inv) & HΨ:v) HΦ".

      wp۰rec. wp۰pures.

      wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
      iInv "Hinv" as "(:inv۰inner)".
      wp۰cas.

      - iSplitR "HΨ:v HΦ". { iFrameSteps. }
        iModIntro.

        wp۰apply+ ("IHexchange" with "[$] HΦ").

      - destruct state; zoo۰simp.
        iDestruct "Hstate" as "(:inv۰state۰null v=v' x=x')".
        iMod (tokenｰupdate with "Htoken₁ Htoken₂") as "(Htoken₁ & Htoken₂)".
        iSplitR "Htoken₂ HΦ". { iExists (Offer v x). iFrameSteps. }
        iIntros "!> {% v' x'}".

        iStep 11.

        wp۰bind (𝘅𝗰𝗵𝗴 _ _)%E.
        iInv "Hinv" as "(:inv۰inner)".
        wp۰xchg.
        destruct state as [| v_ a_ | v_ x_ 𝑣 𝑥]; wp۰pures.

        + iDestruct "Hstate" as "(:inv۰state۰null != v=v' x=x')".
          iDestruct (token₁ｰexclusive with "Htoken₂ Htoken₂_") as %[].

        + iDestruct "Hstate" as "(:inv۰state۰offer)".
          iDestruct (tokenｰagree with "Htoken₁ Htoken₂") as %(-> & ->).
          iSplitR "HΨ HΦ". { iExists Null. iFrameSteps. }
          iModIntro.

          wp۰pures.

          iApply ("HΦ" $! None with "HΨ").

        + iDestruct "Hstate" as "(:inv۰state۰accept)".
          iDestruct (tokenｰagree with "Htoken₁ Htoken₂") as %(-> & ->).
          iSplitR "HΧ HΦ". { iExists Null. iFrameSteps. }
          iModIntro.

          wp۰pures.

          iApply ("HΦ" $! (Some 𝑣) with "[$HΧ]").
    }
  Qed.
  Lemma exchanger_1٠exchangeｰspec {γ ι Ψ Χ v} x :
    {{{
      exchanger_1۰inv γ ι Ψ Χ ∗
      Ψ v x
    }}}
      exchanger_1٠exchange γ v
    {{{
      o
    , RET o;
      if o is Some 𝑣 then
        ∃ 𝑥,
        Χ v x 𝑣 𝑥
      else
        Ψ v x
    }}}.
  Proof.
    iPoseProof exchanger_1٠exchangeｰspecｰaux as "(H & _)".
    iApply "H".
  Qed.
End exchanger_1۰G.

Require zoo_saturn.exchanger_1__opaque.

Please opacify.
