Require Import zoo.prelude.
Require Import zoo.iris.base_logic.lib.twins.
Require Import zoo.base.
Require Import zoo_std.option.
Require Export zoo_saturn.channel_sync_1__code.
Require Import zoo_saturn.channel_sync_1__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type v 𝑣 : val.
Implicit Type o : option val.

Module internal.
  Variant offer {X Y} :=
    | Sender v (x : X)
    | Receiver (y : Y).
  #[global] Arguments offer : clear implicits.

  #[global] Instance offerｰinhabited {X Y} `{!Inhabited X} : Inhabited (offer X Y) :=
    populate $ Sender inhabitant inhabitant.
End internal.

Zoo global X Y :=
  { token : twins (leibnizO (internal.offer X Y))
  }.

Section channel_sync_1۰G.
  Context `{channel_sync_1۰G : ChannelSync1G Σ X Y}.

  Implicit Type x 𝑥 : X.
  Implicit Type y 𝑦 : Y.
  Implicit Type Ψₛ : val → X → iProp Σ.
  Implicit Type Ψᵣ : Y → iProp Σ.
  Implicit Type Χₛ Χᵣ : val → X → Y → iProp Σ.

  Definition channel_sync_1۰valid ι Ψₛ Ψᵣ Χₛ Χᵣ : iProp Σ :=
    ▷ □
      ∀ v x y,
      Ψₛ v x -∗
      Ψᵣ y ={⊤ ∖ ↑ι}=∗
        Χₛ v x y ∗
        Χᵣ v x y.
End channel_sync_1۰G.

Module base.
  Section channel_sync_1۰G.
    Context `{channel_sync_1۰G : ChannelSync1G Σ}.
    Context `{!Inhabited X}.
    Context `{!Inhabited Y}.

    Import internal.

    Implicit Type t : location.
    Implicit Type x 𝑥 : X.
    Implicit Type y 𝑦 : Y.
    Implicit Type offer : offer X Y.
    Implicit Type Ψₛ : val → X → iProp Σ.
    Implicit Type Ψᵣ : Y → iProp Σ.
    Implicit Type Χₛ Χᵣ : val → X → Y → iProp Σ.

    Variant state :=
      | Null
      | Sender_offer v x
      | Sender_accept v x y
      | Receiver_offer y
      | Receiver_accept v x y.
    Implicit Type state : state.

    #[local] Please derive Inhabited for state.

    Coercion state۰to_val state : val :=
      match state with
      | Null =>
          §Null
      | Sender_offer v _ =>
          ‘Sender_offer[ v ]
      | Sender_accept v _ _ =>
          ‘Sender_accept[ v ]
      | Receiver_offer _ =>
          §Receiver_offer
      | Receiver_accept _ _ _ =>
          §Receiver_accept
      end.

    Record channel_sync_1۰name :=
      { channel_sync_1۰name۰token : gname
      }.
    Implicit Type γ : channel_sync_1۰name.

    Please derive EqDecision for channel_sync_1۰name.
    Please derive Countable for channel_sync_1۰name.

    #[local] Definition token₁' γ_token offer :=
      twins۰twin₁ γ_token Own offer.
    #[local] Definition token₁ γ offer :=
      token₁' γ.(channel_sync_1۰name۰token) offer.
    #[local] Definition token₂' γ_token offer :=
      twins۰twin₂ γ_token offer.
    #[local] Definition token₂ γ offer :=
      token₂' γ.(channel_sync_1۰name۰token) offer.
    #[local] Definition token γ : iProp Σ :=
      ∃ offer,
      token₁ γ offer ∗
      token₂ γ offer.
    #[local] Instance : CustomIpat "token" :=
      " ( %{offer}
        & Htoken₁
        & Htoken₂{{!}_}
        )
      ".

    #[local] Definition inv۰state۰null γ :=
      token γ.
    #[local] Instance : CustomIpat "inv۰state۰null" :=
      " (:token)
      ".
    #[local] Definition inv۰state۰sender_offer γ Ψₛ v x : iProp Σ :=
      token₁ γ (Sender v x) ∗
      Ψₛ v x.
    #[local] Instance : CustomIpat "inv۰state۰sender_offer" :=
      " ( Htoken₁
        & HΨₛ
        )
      ".
    #[local] Definition inv۰state۰sender_accept γ Χᵣ v x y : iProp Σ :=
      token₁ γ (Receiver y) ∗
      Χᵣ v x y.
    #[local] Instance : CustomIpat "inv۰state۰sender_accept" :=
      " ( Htoken₁
        & HΧᵣ
        )
      ".
    #[local] Definition inv۰state۰receiver_offer γ Ψᵣ y : iProp Σ :=
      token₁ γ (Receiver y) ∗
      Ψᵣ y.
    #[local] Instance : CustomIpat "inv۰state۰receiver_offer" :=
      " ( Htoken₁
        & HΨᵣ
        )
      ".
    #[local] Definition inv۰state۰receiver_accept γ Χₛ v x y : iProp Σ :=
      token₁ γ (Sender v x) ∗
      Χₛ v x y.
    #[local] Instance : CustomIpat "inv۰state۰receiver_accept" :=
      " ( Htoken₁
        & HΧₛ
        )
      ".
    #[local] Definition inv۰state γ Ψₛ Ψᵣ Χₛ Χᵣ state :=
      match state with
      | Null =>
          inv۰state۰null γ
      | Sender_offer v x =>
          inv۰state۰sender_offer γ Ψₛ v x
      | Sender_accept v x y =>
          inv۰state۰sender_accept γ Χᵣ v x y
      | Receiver_offer y =>
          inv۰state۰receiver_offer γ Ψᵣ y
      | Receiver_accept v x y =>
          inv۰state۰receiver_accept γ Χₛ v x y
      end.

    #[local] Definition inv۰inner t ι Ψₛ Ψᵣ Χₛ Χᵣ : iProp Σ :=
      ∃ state,
      t ↦ᵣ state ∗
      inv۰state ι Ψₛ Ψᵣ Χₛ Χᵣ state.
    #[local] Instance : CustomIpat "inv۰inner" :=
      " ( %state
        & Ht
        & Hstate
        )
      ".
    Please Definition channel_sync_1۰inv t γ ι Ψₛ Ψᵣ Χₛ Χᵣ : iProp Σ :=
      channel_sync_1۰valid ι Ψₛ Ψᵣ Χₛ Χᵣ ∗
      inv ι (inv۰inner t γ Ψₛ Ψᵣ Χₛ Χᵣ).
    #[local] Instance : CustomIpat "inv" :=
      " ( #Hvalid
        & #Hinv
        )
      ".

    #[global] Instance channel_sync_1۰invｰcontractive t γ ι n :
      Proper (
        (pointwise_relation _ $ pointwise_relation _ $ dist_later n) ==>
        (pointwise_relation _ $ dist_later n) ==>
        (pointwise_relation _ $ pointwise_relation _ $ pointwise_relation _ $ dist_later n) ==>
        (pointwise_relation _ $ pointwise_relation _ $ pointwise_relation _ $ dist_later n) ==>
        (≡{n}≡)
      ) (channel_sync_1۰inv t γ ι).
    Proof.
      rewrite /channel_sync_1۰inv /channel_sync_1۰valid /inv۰inner /inv۰state /inv۰state۰sender_offer /inv۰state۰sender_accept /inv۰state۰receiver_offer /inv۰state۰receiver_accept.
      intros Ψₛ1 Ψₛ2 HΨₛ Ψᵣ1 Ψᵣ2 HΨᵣ Χₛ1 Χₛ2 HΧₛ Χᵣ1 Χᵣ2 HΧᵣ.
      repeat (apply HΨₛ || apply HΨᵣ || apply HΧₛ || apply HΧᵣ || f_contractive || f_equiv || done).
    Qed.
    #[global] Instance channel_sync_1۰invｰproper t γ ι :
      Proper (
        (pointwise_relation _ $ pointwise_relation _ (≡)) ==>
        pointwise_relation _ (≡) ==>
        (pointwise_relation _ $ pointwise_relation _ $ pointwise_relation _ (≡)) ==>
        (pointwise_relation _ $ pointwise_relation _ $ pointwise_relation _ (≡)) ==>
        (≡)
      ) (channel_sync_1۰inv t γ ι).
    Proof.
      rewrite /channel_sync_1۰inv /channel_sync_1۰valid /inv۰inner /inv۰state /inv۰state۰sender_offer /inv۰state۰sender_accept /inv۰state۰receiver_offer /inv۰state۰receiver_accept.
      intros Ψₛ1 Ψₛ2 HΨₛ Ψᵣ1 Ψᵣ2 HΨᵣ Χₛ1 Χₛ2 HΧₛ Χᵣ1 Χᵣ2 HΧᵣ.
      repeat (apply HΨₛ || apply HΨᵣ || apply HΧₛ || apply HΧᵣ || f_equiv || done).
    Qed.

    #[global] Instance channel_sync_1۰invｰpersistent t γ ι Ψₛ Ψᵣ Χₛ Χᵣ :
      Persistent (channel_sync_1۰inv t γ ι Ψₛ Ψᵣ Χₛ Χᵣ).
    Proof.
      apply _.
    Qed.

    #[local] Lemma tokenｰalloc :
      ⊢ |==>
        ∃ γ_token,
        token₁' γ_token inhabitant ∗
        token₂' γ_token inhabitant.
    Proof.
      apply twinsｰalloc'.
    Qed.
    #[local] Lemma token₁ｰexclusive γ offer1 offer2 :
      token₂ γ offer1 -∗
      token₂ γ offer2 -∗
      False.
    Proof.
      apply twins۰twin₂ｰexclusive.
    Qed.
    #[local] Lemma tokenｰagree γ offer1 offer2 :
      token₁ γ offer1 -∗
      token₂ γ offer2 -∗
      ⌜offer1 = offer2⌝.
    Proof.
      apply: twinsｰagreeｰL.
    Qed.
    #[local] Lemma tokenｰupdate {γ offer1 offer2} offer :
      token₁ γ offer1 -∗
      token₂ γ offer2 ==∗
        token₁ γ offer ∗
        token₂ γ offer.
    Proof.
      apply twinsｰupdate.
    Qed.

    Lemma channel_sync_1٠createｰspec ι Ψₛ Ψᵣ Χₛ Χᵣ :
      {{{
        channel_sync_1۰valid ι Ψₛ Ψᵣ Χₛ Χᵣ
      }}}
        channel_sync_1٠create ()
      {{{
        t γ
      , RET #t;
        meta_token t ⊤ ∗
        channel_sync_1۰inv t γ ι Ψₛ Ψᵣ Χₛ Χᵣ
      }}}.
    Proof.
      iIntros "%Φ Hvalid HΦ".

      wp۰rec.
      wp۰ref t as "Hmeta" "Ht".

      iMod tokenｰalloc as "(%γ۰token & Htoken₁ & Htoken₂)".

      pose γ :=
        {|channel_sync_1۰name۰token := γ۰token
        |}.

      iApply ("HΦ" $! t γ).
      iFrameSteps. iExists Null. iSteps.
    Qed.

    #[local] Lemma channel_sync_1٠sendｰspecｰaux t γ ι Ψₛ Ψᵣ Χₛ Χᵣ v x :
      ⊢ {{{
          channel_sync_1۰inv t γ ι Ψₛ Ψᵣ Χₛ Χᵣ ∗
          Ψₛ v x
        }}}
          channel_sync_1٠send #t v
        {{{
          b
        , RET #b;
          if b then
            ∃ y,
            Χₛ v x y
          else
            Ψₛ v x
        }}}
      ∧ {{{
          channel_sync_1۰inv t γ ι Ψₛ Ψᵣ Χₛ Χᵣ ∗
          Ψₛ v x
        }}}
          channel_sync_1٠send_aux #t v
        {{{
          b
        , RET #b;
          if b then
            ∃ y,
            Χₛ v x y
          else
            Ψₛ v x
        }}}.
    Proof.
      iLöb as "HLöb".
      iDestruct "HLöb" as "(IHsend & IHsend_aux)".
      iSplit.

      { iClear "IHsend".
        iIntros "!> %Φ ((:inv) & HΨₛ) HΦ".

        wp۰rec. wp۰pures.

        wp۰bind (!_)%E.
        iInv "Hinv" as "(:inv۰inner)".
        wp۰load.
        iSplitR "HΨₛ HΦ". { iFrameSteps. }
        iModIntro.

        destruct state as [| v' x' | v' x' y | y | v' x' y]; wp۰pures.

        - wp۰apply ("IHsend_aux" with "[$] HΦ").

        - iSteps.

        - iSteps.

        - wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
          iInv "Hinv" as "(:inv۰inner)".
          wp۰cas.

          + iSplitR "HΨₛ HΦ". { iFrameSteps. }
            iSteps.

          + destruct state; zoo۰simp.
            iDestruct "Hstate" as "(:inv۰state۰receiver_offer)".
            iMod ("Hvalid" with "HΨₛ HΨᵣ") as "(HΧₛ & HΧᵣ)".
            iSplitR "HΧₛ HΦ". { iExists (Sender_accept v x _). iFrameSteps. }
            iSteps.

        - iSteps.
      }

      { iClear "IHsend_aux".
        iIntros "!> %Φ ((:inv) & HΨ) HΦ".

        wp۰rec. wp۰pures.

        wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
        iInv "Hinv" as "(:inv۰inner)".
        wp۰cas.

        - iSplitR "HΨ HΦ". { iFrameSteps. }
          iModIntro.

          wp۰apply+ ("IHsend" with "[$] HΦ").

        - destruct state; zoo۰simp.
          iDestruct "Hstate" as "(:inv۰state۰null)".
          iMod (tokenｰupdate with "Htoken₁ Htoken₂") as "(Htoken₁ & Htoken₂)".
          iSplitR "Htoken₂ HΦ". { iExists (Sender_offer v x). iFrameSteps. }
          iIntros "!> {% offer}".

          iStep 11.

          wp۰bind (𝘅𝗰𝗵𝗴 _ _)%E.
          iInv "Hinv" as "(:inv۰inner)".
          wp۰xchg.
          destruct state as [| v_ x_ | v' x' y | y | v_ x_ y]; wp۰pures.

          + iDestruct "Hstate" as "(:inv۰state۰null !=)".
            iDestruct (token₁ｰexclusive with "Htoken₂ Htoken₂_") as %[].

          + iDestruct "Hstate" as "(:inv۰state۰sender_offer)".
            iDestruct (tokenｰagree with "Htoken₁ Htoken₂") as %[= -> ->].
            iSplitR "HΨₛ HΦ". { iExists Null. iFrameSteps. }
            iSteps.

          + iDestruct "Hstate" as "(:inv۰state۰sender_accept)".
            iDestruct (tokenｰagree with "Htoken₁ Htoken₂") as %[=].

          + iDestruct "Hstate" as "(:inv۰state۰receiver_offer)".
            iDestruct (tokenｰagree with "Htoken₁ Htoken₂") as %[=].

          + iDestruct "Hstate" as "(:inv۰state۰receiver_accept v=v_)".
            iDestruct (tokenｰagree with "Htoken₁ Htoken₂") as %[= -> ->].
            iSplitR "HΧₛ HΦ". { iExists Null. iFrameSteps. }
            iSteps.
      }
    Qed.
    Lemma channel_sync_1٠sendｰspec {t γ ι Ψₛ Ψᵣ Χₛ Χᵣ v} x :
      {{{
        channel_sync_1۰inv t γ ι Ψₛ Ψᵣ Χₛ Χᵣ ∗
        Ψₛ v x
      }}}
        channel_sync_1٠send #t v
      {{{
        b
      , RET #b;
        if b then
          ∃ y,
          Χₛ v x y
        else
          Ψₛ v x
      }}}.
    Proof.
      iPoseProof channel_sync_1٠sendｰspecｰaux as "(H & _)".
      iApply "H".
    Qed.

    #[local] Lemma channel_sync_1٠recvｰspecｰaux t γ ι Ψₛ Ψᵣ Χₛ Χᵣ y :
      ⊢ {{{
          channel_sync_1۰inv t γ ι Ψₛ Ψᵣ Χₛ Χᵣ ∗
          Ψᵣ y
        }}}
          channel_sync_1٠recv #t
        {{{
          o
        , RET o;
          if o is Some v then
            ∃ x,
            Χᵣ v x y
          else
            Ψᵣ y
        }}}
      ∧ {{{
          channel_sync_1۰inv t γ ι Ψₛ Ψᵣ Χₛ Χᵣ ∗
          Ψᵣ y
        }}}
          channel_sync_1٠recv_aux #t
        {{{
          o
        , RET o;
          if o is Some v then
            ∃ x,
            Χᵣ v x y
          else
            Ψᵣ y
        }}}.
    Proof.
      iLöb as "HLöb".
      iDestruct "HLöb" as "(IHrecv & IHrecv_aux)".
      iSplit.

      { iClear "IHrecv".
        iIntros "!> %Φ ((:inv) & HΨᵣ) HΦ".

        wp۰rec. wp۰pures.

        wp۰bind (!_)%E.
        iInv "Hinv" as "(:inv۰inner)".
        wp۰load.
        iSplitR "HΨᵣ HΦ". { iFrameSteps. }
        iModIntro.

        destruct state as [| v x | v x y' | y' | x v y']; wp۰pures.

        - wp۰apply ("IHrecv_aux" with "[$] HΦ").

        - wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
          iInv "Hinv" as "(:inv۰inner)".
          wp۰cas.

          + iSplitR "HΨᵣ HΦ". { iFrameSteps. }
            iModIntro.

            wp۰pures.

            iApply ("HΦ" $! None with "HΨᵣ").

          + destruct state; zoo۰simp.
            iDestruct "Hstate" as "(:inv۰state۰sender_offer)".
            iMod ("Hvalid" with "HΨₛ HΨᵣ") as "(HΧₛ & HΧᵣ)".
            iSplitR "HΧᵣ HΦ". { iExists (Receiver_accept v _ y). iFrameSteps. }
            iModIntro.

            wp۰pures.

            iApply ("HΦ" $! (Some v) with "[$HΧᵣ]").

        - iApply ("HΦ" $! None with "HΨᵣ").

        - iApply ("HΦ" $! None with "HΨᵣ").

        - iApply ("HΦ" $! None with "HΨᵣ").
      }

      { iClear "IHrecv_aux".
        iIntros "!> %Φ ((:inv) & HΨᵣ) HΦ".

        wp۰rec. wp۰pures.

        wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
        iInv "Hinv" as "(:inv۰inner)".
        wp۰cas.

        - iSplitR "HΨᵣ HΦ". { iFrameSteps. }
          iModIntro.

          wp۰apply+ ("IHrecv" with "[$] HΦ").

        - destruct state; zoo۰simp.
          iDestruct "Hstate" as "(:inv۰state۰null)".
          iMod (tokenｰupdate with "Htoken₁ Htoken₂") as "(Htoken₁ & Htoken₂)".
          iSplitR "Htoken₂ HΦ". { iExists (Receiver_offer y). iFrameSteps. }
          iIntros "!> {% offer}".

          iStep 11.

          wp۰bind (𝘅𝗰𝗵𝗴 _ _)%E.
          iInv "Hinv" as "(:inv۰inner)".
          wp۰xchg.
          destruct state as [| v x | v x y_ | y_ | v x y']; wp۰pures.

          + iDestruct "Hstate" as "(:inv۰state۰null !=)".
            iDestruct (token₁ｰexclusive with "Htoken₂ Htoken₂_") as %[].

          + iDestruct "Hstate" as "(:inv۰state۰sender_offer)".
            iDestruct (tokenｰagree with "Htoken₁ Htoken₂") as %[=].

          + iDestruct "Hstate" as "(:inv۰state۰sender_accept)".
            iDestruct (tokenｰagree with "Htoken₁ Htoken₂") as %[= ->].
            iSplitR "HΧᵣ HΦ". { iExists Null. iFrameSteps. }
            iModIntro.

            wp۰pures.

            iApply ("HΦ" $! (Some v) with "[$HΧᵣ]").

          + iDestruct "Hstate" as "(:inv۰state۰receiver_offer)".
            iDestruct (tokenｰagree with "Htoken₁ Htoken₂") as %[= ->].
            iSplitR "HΨᵣ HΦ". { iExists Null. iFrameSteps. }
            iModIntro.

            wp۰pures.

            iApply ("HΦ" $! None with "HΨᵣ").

          + iDestruct "Hstate" as "(:inv۰state۰receiver_accept)".
            iDestruct (tokenｰagree with "Htoken₁ Htoken₂") as %[=].
      }
    Qed.
    Lemma channel_sync_1٠recvｰspec {t γ ι Ψₛ Ψᵣ Χₛ Χᵣ} y :
      {{{
        channel_sync_1۰inv t γ ι Ψₛ Ψᵣ Χₛ Χᵣ ∗
        Ψᵣ y
      }}}
        channel_sync_1٠recv #t
      {{{
        o
      , RET o;
        if o is Some v then
          ∃ x,
          Χᵣ v x y
        else
          Ψᵣ y
      }}}.
    Proof.
      iPoseProof channel_sync_1٠recvｰspecｰaux as "(H & _)".
      iApply "H".
    Qed.
  End channel_sync_1۰G.

  Please opacify.
End base.

Require zoo_saturn.channel_sync_1__opaque.

Section channel_sync_1۰G.
  Context `{channel_sync_1۰G : ChannelSync1G Σ}.
  Context `{!Inhabited X}.
  Context `{!Inhabited Y}.

  Implicit Type 𝑡 : location.
  Implicit Type t : val.
  Implicit Type γ : base.channel_sync_1۰name.
  Implicit Type x 𝑥 : X.
  Implicit Type y 𝑦 : Y.
  Implicit Type Ψₛ : val → X → iProp Σ.
  Implicit Type Ψᵣ : Y → iProp Σ.
  Implicit Type Χₛ Χᵣ : val → X → Y → iProp Σ.

  Please Definition channel_sync_1۰inv t ι Ψₛ Ψᵣ Χₛ Χᵣ : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.channel_sync_1۰inv 𝑡 γ ι Ψₛ Ψᵣ Χₛ Χᵣ.
  #[local] Instance : CustomIpat "inv" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hinv{_{}}
      )
    ".

  #[global] Instance channel_sync_1۰invｰcontractive t ι n :
    Proper (
      (pointwise_relation _ $ pointwise_relation _ $ dist_later n) ==>
      (pointwise_relation _ $ dist_later n) ==>
      (pointwise_relation _ $ pointwise_relation _ $ pointwise_relation _ $ dist_later n) ==>
      (pointwise_relation _ $ pointwise_relation _ $ pointwise_relation _ $ dist_later n) ==>
      (≡{n}≡)
    ) (channel_sync_1۰inv t ι).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance channel_sync_1۰invｰproper t ι :
    Proper (
      (pointwise_relation _ $ pointwise_relation _ (≡)) ==>
      pointwise_relation _ (≡) ==>
      (pointwise_relation _ $ pointwise_relation _ $ pointwise_relation _ (≡)) ==>
      (pointwise_relation _ $ pointwise_relation _ $ pointwise_relation _ (≡)) ==>
      (≡)
    ) (channel_sync_1۰inv t ι).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance channel_sync_1۰invｰpersistent t ι Ψₛ Ψᵣ Χₛ Χᵣ :
    Persistent (channel_sync_1۰inv t ι Ψₛ Ψᵣ Χₛ Χᵣ).
  Proof.
    apply _.
  Qed.

  Lemma channel_sync_1٠createｰspec ι Ψₛ Ψᵣ Χₛ Χᵣ :
    {{{
      channel_sync_1۰valid ι Ψₛ Ψᵣ Χₛ Χᵣ
    }}}
      channel_sync_1٠create ()
    {{{
      t
    , RET t;
      channel_sync_1۰inv t ι Ψₛ Ψᵣ Χₛ Χᵣ
    }}}.
  Proof.
    iIntros "%Φ Hvalid HΦ".

    iApply wpｰfupd.
    wp۰apply (base.channel_sync_1٠createｰspec with "Hvalid") as (𝑡 γ) "(Hmeta & Hinv)".
    iMod (metaｰset γ with "Hmeta") as "#Hmeta". 1: done.
    iSteps.
  Qed.

  Lemma channel_sync_1٠sendｰspec {t ι Ψₛ Ψᵣ Χₛ Χᵣ v} x :
    {{{
      channel_sync_1۰inv t ι Ψₛ Ψᵣ Χₛ Χᵣ ∗
      Ψₛ v x
    }}}
      channel_sync_1٠send t v
    {{{
      b
    , RET #b;
      if b then
        ∃ y,
        Χₛ v x y
      else
        Ψₛ v x
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & HΨₛ) HΦ".

    wp۰apply (base.channel_sync_1٠sendｰspec with "[$Hinv $HΨₛ] HΦ").
  Qed.

  Lemma channel_sync_1٠recvｰspec {t ι Ψₛ Ψᵣ Χₛ Χᵣ} y :
    {{{
      channel_sync_1۰inv t ι Ψₛ Ψᵣ Χₛ Χᵣ ∗
      Ψᵣ y
    }}}
      channel_sync_1٠recv t
    {{{
      o
    , RET o;
      if o is Some v then
        ∃ x,
        Χᵣ v x y
      else
        Ψᵣ y
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & HΨᵣ) HΦ".

    wp۰apply (base.channel_sync_1٠recvｰspec with "[$Hinv $HΨᵣ] HΦ").
  Qed.
End channel_sync_1۰G.

Please opacify.
