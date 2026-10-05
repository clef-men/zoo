Require Import zoo.prelude.
Require Import zoo.iris.base_logic.lib.twins.
Require Import zoo.base.
Require Import zoo_std.option.
Require Export zoo_saturn.channel_sync_1__code.
Require Import zoo_saturn.channel_sync_1__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type v w : val.
Implicit Type o : option val.

Zoo global :=
  { token : twins (leibnizO (option val))
  }.

Section channel_sync_1۰G.
  Context `{channel_sync_1۰G : ChannelSync1G Σ}.

  Implicit Type Ψ : option val → iProp Σ.
  Implicit Type Χ : option val → iProp Σ.

  Definition channel_sync_1۰valid ι Ψ Χ : iProp Σ :=
    ▷ □
      ∀ v,
      Ψ (Some v) -∗
      Ψ None ={⊤ ∖ ↑ι}=∗
        Χ (Some v) ∗
        Χ None.
End channel_sync_1۰G.

Module base.
  Section channel_sync_1۰G.
    Context `{channel_sync_1۰G : ChannelSync1G Σ}.

    Implicit Type t : location.
    Implicit Type Ψ : option val → iProp Σ.
    Implicit Type Χ : option val → iProp Σ.

    Variant state :=
      | Null
      | Sender_offer v
      | Sender_accept v
      | Receiver_offer
      | Receiver_accept.
    Implicit Type state : state.

    #[local] Please derive Inhabited for state.

    Coercion state۰to_val state : val :=
      match state with
      | Null =>
          §Null
      | Sender_offer v =>
          ‘Sender_offer[ v ]
      | Sender_accept v =>
          ‘Sender_accept[ v ]
      | Receiver_offer =>
          §Receiver_offer
      | Receiver_accept =>
          §Receiver_accept
      end.

    Record channel_sync_1۰name :=
      { channel_sync_1۰name۰token : gname
      }.
    Implicit Type γ : channel_sync_1۰name.

    Please derive EqDecision for channel_sync_1۰name.
    Please derive Countable for channel_sync_1۰name.

    #[local] Definition token₁' γ_token o :=
      twins۰twin₁ γ_token Own o.
    #[local] Definition token₁ γ o :=
      token₁' γ.(channel_sync_1۰name۰token) o.
    #[local] Definition token₂' γ_token o :=
      twins۰twin₂ γ_token o.
    #[local] Definition token₂ γ o :=
      token₂' γ.(channel_sync_1۰name۰token) o.
    #[local] Definition token γ : iProp Σ :=
      ∃ o,
      token₁ γ o ∗
      token₂ γ o.
    #[local] Instance : CustomIpat "token" :=
      " ( %{o}
        & Htoken₁
        & Htoken₂{{!}_}
        )
      ".

    #[local] Definition inv۰state۰null γ :=
      token γ.
    #[local] Instance : CustomIpat "inv۰state۰null" :=
      " (:token)
      ".
    #[local] Definition inv۰state۰sender_offer γ Ψ v : iProp Σ :=
      token₁ γ (Some v) ∗
      Ψ (Some v).
    #[local] Instance : CustomIpat "inv۰state۰sender_offer" :=
      " ( Htoken₁
        & HΨ{:{v}}
        )
      ".
    #[local] Definition inv۰state۰sender_accept γ Χ v : iProp Σ :=
      token₁ γ None ∗
      Χ (Some v).
    #[local] Instance : CustomIpat "inv۰state۰sender_accept" :=
      " ( Htoken₁
        & HΧ
        )
      ".
    #[local] Definition inv۰state۰receiver_offer γ Ψ : iProp Σ :=
      token₁ γ None ∗
      Ψ None.
    #[local] Instance : CustomIpat "inv۰state۰receiver_offer" :=
      " ( Htoken₁
        & HΨ
        )
      ".
    #[local] Definition inv۰state۰receiver_accept γ Χ : iProp Σ :=
      ∃ v,
      token₁ γ (Some v) ∗
      Χ None.
    #[local] Instance : CustomIpat "inv۰state۰receiver_accept" :=
      " ( %{v}
        & Htoken₁
        & HΧ
        )
      ".
    #[local] Definition inv۰state γ Ψ Χ state :=
      match state with
      | Null =>
          inv۰state۰null γ
      | Sender_offer v =>
          inv۰state۰sender_offer γ Ψ v
      | Sender_accept v =>
          inv۰state۰sender_accept γ Χ v
      | Receiver_offer =>
          inv۰state۰receiver_offer γ Ψ
      | Receiver_accept =>
          inv۰state۰receiver_accept γ Χ
      end.

    #[local] Definition inv۰inner t ι Ψ Χ : iProp Σ :=
      ∃ state,
      t ↦ᵣ state ∗
      inv۰state ι Ψ Χ state.
    #[local] Instance : CustomIpat "inv۰inner" :=
      " ( %state{}
        & Ht
        & Hstate
        )
      ".
    Please Definition channel_sync_1۰inv t γ ι Ψ Χ : iProp Σ :=
      channel_sync_1۰valid ι Ψ Χ ∗
      inv ι (inv۰inner t γ Ψ Χ).
    #[local] Instance : CustomIpat "inv" :=
      " ( #Hvalid
        & #Hinv
        )
      ".

    #[global] Instance channel_sync_1۰invｰcontractive t γ ι n :
      Proper (
        (pointwise_relation _ $ dist_later n) ==>
        (pointwise_relation _ $ dist_later n) ==>
        (≡{n}≡)
      ) (channel_sync_1۰inv t γ ι).
    Proof.
      rewrite /channel_sync_1۰inv /channel_sync_1۰valid /inv۰inner /inv۰state /inv۰state۰sender_offer /inv۰state۰sender_accept /inv۰state۰receiver_offer /inv۰state۰receiver_accept.
      intros Ψ1 Ψ2 HΨ Χ1 Χ2 HΧ.
      repeat (apply HΨ || apply HΧ || f_contractive || f_equiv || done).
    Qed.
    #[global] Instance channel_sync_1۰invｰproper t γ ι :
      Proper (
        pointwise_relation _ (≡) ==>
        pointwise_relation _ (≡) ==>
        (≡)
      ) (channel_sync_1۰inv t γ ι).
    Proof.
      rewrite /channel_sync_1۰inv /channel_sync_1۰valid /inv۰inner /inv۰state /inv۰state۰sender_offer /inv۰state۰sender_accept /inv۰state۰receiver_offer /inv۰state۰receiver_accept.
      solve_proper.
    Qed.

    #[global] Instance channel_sync_1۰invｰpersistent t γ ι Ψ Χ :
      Persistent (channel_sync_1۰inv t γ ι Ψ Χ).
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
    #[local] Lemma token₁ｰexclusive γ o1 o2 :
      token₂ γ o1 -∗
      token₂ γ o2 -∗
      False.
    Proof.
      apply twins۰twin₂ｰexclusive.
    Qed.
    #[local] Lemma tokenｰagree γ o1 o2 :
      token₁ γ o1 -∗
      token₂ γ o2 -∗
      ⌜o1 = o2⌝.
    Proof.
      apply: twinsｰagreeｰL.
    Qed.
    #[local] Lemma tokenｰupdate {γ o1 o2} o :
      token₁ γ o1 -∗
      token₂ γ o2 ==∗
        token₁ γ o ∗
        token₂ γ o.
    Proof.
      apply twinsｰupdate.
    Qed.

    Lemma channel_sync_1٠createｰspec ι Ψ Χ :
      {{{
        channel_sync_1۰valid ι Ψ Χ
      }}}
        channel_sync_1٠create ()
      {{{
        t γ
      , RET #t;
        meta_token t ⊤ ∗
        channel_sync_1۰inv t γ ι Ψ Χ
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

    #[local] Lemma channel_sync_1٠sendｰspecｰaux t γ ι Ψ Χ v :
      ⊢ {{{
          channel_sync_1۰inv t γ ι Ψ Χ ∗
          Ψ (Some v)
        }}}
          channel_sync_1٠send #t v
        {{{
          b
        , RET #b;
          if b then
            Χ None
          else
            Ψ (Some v)
        }}}
      ∧ {{{
          channel_sync_1۰inv t γ ι Ψ Χ ∗
          Ψ (Some v)
        }}}
          channel_sync_1٠send_aux #t v
        {{{
          b
        , RET #b;
          if b then
            Χ None
          else
            Ψ (Some v)
        }}}.
    Proof.
      iLöb as "HLöb".
      iDestruct "HLöb" as "(IHsend & IHsend_aux)".
      iSplit.

      { iClear "IHsend".
        iIntros "!> %Φ ((:inv) & HΨ:v) HΦ".

        wp۰rec. wp۰pures.

        wp۰bind (!_)%E.
        iInv "Hinv" as "(:inv۰inner =1)".
        wp۰load.
        iSplitR "HΨ:v HΦ". { iFrameSteps. }
        iModIntro.

        destruct state1 as [| v' | v' | |]; wp۰pures.

        - wp۰apply ("IHsend_aux" with "[$] HΦ").

        - iSteps.

        - iSteps.

        - wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
          iInv "Hinv" as "(:inv۰inner =2)".
          wp۰cas.

          + iSplitR "HΨ:v HΦ". { iFrameSteps. }
            iSteps.

          + destruct state2; zoo۰simp.
            iDestruct "Hstate" as "(:inv۰state۰receiver_offer)".
            iMod ("Hvalid" with "HΨ:v HΨ") as "(HΧ:v & HΧ)".
            iSplitR "HΧ HΦ". { iExists (Sender_accept v). iFrameSteps. }
            iSteps.

        - iSteps.
      }

      { iClear "IHsend_aux".
        iIntros "!> %Φ ((:inv) & HΨ:v) HΦ".

        wp۰rec. wp۰pures.

        wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
        iInv "Hinv" as "(:inv۰inner =1)".
        wp۰cas.

        - iSplitR "HΨ:v HΦ". { iFrameSteps. }
          iModIntro.

          wp۰apply+ ("IHsend" with "[$] HΦ").

        - destruct state1; zoo۰simp.
          iDestruct "Hstate" as "(:inv۰state۰null)".
          iMod (tokenｰupdate with "Htoken₁ Htoken₂") as "(Htoken₁ & Htoken₂)".
          iSplitR "Htoken₂ HΦ". { iExists (Sender_offer _). iFrameSteps. }
          iIntros "!> {% o}".

          iStep 11.

          wp۰bind (𝘅𝗰𝗵𝗴 _ _)%E.
          iInv "Hinv" as "(:inv۰inner =2)".
          wp۰xchg.
          destruct state2 as [| v_ | v' | |]; wp۰pures.

          + iDestruct "Hstate" as "(:inv۰state۰null !=)".
            iDestruct (token₁ｰexclusive with "Htoken₂ Htoken₂_") as %[].

          + iDestruct "Hstate" as "(:inv۰state۰sender_offer)".
            iDestruct (tokenｰagree with "Htoken₁ Htoken₂") as %->.
            iSplitR "HΨ HΦ". { iExists Null. iFrameSteps. }
            iSteps.

          + iDestruct "Hstate" as "(:inv۰state۰sender_accept v=v_)".
            iDestruct (tokenｰagree with "Htoken₁ Htoken₂") as %[=].

          + iDestruct "Hstate" as "(:inv۰state۰receiver_offer)".
            iDestruct (tokenｰagree with "Htoken₁ Htoken₂") as %[=].

          + iDestruct "Hstate" as "(:inv۰state۰receiver_accept v=v_)".
            iDestruct (tokenｰagree with "Htoken₁ Htoken₂") as %->.
            iSplitR "HΧ HΦ". { iExists Null. iFrameSteps. }
            iSteps.
      }
    Qed.
    Lemma channel_sync_1٠sendｰspec t γ ι Ψ Χ v :
      {{{
        channel_sync_1۰inv t γ ι Ψ Χ ∗
        Ψ (Some v)
      }}}
        channel_sync_1٠send #t v
      {{{
        b
      , RET #b;
        if b then
          Χ None
        else
          Ψ (Some v)
      }}}.
    Proof.
      iPoseProof channel_sync_1٠sendｰspecｰaux as "(H & _)".
      iApply "H".
    Qed.

    #[local] Lemma channel_sync_1٠recvｰspecｰaux t γ ι Ψ Χ :
      ⊢ {{{
          channel_sync_1۰inv t γ ι Ψ Χ ∗
          Ψ None
        }}}
          channel_sync_1٠recv #t
        {{{
          o
        , RET o;
          if o is Some _ then
            Χ o
          else
            Ψ None
        }}}
      ∧ {{{
          channel_sync_1۰inv t γ ι Ψ Χ ∗
          Ψ None
        }}}
          channel_sync_1٠recv_aux #t
        {{{
          o
        , RET o;
          if o is Some _ then
            Χ o
          else
            Ψ None
        }}}.
    Proof.
      iLöb as "HLöb".
      iDestruct "HLöb" as "(IHrecv & IHrecv_aux)".
      iSplit.

      { iClear "IHrecv".
        iIntros "!> %Φ ((:inv) & HΨ) HΦ".

        wp۰rec. wp۰pures.

        wp۰bind (!_)%E.
        iInv "Hinv" as "(:inv۰inner =1)".
        wp۰load.
        iSplitR "HΨ HΦ". { iFrameSteps. }
        iModIntro.

        destruct state1 as [| v | v | |]; wp۰pures.

        - wp۰apply ("IHrecv_aux" with "[$] HΦ").

        - wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
          iInv "Hinv" as "(:inv۰inner =2)".
          wp۰cas.

          + iSplitR "HΨ HΦ". { iFrameSteps. }
            iModIntro.

            wp۰pures.

            iApply ("HΦ" $! None with "HΨ").

          + destruct state2; zoo۰simp.
            iDestruct "Hstate" as "(:inv۰state۰sender_offer v)".
            iMod ("Hvalid" with "HΨ:v HΨ") as "(HΧ:v & HΧ)".
            iSplitR "HΧ:v HΦ". { iExists Receiver_accept. iFrameSteps. }
            iModIntro.

            wp۰pures.

            iApply ("HΦ" $! (Some v) with "HΧ:v").

        - iApply ("HΦ" $! None with "HΨ").

        - iApply ("HΦ" $! None with "HΨ").

        - iApply ("HΦ" $! None with "HΨ").
      }

      { iClear "IHrecv_aux".
        iIntros "!> %Φ ((:inv) & HΨ) HΦ".

        wp۰rec. wp۰pures.

        wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
        iInv "Hinv" as "(:inv۰inner =1)".
        wp۰cas.

        - iSplitR "HΨ HΦ". { iFrameSteps. }
          iModIntro.

          wp۰apply+ ("IHrecv" with "[$] HΦ").

        - destruct state1; zoo۰simp.
          iDestruct "Hstate" as "(:inv۰state۰null)".
          iMod (tokenｰupdate with "Htoken₁ Htoken₂") as "(Htoken₁ & Htoken₂)".
          iSplitR "Htoken₂ HΦ". { iExists Receiver_offer. iFrameSteps. }
          iIntros "!> {% o}".

          iStep 11.

          wp۰bind (𝘅𝗰𝗵𝗴 _ _)%E.
          iInv "Hinv" as "(:inv۰inner =2)".
          wp۰xchg.
          destruct state2 as [| v | v | |]; wp۰pures.

          + iDestruct "Hstate" as "(:inv۰state۰null !=)".
            iDestruct (token₁ｰexclusive with "Htoken₂ Htoken₂_") as %[].

          + iDestruct "Hstate" as "(:inv۰state۰sender_offer)".
            iDestruct (tokenｰagree with "Htoken₁ Htoken₂") as %[=].

          + iDestruct "Hstate" as "(:inv۰state۰sender_accept)".
            iSplitR "HΧ HΦ". { iExists Null. iFrameSteps. }
            iModIntro.

            wp۰pures.

            iApply ("HΦ" $! (Some v) with "HΧ").

          + iDestruct "Hstate" as "(:inv۰state۰receiver_offer)".
            iSplitR "HΨ HΦ". { iExists Null. iFrameSteps. }
            iModIntro.

            wp۰pures.

            iApply ("HΦ" $! None with "HΨ").

          + iDestruct "Hstate" as "(:inv۰state۰receiver_accept)".
            iDestruct (tokenｰagree with "Htoken₁ Htoken₂") as %[=].
      }
    Qed.
    Lemma channel_sync_1٠recvｰspec t γ ι Ψ Χ :
      {{{
        channel_sync_1۰inv t γ ι Ψ Χ ∗
        Ψ None
      }}}
        channel_sync_1٠recv #t
      {{{
        o
      , RET o;
        if o is Some _ then
          Χ o
        else
          Ψ None
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

  Implicit Type 𝑡 : location.
  Implicit Type t : val.
  Implicit Type γ : base.channel_sync_1۰name.
  Implicit Type Ψ : option val → iProp Σ.
  Implicit Type Χ : option val → iProp Σ.

  Please Definition channel_sync_1۰inv t ι Ψ Χ : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.channel_sync_1۰inv 𝑡 γ ι Ψ Χ.
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
      (pointwise_relation _ $ dist_later n) ==>
      (pointwise_relation _ $ dist_later n) ==>
      (≡{n}≡)
    ) (channel_sync_1۰inv t ι).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance channel_sync_1۰invｰproper t ι :
    Proper (
      pointwise_relation _ (≡) ==>
      pointwise_relation _ (≡) ==>
      (≡)
    ) (channel_sync_1۰inv t ι).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance channel_sync_1۰invｰpersistent t ι Ψ Χ :
    Persistent (channel_sync_1۰inv t ι Ψ Χ).
  Proof.
    apply _.
  Qed.

  Lemma channel_sync_1٠createｰspec ι Ψ Χ :
    {{{
      channel_sync_1۰valid ι Ψ Χ
    }}}
      channel_sync_1٠create ()
    {{{
      t
    , RET t;
      channel_sync_1۰inv t ι Ψ Χ
    }}}.
  Proof.
    iIntros "%Φ Hvalid HΦ".

    iApply wpｰfupd.
    wp۰apply (base.channel_sync_1٠createｰspec with "Hvalid") as (𝑡 γ) "(Hmeta & Hinv)".
    iMod (metaｰset γ with "Hmeta") as "#Hmeta". 1: done.
    iSteps.
  Qed.

  Lemma channel_sync_1٠sendｰspec t ι Ψ Χ v :
    {{{
      channel_sync_1۰inv t ι Ψ Χ ∗
      Ψ (Some v)
    }}}
      channel_sync_1٠send t v
    {{{
      b
    , RET #b;
      if b then
        Χ None
      else
        Ψ (Some v)
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & HΨ) HΦ".

    wp۰apply (base.channel_sync_1٠sendｰspec with "[$Hinv $HΨ] HΦ").
  Qed.
End channel_sync_1۰G.

Please opacify.
