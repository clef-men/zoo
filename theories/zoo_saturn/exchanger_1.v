Require Import zoo.prelude.
Require Import zoo.iris.base_logic.lib.twins.
Require Import zoo.base.
Require Import zoo_std.option.
Require Export zoo_saturn.exchanger_1__code.
Require Import zoo_saturn.exchanger_1__types.
Require Import zoo.options.

Implicit Type v w : val.
Implicit Type o : option val.

Zoo global :=
  { token : twins (leibnizO val)
  }.

Section exchanger_1۰G.
  Context `{exchanger_1۰G : Exchanger1G Σ}.

  Implicit Type Ψ : val → iProp Σ.
  Implicit Type Χ : val → val → iProp Σ.

  Definition exchanger_1۰valid ι Ψ Χ : iProp Σ :=
    ▷ □ ∀ v1 v2,
      Ψ v1 -∗
      Ψ v2 ={⊤ ∖ ↑ι}=∗
        Χ v1 v2 ∗
        Χ v2 v1.
End exchanger_1۰G.

Module base.
  Section exchanger_1۰G.
    Context `{exchanger_1۰G : Exchanger1G Σ}.

    Implicit Type t : location.
    Implicit Type Ψ : val → iProp Σ.
    Implicit Type Χ : val → val → iProp Σ.

    Variant state :=
      | Null
      | Offer v
      | Accept w.
    Implicit Type state : state.

    #[local] Please derive Inhabited for state.

    Coercion state۰to_val state : val :=
      match state with
      | Null =>
          §Null
      | Offer v =>
          ‘Offer[ v ]
      | Accept w =>
          ‘Accept[ w ]
      end.

    Record exchanger_1۰name :=
      { exchanger_1۰name۰token : gname
      }.
    Implicit Type γ : exchanger_1۰name.

    Please derive EqDecision for exchanger_1۰name.
    Please derive Countable for exchanger_1۰name.

    #[local] Definition token₁' γ_token v :=
      twins۰twin₁ γ_token Own v.
    #[local] Definition token₁ γ v :=
      token₁' γ.(exchanger_1۰name۰token) v.
    #[local] Definition token₂' γ_token v :=
      twins۰twin₂ γ_token v.
    #[local] Definition token₂ γ v :=
      token₂' γ.(exchanger_1۰name۰token) v.
    #[local] Definition token γ : iProp Σ :=
      ∃ v,
      token₁ γ v ∗
      token₂ γ v.
    #[local] Instance : CustomIpat "token" :=
      " ( %{v}
        & Htoken₁
        & Htoken₂{{!}_}
        )
      ".

    #[local] Definition inv۰state۰null γ :=
      token γ.
    #[local] Instance : CustomIpat "inv۰state۰null" :=
      " (:token)
      ".
    #[local] Definition inv۰state۰offer γ Ψ v : iProp Σ :=
      token₁ γ v ∗
      Ψ v.
    #[local] Instance : CustomIpat "inv۰state۰offer" :=
      " ( Htoken₁
        & HΨ{:{v}}
        )
      ".
    #[local] Definition inv۰state۰accept γ Χ w : iProp Σ :=
      ∃ v,
      token₁ γ v ∗
      Χ v w.
    #[local] Instance : CustomIpat "inv۰state۰accept" :=
      " ( %{v}
        & Htoken₁
        & HΧ
        )
      ".
    #[local] Definition inv۰state γ Ψ Χ state :=
      match state with
      | Null =>
          inv۰state۰null γ
      | Offer v =>
          inv۰state۰offer γ Ψ v
      | Accept w =>
          inv۰state۰accept γ Χ w
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
    Definition exchanger_1۰inv t γ ι Ψ Χ : iProp Σ :=
      exchanger_1۰valid ι Ψ Χ ∗
      inv ι (inv۰inner t γ Ψ Χ).
    #[local] Instance : CustomIpat "inv" :=
      " ( #Hvalid
        & #Hinv
        )
      ".

    #[global] Instance exchanger_1۰invｰcontractive t γ ι n :
      Proper (
        (pointwise_relation _ $ dist_later n) ==>
        (pointwise_relation _ $ pointwise_relation _ $ dist_later n) ==>
        (≡{n}≡)
      ) (exchanger_1۰inv t γ ι).
    Proof.
      rewrite /exchanger_1۰inv /exchanger_1۰valid /inv۰inner /inv۰state /inv۰state۰offer /inv۰state۰accept.
      intros Ψ1 Ψ2 HΨ Χ1 Χ2 HΧ.
      repeat (apply HΨ || apply HΧ || f_contractive || f_equiv || done).
    Qed.
    #[global] Instance exchanger_1۰invｰproper t γ ι :
      Proper (
        pointwise_relation _ (≡) ==>
        (pointwise_relation _ $ pointwise_relation _ (≡)) ==>
        (≡)
      ) (exchanger_1۰inv t γ ι).
    Proof.
      rewrite /exchanger_1۰inv /exchanger_1۰valid /inv۰inner /inv۰state /inv۰state۰offer /inv۰state۰accept.
      solve_proper.
    Qed.

    #[global] Instance exchanger_1۰invｰpersistent t γ ι Ψ Χ :
      Persistent (exchanger_1۰inv t γ ι Ψ Χ).
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
    #[local] Lemma token₁ｰexclusive γ v1 v2 :
      token₂ γ v1 -∗
      token₂ γ v2 -∗
      False.
    Proof.
      apply twins۰twin₂ｰexclusive.
    Qed.
    #[local] Lemma tokenｰagree γ v1 v2 :
      token₁ γ v1 -∗
      token₂ γ v2 -∗
      ⌜v1 = v2⌝.
    Proof.
      apply: twinsｰagreeｰL.
    Qed.
    #[local] Lemma tokenｰupdate {γ v1 v2} v :
      token₁ γ v1 -∗
      token₂ γ v2 ==∗
        token₁ γ v ∗
        token₂ γ v.
    Proof.
      apply twinsｰupdate.
    Qed.

    Lemma exchanger_1٠createｰspec ι Ψ Χ :
      {{{
        exchanger_1۰valid ι Ψ Χ
      }}}
        exchanger_1٠create ()
      {{{
        t γ
      , RET #t;
        meta_token t ⊤ ∗
        exchanger_1۰inv t γ ι Ψ Χ
      }}}.
    Proof.
      iIntros "%Φ Hvalid HΦ".

      wp۰rec.
      wp۰ref t as "Hmeta" "Ht".

      iMod tokenｰalloc as "(%γ۰token & Htoken₁ & Htoken₂)".

      pose γ :=
        {|exchanger_1۰name۰token := γ۰token
        |}.

      iApply ("HΦ" $! t γ).
      iFrameSteps. iExists Null. iSteps.
    Qed.

    #[local] Lemma exchanger_1٠exchangeｰspecｰaux t γ ι Ψ Χ v :
      ⊢ {{{
          exchanger_1۰inv t γ ι Ψ Χ ∗
          Ψ v
        }}}
          exchanger_1٠exchange #t v
        {{{
          o
        , RET o;
          if o is Some w then
            Χ v w
          else
            Ψ v
        }}}
      ∧ {{{
          exchanger_1۰inv t γ ι Ψ Χ ∗
          Ψ v
        }}}
          exchanger_1٠exchange_aux #t v
        {{{
          o
        , RET o;
          if o is Some w then
            Χ v w
          else
            Ψ v
        }}}.
    Proof.
      iLöb as "HLöb".
      iDestruct "HLöb" as "(IHexchange & IHexchange_aux)".
      iSplit.

      { iClear "IHexchange".
        iIntros "!> %Φ ((:inv) & HΨ:v) HΦ".

        wp۰rec. wp۰pures.

        wp۰bind (!_)%E.
        iInv "Hinv" as "(:inv۰inner =1)".
        wp۰load.
        iSplitR "HΨ:v HΦ". { iFrameSteps. }
        iModIntro.

        destruct state1 as [| v' | w]; wp۰pures.

        - wp۰apply ("IHexchange_aux" with "[$] HΦ").

        - wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
          iInv "Hinv" as "(:inv۰inner =2)".
          wp۰cas.

          + iSplitR "HΨ:v HΦ". { iFrameSteps. }
            iModIntro.

            wp۰pures.

            iApply ("HΦ" $! None with "HΨ:v").

          + destruct state2; zoo۰simp.
            iDestruct "Hstate" as "(:inv۰state۰offer v=v')".
            iMod ("Hvalid" with "HΨ:v HΨ:v'") as "(HΧ:v & HΧ:v')".
            iSplitR "HΧ:v HΦ". { iExists (Accept v). iFrameSteps. }
            iModIntro.

            wp۰pures.

            iApply ("HΦ" $! (Some v') with "HΧ:v").

        - iApply ("HΦ" $! None with "HΨ:v").
      }

      { iClear "IHexchange_aux".
        iIntros "!> %Φ ((:inv) & HΨ:v) HΦ".

        wp۰rec. wp۰pures.

        wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
        iInv "Hinv" as "(:inv۰inner =1)".
        wp۰cas.

        - iSplitR "HΨ:v HΦ". { iFrameSteps. }
          iModIntro.

          wp۰apply+ ("IHexchange" with "[$] HΦ").

        - destruct state1; zoo۰simp.
          iDestruct "Hstate" as "(:inv۰state۰null v=v')".
          iMod (tokenｰupdate with "Htoken₁ Htoken₂") as "(Htoken₁ & Htoken₂)".
          iSplitR "Htoken₂ HΦ". { iExists (Offer _). iFrameSteps. }
          iIntros "!> {% v'}".

          iStep 11.

          wp۰bind (𝘅𝗰𝗵𝗴 _ _)%E.
          iInv "Hinv" as "(:inv۰inner =2)".
          wp۰xchg.
          destruct state2 as [| v_ | w]; wp۰pures.

          + iDestruct "Hstate" as "(:inv۰state۰null != v=w)".
            iDestruct (token₁ｰexclusive with "Htoken₂ Htoken₂_") as %[].

          + iDestruct "Hstate" as "(:inv۰state۰offer)".
            iDestruct (tokenｰagree with "Htoken₁ Htoken₂") as %->.
            iSplitR "HΨ HΦ". { iExists Null. iFrameSteps. }
            iModIntro.

            wp۰pures.

            iApply ("HΦ" $! None with "HΨ").

          + iDestruct "Hstate" as "(:inv۰state۰accept v=v_)".
            iDestruct (tokenｰagree with "Htoken₁ Htoken₂") as %->.
            iSplitR "HΧ HΦ". { iExists Null. iFrameSteps. }
            iModIntro.

            wp۰pures.

            iApply ("HΦ" $! (Some w) with "HΧ").
      }
    Qed.
    Lemma exchanger_1٠exchangeｰspec t γ ι Ψ Χ v :
      {{{
        exchanger_1۰inv t γ ι Ψ Χ ∗
        Ψ v
      }}}
        exchanger_1٠exchange #t v
      {{{
        o
      , RET o;
        if o is Some w then
          Χ v w
        else
          Ψ v
      }}}.
    Proof.
      iPoseProof exchanger_1٠exchangeｰspecｰaux as "(H & _)".
      iApply "H".
    Qed.
  End exchanger_1۰G.

  #[global] Opaque exchanger_1۰inv.
End base.

Require zoo_saturn.exchanger_1__opaque.

Section exchanger_1۰G.
  Context `{exchanger_1۰G : Exchanger1G Σ}.

  Implicit Type 𝑡 : location.
  Implicit Type t : val.
  Implicit Type γ : base.exchanger_1۰name.
  Implicit Type Ψ : val → iProp Σ.
  Implicit Type Χ : val → val → iProp Σ.

  Definition exchanger_1۰inv t ι Ψ Χ : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.exchanger_1۰inv 𝑡 γ ι Ψ Χ.
  #[local] Instance : CustomIpat "inv" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hinv{_{}}
      )
    ".

  #[global] Instance exchanger_1۰invｰcontractive t ι n :
    Proper (
      (pointwise_relation _ $ dist_later n) ==>
      (pointwise_relation _ $ pointwise_relation _ $ dist_later n) ==>
      (≡{n}≡)
    ) (exchanger_1۰inv t ι).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance exchanger_1۰invｰproper t ι :
    Proper (
      pointwise_relation _ (≡) ==>
      (pointwise_relation _ $ pointwise_relation _ (≡)) ==>
      (≡)
    ) (exchanger_1۰inv t ι).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance exchanger_1۰invｰpersistent t ι Ψ Χ :
    Persistent (exchanger_1۰inv t ι Ψ Χ).
  Proof.
    apply _.
  Qed.

  Lemma exchanger_1٠createｰspec ι Ψ Χ :
    {{{
      exchanger_1۰valid ι Ψ Χ
    }}}
      exchanger_1٠create ()
    {{{
      t
    , RET t;
      exchanger_1۰inv t ι Ψ Χ
    }}}.
  Proof.
    iIntros "%Φ Hvalid HΦ".

    iApply wpｰfupd.
    wp۰apply (base.exchanger_1٠createｰspec with "Hvalid") as (𝑡 γ) "(Hmeta & Hinv)".
    iMod (metaｰset γ with "Hmeta") as "#Hmeta". 1: done.
    iSteps.
  Qed.

  Lemma exchanger_1٠exchangeｰspec t ι Ψ Χ v :
    {{{
      exchanger_1۰inv t ι Ψ Χ ∗
      Ψ v
    }}}
      exchanger_1٠exchange t v
    {{{
      o
    , RET o;
      if o is Some w then
        Χ v w
      else
        Ψ v
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & HΨ) HΦ".

    wp۰apply (base.exchanger_1٠exchangeｰspec with "[$Hinv $HΨ] HΦ").
  Qed.
End exchanger_1۰G.

#[global] Opaque exchanger_1۰inv.
