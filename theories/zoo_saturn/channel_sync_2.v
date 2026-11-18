Require Import zoo.prelude.
Require Import zoo.base.
Require Import zoo_std.option.
Require Export zoo_saturn.channel_sync_2__code.
Require Import zoo_saturn.channel_sync_2__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type cap_log : nat.
Implicit Type log : Z.
Implicit Type v : val.
Implicit Type channel : channel_sync_1۰name.
Implicit Type channels : list channel_sync_1۰name.

Zoo name :=
  { #𝑐𝘩𝑎𝑛𝑛𝑒𝑙𝑠 : val
  ; channels : list channel_sync_1۰name
  ; #capacity_log : nat
  }.

Zoo global X Y :=
  { channel : channel_sync_1 X Y
  }.

Section channel_sync_2۰G.
  Context `{channel_sync_2۰G : ChannelSync2G Σ X Y}.
  Context `{!Inhabited X}.
  Context `{!Inhabited Y}.

  Implicit Type x 𝑥 : X.
  Implicit Type y 𝑦 : Y.
  Implicit Type Ψₛ : val → X → iProp Σ.
  Implicit Type Ψᵣ : Y → iProp Σ.
  Implicit Type Χₛ Χᵣ : val → X → Y → iProp Σ.

  Definition channel_sync_2۰valid :=
    channel_sync_1۰valid (X := X) (Y := Y).

  Please Definition channel_sync_2۰init γ : iProp Σ :=
    ⌜length γ.(channel_sync_2۰name۰channels) = 2 ^ γ.(channel_sync_2۰name۰capacity_log)⌝ ∗
    array۰model γ.(channel_sync_2۰name۰𝑐𝘩𝑎𝑛𝑛𝑒𝑙𝑠) Own ((♯) <$> γ.(channel_sync_2۰name۰channels)) ∗
    [∗ list] channel ∈ γ.(channel_sync_2۰name۰channels), channel_sync_1۰init channel.
  #[local] Instance : CustomIpat "init" :=
    " ( %Hchannels{}
      & H𝑐𝘩𝑎𝑛𝑛𝑒𝑙𝑠{}
      & Hchannels{}
      )
    ".

  Please Definition channel_sync_2۰inv γ ι Ψₛ Ψᵣ Χₛ Χᵣ : iProp Σ :=
    ⌜length γ.(channel_sync_2۰name۰channels) = 2 ^ γ.(channel_sync_2۰name۰capacity_log)⌝ ∗
    array۰model γ.(channel_sync_2۰name۰𝑐𝘩𝑎𝑛𝑛𝑒𝑙𝑠) Discard ((♯) <$> γ.(channel_sync_2۰name۰channels)) ∗
    [∗ list] channel ∈ γ.(channel_sync_2۰name۰channels), channel_sync_1۰inv channel ι Ψₛ Ψᵣ Χₛ Χᵣ.
  #[local] Instance : CustomIpat "inv" :=
    " ( %Hchannels
      & #H𝑐𝘩𝑎𝑛𝑛𝑒𝑙𝑠
      & #Hchannels
      )
    ".

  #[global] Instance channel_sync_2۰invｰcontractive γ ι n :
    Proper (
      (pointwise_relation _ $ pointwise_relation _ $ dist_later n) ==>
      (pointwise_relation _ $ dist_later n) ==>
      (pointwise_relation _ $ pointwise_relation _ $ pointwise_relation _ $ dist_later n) ==>
      (pointwise_relation _ $ pointwise_relation _ $ pointwise_relation _ $ dist_later n) ==>
      (≡{n}≡)
    ) (channel_sync_2۰inv γ ι).
  Proof.
    rewrite /channel_sync_2۰inv.
    solve_proper.
  Qed.
  #[global] Instance channel_sync_2۰invｰproper γ ι :
    Proper (
      (pointwise_relation _ $ pointwise_relation _ (≡)) ==>
      pointwise_relation _ (≡) ==>
      (pointwise_relation _ $ pointwise_relation _ $ pointwise_relation _ (≡)) ==>
      (pointwise_relation _ $ pointwise_relation _ $ pointwise_relation _ (≡)) ==>
      (≡)
    ) (channel_sync_2۰inv γ ι).
  Proof.
    rewrite /channel_sync_2۰inv.
    solve_proper.
  Qed.

  Zoo derive Timeless for channel_sync_2۰init.

  Zoo derive Persistent for channel_sync_2۰inv.

  Lemma channel_sync_2۰initｰexclusive γ :
    channel_sync_2۰init γ -∗
    channel_sync_2۰init γ -∗
    False.
  Proof.
    iIntros "(:init =1) (:init =2)".
    iApply (array۰modelｰexclusive with "H𝑐𝘩𝑎𝑛𝑛𝑒𝑙𝑠1 H𝑐𝘩𝑎𝑛𝑛𝑒𝑙𝑠2").
    { simp_length. lia. }
  Qed.
  Lemma channel_sync_2۰initｰtoｰinv {γ} ι Ψₛ Ψᵣ Χₛ Χᵣ E :
    channel_sync_2۰init γ -∗
    channel_sync_2۰valid ι Ψₛ Ψᵣ Χₛ Χᵣ ={E}=∗
    channel_sync_2۰inv γ ι Ψₛ Ψᵣ Χₛ Χᵣ.
  Proof.
    iIntros "(:init) #Hvalid".
    iMod (array۰modelｰpersist with "H𝑐𝘩𝑎𝑛𝑛𝑒𝑙𝑠") as "#H𝑐𝘩𝑎𝑛𝑛𝑒𝑙𝑠".
    iFrame "#". iSteps.
    iApply big_sepL_fupd.
    iApply (big_sepL_impl with "Hchannels"). iIntros "!> %i %channel %Hlookup Hinit".
    iApply (channel_sync_1۰initｰtoｰinv with "Hinit Hvalid").
  Qed.

  Lemma channel_sync_2٠createｰspecｰinit (cap_log : Z) :
    (0 ≤ cap_log)%Z →
    {{{
      True
    }}}
      channel_sync_2٠create #cap_log
    {{{
      γ
    , RET γ;
      channel_sync_2۰init γ
    }}}.
  Proof.
    iIntros "%Hcap_log %Φ _ HΦ".
    Z_to_nat cap_log.

    wp۰rec.

    wp۰apply+ (array٠unsafe_initｰspecｰdisentangled (λ _ 𝑐𝘩𝑎𝑛𝑛𝑒𝑙,
      ∃ channel,
      ⌜𝑐𝘩𝑎𝑛𝑛𝑒𝑙 = channel⌝ ∗
      channel_sync_1۰init channel
    )%I) as (𝑐𝘩𝑎𝑛𝑛𝑒𝑙𝑠 𝑐𝘩𝑎𝑛𝑛𝑒𝑙s) "(%H𝑐𝘩𝑎𝑛𝑛𝑒𝑙s & H𝑐𝘩𝑎𝑛𝑛𝑒𝑙𝑠 & H𝑐𝘩𝑎𝑛𝑛𝑒𝑙s)".
    { apply Z.shiftl_nonneg => //. }
    { iIntros "!> %i _".
      wp۰apply (channel_sync_1٠createｰspecｰinit with "[//]") as (channel) "Hchannel".
      iSteps.
    }
    iDestruct (big_sepLｰexists with "H𝑐𝘩𝑎𝑛𝑛𝑒𝑙s") as "(%channels & %Hchannels & Hchannels)".
    iDestruct (big_sepL2_sep with "Hchannels") as "(H𝑐𝘩𝑎𝑛𝑛𝑒𝑙s & Hchannels)".
    iDestruct (big_sepL2ｰForall2 with "H𝑐𝘩𝑎𝑛𝑛𝑒𝑙s") as %->%listｰfmapｰaltｰForall2ｰl. iClear "H𝑐𝘩𝑎𝑛𝑛𝑒𝑙s".
    iDestruct (big_sepL2_const_sepL_r with "Hchannels") as "(_ & Hchannels)".

    wp۰pures.

    pose γ :=
      {|channel_sync_2۰name۰𝑐𝘩𝑎𝑛𝑛𝑒𝑙𝑠 := 𝑐𝘩𝑎𝑛𝑛𝑒𝑙𝑠
      ; channel_sync_2۰name۰channels := channels
      ; channel_sync_2۰name۰capacity_log := cap_log
      |}.

    iApply ("HΦ" $! γ).
    iFrameSteps. iPureIntro.
    rewrite Hchannels H𝑐𝘩𝑎𝑛𝑛𝑒𝑙s Z.shiftl_1_l. lia.
  Qed.
  Lemma channel_sync_2٠createｰspec ι Ψₛ Ψᵣ Χₛ Χᵣ (cap_log : Z) :
    (0 ≤ cap_log)%Z →
    {{{
      channel_sync_2۰valid ι Ψₛ Ψᵣ Χₛ Χᵣ
    }}}
      channel_sync_2٠create #cap_log
    {{{
      γ
    , RET γ;
      channel_sync_2۰inv γ ι Ψₛ Ψᵣ Χₛ Χᵣ
    }}}.
  Proof.
    iIntros "%Hcap_log %Φ Hvalid HΦ".

    iApply wpｰfupd.
    wp۰apply (channel_sync_2٠createｰspecｰinit with "[//]") as (γ) "Hinit". 1: done.
    iMod (channel_sync_2۰initｰtoｰinv with "Hinit Hvalid") as "Hinv".
    iApply ("HΦ" with "Hinv").
  Qed.

  #[local] Lemma channel_sync_2٠random_channelｰspec γ ι Ψₛ Ψᵣ Χₛ Χᵣ log :
    (0 ≤ log ≤ γ.(channel_sync_2۰name۰capacity_log))%Z →
    {{{
      channel_sync_2۰inv γ ι Ψₛ Ψᵣ Χₛ Χᵣ
    }}}
      channel_sync_2٠random_channel γ #log
    {{{
      channel
    , RET channel;
      channel_sync_1۰inv channel ι Ψₛ Ψᵣ Χₛ Χᵣ
    }}}.
  Proof.
    iIntros "%Hlog %Φ (:inv) HΦ".

    wp۰rec.
    wp۰apply+ random٠intｰspec as (i) "%Hi".
    { rewrite Z.shiftl_1_l. lia. }

    destruct (lookup_lt_is_Some_2 γ.(channel_sync_2۰name۰channels) ₊i) as (channel & Hchannels_lookup).
    { apply (Nat.lt_le_trans _ ₊(1 ≪ log) _). 1: lia.
      rewrite Z.shiftl_1_l Hchannels Znat.Z2Nat.inj_pow. 1,2: lia.
      apply Nat.pow_le_mono_r. 1,2: lia.
    }
    wp۰apply+ (array٠unsafe_getｰspec ₊i with "H𝑐𝘩𝑎𝑛𝑛𝑒𝑙𝑠") as "_". 1,3: lia.
    { rewrite list_lookup_fmap Hchannels_lookup //. }

    iDestruct (big_sepL_lookup with "Hchannels") as "Hchannel". 1: done.
    iSteps.
  Qed.

  #[local] Lemma channel_sync_2٠send₁ｰspec {γ ι Ψₛ Ψᵣ Χₛ Χᵣ v} x log :
    (0 ≤ log)%Z →
    {{{
      channel_sync_2۰inv γ ι Ψₛ Ψᵣ Χₛ Χᵣ ∗
      Ψₛ v x
    }}}
      channel_sync_2٠send₁ γ v #log
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
    iIntros "%Hlog %Φ (#Hinv & HΨₛ) HΦ".

    iLöb as "HLöb" forall (log Hlog).

    wp۰rec. wp۰pures.
    case_bool_decide; wp۰pures.

    - iSteps.

    - wp۰apply (channel_sync_2٠random_channelｰspec with "Hinv") as (channel) "Hchannel". 1: lia.
      wp۰apply+ (channel_sync_1٠sendｰspec with "[$]") as ([]) "H".
      all:wp۰pures.

      + iSteps.

      + wp۰apply ("HLöb" with "[%] H HΦ"). 1: lia.
  Qed.

  Lemma channel_sync_2٠sendｰspec {γ ι Ψₛ Ψᵣ Χₛ Χᵣ v} x :
    {{{
      channel_sync_2۰inv γ ι Ψₛ Ψᵣ Χₛ Χᵣ ∗
      Ψₛ v x
    }}}
      channel_sync_2٠send γ v
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
    iIntros "%Φ (#Hinv & HΨₛ) HΦ".

    wp۰rec.
    wp۰apply+ (channel_sync_2٠send₁ｰspec with "[$Hinv $HΨₛ] HΦ"). 1: done.
  Qed.

  #[local] Lemma channel_sync_2٠recv₁ｰspec {γ ι Ψₛ Ψᵣ Χₛ Χᵣ} y log :
    (0 ≤ log)%Z →
    {{{
      channel_sync_2۰inv γ ι Ψₛ Ψᵣ Χₛ Χᵣ ∗
      Ψᵣ y
    }}}
      channel_sync_2٠recv₁ γ #log
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
    iIntros "%Hlog %Φ (#Hinv & HΨᵣ) HΦ".

    iLöb as "HLöb" forall (log Hlog).

    wp۰rec. wp۰pures.
    case_bool_decide; wp۰pures.

    - iApply ("HΦ" $! None with "HΨᵣ").

    - wp۰apply (channel_sync_2٠random_channelｰspec with "Hinv") as (channel) "Hchannel". 1: lia.
      wp۰apply+ (channel_sync_1٠recvｰspec with "[$]") as ([𝑣 |]) "H".
      all:wp۰pures.

      + iApply ("HΦ" $! (Some 𝑣) with "H").

      + wp۰apply ("HLöb" with "[%] H HΦ"). 1: lia.
  Qed.

  Lemma channel_sync_2٠recvｰspec {γ ι Ψₛ Ψᵣ Χₛ Χᵣ} y :
    {{{
      channel_sync_2۰inv γ ι Ψₛ Ψᵣ Χₛ Χᵣ ∗
      Ψᵣ y
    }}}
      channel_sync_2٠recv γ
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
    iIntros "%Φ (#Hinv & HΨ) HΦ".

    wp۰rec.
    wp۰apply+ (channel_sync_2٠recv₁ｰspec with "[$Hinv $HΨ] HΦ"). 1: done.
  Qed.
End channel_sync_2۰G.

Require zoo_saturn.channel_sync_2__opaque.

Please opacify.
