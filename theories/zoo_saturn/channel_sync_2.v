Require Import zoo.prelude.
Require Import zoo.base.
Require Import zoo_std.option.
Require Export zoo_saturn.channel_sync_2__code.
Require Import zoo_saturn.channel_sync_2__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type cap_log : nat.
Implicit Type log : Z.
Implicit Type v t chan : val.

Zoo global X Y :=
  { channel : channel_sync_1 X Y
  }.

Module internal.
  Record metadata :=
    { metadata۰𝑐𝘩𝑎𝑛𝑛𝑒𝑙𝑠 : val
    ; metadata۰channels : list val
    ; metadata۰capacity_log : nat
    }.
  Implicit Type γ : metadata.

  Coercion metadata۰to_val γ : val :=
    ( γ.(metadata۰𝑐𝘩𝑎𝑛𝑛𝑒𝑙𝑠)
    , #γ.(metadata۰capacity_log)
    ).
End internal.

Section channel_sync_2۰G.
  Context `{channel_sync_2۰G : ChannelSync2G Σ}.
  Context `{!Inhabited X}.
  Context `{!Inhabited Y}.

  Import internal.

  Implicit Type γ : metadata.
  Implicit Type x 𝑥 : X.
  Implicit Type y 𝑦 : Y.
  Implicit Type Ψₛ : val → X → iProp Σ.
  Implicit Type Ψᵣ : Y → iProp Σ.
  Implicit Type Χₛ Χᵣ : val → X → Y → iProp Σ.

  Definition channel_sync_2۰valid :=
    channel_sync_1۰valid (X := X) (Y := Y).

  #[local] Definition inv' γ ι Ψₛ Ψᵣ Χₛ Χᵣ : iProp Σ :=
    ⌜length γ.(metadata۰channels) = 2 ^ γ.(metadata۰capacity_log)⌝ ∗
    array۰model γ.(metadata۰𝑐𝘩𝑎𝑛𝑛𝑒𝑙𝑠) Discard γ.(metadata۰channels) ∗
    [∗ list] chan ∈ γ.(metadata۰channels), channel_sync_1۰inv chan ι Ψₛ Ψᵣ Χₛ Χᵣ.
  #[local] Instance : CustomIpat "inv'" :=
    " ( %Hchannels
      & #H𝑐𝘩𝑎𝑛𝑛𝑒𝑙𝑠
      & #Hchannels
      )
    ".
  Please Definition channel_sync_2۰inv t ι Ψₛ Ψᵣ Χₛ Χᵣ : iProp Σ :=
    ∃ γ,
    ⌜t = γ⌝ ∗
    inv' γ ι Ψₛ Ψᵣ Χₛ Χᵣ.
  #[local] Instance : CustomIpat "inv" :=
    " ( %γ
      & ->
      & Hinv
      )
    ".

  #[global] Instance channel_sync_2۰invｰcontractive t ι n :
    Proper (
      (pointwise_relation _ $ pointwise_relation _ $ dist_later n) ==>
      (pointwise_relation _ $ dist_later n) ==>
      (pointwise_relation _ $ pointwise_relation _ $ pointwise_relation _ $ dist_later n) ==>
      (pointwise_relation _ $ pointwise_relation _ $ pointwise_relation _ $ dist_later n) ==>
      (≡{n}≡)
    ) (channel_sync_2۰inv t ι).
  Proof.
    rewrite /channel_sync_2۰inv /inv'.
    solve_proper.
  Qed.
  #[global] Instance channel_sync_2۰invｰproper t ι :
    Proper (
      (pointwise_relation _ $ pointwise_relation _ (≡)) ==>
      pointwise_relation _ (≡) ==>
      (pointwise_relation _ $ pointwise_relation _ $ pointwise_relation _ (≡)) ==>
      (pointwise_relation _ $ pointwise_relation _ $ pointwise_relation _ (≡)) ==>
      (≡)
    ) (channel_sync_2۰inv t ι).
  Proof.
    rewrite /channel_sync_2۰inv /inv'.
    solve_proper.
  Qed.

  #[global] Instance channel_sync_2۰invｰpersistent t ι Ψₛ Ψᵣ Χₛ Χᵣ :
    Persistent (channel_sync_2۰inv t ι Ψₛ Ψᵣ Χₛ Χᵣ).
  Proof.
    apply _.
  Qed.

  Lemma channel_sync_2٠createｰspec ι Ψₛ Ψᵣ Χₛ Χᵣ (cap_log : Z) :
    (0 ≤ cap_log)%Z →
    {{{
      channel_sync_2۰valid ι Ψₛ Ψᵣ Χₛ Χᵣ
    }}}
      channel_sync_2٠create #cap_log
    {{{
      t
    , RET t;
      channel_sync_2۰inv t ι Ψₛ Ψᵣ Χₛ Χᵣ
    }}}.
  Proof.
    iIntros "%Hcap_log %Φ #Hvalid HΦ".
    Z_to_nat cap_log.

    wp۰rec.

    wp۰apply+ (array٠unsafe_initｰspecｰdisentangled (λ _ chan,
      channel_sync_1۰inv chan ι Ψₛ Ψᵣ Χₛ Χᵣ
    )) as (𝑐𝘩𝑎𝑛𝑠 chans) "(%Hchans & H𝑐𝘩𝑎𝑛𝑠 & Hchans)".
    { apply Z.shiftl_nonneg => //. }
    { iIntros "!> %i _".
      wp۰apply (channel_sync_1٠createｰspec with "Hvalid").
      iSteps.
    }
    iMod (array۰modelｰpersist with "H𝑐𝘩𝑎𝑛𝑠") as "#H𝑐𝘩𝑎𝑛𝑠".

    wp۰pures.

    pose γ :=
      {|metadata۰𝑐𝘩𝑎𝑛𝑛𝑒𝑙𝑠 := 𝑐𝘩𝑎𝑛𝑠
      ; metadata۰channels := chans
      ; metadata۰capacity_log := cap_log
      |}.

    iApply "HΦ".
    iExists γ. iFrameSteps. iPureIntro.
    rewrite Hchans Z.shiftl_1_l. lia.
  Qed.

  #[local] Lemma channel_sync_2٠send₁ｰspec {γ ι Ψₛ Ψᵣ Χₛ Χᵣ v} x log :
    (0 ≤ log)%Z →
    {{{
      inv' γ ι Ψₛ Ψᵣ Χₛ Χᵣ ∗
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
    iIntros "%Hlog %Φ ((:inv') & HΨₛ) HΦ".

    iLöb as "HLöb" forall (log Hlog).

    wp۰rec. wp۰pures.
    case_bool_decide; wp۰pures.

    - iSteps.

    - wp۰apply random٠intｰspec as (i) "%Hi".
      { rewrite Z.shiftl_1_l. lia. }

      destruct (lookup_lt_is_Some_2 γ.(metadata۰channels) ₊i).
      { apply (Nat.lt_le_trans _ ₊(1 ≪ log) _). 1: lia.
        rewrite Z.shiftl_1_l Hchannels Znat.Z2Nat.inj_pow. 1,2: lia.
        apply Nat.pow_le_mono_r. 1,2: lia.
      }
      wp۰apply+ (array٠unsafe_getｰspec with "H𝑐𝘩𝑎𝑛𝑛𝑒𝑙𝑠") as "_". 1-3: done || lia.

      wp۰apply+ (channel_sync_1٠sendｰspec with "[HΨₛ]") as ([]) "H".
      { iDestruct (big_sepL_lookup with "Hchannels") as "$" => //. }
      all:wp۰pures.

      + iSteps.

      + wp۰apply ("HLöb" with "[%] H HΦ"). 1: lia.
  Qed.

  Lemma channel_sync_2٠sendｰspec {t ι Ψₛ Ψᵣ Χₛ Χᵣ v} x :
    {{{
      channel_sync_2۰inv t ι Ψₛ Ψᵣ Χₛ Χᵣ ∗
      Ψₛ v x
    }}}
      channel_sync_2٠send t v
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

    wp۰rec.
    wp۰apply+ (channel_sync_2٠send₁ｰspec with "[$Hinv $HΨₛ] HΦ"). 1: done.
  Qed.

  #[local] Lemma channel_sync_2٠recv₁ｰspec {γ ι Ψₛ Ψᵣ Χₛ Χᵣ} y log :
    (0 ≤ log)%Z →
    {{{
      inv' γ ι Ψₛ Ψᵣ Χₛ Χᵣ ∗
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
    iIntros "%Hlog %Φ ((:inv') & HΨᵣ) HΦ".

    iLöb as "HLöb" forall (log Hlog).

    wp۰rec. wp۰pures.
    case_bool_decide; wp۰pures.

    - iApply ("HΦ" $! None with "HΨᵣ").

    - wp۰apply random٠intｰspec as (i) "%Hi".
      { rewrite Z.shiftl_1_l. lia. }

      destruct (lookup_lt_is_Some_2 γ.(metadata۰channels) ₊i).
      { apply (Nat.lt_le_trans _ ₊(1 ≪ log) _). 1: lia.
        rewrite Z.shiftl_1_l Hchannels Znat.Z2Nat.inj_pow. 1,2: lia.
        apply Nat.pow_le_mono_r. 1,2: lia.
      }
      wp۰apply+ (array٠unsafe_getｰspec with "H𝑐𝘩𝑎𝑛𝑛𝑒𝑙𝑠") as "_". 1-3: done || lia.

      wp۰apply+ (channel_sync_1٠recvｰspec with "[HΨᵣ]") as ([𝑣 |]) "H".
      { iDestruct (big_sepL_lookup with "Hchannels") as "$" => //. }
      all:wp۰pures.

      + iApply ("HΦ" $! (Some 𝑣) with "H").

      + wp۰apply ("HLöb" with "[%] H HΦ"). 1: lia.
  Qed.

  Lemma channel_sync_2٠recvｰspec {t ι Ψₛ Ψᵣ Χₛ Χᵣ} y :
    {{{
      channel_sync_2۰inv t ι Ψₛ Ψᵣ Χₛ Χᵣ ∗
      Ψᵣ y
    }}}
      channel_sync_2٠recv t
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
    iIntros "%Φ ((:inv) & HΨ) HΦ".

    wp۰rec.
    wp۰apply+ (channel_sync_2٠recv₁ｰspec with "[$Hinv $HΨ] HΦ"). 1: done.
  Qed.
End channel_sync_2۰G.

Require zoo_saturn.channel_sync_2__opaque.

Please opacify.
