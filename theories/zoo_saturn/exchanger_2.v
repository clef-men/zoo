Require Import zoo.prelude.
Require Import zoo.base.
Require Import zoo_std.option.
Require Export zoo_saturn.exchanger_2__code.
Require Import zoo_saturn.exchanger_2__types.
Require Import zoo.options.

Implicit Type cap_log : nat.
Implicit Type log : Z.
Implicit Type v t exchanger : val.

Zoo global X :=
  { exchanger : exchanger_1 X
  }.

Module internal.
  Record metadata :=
    { metadata۰𝑒𝑥𝑐𝘩𝑎𝑛𝑔𝑒𝑟𝑠 : val
    ; metadata۰exchangers : list val
    ; metadata۰capacity_log : nat
    }.
  Implicit Type γ : metadata.

  Coercion metadata۰to_val γ : val :=
    ( γ.(metadata۰𝑒𝑥𝑐𝘩𝑎𝑛𝑔𝑒𝑟𝑠)
    , #γ.(metadata۰capacity_log)
    ).
End internal.

Section exchanger_2۰G.
  Context `{exchanger_2۰G : Exchanger2G Σ}.
  Context `{!Inhabited X}.

  Import internal.

  Implicit Type γ : metadata.
  Implicit Type x 𝑥 : X.
  Implicit Type Ψ : val → X → iProp Σ.
  Implicit Type Χ : val → X → val → X → iProp Σ.

  Definition exchanger_2۰valid :=
    exchanger_1۰valid (X := X).

  #[local] Definition inv' γ ι Ψ Χ : iProp Σ :=
    ⌜length γ.(metadata۰exchangers) = 2 ^ γ.(metadata۰capacity_log)⌝ ∗
    array۰model γ.(metadata۰𝑒𝑥𝑐𝘩𝑎𝑛𝑔𝑒𝑟𝑠) Discard γ.(metadata۰exchangers) ∗
    [∗ list] exchanger ∈ γ.(metadata۰exchangers), exchanger_1۰inv exchanger ι Ψ Χ.
  #[local] Instance : CustomIpat "inv'" :=
    " ( %Hexchangers
      & #H𝑒𝑥𝑐𝘩𝑎𝑛𝑔𝑒𝑟𝑠
      & #Hexchangers
      )
    ".
  Please Definition exchanger_2۰inv t ι Ψ Χ : iProp Σ :=
    ∃ γ,
    ⌜t = γ⌝ ∗
    inv' γ ι Ψ Χ.
  #[local] Instance : CustomIpat "inv" :=
    " ( %γ
      & ->
      & Hinv
      )
    ".

  #[global] Instance exchanger_2۰invｰcontractive t ι n :
    Proper (
      (pointwise_relation _ $ pointwise_relation _ $ dist_later n) ==>
      (pointwise_relation _ $ pointwise_relation _ $ pointwise_relation _ $ pointwise_relation _ $ dist_later n) ==>
      (≡{n}≡)
    ) (exchanger_2۰inv t ι).
  Proof.
    rewrite /exchanger_2۰inv /inv'.
    solve_proper.
  Qed.
  #[global] Instance exchanger_2۰invｰproper t ι :
    Proper (
      (pointwise_relation _ $ pointwise_relation _ (≡)) ==>
      (pointwise_relation _ $ pointwise_relation _ $ pointwise_relation _ $ pointwise_relation _ (≡)) ==>
      (≡)
    ) (exchanger_2۰inv t ι).
  Proof.
    rewrite /exchanger_2۰inv /inv'.
    solve_proper.
  Qed.

  #[global] Instance exchanger_2۰invｰpersistent t ι Ψ Χ :
    Persistent (exchanger_2۰inv t ι Ψ Χ).
  Proof.
    apply _.
  Qed.

  Lemma exchanger_2٠createｰspec ι Ψ Χ (cap_log : Z) :
    (0 ≤ cap_log)%Z →
    {{{
      exchanger_2۰valid ι Ψ Χ
    }}}
      exchanger_2٠create #cap_log
    {{{
      t
    , RET t;
      exchanger_2۰inv t ι Ψ Χ
    }}}.
  Proof.
    iIntros "%Hcap_log %Φ #Hvalid HΦ".
    Z_to_nat cap_log.

    wp۰rec.

    wp۰apply+ (array٠unsafe_initｰspecｰdisentangled (λ _ exchanger,
      exchanger_1۰inv exchanger ι Ψ Χ
    )) as (𝑒𝑥𝑐𝘩𝑎𝑛𝑔𝑒𝑟𝑠 exchangers) "(%Hexchangers & H𝑒𝑥𝑐𝘩𝑎𝑛𝑔𝑒𝑟𝑠 & Hexchangers)".
    { apply Z.shiftl_nonneg => //. }
    { iIntros "!> %i _".
      wp۰apply (exchanger_1٠createｰspec with "Hvalid").
      iSteps.
    }
    iMod (array۰modelｰpersist with "H𝑒𝑥𝑐𝘩𝑎𝑛𝑔𝑒𝑟𝑠") as "#H𝑒𝑥𝑐𝘩𝑎𝑛𝑔𝑒𝑟𝑠".

    wp۰pures.

    pose γ :=
      {|metadata۰𝑒𝑥𝑐𝘩𝑎𝑛𝑔𝑒𝑟𝑠 := 𝑒𝑥𝑐𝘩𝑎𝑛𝑔𝑒𝑟𝑠
      ; metadata۰exchangers := exchangers
      ; metadata۰capacity_log := cap_log
      |}.

    iApply "HΦ".
    iExists γ. iFrameSteps. iPureIntro.
    rewrite Hexchangers Z.shiftl_1_l. lia.
  Qed.

  #[local] Lemma exchanger_2٠exchange₁ｰspec {γ ι Ψ Χ v} x log :
    (0 ≤ log)%Z →
    {{{
      inv' γ ι Ψ Χ ∗
      Ψ v x
    }}}
      exchanger_2٠exchange₁ γ v #log
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
    iIntros "%Hlog %Φ ((:inv') & HΨ) HΦ".

    iLöb as "HLöb" forall (log Hlog).

    wp۰rec. wp۰pures.
    case_bool_decide; wp۰pures.

    - iApply ("HΦ" $! None with "HΨ").

    - wp۰apply random٠intｰspec as (i) "%Hi".
      { rewrite Z.shiftl_1_l. lia. }

      destruct (lookup_lt_is_Some_2 γ.(metadata۰exchangers) ₊i).
      { apply (Nat.lt_le_trans _ ₊(1 ≪ log) _). 1: lia.
        rewrite Z.shiftl_1_l Hexchangers Znat.Z2Nat.inj_pow. 1,2: lia.
        apply Nat.pow_le_mono_r. 1,2: lia.
      }
      wp۰apply+ (array٠unsafe_getｰspec with "H𝑒𝑥𝑐𝘩𝑎𝑛𝑔𝑒𝑟𝑠") as "_". 1-3: done || lia.

      wp۰apply+ (exchanger_1٠exchangeｰspec with "[HΨ]") as ([𝑣 |]) "H".
      { iDestruct (big_sepL_lookup with "Hexchangers") as "$" => //. }
      all:wp۰pures.

      + iApply ("HΦ" $! (Some 𝑣) with "H").

      + wp۰apply ("HLöb" with "[%] H HΦ"). 1: lia.
  Qed.

  Lemma exchanger_2٠exchangeｰspec {t ι Ψ Χ v} x :
    {{{
      exchanger_2۰inv t ι Ψ Χ ∗
      Ψ v x
    }}}
      exchanger_2٠exchange t v
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
    iIntros "%Φ ((:inv) & HΨ) HΦ".

    wp۰rec.
    wp۰apply+ (exchanger_2٠exchange₁ｰspec with "[$Hinv $HΨ] HΦ"). 1: done.
  Qed.
End exchanger_2۰G.

Require zoo_saturn.exchanger_2__opaque.

Please opacify.
