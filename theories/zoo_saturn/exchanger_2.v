Require Import zoo.prelude.
Require Import zoo.base.
Require Import zoo_std.option.
Require Export zoo_saturn.exchanger_2__code.
Require Import zoo_saturn.exchanger_2__types.
Require Import zoo.options.

Implicit Type cap_log : nat.
Implicit Type log : Z.
Implicit Type v : val.
Implicit Type exchanger : exchanger_1۰name.
Implicit Type exchangers : list exchanger_1۰name.

Zoo name :=
  { #𝑒𝑥𝑐𝘩𝑎𝑛𝑔𝑒𝑟𝑠 : val
  ; exchangers : list exchanger_1۰name
  ; #capacity_log : nat
  }.

Zoo global X :=
  { exchanger : exchanger_1 X
  }.

Section exchanger_2۰G.
  Context `{exchanger_2۰G : Exchanger2G Σ X}.
  Context `{!Inhabited X}.

  Implicit Type x 𝑥 : X.
  Implicit Type Ψ : val → X → iProp Σ.
  Implicit Type Χ : val → X → val → X → iProp Σ.

  Definition exchanger_2۰valid :=
    exchanger_1۰valid (X := X).

  Please Definition exchanger_2۰init γ : iProp Σ :=
    ⌜length γ.(exchanger_2۰name۰exchangers) = 2 ^ γ.(exchanger_2۰name۰capacity_log)⌝ ∗
    array۰model γ.(exchanger_2۰name۰𝑒𝑥𝑐𝘩𝑎𝑛𝑔𝑒𝑟𝑠) Own ((♯) <$> γ.(exchanger_2۰name۰exchangers)) ∗
    [∗ list] exchanger ∈ γ.(exchanger_2۰name۰exchangers), exchanger_1۰init exchanger.
  #[local] Instance : CustomIpat "init" :=
    " ( %Hexchangers{}
      & H𝑒𝑥𝑐𝘩𝑎𝑛𝑔𝑒𝑟𝑠{}
      & Hexchangers{}
      )
    ".

  Please Definition exchanger_2۰inv γ ι Ψ Χ : iProp Σ :=
    ⌜length γ.(exchanger_2۰name۰exchangers) = 2 ^ γ.(exchanger_2۰name۰capacity_log)⌝ ∗
    array۰model γ.(exchanger_2۰name۰𝑒𝑥𝑐𝘩𝑎𝑛𝑔𝑒𝑟𝑠) Discard ((♯) <$> γ.(exchanger_2۰name۰exchangers)) ∗
    [∗ list] exchanger ∈ γ.(exchanger_2۰name۰exchangers), exchanger_1۰inv exchanger ι Ψ Χ.
  #[local] Instance : CustomIpat "inv" :=
    " ( %Hexchangers
      & #H𝑒𝑥𝑐𝘩𝑎𝑛𝑔𝑒𝑟𝑠
      & #Hexchangers
      )
    ".

  #[global] Instance exchanger_2۰invｰcontractive γ ι n :
    Proper (
      (pointwise_relation _ $ pointwise_relation _ $ dist_later n) ==>
      (pointwise_relation _ $ pointwise_relation _ $ pointwise_relation _ $ pointwise_relation _ $ dist_later n) ==>
      (≡{n}≡)
    ) (exchanger_2۰inv γ ι).
  Proof.
    rewrite /exchanger_2۰inv.
    solve_proper.
  Qed.
  #[global] Instance exchanger_2۰invｰproper γ ι :
    Proper (
      (pointwise_relation _ $ pointwise_relation _ (≡)) ==>
      (pointwise_relation _ $ pointwise_relation _ $ pointwise_relation _ $ pointwise_relation _ (≡)) ==>
      (≡)
    ) (exchanger_2۰inv γ ι).
  Proof.
    rewrite /exchanger_2۰inv.
    solve_proper.
  Qed.

  Zoo derive Timeless for exchanger_2۰init.

  Zoo derive Persistent for exchanger_2۰inv.

  Lemma exchanger_2۰initｰexclusive γ :
    exchanger_2۰init γ -∗
    exchanger_2۰init γ -∗
    False.
  Proof.
    iIntros "(:init =1) (:init =2)".
    iApply (array۰modelｰexclusive with "H𝑒𝑥𝑐𝘩𝑎𝑛𝑔𝑒𝑟𝑠1 H𝑒𝑥𝑐𝘩𝑎𝑛𝑔𝑒𝑟𝑠2").
    { simp_length. lia. }
  Qed.
  Lemma exchanger_2۰initｰtoｰinv {γ} ι Ψ Χ E :
    exchanger_2۰init γ -∗
    exchanger_2۰valid ι Ψ Χ ={E}=∗
    exchanger_2۰inv γ ι Ψ Χ.
  Proof.
    iIntros "(:init) #Hvalid".
    iMod (array۰modelｰpersist with "H𝑒𝑥𝑐𝘩𝑎𝑛𝑔𝑒𝑟𝑠") as "#H𝑒𝑥𝑐𝘩𝑎𝑛𝑔𝑒𝑟𝑠".
    iFrame "#". iSteps.
    iApply big_sepL_fupd.
    iApply (big_sepL_impl with "Hexchangers"). iIntros "!> %i %exchanger %Hlookup Hinit".
    iApply (exchanger_1۰initｰtoｰinv with "Hinit Hvalid").
  Qed.

  Lemma exchanger_2٠createｰspecｰinit (cap_log : Z) :
    (0 ≤ cap_log)%Z →
    {{{
      True
    }}}
      exchanger_2٠create #cap_log
    {{{
      γ
    , RET γ;
      exchanger_2۰init γ
    }}}.
  Proof.
    iIntros "%Hcap_log %Φ _ HΦ".
    Z_to_nat cap_log.

    wp۰rec.

    wp۰apply+ (array٠unsafe_initｰspecｰdisentangled (λ _ 𝑒𝑥𝑐𝘩𝑎𝑛𝑔𝑒𝑟,
      ∃ exchanger,
      ⌜𝑒𝑥𝑐𝘩𝑎𝑛𝑔𝑒𝑟 = exchanger⌝ ∗
      exchanger_1۰init exchanger
    )%I) as (𝑒𝑥𝑐𝘩𝑎𝑛𝑔𝑒𝑟𝑠 𝑒𝑥𝑐𝘩𝑎𝑛𝑔𝑒𝑟s) "(%H𝑒𝑥𝑐𝘩𝑎𝑛𝑔𝑒𝑟s & H𝑒𝑥𝑐𝘩𝑎𝑛𝑔𝑒𝑟𝑠 & H𝑒𝑥𝑐𝘩𝑎𝑛𝑔𝑒𝑟s)".
    { apply Z.shiftl_nonneg => //. }
    { iIntros "!> %i _".
      wp۰apply (exchanger_1٠createｰspecｰinit with "[//]") as (exchanger) "Hexchanger".
      iSteps.
    }
    iDestruct (big_sepLｰexists with "H𝑒𝑥𝑐𝘩𝑎𝑛𝑔𝑒𝑟s") as "(%exchangers & %Hexchangers & Hexchangers)".
    iDestruct (big_sepL2_sep with "Hexchangers") as "(H𝑒𝑥𝑐𝘩𝑎𝑛𝑔𝑒𝑟s & Hexchangers)".
    iDestruct (big_sepL2ｰForall2 with "H𝑒𝑥𝑐𝘩𝑎𝑛𝑔𝑒𝑟s") as %->%listｰfmapｰaltｰForall2ｰl. iClear "H𝑒𝑥𝑐𝘩𝑎𝑛𝑔𝑒𝑟s".
    iDestruct (big_sepL2_const_sepL_r with "Hexchangers") as "(_ & Hexchangers)".

    wp۰pures.

    pose γ :=
      {|exchanger_2۰name۰𝑒𝑥𝑐𝘩𝑎𝑛𝑔𝑒𝑟𝑠 := 𝑒𝑥𝑐𝘩𝑎𝑛𝑔𝑒𝑟𝑠
      ; exchanger_2۰name۰exchangers := exchangers
      ; exchanger_2۰name۰capacity_log := cap_log
      |}.

    iApply ("HΦ" $! γ).
    iFrameSteps. iPureIntro.
    rewrite Hexchangers H𝑒𝑥𝑐𝘩𝑎𝑛𝑔𝑒𝑟s Z.shiftl_1_l. lia.
  Qed.
  Lemma exchanger_2٠createｰspec ι Ψ Χ (cap_log : Z) :
    (0 ≤ cap_log)%Z →
    {{{
      exchanger_2۰valid ι Ψ Χ
    }}}
      exchanger_2٠create #cap_log
    {{{
      γ
    , RET γ;
      exchanger_2۰inv γ ι Ψ Χ
    }}}.
  Proof.
    iIntros "%Hcap_log %Φ Hvalid HΦ".

    iApply wpｰfupd.
    wp۰apply (exchanger_2٠createｰspecｰinit with "[//]") as (γ) "Hinit". 1: done.
    iMod (exchanger_2۰initｰtoｰinv with "Hinit Hvalid") as "Hinv".
    iApply ("HΦ" with "Hinv").
  Qed.

  #[local] Lemma exchanger_2٠random_exchangerｰspec γ ι Ψ Χ log :
    (0 ≤ log ≤ γ.(exchanger_2۰name۰capacity_log))%Z →
    {{{
      exchanger_2۰inv γ ι Ψ Χ
    }}}
      exchanger_2٠random_exchanger γ #log
    {{{
      exchanger
    , RET exchanger;
      exchanger_1۰inv exchanger ι Ψ Χ
    }}}.
  Proof.
    iIntros "%Hlog %Φ (:inv) HΦ".

    wp۰rec.
    wp۰apply+ random٠intｰspec as (i) "%Hi".
    { rewrite Z.shiftl_1_l. lia. }

    destruct (lookup_lt_is_Some_2 γ.(exchanger_2۰name۰exchangers) ₊i) as (exchanger & Hexchangers_lookup).
    { apply (Nat.lt_le_trans _ ₊(1 ≪ log) _). 1: lia.
      rewrite Z.shiftl_1_l Hexchangers Znat.Z2Nat.inj_pow. 1,2: lia.
      apply Nat.pow_le_mono_r. 1,2: lia.
    }
    wp۰apply+ (array٠unsafe_getｰspec ₊i with "H𝑒𝑥𝑐𝘩𝑎𝑛𝑔𝑒𝑟𝑠") as "_". 1,3: lia.
    { rewrite list_lookup_fmap Hexchangers_lookup //. }

    iDestruct (big_sepL_lookup with "Hexchangers") as "Hexchanger". 1: done.
    iSteps.
  Qed.

  #[local] Lemma exchanger_2٠exchange₁ｰspec {γ ι Ψ Χ v} x log :
    (0 ≤ log)%Z →
    {{{
      exchanger_2۰inv γ ι Ψ Χ ∗
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
    iIntros "%Hlog %Φ (#Hinv & HΨ) HΦ".

    iLöb as "HLöb" forall (log Hlog).

    wp۰rec. wp۰pures.
    case_bool_decide; wp۰pures.

    - iApply ("HΦ" $! None with "HΨ").

    - wp۰apply (exchanger_2٠random_exchangerｰspec with "Hinv") as (exchanger) "Hexchanger". 1: lia.
      wp۰apply+ (exchanger_1٠exchangeｰspec with "[$]") as ([𝑣 |]) "H".
      all:wp۰pures.

      + iApply ("HΦ" $! (Some 𝑣) with "H").

      + wp۰apply ("HLöb" with "[%] H HΦ"). 1: lia.
  Qed.

  Lemma exchanger_2٠exchangeｰspec {γ ι Ψ Χ v} x :
    {{{
      exchanger_2۰inv γ ι Ψ Χ ∗
      Ψ v x
    }}}
      exchanger_2٠exchange γ v
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
    iIntros "%Φ (#Hinv & HΨ) HΦ".

    wp۰rec.
    wp۰apply+ (exchanger_2٠exchange₁ｰspec with "[$Hinv $HΨ] HΦ"). 1: done.
  Qed.
End exchanger_2۰G.

Require zoo_saturn.exchanger_2__opaque.

Please opacify.
