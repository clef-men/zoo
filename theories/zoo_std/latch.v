Require Import zoo.prelude.
Require Import zoo.iris.base_logic.lib.auth_nat_add.
Require Import zoo.base.
Require Export zoo_std.latch__code.
Require Import zoo_std.latch__types.
Require Import zoo.options.

Implicit Type nt nr : nat.

Zoo name :=
  { self : location
  ; size : nat
  ; mutex : val
  ; condition : val
  ; tokens : gname
  ; receipts : gname
  }.

Zoo global :=
  { mutex : mutex
  ; tokens : auth_nat_add
  ; receipts : auth_nat_add
  }.

Section latch_G.
  Context `{latch_G : LatchG Σ}.

  Implicit Type P Q : iProp Σ.

  Definition latch۰valid sz P Q : iProp Σ :=
    ([∗ list] _ ∈ seq 0 sz, P) ={⊤}=∗
    [∗ list] _ ∈ seq 0 sz, Q.

  #[local] Definition tokens۰auth' γ_tokens nt :=
    auth_nat_add۰auth γ_tokens Own nt.
  #[local] Definition tokens۰auth γ nt :=
    tokens۰auth' γ.(latch۰name۰tokens) nt.
  #[local] Definition tokens۰frag' γ_tokens :=
    auth_nat_add۰frag γ_tokens 1.
  #[local] Definition tokens۰frag γ :=
    tokens۰frag' γ.(latch۰name۰tokens).

  #[local] Definition receipts۰auth' γ_receipts nr :=
    auth_nat_add۰auth γ_receipts Own nr.
  #[local] Definition receipts۰auth γ nr :=
    receipts۰auth' γ.(latch۰name۰receipts) nr.
  #[local] Definition receipts۰frag' γ_receipts :=
    auth_nat_add۰frag γ_receipts 1.
  #[local] Definition receipts۰frag γ :=
    receipts۰frag' γ.(latch۰name۰receipts).

  Please Definition latch۰init γ sz : iProp Σ :=
    ⌜sz = γ.(latch۰name۰size)⌝ ∗
    γ.(latch۰name۰self).[counter] ↦ #γ.(latch۰name۰size) ∗
    γ.(latch۰name۰self).[mutex] ↦□ γ.(latch۰name۰mutex) ∗
    mutex۰init γ.(latch۰name۰mutex) false ∗
    γ.(latch۰name۰self).[condition] ↦□ γ.(latch۰name۰condition) ∗
    condition۰inv γ.(latch۰name۰condition) ∗
    tokens۰auth γ γ.(latch۰name۰size) ∗
    receipts۰auth γ 0.
  #[local] Instance : CustomIpat "init" :=
    " ( ->
      & Hself۰counter
      & Hself۰mutex
      & Hmutex۰init
      & Hself۰condition
      & Hcondition۰inv
      & Htokens۰auth
      & Hreceipts۰auth
      )
    ".

  #[local] Definition inv۰valid γ P Q nt : iProp Σ :=
    ([∗ list] _ ∈ seq 0 nt, P) ={⊤}=∗
    [∗ list] _ ∈ seq 0 γ.(latch۰name۰size), Q.
  #[local] Definition inv۰pre γ P Q nt nr : iProp Σ :=
    ⌜nr = γ.(latch۰name۰size) - nt⌝ ∗
    inv۰valid γ P Q nt.
  #[local] Instance : CustomIpat "inv۰pre" :=
    " ( ->
      & HQs
      )
    ".
  #[local] Definition inv۰post γ Q nr : iProp Σ :=
    [∗ list] _ ∈ seq 0 nr, Q.
  #[local] Instance : CustomIpat "inv۰post" :=
    " HQs
    ".
  #[local] Definition inv۰inner γ P Q : iProp Σ :=
    ∃ nt nr,
    ⌜nt ≤ γ.(latch۰name۰size)⌝ ∗
    γ.(latch۰name۰self).[counter] ↦ #nt ∗
    tokens۰auth γ nt ∗
    receipts۰auth γ nr ∗
    if decide (nt = 0) then
      inv۰post γ Q nr
    else
      inv۰pre γ P Q nt nr.
  #[local] Instance : CustomIpat "inv۰inner" :=
    " ( %nt{}
      & %nr{}
      & %
      & Hself۰counter
      & Htokens۰auth
      & Hreceipts۰auth
      & Hinv
      )
    ".
  Please Definition latch۰inv γ P Q : iProp Σ :=
    γ.(latch۰name۰self).[mutex] ↦□ γ.(latch۰name۰mutex) ∗
    mutex۰inv γ.(latch۰name۰mutex) (inv۰inner γ P Q) ∗
    γ.(latch۰name۰self).[condition] ↦□ γ.(latch۰name۰condition) ∗
    condition۰inv γ.(latch۰name۰condition).
  #[local] Instance : CustomIpat "inv" :=
    " ( #Hself۰mutex
      & #Hmutex۰inv
      & #Hself۰condition
      & #Hcondition۰inv
      )
    ".

  Please Definition latch۰token γ :=
    tokens۰frag γ.
  #[local] Instance : CustomIpat "token" :=
    " Htokens۰frag
    ".

  #[global] Instance latch۰invｰcontractive γ n :
    Proper (
      dist_later n ==>
      dist_later n ==>
      (≡{n}≡)
    ) (latch۰inv γ).
  Proof.
    rewrite /latch۰inv /inv۰inner /inv۰pre /inv۰post /inv۰valid.
    solve_contractive.
  Qed.
  #[global] Instance latch۰invｰproper γ :
    Proper (
      (≡) ==>
      (≡) ==>
      (≡)
    ) (latch۰inv γ).
  Proof.
    rewrite /latch۰inv /inv۰inner /inv۰pre /inv۰post /inv۰valid.
    solve_proper.
  Qed.

  Zoo derive Timeless for latch۰init.
  Zoo derive Timeless for latch۰token.

  Zoo derive Persistent for latch۰inv.

  #[local] Lemma tokensｰalloc sz :
    ⊢ |==>
      ∃ γ_tokens,
      tokens۰auth' γ_tokens sz ∗
      [∗ list] _ ∈ seq 0 sz, tokens۰frag' γ_tokens.
  Proof.
    iMod auth_nat_addｰalloc as (γ_tokens) "($ & Hfrag)".
    iDestruct (auth_nat_add۰fragｰatomize with "Hfrag") as "$" => //.
  Qed.
  #[local] Lemma tokens۰fragｰvalid γ nt :
    tokens۰auth γ nt -∗
    tokens۰frag γ -∗
    ⌜0 < nt⌝.
  Proof.
    apply auth_nat_add۰fragｰvalid.
  Qed.
  #[local] Lemma tokensｰdecr γ nt :
    tokens۰auth γ nt -∗
    tokens۰frag γ ==∗
    tokens۰auth γ (nt - 1).
  Proof.
    apply auth_nat_addｰupdateｰdecrease.
  Qed.

  Opaque tokens۰auth'.
  Opaque tokens۰frag'.

  #[local] Lemma receiptsｰalloc :
    ⊢ |==>
      ∃ γ_receipts,
      receipts۰auth' γ_receipts 0.
  Proof.
    iMod auth_nat_addｰalloc as (γ_receipts) "($ & _)" => //.
  Qed.
  #[local] Lemma receipts۰fragｰvalid γ nr :
    receipts۰auth γ nr -∗
    receipts۰frag γ -∗
    ⌜0 < nr⌝.
  Proof.
    apply auth_nat_add۰fragｰvalid.
  Qed.
  #[local] Lemma receiptsｰincr γ nr :
    receipts۰auth γ nr ⊢ |==>
      receipts۰auth γ ˖nr ∗
      receipts۰frag γ.
  Proof.
    apply auth_nat_addｰupdateｰincr.
  Qed.
  #[local] Lemma receiptsｰdecr γ nr :
    receipts۰auth γ nr -∗
    receipts۰frag γ ==∗
    receipts۰auth γ (nr - 1).
  Proof.
    apply auth_nat_addｰupdateｰdecrease.
  Qed.

  Opaque receipts۰auth'.
  Opaque receipts۰frag'.

  Lemma latch۰initｰexclusive γ sz1 sz2 :
    latch۰init γ sz1 -∗
    latch۰init γ sz2 -∗
    False.
  Proof.
    iSteps.
  Qed.
  Lemma latch۰initｰtoｰinv {γ sz} P Q E :
    latch۰init γ sz -∗
    latch۰valid sz P Q ={E}=∗
    latch۰inv γ P Q.
  Proof.
    iIntros "(:init) Hvalid".
    iFrame.
    iApply (mutex۰initｰtoｰinv with "Hmutex۰init").
    { iFrameSteps. case_decide; iSteps. }
  Qed.

  Lemma latch٠createｰspecｰinit sz :
    (0 ≤ sz)%Z →
    {{{
      True
    }}}
      latch٠create #sz
    {{{
      γ
    , RET γ;
      latch۰init γ ₊sz ∗
      [∗ list] _ ∈ seq 0 ₊sz, latch۰token γ
    }}}.
  Proof.
    iIntros "%Hsz %Φ _ HΦ".

    wp۰rec.
    wp۰apply (condition٠createｰspec with "[//]") as (cond) "Hcond۰inv".
    wp۰apply (mutex٠createｰspecｰinit with "[//]") as (mtx) "Hmtx۰init".
    wp۰block t as "Ht۰counter #Ht۰mutex #Ht۰condition".

    iMod (tokensｰalloc ₊sz) as (γ_tokens) "(Htokens۰auth & Htokens۰frags)".
    iMod receiptsｰalloc as (γ_receipts) "Hreceipts۰auth".

    pose γ :=
      {|latch۰name۰self := t
      ; latch۰name۰size := ₊sz
      ; latch۰name۰mutex := mtx
      ; latch۰name۰condition := cond
      ; latch۰name۰tokens := γ_tokens
      ; latch۰name۰receipts := γ_receipts
      |}.

    iApply ("HΦ" $! γ).
    iFrameSteps.
  Qed.
  Lemma latch٠createｰspec P Q sz :
    (0 ≤ sz)%Z →
    {{{
      latch۰valid ₊sz P Q
    }}}
      latch٠create #sz
    {{{
      γ
    , RET γ;
      latch۰inv γ P Q ∗
      [∗ list] _ ∈ seq 0 ₊sz, latch۰token γ
    }}}.
  Proof.
    iIntros "%Hsz %Φ Hvalid HΦ".

    iApply wpｰfupd.
    wp۰apply (latch٠createｰspecｰinit with "[//]") as (γ) "(Hinit & Htokens)". 1: done.
    iMod (latch۰initｰtoｰinv with "Hinit Hvalid") as "Hinv".
    iSteps.
  Qed.

  Lemma latch٠waitｰspec γ P Q :
    {{{
      latch۰inv γ P Q ∗
      latch۰token γ ∗
      ▷ P
    }}}
      latch٠wait γ
    {{{
      RET ();
      Q
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & (:token) & HP) HΦ".

    wp۰rec. wp۰load.
    wp۰apply (mutex٠protectｰspec (λ res,
      ⌜res = ()%V⌝ ∗
      Q
    )%I with "[$Hmutex۰inv Htokens۰frag HP]").
    { iIntros "Hmutex۰locked (:inv۰inner =1)".

      wp۰load. wp۰store. do 2 wp۰load.

      iDestruct (tokens۰fragｰvalid with "Htokens۰auth Htokens۰frag") as %?.
      iEval (rewrite decide_False; first lia) in "Hinv".
      iDestruct "Hinv" as "(:inv۰pre)".
      iMod (tokensｰdecr with "Htokens۰auth Htokens۰frag") as "Htokens۰auth".
      iMod (receiptsｰincr with "Hreceipts۰auth") as "(Hreceipts۰auth & Hreceipts۰frag)".
      iAssert (inv۰valid γ P Q (nt1 - 1)) with "[HP HQs]" as "HQs".
      { iIntros "HPs".
        iApply "HQs".
        iApply (big_sepLｰseqｰsnoc₂' with "HPs HP"). 1: lia.
      }
      iAssert (inv۰inner γ P Q) with "[> - Hreceipts۰frag Hmutex۰locked]" as "Hinv".
      { iFrameSteps.
        case_decide as Hcase.
        - replace nt1 with 1 by lia.
          replace ˖(γ.(latch۰name۰size) - 1) with γ.(latch۰name۰size) by lia.
          iSteps.
        - iSteps.
      }

      wp۰apply (condition٠wait_untilｰspec (λ b,
        if b then
          Q
        else
          receipts۰frag γ
      )%I with "[-]").
      { iFrame "#∗".
        iIntros "!> Hmutex۰locked (:inv۰inner =2) Hreceipts۰frag".

        wp۰load. wp۰pures.
        case_bool_decide.

        - replace nt2 with 0 by lia.
          iDestruct "Hinv" as "(:inv۰post)".
          iDestruct (receipts۰fragｰvalid with "Hreceipts۰auth Hreceipts۰frag") as %?.
          iMod (receiptsｰdecr with "Hreceipts۰auth Hreceipts۰frag") as "Hreceipts۰auth".
          iDestruct (big_sepLｰseqｰsnoc₁' with "HQs") as "(HQs & HQ)". 1: done.
          iFrameSteps.

        - iFrameSteps.
      }

      iSteps.
    }

    iSteps.
  Qed.
End latch_G.

Require zoo_std.latch__opaque.

Please opacify.
