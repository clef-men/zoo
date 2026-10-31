Require Import stdpp.finite.

Require Import zoo.prelude.
Require Import zoo.iris.bi.big_op.
Require Import zoo.iris.base_logic.lib.excl.
Require Import zoo.base.
Require Export zoo_std.semaphore__code.
Require Import zoo_std.semaphore__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type cnt : nat.
Implicit Type γ_tokens : list gname.

Zoo name :=
  { self : location
  ; mutex : val
  ; condition : val
  ; tokens : list gname
  }.

Zoo global :=
  { mutex : mutex
  ; tokens : excl unitO
  }.

Section semaphore۰G.
  Context `{semaphore۰G : SemaphoreG Σ}.

  Implicit Type P : iProp Σ.

  #[local] Definition tokens۰auth' γ_tokens cap : iProp Σ :=
    ⌜length γ_tokens = cap⌝.
  #[local] Definition tokens۰auth γ :=
    tokens۰auth' γ.(semaphore۰name۰tokens).
  #[local] Instance : CustomIpat "tokens۰auth" :=
    " %Htokens
    ".
  #[local] Definition tokens۰frag' γ_tokens : iProp Σ :=
    ∃ i η,
    ⌜γ_tokens !! i = Some η⌝ ∗
    excl η ().
  #[local] Definition tokens۰frag γ :=
    tokens۰frag' γ.(semaphore۰name۰tokens).
  #[local] Instance : CustomIpat "tokens۰frag" :=
    " ( %i
      & %η
      & %Htokens_lookup
      & Hexcl
      )
    ".

  #[local] Definition inv۰inner γ P : iProp Σ :=
    ∃ cnt,
    γ.(semaphore۰name۰self).[count] ↦ #cnt ∗
    [∗ list] _ ∈ seq 0 ˖cnt,
      tokens۰frag γ ∗
      P.
  #[local] Instance : CustomIpat "inv۰inner" :=
    " ( %cnt
      & Hself_count
      & H
      )
    ".
  Please Definition semaphore۰inv γ cap P : iProp Σ :=
    γ.(semaphore۰name۰self).[mutex] ↦□ γ.(semaphore۰name۰mutex) ∗
    mutex۰inv γ.(semaphore۰name۰mutex) (inv۰inner γ P) ∗
    γ.(semaphore۰name۰self).[condition] ↦□ γ.(semaphore۰name۰condition) ∗
    condition۰inv γ.(semaphore۰name۰condition) ∗
    tokens۰auth γ cap.
  #[local] Instance : CustomIpat "inv" :=
    " ( #Hself_mutex
      & #Hmutex_inv
      & #Hself_condition
      & #Hcondition_inv
      & #Htokens_auth
      )
    ".

  Please Definition semaphore۰locked :=
    tokens۰frag.
  #[local] Instance : CustomIpat "locked" :=
    " Htokens_frag
    ".

  #[global] Instance semaphore۰invｰcontractive γ cap :
    Contractive (semaphore۰inv γ cap).
  Proof.
    rewrite /semaphore۰inv /inv۰inner.
    solve_contractive.
  Qed.
  #[global] Instance semaphore۰invｰne γ cap :
    NonExpansive (semaphore۰inv γ cap).
  Proof.
    apply _.
  Qed.
  #[global] Instance semaphore۰invｰproper γ cap :
    Proper ((≡) ==> (≡)) (semaphore۰inv γ cap).
  Proof.
    apply _.
  Qed.

  Zoo derive Timeless for semaphore۰locked.

  #[local] Zoo derive Persistent for tokens۰auth.
  Zoo derive Persistent for semaphore۰inv.

  #[local] Lemma tokensｰalloc cap :
    ⊢ |==>
      ∃ γ_tokens,
      tokens۰auth' γ_tokens cap ∗
      [∗ list] _ ∈ seq 0 cap, tokens۰frag' γ_tokens.
  Proof.
    iAssert (
      [∗ list] _ ∈ seq 0 cap,
        |==>
        ∃ η,
        excl (excl۰G := semaphore۰G۰tokens۰G) η ()
    )%I as "-#H".
    { iApply big_sepL_intro. iIntros "!> % % _".
      iApply exclｰalloc.
    }
    iMod (big_sepL_bupd with "H") as "H".
    iDestruct (big_sepLｰexists with "H") as "(%ηs & %Hηs & H)". simp_length in Hηs.
    iDestruct (big_sepL2ｰretractｰr with "H") as "(_ & H)".
    iApply big_sepLｰretractｰindex in "H".
    iSteps.
  Qed.
  #[local] Lemma tokens۰fragsｰvalid γ cap n :
    tokens۰auth γ cap -∗
    ([∗ list] _ ∈ seq 0 n, tokens۰frag γ) -∗
    ⌜n ≤ cap⌝.
  Proof.
    rewrite Nat.le_ngt.
    iIntros "(:tokens۰auth) Htokens_frags %Hn".
    iDestruct (big_sepLｰseqｰexists with "Htokens_frags") as "(%is & %His & Htokens_frags)".
    iDestruct (big_sepLｰexists with "Htokens_frags") as "(%ηs & %Hηs & Htokens_frags)".
    iAssert ⌜ηs ⊆ γ.(semaphore۰name۰tokens)⌝%I as %(i1 & i2 & η & ? & Htokens_lookup_1 & Htokens_lookup_2)%list_pigeonhole; last lia.
    { iIntros (η Hηs_elem).
      iDestruct (big_sepL2ｰelem_ofｰr' with "Htokens_frags") as "(%i & %His_elem & %Htokens_lookup & _)"; first done.
      rewrite list_elem_of_lookup. iSteps.
    }
    iDestruct (big_sepL2ｰdelete'ｰr i1 with "Htokens_frags") as "(%j1 & _ & (_ & Hexcl_1) & Htokens_frags)"; first done.
    iDestruct (big_sepL2ｰdelete'ｰr i2 with "Htokens_frags") as "(%j2 & _ & H & Htokens_frags)"; first done.
    iDestruct ("H" with "[%]") as "(_ & Hexcl_2)"; first lia.
    iApply (exclｰexclusive with "Hexcl_1 Hexcl_2").
  Qed.

  Opaque tokens۰auth.
  Opaque tokens۰frag.

  Lemma semaphore٠createｰspec {cap} P :
    (0 < cap)%Z →
    {{{
      [∗ list] _ ∈ seq 0 ₊cap, P
    }}}
      semaphore٠create #cap
    {{{
      γ
    , RET γ;
      semaphore۰inv γ ₊cap P
    }}}.
  Proof.
    iIntros "%Hcap %Φ HPs HΦ".

    wp۰rec.
    wp۰apply+ (condition٠createｰspec with "[//]") as (cond) "#Hcondition_inv".
    wp۰apply (mutex٠createｰspecｰinit with "[//]") as (mtx) "Hmutex_init".
    wp۰block t as "#Ht_mutex #Ht_condition Ht_count".

    iMod tokensｰalloc as "(%γ_tokens & Htokens_auth & Htokens_frags)".

    pose γ :=
      {|semaphore۰name۰self := t
      ; semaphore۰name۰mutex := mtx
      ; semaphore۰name۰condition := cond
      ; semaphore۰name۰tokens := γ_tokens
      |}.

    replace ₊cap with ˖₊(cap - 1) by lia.
    iMod (mutex۰initｰtoｰinv (inv۰inner γ P) with "Hmutex_init [Ht_count Htokens_frags HPs]") as "#Hmutex_inv".
    { iDestruct (big_sepL_sep_2 with "Htokens_frags HPs") as "H".
      iFrameSteps.
    }

    iApply ("HΦ" $! γ).
    iFrameSteps.
  Qed.

  Lemma semaphore٠try_lockｰspec γ cap P :
    {{{
      semaphore۰inv γ cap P
    }}}
      semaphore٠try_lock γ
    {{{
      b
    , RET #b;
      if b then
        semaphore۰locked γ ∗
        P
      else
        True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec. wp۰load.

    wp۰apply (mutex٠protectｰspec (λ v,
      ∃ b,
      ⌜v = #b⌝ ∗
      if b then
        tokens۰frag γ ∗
        P
      else
        True
    )%I with "[$Hmutex_inv]") as (res) "(%b & -> & H)".
    { iIntros "Hmutex_locked (:inv۰inner)".
      wp۰load. wp۰pures.
      case_bool_decide; last iSteps.
      wp۰store.
      rewrite seq_S. iDestruct (big_sepL_snoc with "H") as "(H & Htokens_frag & HP)".
      iStep 5. iSplitR "Htokens_frag HP"; last iSteps.
      replace cnt with ˖₊(⁺cnt - 1) by lia.
      iFrameSteps.
    }

    destruct b; iSteps.
  Qed.

  Lemma semaphore٠lockｰspec γ cap P :
    {{{
      semaphore۰inv γ cap P
    }}}
      semaphore٠lock γ
    {{{
      RET ();
      semaphore۰locked γ ∗
      P
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec. wp۰load.

    wp۰apply (mutex٠protectｰspec (λ v,
      ⌜v = ()%V⌝ ∗
      tokens۰frag γ ∗
      P
    )%I with "[$Hmutex_inv]"); last iSteps.
    iIntros "Hmutex_locked Hinv_inner".
    do 2 wp۰load.
    wp۰apply (condition٠wait_untilｰspec' (λ b,
      if b then
        ∃ cnt,
        ⌜0 < cnt⌝ ∗
        γ.(semaphore۰name۰self).[count] ↦ #cnt ∗
        [∗ list] _ ∈ seq 0 ˖cnt,
          tokens۰frag γ ∗
          P
      else
        True
    )%I with "[$Hcondition_inv $Hmutex_inv $Hmutex_locked $Hinv_inner]") as "(Hmutex_locked & (%cnt & %Hcnt & Hself_count & H))".
    { iIntros "!> Hmutex_locked (:inv۰inner) _".
      wp۰load. wp۰pures.
      case_bool_decide; iStepFrameSteps.
    }
    wp۰load. wp۰store.
    rewrite seq_S. iDestruct (big_sepL_snoc with "H") as "(H & Htokens_frag & HP)".
    iFrame "Hmutex_locked". iSplitR "Htokens_frag HP"; last iSteps.
    replace (⁺cnt - 1)%Z with ⁺(cnt - 1) by lia.
    replace cnt with ˖(cnt - 1) at 2 by lia.
    iSteps.
  Qed.

  Lemma semaphore٠unlockｰspec γ cap P :
    {{{
      semaphore۰inv γ cap P ∗
      semaphore۰locked γ ∗
      P
    }}}
      semaphore٠unlock γ
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & (:locked) & HP) HΦ".

    wp۰rec. wp۰load.

    wp۰apply (mutex٠protectｰspec (λ v,
      ⌜v = ()%V⌝
    )%I with "[$Hmutex_inv Htokens_frag HP]"); last iSteps.
    iIntros "Hmutex_locked (:inv۰inner)".
    wp۰load. wp۰store.
    iDestruct (big_sepLｰsnoc₂ ˖cnt with "H [$]") as "H".
    rewrite -seq_S. iFrameSteps.
  Qed.
End semaphore۰G.

Require zoo_std.semaphore__opaque.

Please opacify.
