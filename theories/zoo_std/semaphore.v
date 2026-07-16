Require Import stdpp.finite.

Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Import zoo.iris.bi.big_op.
Require Import zoo.iris.base_logic.lib.excl.
Require Import zoo.base.
Require Export zoo_std.semaphore__code.
Require Import zoo_std.semaphore__types.
Require Import zoo_std.condition.
Require Import zoo.options.

Implicit Types b : bool.
Implicit Types cnt : nat.
Implicit Types l : location.
Implicit Types t : val.

Class SemaphoreG Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] semaphore۰G۰mutex۰G :: MutexG Σ
  ; #[local] semaphore۰G۰tokens۰G :: ExclG Σ unitO
  }.

Definition semaphore۰Σ :=
  #[mutex۰Σ
  ; excl۰Σ unitO
  ].
#[global] Instance subG𑁒semaphore۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG semaphore۰Σ Σ →
  SemaphoreG Σ.
Proof.
  solve_inG.
Qed.

Section semaphore۰G.
  Context `{semaphore۰G : SemaphoreG Σ}.

  Implicit Types P : iProp Σ.

  Record metadata :=
    { metadata۰mutex : val
    ; metadata۰condition : val
    ; metadata۰tokens : list gname
    }.
  Implicit Types γ : metadata.
  Implicit Types γ_tokens : list gname.

  #[local] Instance metadata𑁒eq_dec : EqDecision metadata :=
    ltac:(solve_decision).
  #[local] Instance metadata𑁒countable :
    Countable metadata.
  Proof.
    solve_countable.
  Qed.

  #[local] Definition tokens۰auth' γ_tokens cap : iProp Σ :=
    ⌜length γ_tokens = cap⌝.
  #[local] Definition tokens۰auth γ :=
    tokens۰auth' γ.(metadata۰tokens).
  #[local] Instance : CustomIpat "tokens۰auth" :=
    " %Htokens
    ".
  #[local] Definition tokens۰frag' γ_tokens : iProp Σ :=
    ∃ i η,
    ⌜γ_tokens !! i = Some η⌝ ∗
    excl η ().
  #[local] Definition tokens۰frag γ :=
    tokens۰frag' γ.(metadata۰tokens).
  #[local] Instance : CustomIpat "tokens۰frag" :=
    " ( %i
      & %η
      & %Htokens_lookup
      & Hexcl
      )
    ".

  #[local] Definition inv۰inner l γ P : iProp Σ :=
    ∃ cnt,
    l.[count] ↦ #cnt ∗
    [∗ list] _ ∈ seq 0 ˖cnt,
      tokens۰frag γ ∗
      P.
  #[local] Instance : CustomIpat "inv۰inner" :=
    " ( %cnt
      & Hl_count
      & H
      )
    ".
  Definition semaphore۰inv t cap P : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    l ↪ γ ∗
    l.[mutex] ↦□ γ.(metadata۰mutex) ∗
    mutex۰inv γ.(metadata۰mutex) (inv۰inner l γ P) ∗
    l.[condition] ↦□ γ.(metadata۰condition) ∗
    condition۰inv γ.(metadata۰condition) ∗
    tokens۰auth γ cap.
  #[local] Instance : CustomIpat "inv" :=
    " ( %l
      & %γ
      & ->
      & #Hmeta
      & #Hl_mutex
      & #Hmutex_inv
      & #Hl_condition
      & #Hcondition_inv
      & #Htokens_auth
      )
    ".

  Definition semaphore۰locked t : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    l ↪ γ ∗
    tokens۰frag γ.
  #[local] Instance : CustomIpat "locked" :=
    " ( %l_
      & %γ_
      & %Heq
      & #Hmeta_
      & Htokens_frag
      )
    ".

  #[global] Instance semaphore۰inv𑁒contractive t cap :
    Contractive (semaphore۰inv t cap).
  Proof.
    rewrite /semaphore۰inv /inv۰inner.
    solve_contractive.
  Qed.
  #[global] Instance semaphore۰inv𑁒ne t cap :
    NonExpansive (semaphore۰inv t cap).
  Proof.
    apply _.
  Qed.
  #[global] Instance semaphore۰inv𑁒proper t cap :
    Proper ((≡) ==> (≡)) (semaphore۰inv t cap).
  Proof.
    apply _.
  Qed.

  #[global] Instance semaphore۰locked𑁒timeless t :
    Timeless (semaphore۰locked t).
  Proof.
    apply _.
  Qed.

  #[local] Instance tokens۰auth𑁒persistent γ cap :
    Persistent (tokens۰auth γ cap).
  Proof.
    apply _.
  Qed.
  #[global] Instance semaphore۰inv𑁒persistent t cap P :
    Persistent (semaphore۰inv t cap P).
  Proof.
    apply _.
  Qed.

  #[local] Lemma tokens𑁒alloc cap :
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
      iApply excl𑁒alloc.
    }
    iMod (big_sepL_bupd with "H") as "H".
    iDestruct (big_sepL𑁒exists with "H") as "(%ηs & %Hηs & H)". simpl_length in Hηs.
    iDestruct (big_sepL2𑁒retract𑁒r with "H") as "(_ & H)".
    iDestruct (big_sepL𑁒retract𑁒index with "H") as "H".
    iSteps.
  Qed.
  #[local] Lemma tokens۰frags𑁒valid γ cap n :
    tokens۰auth γ cap -∗
    ([∗ list] _ ∈ seq 0 n, tokens۰frag γ) -∗
    ⌜n ≤ cap⌝.
  Proof.
    rewrite Nat.le_ngt.
    iIntros "(:tokens۰auth) Htokens_frags %Hn".
    iDestruct (big_sepL𑁒seq𑁒exists with "Htokens_frags") as "(%is & %His & Htokens_frags)".
    iDestruct (big_sepL𑁒exists with "Htokens_frags") as "(%ηs & %Hηs & Htokens_frags)".
    iAssert ⌜ηs ⊆ γ.(metadata۰tokens)⌝%I as %(i1 & i2 & η & ? & Htokens_lookup_1 & Htokens_lookup_2)%list_pigeonhole; last lia.
    { iIntros (η Hηs_elem).
      iDestruct (big_sepL2𑁒elem_of𑁒r' with "Htokens_frags") as "(%i & %His_elem & %Htokens_lookup & _)"; first done.
      rewrite list_elem_of_lookup. iSteps.
    }
    iDestruct (big_sepL2𑁒delete'𑁒r i1 with "Htokens_frags") as "(%j1 & _ & (_ & Hexcl_1) & Htokens_frags)"; first done.
    iDestruct (big_sepL2𑁒delete'𑁒r i2 with "Htokens_frags") as "(%j2 & _ & H & Htokens_frags)"; first done.
    iDestruct ("H" with "[%]") as "(_ & Hexcl_2)"; first lia.
    iApply (excl𑁒exclusive with "Hexcl_1 Hexcl_2").
  Qed.

  Opaque tokens۰auth.
  Opaque tokens۰frag.

  Lemma semaphore٠create𑁒spec {cap} P :
    (0 < cap)%Z →
    {{{
      [∗ list] _ ∈ seq 0 ₊cap, P
    }}}
      semaphore٠create #cap
    {{{
      t
    , RET t;
      semaphore۰inv t ₊cap P
    }}}.
  Proof.
    iIntros "%Hcap %Φ HPs HΦ".

    wp۰rec.
    wp۰apply+ (condition٠create𑁒spec with "[//]") as (cond) "#Hcondition_inv".
    wp۰apply (mutex٠create𑁒spec𑁒init with "[//]") as (mtx) "Hmutex_init".
    wp۰block l as "Hmeta" "(Hl_mutex & Hl_condition & Hl_count & _)".
    iMod (pointsto𑁒persist with "Hl_mutex") as "#Hl_mutex".
    iMod (pointsto𑁒persist with "Hl_condition") as "#Hl_condition".

    iMod tokens𑁒alloc as "(%γ_tokens & Htokens_auth & Htokens_frags)".

    pose γ :=
      {|metadata۰mutex := mtx
      ; metadata۰condition := cond
      ; metadata۰tokens := γ_tokens
      |}.
    iMod (meta𑁒set γ with "Hmeta") as "#Hmeta"; first done.

    replace ₊cap with ˖₊(cap - 1) by lia.
    iMod (mutex۰init𑁒to𑁒inv (inv۰inner l γ P) with "Hmutex_init [Hl_count Htokens_frags HPs]") as "#Hmutex_inv".
    { iDestruct (big_sepL_sep_2 with "Htokens_frags HPs") as "H".
      iFrameSteps.
    }
    iSteps.
  Qed.

  Lemma semaphore٠try_lock𑁒spec t cap P :
    {{{
      semaphore۰inv t cap P
    }}}
      semaphore٠try_lock t
    {{{
      b
    , RET #b;
      if b then
        semaphore۰locked t ∗
        P
      else
        True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec. wp۰load.

    wp۰apply (mutex٠protect𑁒spec (λ v,
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

  Lemma semaphore٠lock𑁒spec t cap P :
    {{{
      semaphore۰inv t cap P
    }}}
      semaphore٠lock t
    {{{
      RET ();
      semaphore۰locked t ∗
      P
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec. wp۰load.

    wp۰apply (mutex٠protect𑁒spec (λ v,
      ⌜v = ()%V⌝ ∗
      tokens۰frag γ ∗
      P
    )%I with "[$Hmutex_inv]"); last iSteps.
    iIntros "Hmutex_locked Hinv_inner".
    do 2 wp۰load.
    wp۰apply (condition٠wait_until𑁒spec' (λ b,
      if b then
        ∃ cnt,
        ⌜0 < cnt⌝ ∗
        l.[count] ↦ #cnt ∗
        [∗ list] _ ∈ seq 0 ˖cnt,
          tokens۰frag γ ∗
          P
      else
        True
    )%I with "[$Hcondition_inv $Hmutex_inv $Hmutex_locked $Hinv_inner]") as "(Hmutex_locked & (%cnt & %Hcnt & Hl_count & H))".
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

  Lemma semaphore٠unlock𑁒spec t cap P :
    {{{
      semaphore۰inv t cap P ∗
      semaphore۰locked t ∗
      P
    }}}
      semaphore٠unlock t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & (:locked) & HP) HΦ". injection Heq as <-.
    iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp۰rec. wp۰load.

    wp۰apply (mutex٠protect𑁒spec (λ v,
      ⌜v = ()%V⌝
    )%I with "[$Hmutex_inv Htokens_frag HP]"); last iSteps.
    iIntros "Hmutex_locked (:inv۰inner)".
    wp۰load. wp۰store.
    iDestruct (big_sepL𑁒snoc₂ ˖cnt with "H [$]") as "H".
    rewrite -seq_S. iFrameSteps.
  Qed.
End semaphore۰G.

Require zoo_std.semaphore__opaque.

#[global] Opaque semaphore۰inv.
#[global] Opaque semaphore۰locked.
