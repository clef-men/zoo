From zebre Require Import
  prelude.
From zebre.iris.base_logic Require Import
  lib.oneshot
  lib.excl.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Import
  condition.
From zebre.saturn Require Export
  base.
From zebre Require Import
  options.

Implicit Types b : bool.
Implicit Types l : location.

#[local] Notation "'flag'" := (
  in_type "t" 0
)(in custom zebre_field
).
#[local] Notation "'mutex'" := (
  in_type "t" 1
)(in custom zebre_field
).
#[local] Notation "'condition'" := (
  in_type "t" 2
)(in custom zebre_field
).

Definition spsc_latch1_create : val :=
  λ: <>,
    let: "t" := { #false; (); () } in
    "t" <-{mutex} mutex_create () ;;
    "t" <-{condition} condition_create () ;;
    "t".

Definition spsc_latch1_signal : val :=
  λ: "t",
    mutex_protect "t".{mutex} (λ: <>,
      "t" <-{flag} #true
    ) ;;
    condition_signal "t".{condition}.

Definition spsc_latch1_wait : val :=
  λ: "t",
    let: "mtx" := "t".{mutex} in
    let: "cond" := "t".{condition} in
    mutex_protect "mtx" (λ: <>,
      condition_wait_until "cond" "mtx" (λ: <>, "t".{flag})
    ).

Class SpscLatch1G Σ `{zebre_G : !ZebreG Σ} := {
  #[local] spsc_latch1_G_mutex_G :: MutexG Σ ;
  #[local] spsc_latch1_G_producer_G :: OneshotG Σ unit unit ;
  #[local] spsc_latch1_G_consumer_G :: ExclG Σ unitO ;
}.

Definition spsc_latch1_Σ := #[
  mutex_Σ ;
  oneshot_Σ unit unit ;
  excl_Σ unitO
].
#[global] Instance subG_spsc_latch1_Σ Σ `{zebre_G : !ZebreG Σ} :
  subG spsc_latch1_Σ Σ →
  SpscLatch1G Σ .
Proof.
  solve_inG.
Qed.

Section spsc_latch1_G.
  Context `{spsc_latch1_G : SpscLatch1G Σ}.

  Record spsc_latch1_meta := {
    spsc_latch1_meta_producer : gname ;
    spsc_latch1_meta_consumer : gname ;
  }.
  Implicit Types γ : spsc_latch1_meta.

  #[local] Instance spsc_latch1_meta_eq_dec : EqDecision spsc_latch1_meta :=
    ltac:(solve_decision).
  #[local] Instance spsc_latch1_meta_countable :
    Countable spsc_latch1_meta.
  Proof.
    pose encode γ := (
      γ.(spsc_latch1_meta_producer),
      γ.(spsc_latch1_meta_consumer)
    ).
    pose decode := λ '(γ_producer, γ_consumer), {|
      spsc_latch1_meta_producer := γ_producer ;
      spsc_latch1_meta_consumer := γ_consumer ;
    |}.
    refine (inj_countable' encode decode _). intros []. done.
  Qed.

  #[local] Definition spsc_latch1_inv_inner l γ P : iProp Σ :=
    ∃ b,
    l.[flag] ↦ #b ∗
    if b then
      oneshot_shot γ.(spsc_latch1_meta_producer) () ∗
      (P ∨ excl γ.(spsc_latch1_meta_consumer) ())
    else
      oneshot_pending γ.(spsc_latch1_meta_producer) (DfracOwn (1/3)) ().
  #[local] Definition spsc_latch1_inv t P : iProp Σ :=
    ∃ l γ mtx cond,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    l.[mutex] ↦□ mtx ∗
    mutex_inv mtx (spsc_latch1_inv_inner l γ P) ∗
    l.[condition] ↦□ cond ∗
    condition_inv cond.

  Definition spsc_latch1_producer t : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    oneshot_pending γ.(spsc_latch1_meta_producer) (DfracOwn (2/3)) ().

  Definition spsc_latch1_consumer t : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    excl γ.(spsc_latch1_meta_consumer) ().

  #[global] Instance spsc_latch1_inv_persistent t P :
    Persistent (spsc_latch1_inv t P).
  Proof.
    apply _.
  Qed.
  #[global] Instance spsc_latch1_producer_timeless t :
    Timeless (spsc_latch1_producer t).
  Proof.
    apply _.
  Qed.
  #[global] Instance spsc_latch1_consumer_timeless t :
    Timeless (spsc_latch1_consumer t).
  Proof.
    apply _.
  Qed.

  Lemma spsc_latch1_producer_exclusive t :
    spsc_latch1_producer t -∗
    spsc_latch1_producer t -∗
    False.
  Proof.
    iIntros "(%l & %γ & -> & #Hmeta & Hpending) (%_l & %_γ & %Heq & _Hmeta & Hpending')". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iDestruct (oneshot_pending_valid_2 with "Hpending Hpending'") as %(? & _). done.
  Qed.

  Lemma spsc_latch1_consumer_exclusive t :
    spsc_latch1_consumer t -∗
    spsc_latch1_consumer t -∗
    False.
  Proof.
    iIntros "(%l & %γ & -> & #Hmeta & Hexcl) (%_l & %_γ & %Heq & _Hmeta & Hexcl')". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iDestruct (excl_exclusive with "Hexcl Hexcl'") as %[].
  Qed.

  Lemma spsc_latch1_create_spec P :
    {{{ True }}}
      spsc_latch1_create ()
    {{{ t,
      RET t;
      spsc_latch1_inv t P ∗
      spsc_latch1_producer t ∗
      spsc_latch1_consumer t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_rec.

    wp_record l as "Hmeta" "(Hflag & Hmtx & Hcond & _)".

    iMod (oneshot_alloc ()) as "(%γ_producer & Hpending)".
    iEval (assert (1 = 2/3 + 1/3)%Qp as -> by compute_done) in "Hpending".
    iDestruct "Hpending" as "(Hpending1 & Hpending2)".

    iMod (excl_alloc (excl_G := spsc_latch1_G_consumer_G) ()) as "(%γ_consumer & Hexcl)".

    pose γ := {|
      spsc_latch1_meta_producer := γ_producer ;
      spsc_latch1_meta_consumer := γ_consumer ;
    |}.
    iMod (meta_set _ _ γ nroot with "Hmeta") as "#Hmeta"; first done.

    wp_smart_apply (mutex_create_spec (spsc_latch1_inv_inner l γ P) with "[Hflag Hpending2]") as "%mtx #Hmtx_inv"; first iSteps.
    wp_store.
    iMod (pointsto_persist with "Hmtx") as "Hmtx".

    wp_smart_apply (condition_create_spec _ with "[//]") as "%cond #Hcond_inv".
    wp_store.
    iMod (pointsto_persist with "Hcond") as "Hcond".

    iSteps.
  Qed.

  Lemma spsc_latch1_signal_spec t P :
    {{{
      spsc_latch1_inv t P ∗
      spsc_latch1_producer t ∗
      P
    }}}
      spsc_latch1_signal t
    {{{
      RET (); True
    }}}.
  Proof.
    iIntros "%Φ ((%l & %γ & %mtx & %cond & -> & #Hmeta & #Hmtx & #Hmtx_inv & #Hcond & #Hcond_inv) & (%_l & %_γ & %Heq & _Hmeta & Hpending) & HP) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    wp_rec.
    wp_load.
    wp_apply (mutex_protect_spec (λ _, True%I) with "[$Hmtx_inv Hpending HP]") as "% _".
    { iIntros "Hmtx_locked (%b & Hflag & Hb)". destruct b.
      - iDestruct "Hb" as "(Hshot & _)".
        iDestruct (oneshot_pending_shot with "Hpending Hshot") as %[].
      - iCombine "Hpending Hb" as "Hpending".
        assert (2/3 + 1/3 = 1)%Qp as -> by compute_done.
        iMod (oneshot_update_shot with "Hpending") as "Hshot".
        iSteps.
    }
    wp_load.
    wp_apply (condition_signal_spec with "Hcond_inv").
    iSteps.
  Qed.

  Lemma spsc_latch1_wait_spec t P :
    {{{
      spsc_latch1_inv t P ∗
      spsc_latch1_consumer t
    }}}
      spsc_latch1_wait t
    {{{
      RET ();
      P
    }}}.
  Proof.
    iIntros "%Φ ((%l & %γ & %mtx & %cond & -> & #Hmeta & #Hmtx & #Hmtx_inv & #Hcond & #Hcond_inv) & (%_l & %_γ & %Heq & _Hmeta & Hexcl)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    wp_rec.
    do 2 wp_load.
    wp_smart_apply (mutex_protect_spec (λ res, ⌜res = ()%V⌝ ∗ P)%I with "[$Hmtx_inv Hexcl]").
    { iIntros "Hmtx_locked Hsignal_inv".
      pose (Ψ b := (
        if b then
          P
        else
          excl γ.(spsc_latch1_meta_consumer) ()
      )%I).
      wp_smart_apply (condition_wait_until_spec Ψ with "[$Hcond_inv $Hmtx_inv $Hmtx_locked $Hsignal_inv $Hexcl]").
      { clear. iStep 15 as (Φ b) "Hb Hexcl Hflag".
        destruct b; last iSteps.
        iDestruct "Hb" as "(Hshot & [Hmodel | Hexcl'])"; first iSmash.
        iDestruct (excl_exclusive with "Hexcl Hexcl'") as %[].
      }
      iSteps.
    }
    iSteps.
  Qed.
End spsc_latch1_G.

#[global] Opaque spsc_latch1_create.
#[global] Opaque spsc_latch1_wait.
#[global] Opaque spsc_latch1_signal.

#[global] Opaque spsc_latch1_inv.
#[global] Opaque spsc_latch1_producer.
#[global] Opaque spsc_latch1_consumer.