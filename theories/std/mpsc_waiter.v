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
From zebre.std Require Export
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

Definition mpsc_waiter_create : val :=
  λ: <>,
    { #false;
      mutex_create ();
      condition_create ()
    }.

Definition mpsc_waiter_signal : val :=
  λ: "t",
    if: "t".{flag} then (
      #true
    ) else (
      let: "res" :=
        mutex_protect "t".{mutex} (λ: <>,
          if: "t".{flag} then (
            #true
          ) else (
            "t" <-{flag} #true ;;
            #false
          )
        )
      in
      condition_broadcast "t".{condition} ;;
      "res"
    ).

Definition mpsc_waiter_try_wait : val :=
  λ: "t",
    "t".{flag}.

Definition mpsc_waiter_wait : val :=
  λ: "t",
    ifnot: mpsc_waiter_try_wait "t" then (
      let: "mtx" := "t".{mutex} in
      let: "cond" := "t".{condition} in
      mutex_protect "mtx" (λ: <>,
        condition_wait_until "cond" "mtx" (λ: <>, "t".{flag})
      )
    ).

Class MpscWaiterG Σ `{zebre_G : !ZebreG Σ} := {
  #[local] mpsc_waiter_G_mutex_G :: MutexG Σ ;
  #[local] mpsc_waiter_G_lstate_G :: OneshotG Σ unit unit ;
  #[local] mpsc_waiter_G_consumer_G :: ExclG Σ unitO ;
}.

Definition mpsc_waiter_Σ := #[
  mutex_Σ ;
  oneshot_Σ unit unit ;
  excl_Σ unitO
].
#[global] Instance subG_mpsc_waiter_Σ Σ `{zebre_G : !ZebreG Σ} :
  subG mpsc_waiter_Σ Σ →
  MpscWaiterG Σ .
Proof.
  solve_inG.
Qed.

Section mpsc_waiter_G.
  Context `{mpsc_waiter_G : MpscWaiterG Σ}.

  Record mpsc_waiter_meta := {
    mpsc_waiter_meta_lstate : gname ;
    mpsc_waiter_meta_consumer : gname ;
  }.
  Implicit Types γ : mpsc_waiter_meta.

  #[local] Instance mpsc_waiter_meta_eq_dec : EqDecision mpsc_waiter_meta :=
    ltac:(solve_decision).
  #[local] Instance mpsc_waiter_meta_countable :
    Countable mpsc_waiter_meta.
  Proof.
    pose encode γ := (
      γ.(mpsc_waiter_meta_lstate),
      γ.(mpsc_waiter_meta_consumer)
    ).
    pose decode := λ '(γ_lstate, γ_consumer), {|
      mpsc_waiter_meta_lstate := γ_lstate ;
      mpsc_waiter_meta_consumer := γ_consumer ;
    |}.
    refine (inj_countable' encode decode _). intros []. done.
  Qed.

  #[local] Definition mpsc_waiter_inv_inner l γ P : iProp Σ :=
    ∃ b,
    l.[flag] ↦ #b ∗
    if b then
      oneshot_shot γ.(mpsc_waiter_meta_lstate) () ∗
      (P ∨ excl γ.(mpsc_waiter_meta_consumer) ())
    else
      oneshot_pending γ.(mpsc_waiter_meta_lstate) (DfracOwn 1) ().
  Definition mpsc_waiter_inv t P : iProp Σ :=
    ∃ l γ mtx cond,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    l.[mutex] ↦□ mtx ∗
    mutex_inv mtx True ∗
    l.[condition] ↦□ cond ∗
    condition_inv cond ∗
    inv nroot (mpsc_waiter_inv_inner l γ P).

  Definition mpsc_waiter_consumer t : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    excl γ.(mpsc_waiter_meta_consumer) ().

  Definition mpsc_waiter_signaled t : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    oneshot_shot γ.(mpsc_waiter_meta_lstate) ().

  #[global] Instance mpsc_waiter_inv_contractive t :
    Contractive (mpsc_waiter_inv t).
  Proof.
    rewrite /mpsc_waiter_inv /mpsc_waiter_inv_inner. solve_contractive.
  Qed.
  #[global] Instance mpsc_waiter_inv_ne t :
    NonExpansive (mpsc_waiter_inv t).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpsc_waiter_inv_proper t :
    Proper ((≡) ==> (≡)) (mpsc_waiter_inv t).
  Proof.
    apply _.
  Qed.

  #[global] Instance mpsc_waiter_inv_persistent t P :
    Persistent (mpsc_waiter_inv t P).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpsc_waiter_signaled_persistent t :
    Persistent (mpsc_waiter_signaled t).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpsc_waiter_consumer_timeless t :
    Timeless (mpsc_waiter_consumer t).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpsc_waiter_signaled_timeless t :
    Timeless (mpsc_waiter_signaled t).
  Proof.
    apply _.
  Qed.

  Lemma mpsc_waiter_consumer_exclusive t :
    mpsc_waiter_consumer t -∗
    mpsc_waiter_consumer t -∗
    False.
  Proof.
    iIntros "(%l & %γ & -> & #Hmeta & Hconsumer1) (%_l & %_γ & %Heq & _Hmeta & Hconsumer2)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iApply (excl_exclusive with "Hconsumer1 Hconsumer2").
  Qed.

  Lemma mpsc_waiter_create_spec P :
    {{{ True }}}
      mpsc_waiter_create ()
    {{{ t,
      RET t;
      mpsc_waiter_inv t P ∗
      mpsc_waiter_consumer t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_rec.
    wp_smart_apply (mutex_create_spec True with "[//]") as "%mtx #Hmtx_inv".
    wp_smart_apply (condition_create_spec _ with "[//]") as "%cond #Hcond_inv".
    wp_record l as "Hmeta" "(Hflag & Hmtx & Hcond & _)".
    iMod (pointsto_persist with "Hmtx") as "Hmtx".
    iMod (pointsto_persist with "Hcond") as "Hcond".

    iMod (oneshot_alloc ()) as "(%γ_lstate & Hpending)".

    iMod (excl_alloc (excl_G := mpsc_waiter_G_consumer_G) ()) as "(%γ_consumer & Hconsumer)".

    pose γ := {|
      mpsc_waiter_meta_lstate := γ_lstate ;
      mpsc_waiter_meta_consumer := γ_consumer ;
    |}.
    iMod (meta_set _ _ γ with "Hmeta") as "#Hmeta"; first done.

    iSteps.
  Qed.

  Lemma mpsc_waiter_signal_spec t P :
    {{{
      mpsc_waiter_inv t P ∗
      P
    }}}
      mpsc_waiter_signal t
    {{{ b,
      RET #b;
      mpsc_waiter_signaled t
    }}}.
  Proof.
    iIntros "%Φ ((%l & %γ & %mtx & %cond & -> & #Hmeta & #Hmtx & #Hmtx_inv & #Hcond & #Hcond_inv & #Hinv) & HP) HΦ".

    wp_rec.
    wp_pures.

    wp_bind (!_)%E.
    iInv "Hinv" as "(%b & Hflag & Hb)".
    wp_load.
    destruct b; first iSteps.
    iSplitR "HP HΦ"; first iSteps.
    iModIntro.

    wp_load.
    pose (Ψ_mtx res := (
      ∃ b,
      ⌜res = #b⌝ ∗
      oneshot_shot γ.(mpsc_waiter_meta_lstate)  ()
    )%I).
    wp_smart_apply (mutex_protect_spec Ψ_mtx with "[$Hmtx_inv HP]"); last first.
    { iSteps. iModIntro.
      wp_apply (condition_broadcast_spec with "Hcond_inv").
      iSteps.
    }
    iIntros "Hmtx_locked _".
    wp_pures.

    wp_bind (!_)%E.
    iInv "Hinv" as "(%b & Hflag & Hb)".
    wp_load.
    destruct b; first iSteps.
    iSplitR "HP Hmtx_locked"; first iSteps.
    iModIntro.

    wp_pures.

    wp_bind (_ <- _)%E.
    iInv "Hinv" as "(%b & Hflag & Hb)".
    wp_store.
    destruct b; first iSteps.
    iMod (oneshot_update_shot with "Hb") as "#Hshot".
    iSteps.
  Qed.

  Lemma mpsc_waiter_try_wait_spec_signaled t P :
    {{{
      mpsc_waiter_inv t P ∗
      mpsc_waiter_consumer t ∗
      mpsc_waiter_signaled t
    }}}
      mpsc_waiter_try_wait t
    {{{
      RET #true;
      P
    }}}.
  Proof.
    iIntros "%Φ ((%l & %γ & %mtx & %cond & -> & #Hmeta & #Hmtx & #Hmtx_inv & #Hcond & #Hcond_inv & #Hinv) & (%_l1 & %_γ1 & %Heq1 & _Hmeta1 & Hconsumer) & (%_l2 & %_γ2 & %Heq2 & _Hmeta2 & #Hshot)) HΦ". injection Heq1 as <-. injection Heq2 as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta1") as %<-. iClear "_Hmeta1".
    iDestruct (meta_agree with "Hmeta _Hmeta2") as %<-. iClear "_Hmeta2".

    wp_rec.
    wp_pures.

    iInv "Hinv" as "(%b & Hflag & Hb)".
    wp_load.
    destruct b; last first.
    { iDestruct (oneshot_pending_shot with "Hb Hshot") as %[]. }
    iDestruct "Hb" as "(_ & [HP | Hconsumer'])"; last first.
    { iDestruct (excl_exclusive with "Hconsumer Hconsumer'") as %[]. }
    iSmash.
  Qed.
  Lemma mpsc_waiter_try_wait_spec t P :
    {{{
      mpsc_waiter_inv t P ∗
      mpsc_waiter_consumer t
    }}}
      mpsc_waiter_try_wait t
    {{{ b,
      RET #b;
      if b then
        P
      else
        mpsc_waiter_consumer t
    }}}.
  Proof.
    iIntros "%Φ ((%l & %γ & %mtx & %cond & -> & #Hmeta & #Hmtx & #Hmtx_inv & #Hcond & #Hcond_inv & #Hinv) & (%_l & %_γ & %Heq & _Hmeta & Hconsumer)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".

    wp_rec.
    wp_pures.

    iInv "Hinv" as "(%b & Hflag & Hb)".
    wp_load.
    destruct b; last iSteps.
    iDestruct "Hb" as "(Hshot & [HP | Hconsumer'])"; last first.
    { iDestruct (excl_exclusive with "Hconsumer Hconsumer'") as %[]. }
    iSmash.
  Qed.

  Lemma mpsc_waiter_wait_spec t P :
    {{{
      mpsc_waiter_inv t P ∗
      mpsc_waiter_consumer t
    }}}
      mpsc_waiter_wait t
    {{{
      RET ();
      P
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & Hconsumer) HΦ".

    wp_rec.
    wp_apply (mpsc_waiter_try_wait_spec with "[$Hinv $Hconsumer]") as ([]) "Hconsumer"; first iSteps.

    iDestruct "Hinv" as "(%l & %γ & %mtx & %cond & -> & #Hmeta & #Hmtx & #Hmtx_inv & #Hcond & #Hcond_inv & #Hinv)".
    iDestruct "Hconsumer" as "(%_l & %_γ & %Heq & _Hmeta & Hconsumer)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".

    do 2 wp_load.
    pose Ψ_mtx res := (
      ⌜res = ()%V⌝ ∗
      P
    )%I.
    wp_smart_apply (mutex_protect_spec Ψ_mtx with "[$Hmtx_inv Hconsumer]"); last iSteps.
    iIntros "Hmtx_locked _".
    pose (Ψ_cond b := (
      if b then
        P
      else
        excl γ.(mpsc_waiter_meta_consumer) ()
    )%I).
    wp_smart_apply (condition_wait_until_spec Ψ_cond with "[$Hcond_inv $Hmtx_inv $Hmtx_locked $Hconsumer]"); last iSteps.

    clear. iIntros "!> %Φ (Hmtx_locked & _ & Hconsumer) HΦ".
    wp_pures.

    iInv "Hinv" as "(%b & Hflag & Hb)".
    wp_load.
    destruct b; last iSteps.
    iDestruct "Hb" as "(Hshot & [HP | Hconsumer'])"; last first.
    { iDestruct (excl_exclusive with "Hconsumer Hconsumer'") as %[]. }
    iSmash.
  Qed.
End mpsc_waiter_G.

#[global] Opaque mpsc_waiter_create.
#[global] Opaque mpsc_waiter_signal.
#[global] Opaque mpsc_waiter_try_wait.
#[global] Opaque mpsc_waiter_wait.

#[global] Opaque mpsc_waiter_inv.
#[global] Opaque mpsc_waiter_consumer.
#[global] Opaque mpsc_waiter_signaled.
