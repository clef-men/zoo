Require Import zoo.prelude.
Require Import zoo.iris.base_logic.lib.oneshot.
Require Import zoo.iris.base_logic.lib.excl.
Require Import zoo.base.
Require Export zoo_std.waiter_mpsc__code.
Require Import zoo_std.waiter_mpsc__types.
Require Import zoo.options.

Implicit Type b : bool.

Zoo name :=
  { self : location
  ; mutex : val
  ; condition : val
  ; lstate : gname
  ; consumer : gname
  }.

Zoo global :=
  { mutex : mutex
  ; lstate : oneshot unit unit
  ; consumer : excl unitO
  }.

Section waiter_mpsc۰G.
  Context `{waiter_mpsc۰G : WaiterMpscG Σ}.

  #[local] Definition inv۰inner γ P : iProp Σ :=
    ∃ b,
    γ.(waiter_mpsc۰name۰self).[flag] ↦ #b ∗
    if b then
      oneshot۰shot γ.(waiter_mpsc۰name۰lstate) () ∗
      (P ∨ excl γ.(waiter_mpsc۰name۰consumer) ())
    else
      oneshot۰pending γ.(waiter_mpsc۰name۰lstate) (DfracOwn 1) ().
  Please Definition waiter_mpsc۰inv γ P : iProp Σ :=
    γ.(waiter_mpsc۰name۰self).[mutex] ↦□ γ.(waiter_mpsc۰name۰mutex) ∗
    mutex۰inv γ.(waiter_mpsc۰name۰mutex) True ∗
    γ.(waiter_mpsc۰name۰self).[condition] ↦□ γ.(waiter_mpsc۰name۰condition) ∗
    condition۰inv γ.(waiter_mpsc۰name۰condition) ∗
    inv nroot (inv۰inner γ P).

  Please Definition waiter_mpsc۰consumer γ :=
    excl γ.(waiter_mpsc۰name۰consumer) ().

  Please Definition waiter_mpsc۰notified γ :=
    oneshot۰shot γ.(waiter_mpsc۰name۰lstate) ().

  #[global] Instance waiter_mpsc۰invｰcontractive γ :
    Contractive (waiter_mpsc۰inv γ).
  Proof.
    rewrite /waiter_mpsc۰inv /inv۰inner.
    solve_contractive.
  Qed.
  #[global] Instance waiter_mpsc۰invｰne γ :
    NonExpansive (waiter_mpsc۰inv γ).
  Proof.
    apply _.
  Qed.
  #[global] Instance waiter_mpsc۰invｰproper γ :
    Proper ((≡) ==> (≡)) (waiter_mpsc۰inv γ).
  Proof.
    apply _.
  Qed.

  Zoo derive Timeless for waiter_mpsc۰consumer.
  Zoo derive Timeless for waiter_mpsc۰notified.

  Zoo derive Persistent for waiter_mpsc۰inv.
  Zoo derive Persistent for waiter_mpsc۰notified.

  Lemma waiter_mpsc۰consumerｰexclusive γ :
    waiter_mpsc۰consumer γ -∗
    waiter_mpsc۰consumer γ -∗
    False.
  Proof.
    apply exclｰexclusive.
  Qed.

  Lemma waiter_mpsc٠createｰspec P :
    {{{
      True
    }}}
      waiter_mpsc٠create ()
    {{{
      γ
    , RET γ;
      waiter_mpsc۰inv γ P ∗
      waiter_mpsc۰consumer γ
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp۰rec.
    wp۰apply+ (condition٠createｰspec with "[//]") as "%cond #Hcondition_inv".
    wp۰apply+ (mutex٠createｰspec True with "[//]") as "%mtx #Hmutex_inv".
    wp۰block t as "#Ht_mutex #Ht_condition Ht_flag".

    iMod (oneshotｰalloc ()) as "(%γ_lstate & Hpending)".

    iMod (exclｰalloc (excl۰G := waiter_mpsc۰G۰consumer۰G) ()) as "(%γ_consumer & Hconsumer)".

    pose γ :=
      {|waiter_mpsc۰name۰self := t
      ; waiter_mpsc۰name۰mutex := mtx
      ; waiter_mpsc۰name۰condition := cond
      ; waiter_mpsc۰name۰lstate := γ_lstate
      ; waiter_mpsc۰name۰consumer := γ_consumer
      |}.

    iApply ("HΦ" $! γ).
    iFrameSteps.
  Qed.

  Lemma waiter_mpsc٠notifyｰspec γ P :
    {{{
      waiter_mpsc۰inv γ P ∗
      P
    }}}
      waiter_mpsc٠notify γ
    {{{
      b
    , RET #b;
      waiter_mpsc۰notified γ
    }}}.
  Proof.
    iIntros "%Φ ((#Hself_mutex & #Hmutex_inv & #Hself_condition & #Hcondition_inv & #Hinv) & HP) HΦ".

    wp۰rec. wp۰pures.

    wp۰bind (_.{flag})%E.
    iInv "Hinv" as "(%b & Hself_flag & Hb)".
    wp۰load.
    destruct b; first iSteps.
    iSplitR "HP HΦ". { iFrameSteps. }
    iModIntro.

    wp۰load.
    pose (Ψ_mtx res := (
      ∃ b,
      ⌜res = #b⌝ ∗
      oneshot۰shot γ.(waiter_mpsc۰name۰lstate) ()
    )%I).
    wp۰apply+ (mutex٠protectｰspec Ψ_mtx with "[$Hmutex_inv HP]"); last iSteps.
    iIntros "Hmutex_locked _".
    wp۰pures.

    wp۰bind (_.{flag})%E.
    iInv "Hinv" as "(%b & Hself_flag & Hb)".
    wp۰load.
    destruct b; first iSteps.
    iSplitR "HP Hmutex_locked". { iFrameSteps. }
    iModIntro.

    wp۰pures.

    wp۰bind (_ <-{flag} _)%E.
    iInv "Hinv" as "(%b & Hself_flag & Hb)".
    wp۰store.
    destruct b; first iSteps.
    iMod (oneshotｰupdateｰshot with "Hb") as "#Hshot".
    iSteps.
  Qed.

  Lemma waiter_mpsc٠try_waitｰspec γ P :
    {{{
      waiter_mpsc۰inv γ P ∗
      waiter_mpsc۰consumer γ
    }}}
      waiter_mpsc٠try_wait γ
    {{{
      b
    , RET #b;
      if b then
        P
      else
        waiter_mpsc۰consumer γ
    }}}.
  Proof.
    iIntros "%Φ ((#Hself_mutex & #Hmutex_inv & #Hself_condition & #Hcondition_inv & #Hinv) & Hconsumer) HΦ".

    wp۰rec. wp۰pures.

    iInv "Hinv" as "(%b & Hself_flag & Hb)".
    wp۰load.
    destruct b; last iSteps.
    iDestruct "Hb" as "(Hshot & [HP | Hconsumer'])"; last first.
    { iDestruct (exclｰexclusive with "Hconsumer Hconsumer'") as %[]. }
    iSmash.
  Qed.
  Lemma waiter_mpsc٠try_waitｰspecｰnotified γ P :
    {{{
      waiter_mpsc۰inv γ P ∗
      waiter_mpsc۰consumer γ ∗
      waiter_mpsc۰notified γ
    }}}
      waiter_mpsc٠try_wait γ
    {{{
      RET true;
      P
    }}}.
  Proof.
    iIntros "%Φ ((#Hself_mutex & #Hmutex_inv & #Hself_condition & #Hcondition_inv & #Hinv) & Hconsumer & #Hshot) HΦ".

    wp۰rec. wp۰pures.

    iInv "Hinv" as "(%b & Hself_flag & Hb)".
    wp۰load.
    destruct b; last first.
    { iDestruct (oneshotｰpendingｰshot with "Hb Hshot") as %[]. }
    iDestruct "Hb" as "(_ & [HP | Hconsumer'])"; last first.
    { iDestruct (exclｰexclusive with "Hconsumer Hconsumer'") as %[]. }
    iSmash.
  Qed.

  Lemma waiter_mpsc٠waitｰspec γ P :
    {{{
      waiter_mpsc۰inv γ P ∗
      waiter_mpsc۰consumer γ
    }}}
      waiter_mpsc٠wait γ
    {{{
      RET ();
      P
    }}}.
  Proof.
    iIntros "%Φ ((#Hself_mutex & #Hmutex_inv & #Hself_condition & #Hcondition_inv & #Hinv) & Hconsumer) HΦ".

    wp۰rec.
    wp۰apply (waiter_mpsc٠try_waitｰspec with "[$]") as ([]) "Hconsumer"; first iSteps.
    do 2 wp۰load.

    pose Ψ_mtx res := (
      ⌜res = ()%V⌝ ∗
      P
    )%I.
    wp۰apply+ (mutex٠protectｰspec Ψ_mtx with "[$Hmutex_inv Hconsumer]"); last iSteps.
    iIntros "Hmutex_locked _".
    pose (Ψ_cond b := (
      if b then
        P
      else
        excl γ.(waiter_mpsc۰name۰consumer) ()
    )%I).
    wp۰apply+ (condition٠wait_untilｰspec Ψ_cond with "[$Hcondition_inv $Hmutex_inv $Hmutex_locked $Hconsumer]"); last iSteps.

    iIntros "!> Hmutex_locked _ Hconsumer".
    wp۰pures.

    iInv "Hinv" as "(%b & Hself_flag & Hb)".
    wp۰load.
    destruct b; last iSteps.
    iDestruct "Hb" as "(Hshot & [HP | Hconsumer'])"; last first.
    { iDestruct (exclｰexclusive with "Hconsumer Hconsumer'") as %[]. }
    iSmash.
  Qed.
End waiter_mpsc۰G.

Require zoo_std.waiter_mpsc__opaque.

Please opacify.
