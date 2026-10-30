Require Import zoo.prelude.
Require Import zoo.iris.base_logic.lib.oneshot.
Require Import zoo.iris.base_logic.lib.excl.
Require Import zoo.base.
Require Export zoo_std.waiter_spsc__code.
Require Import zoo_std.waiter_spsc__types.
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
  ; excl : excl unitO
  }.

Section waiter_spsc۰G.
  Context `{waiter_spsc۰G : WaiterSpscG Σ}.

  Implicit Type P : iProp Σ.

  #[local] Definition inv۰inner γ P : iProp Σ :=
    ∃ b,
    γ.(waiter_spsc۰name۰self).[flag] ↦ #b ∗
    if b then
      oneshot۰shot γ.(waiter_spsc۰name۰lstate) () ∗
      (P ∨ excl γ.(waiter_spsc۰name۰consumer) ())
    else
      oneshot۰pending γ.(waiter_spsc۰name۰lstate) (DfracOwn (1/3)) ().
  Please Definition waiter_spsc۰inv γ P : iProp Σ :=
    γ.(waiter_spsc۰name۰self).[mutex] ↦□ γ.(waiter_spsc۰name۰mutex) ∗
    mutex۰inv γ.(waiter_spsc۰name۰mutex) True ∗
    γ.(waiter_spsc۰name۰self).[condition] ↦□ γ.(waiter_spsc۰name۰condition) ∗
    condition۰inv γ.(waiter_spsc۰name۰condition) ∗
    inv nroot (inv۰inner γ P).

  Please Definition waiter_spsc۰producer γ :=
    oneshot۰pending γ.(waiter_spsc۰name۰lstate) (DfracOwn (2/3)) ().

  Please Definition waiter_spsc۰consumer γ :=
    excl γ.(waiter_spsc۰name۰consumer) ().

  Please Definition waiter_spsc۰notified γ :=
    oneshot۰shot γ.(waiter_spsc۰name۰lstate) ().

  #[global] Instance waiter_spsc۰invｰcontractive γ :
    Contractive (waiter_spsc۰inv γ).
  Proof.
    rewrite /waiter_spsc۰inv /inv۰inner.
    solve_contractive.
  Qed.
  #[global] Instance waiter_spsc۰invｰne γ :
    NonExpansive (waiter_spsc۰inv γ).
  Proof.
    apply _.
  Qed.
  #[global] Instance waiter_spsc۰invｰproper γ :
    Proper ((≡) ==> (≡)) (waiter_spsc۰inv γ).
  Proof.
    apply _.
  Qed.

  Zoo derive Timeless for waiter_spsc۰producer.
  Zoo derive Timeless for waiter_spsc۰consumer.
  Zoo derive Timeless for waiter_spsc۰notified.

  Zoo derive Persistent for waiter_spsc۰inv.
  Zoo derive Persistent for waiter_spsc۰notified.

  Lemma waiter_spsc۰producerｰexclusive γ :
    waiter_spsc۰producer γ -∗
    waiter_spsc۰producer γ -∗
    False.
  Proof.
    iIntros "Hpending1 Hpending2".
    iDestruct (oneshot۰pendingｰvalidｰ2 with "Hpending1 Hpending2") as %(? & _). done.
  Qed.

  Lemma waiter_spsc۰consumerｰexclusive γ :
    waiter_spsc۰consumer γ -∗
    waiter_spsc۰consumer γ -∗
    False.
  Proof.
    apply exclｰexclusive.
  Qed.

  Lemma waiter_spsc٠createｰspec P :
    {{{
      True
    }}}
      waiter_spsc٠create ()
    {{{
      γ
    , RET γ;
      waiter_spsc۰inv γ P ∗
      waiter_spsc۰producer γ ∗
      waiter_spsc۰consumer γ
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp۰rec.
    wp۰apply+ (condition٠createｰspec with "[//]") as "%cond #Hcondition_inv".
    wp۰apply+ (mutex٠createｰspec True with "[//]") as "%mtx #Hmutex_inv".
    wp۰block t as "#Ht_mutex #Ht_condition Ht_flag".

    iMod (oneshotｰalloc ()) as "(%γ_lstate & Hpending)".
    iEval (assert (1 = 2/3 + 1/3)%Qp as -> by compute_done) in "Hpending".
    iDestruct "Hpending" as "(Hpending1 & Hpending2)".

    iMod (exclｰalloc (excl۰G := waiter_spsc۰G۰excl۰G) ()) as "(%γ_consumer & Hconsumer)".

    pose γ :=
      {|waiter_spsc۰name۰self := t
      ; waiter_spsc۰name۰mutex := mtx
      ; waiter_spsc۰name۰condition := cond
      ; waiter_spsc۰name۰lstate := γ_lstate
      ; waiter_spsc۰name۰consumer := γ_consumer
      |}.

    iApply ("HΦ" $! γ).
    iFrameSteps.
  Qed.

  Lemma waiter_spsc٠notifyｰspec γ P :
    {{{
      waiter_spsc۰inv γ P ∗
      waiter_spsc۰producer γ ∗
      P
    }}}
      waiter_spsc٠notify γ
    {{{
      RET ();
      waiter_spsc۰notified γ
    }}}.
  Proof.
    iIntros "%Φ ((#Hself_mutex & #Hmutex_inv & #Hself_condition & #Hcondition_inv & #Hinv) & Hpending & HP) HΦ".

    wp۰rec. wp۰load.
    pose (Ψ_mtx (_ : val) := (
      oneshot۰shot γ.(waiter_spsc۰name۰lstate) ()
    )%I).
    wp۰apply (mutex٠protectｰspec Ψ_mtx with "[$Hmutex_inv Hpending HP]") as (res) "#Hshot".
    { iIntros "Hmutex_locked _".
      wp۰pures.
      wp۰bind (_ <-{flag} _)%E.
      iInv "Hinv" as "(%b & Hself_flag & Hb)".
      wp۰store.
      destruct b.
      { iDestruct "Hb" as "(Hshot & _)".
        iDestruct (oneshotｰpendingｰshot with "Hpending Hshot") as %[].
      }
      iCombine "Hpending Hb" as "Hpending".
      assert (2/3 + 1/3 = 1)%Qp as -> by compute_done.
      iMod (oneshotｰupdateｰshot with "Hpending") as "#Hshot".
      iSteps.
    }
    wp۰load.
    wp۰apply (condition٠notifyｰspec with "Hcondition_inv").
    iSteps.
  Qed.

  Lemma waiter_spsc٠try_waitｰspec γ P :
    {{{
      waiter_spsc۰inv γ P ∗
      waiter_spsc۰consumer γ
    }}}
      waiter_spsc٠try_wait γ
    {{{
      b
    , RET #b;
      if b then
        P
      else
        waiter_spsc۰consumer γ
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
  Lemma waiter_spsc٠try_waitｰspecｰnotified γ P :
    {{{
      waiter_spsc۰inv γ P ∗
      waiter_spsc۰consumer γ ∗
      waiter_spsc۰notified γ
    }}}
      waiter_spsc٠try_wait γ
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

  Lemma waiter_spsc٠waitｰspec γ P :
    {{{
      waiter_spsc۰inv γ P ∗
      waiter_spsc۰consumer γ
    }}}
      waiter_spsc٠wait γ
    {{{
      RET ();
      P
    }}}.
  Proof.
    iIntros "%Φ ((#Hself_mutex & #Hmutex_inv & #Hself_condition & #Hcondition_inv & #Hinv) & Hconsumer) HΦ".

    wp۰rec.
    wp۰apply (waiter_spsc٠try_waitｰspec with "[$]") as ([]) "Hconsumer"; first iSteps.
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
        excl γ.(waiter_spsc۰name۰consumer) ()
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
End waiter_spsc۰G.

Require zoo_std.waiter_spsc__opaque.

Please opacify.
