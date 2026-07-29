Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Import zoo.iris.base_logic.lib.oneshot.
Require Import zoo.iris.base_logic.lib.excl.
Require Import zoo.base.
Require Export zoo_std.mpsc_waiter__code.
Require Import zoo_std.condition.
Require Import zoo_std.mpsc_waiter__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type 𝑡 : location.

Class MpscWaiterG Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] mpsc_waiter۰G۰mutex۰G :: MutexG Σ
  ; #[local] mpsc_waiter۰G۰lstate۰G :: OneshotG Σ unit unit
  ; #[local] mpsc_waiter۰G۰consumer۰G :: ExclG Σ unitO
  }.

Definition mpsc_waiter۰Σ :=
  #[mutex۰Σ
  ; oneshot۰Σ unit unit
  ; excl۰Σ unitO
  ].
#[global] Instance subGｰmpsc_waiter۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG mpsc_waiter۰Σ Σ →
  MpscWaiterG Σ .
Proof.
  solve_inG.
Qed.

Section mpsc_waiter۰G.
  Context `{mpsc_waiter۰G : MpscWaiterG Σ}.

  Record metadata :=
    { metadata۰mutex : val
    ; metadata۰condition : val
    ; metadata۰lstate : gname
    ; metadata۰consumer : gname
    }.
  Implicit Type γ : metadata.

  #[local] Instance metadataｰeq_dec : EqDecision metadata :=
    ltac:(solve_decision).
  #[local] Instance metadataｰcountable :
    Countable metadata.
  Proof.
    solve_countable.
  Qed.

  #[local] Definition inv۰inner 𝑡 γ P : iProp Σ :=
    ∃ b,
    𝑡.[flag] ↦ #b ∗
    if b then
      oneshot۰shot γ.(metadata۰lstate) () ∗
      (P ∨ excl γ.(metadata۰consumer) ())
    else
      oneshot۰pending γ.(metadata۰lstate) (DfracOwn 1) ().
  Definition mpsc_waiter۰inv t P : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    𝑡.[mutex] ↦□ γ.(metadata۰mutex) ∗
    mutex۰inv γ.(metadata۰mutex) True ∗
    𝑡.[condition] ↦□ γ.(metadata۰condition) ∗
    condition۰inv γ.(metadata۰condition) ∗
    inv nroot (inv۰inner 𝑡 γ P).

  Definition mpsc_waiter۰consumer t : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    excl γ.(metadata۰consumer) ().

  Definition mpsc_waiter۰notified t : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    oneshot۰shot γ.(metadata۰lstate) ().

  #[global] Instance mpsc_waiter۰invｰcontractive t :
    Contractive (mpsc_waiter۰inv t).
  Proof.
    rewrite /mpsc_waiter۰inv /inv۰inner. solve_contractive.
  Qed.
  #[global] Instance mpsc_waiter۰invｰne t :
    NonExpansive (mpsc_waiter۰inv t).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpsc_waiter۰invｰproper t :
    Proper ((≡) ==> (≡)) (mpsc_waiter۰inv t).
  Proof.
    apply _.
  Qed.

  #[global] Instance mpsc_waiter۰consumerｰtimeless t :
    Timeless (mpsc_waiter۰consumer t).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpsc_waiter۰notifiedｰtimeless t :
    Timeless (mpsc_waiter۰notified t).
  Proof.
    apply _.
  Qed.

  #[global] Instance mpsc_waiter۰invｰpersistent t P :
    Persistent (mpsc_waiter۰inv t P).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpsc_waiter۰notifiedｰpersistent t :
    Persistent (mpsc_waiter۰notified t).
  Proof.
    apply _.
  Qed.

  Lemma mpsc_waiter۰consumerｰexclusive t :
    mpsc_waiter۰consumer t -∗
    mpsc_waiter۰consumer t -∗
    False.
  Proof.
    iIntros "(%𝑡 & %γ & -> & #Hmeta & Hconsumer1) (%𝑡_ & %γ_ & %Heq & Hmeta_ & Hconsumer2)". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iApply (exclｰexclusive with "Hconsumer1 Hconsumer2").
  Qed.

  Lemma mpsc_waiter٠createｰspec P :
    {{{
      True
    }}}
      mpsc_waiter٠create ()
    {{{
      t
    , RET t;
      mpsc_waiter۰inv t P ∗
      mpsc_waiter۰consumer t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp۰rec.
    wp۰apply+ (condition٠createｰspec with "[//]") as "%cond #Hcondition_inv".
    wp۰apply+ (mutex٠createｰspec True with "[//]") as "%mtx #Hmutex_inv".
    wp۰block 𝑡 as "Hmeta" "(H𝑡_mutex & H𝑡_condition & H𝑡_flag & _)".
    iMod (pointstoｰpersist with "H𝑡_mutex") as "H𝑡_mutex".
    iMod (pointstoｰpersist with "H𝑡_condition") as "H𝑡_condition".

    iMod (oneshotｰalloc ()) as "(%γ_lstate & Hpending)".

    iMod (exclｰalloc (excl۰G := mpsc_waiter۰G۰consumer۰G) ()) as "(%γ_consumer & Hconsumer)".

    pose γ :=
      {|metadata۰mutex := mtx
      ; metadata۰condition := cond
      ; metadata۰lstate := γ_lstate
      ; metadata۰consumer := γ_consumer
      |}.
    iMod (metaｰset γ with "Hmeta") as "#Hmeta"; first done.

    iSteps.
  Qed.

  Lemma mpsc_waiter٠notifyｰspec t P :
    {{{
      mpsc_waiter۰inv t P ∗
      P
    }}}
      mpsc_waiter٠notify t
    {{{
      b
    , RET #b;
      mpsc_waiter۰notified t
    }}}.
  Proof.
    iIntros "%Φ ((%𝑡 & %γ & -> & #Hmeta & #H𝑡_mutex & #Hmutex_inv & #H𝑡_condition & #Hcondition_inv & #Hinv) & HP) HΦ".

    wp۰rec. wp۰pures.

    wp۰bind (_.{flag})%E.
    iInv "Hinv" as "(%b & H𝑡_flag & Hb)".
    wp۰load.
    destruct b; first iSteps.
    iSplitR "HP HΦ". { iFrameSteps. }
    iModIntro.

    wp۰load.
    pose (Ψ_mtx res := (
      ∃ b,
      ⌜res = #b⌝ ∗
      oneshot۰shot γ.(metadata۰lstate)  ()
    )%I).
    wp۰apply+ (mutex٠protectｰspec Ψ_mtx with "[$Hmutex_inv HP]"); last iSteps.
    iIntros "Hmutex_locked _".
    wp۰pures.

    wp۰bind (_.{flag})%E.
    iInv "Hinv" as "(%b & H𝑡_flag & Hb)".
    wp۰load.
    destruct b; first iSteps.
    iSplitR "HP Hmutex_locked". { iFrameSteps. }
    iModIntro.

    wp۰pures.

    wp۰bind (_ <-{flag} _)%E.
    iInv "Hinv" as "(%b & H𝑡_flag & Hb)".
    wp۰store.
    destruct b; first iSteps.
    iMod (oneshotｰupdateｰshot with "Hb") as "#Hshot".
    iSteps.
  Qed.

  Lemma mpsc_waiter٠try_waitｰspec t P :
    {{{
      mpsc_waiter۰inv t P ∗
      mpsc_waiter۰consumer t
    }}}
      mpsc_waiter٠try_wait t
    {{{
      b
    , RET #b;
      if b then
        P
      else
        mpsc_waiter۰consumer t
    }}}.
  Proof.
    iIntros "%Φ ((%𝑡 & %γ & -> & #Hmeta & #H𝑡_mutex & #Hmutex_inv & #H𝑡_condition & #Hcondition_inv & #Hinv) & (%𝑡_ & %γ_ & %Heq & Hmeta_ & Hconsumer)) HΦ". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp۰rec. wp۰pures.

    iInv "Hinv" as "(%b & H𝑡_flag & Hb)".
    wp۰load.
    destruct b; last iSteps.
    iDestruct "Hb" as "(Hshot & [HP | Hconsumer'])"; last first.
    { iDestruct (exclｰexclusive with "Hconsumer Hconsumer'") as %[]. }
    iSmash.
  Qed.
  Lemma mpsc_waiter٠try_waitｰspecｰnotified t P :
    {{{
      mpsc_waiter۰inv t P ∗
      mpsc_waiter۰consumer t ∗
      mpsc_waiter۰notified t
    }}}
      mpsc_waiter٠try_wait t
    {{{
      RET true;
      P
    }}}.
  Proof.
    iIntros "%Φ ((%𝑡 & %γ & -> & #Hmeta & #H𝑡_mutex & #Hmutex_inv & #H𝑡_condition & #Hcondition_inv & #Hinv) & (%𝑡1 & %γ1 & %Heq1 & Hmeta_1 & Hconsumer) & (%𝑡2 & %γ2 & %Heq2 & Hmeta_2 & #Hshot)) HΦ". injection Heq1 as <-. injection Heq2 as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
    iDestruct (metaｰagree with "Hmeta Hmeta_2") as %<-. iClear "Hmeta_2".

    wp۰rec. wp۰pures.

    iInv "Hinv" as "(%b & H𝑡_flag & Hb)".
    wp۰load.
    destruct b; last first.
    { iDestruct (oneshotｰpendingｰshot with "Hb Hshot") as %[]. }
    iDestruct "Hb" as "(_ & [HP | Hconsumer'])"; last first.
    { iDestruct (exclｰexclusive with "Hconsumer Hconsumer'") as %[]. }
    iSmash.
  Qed.

  Lemma mpsc_waiter٠waitｰspec t P :
    {{{
      mpsc_waiter۰inv t P ∗
      mpsc_waiter۰consumer t
    }}}
      mpsc_waiter٠wait t
    {{{
      RET ();
      P
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & Hconsumer) HΦ".

    wp۰rec.
    wp۰apply (mpsc_waiter٠try_waitｰspec with "[$Hinv $Hconsumer]") as ([]) "Hconsumer"; first iSteps.

    iDestruct "Hinv" as "(%𝑡 & %γ & -> & #Hmeta & #H𝑡_mutex & #Hmutex_inv & #H𝑡_condition & #Hcondition_inv & #Hinv)".
    iDestruct "Hconsumer" as "(%𝑡_ & %γ_ & %Heq & Hmeta_ & Hconsumer)". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

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
        excl γ.(metadata۰consumer) ()
    )%I).
    wp۰apply+ (condition٠wait_untilｰspec Ψ_cond with "[$Hcondition_inv $Hmutex_inv $Hmutex_locked $Hconsumer]"); last iSteps.

    iIntros "!> Hmutex_locked _ Hconsumer".
    wp۰pures.

    iInv "Hinv" as "(%b & H𝑡_flag & Hb)".
    wp۰load.
    destruct b; last iSteps.
    iDestruct "Hb" as "(Hshot & [HP | Hconsumer'])"; last first.
    { iDestruct (exclｰexclusive with "Hconsumer Hconsumer'") as %[]. }
    iSmash.
  Qed.
End mpsc_waiter۰G.

Require zoo_std.mpsc_waiter__opaque.

#[global] Opaque mpsc_waiter۰inv.
#[global] Opaque mpsc_waiter۰consumer.
#[global] Opaque mpsc_waiter۰notified.
