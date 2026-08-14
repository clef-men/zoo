Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Import zoo.iris.base_logic.lib.oneshot.
Require Import zoo.iris.base_logic.lib.excl.
Require Import zoo.base.
Require Export zoo_std.waiter_spsc__code.
Require Import zoo_std.waiter_spsc__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type 𝑡 : location.

Class WaiterSpscG Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] waiter_spsc۰G۰mutex۰G :: MutexG Σ
  ; #[local] waiter_spsc۰G۰lstate۰G :: OneshotG Σ unit unit
  ; #[local] waiter_spsc۰G۰excl۰G :: ExclG Σ unitO
  }.

Definition waiter_spsc۰Σ :=
  #[mutex۰Σ
  ; oneshot۰Σ unit unit
  ; excl۰Σ unitO
  ].
#[global] Instance subGｰwaiter_spsc۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG waiter_spsc۰Σ Σ →
  WaiterSpscG Σ .
Proof.
  solve_inG.
Qed.

Section waiter_spsc۰G.
  Context `{waiter_spsc۰G : WaiterSpscG Σ}.

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
      oneshot۰pending γ.(metadata۰lstate) (DfracOwn (1/3)) ().
  Definition waiter_spsc۰inv t P : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    𝑡.[mutex] ↦□ γ.(metadata۰mutex) ∗
    mutex۰inv γ.(metadata۰mutex) True ∗
    𝑡.[condition] ↦□ γ.(metadata۰condition) ∗
    condition۰inv γ.(metadata۰condition) ∗
    inv nroot (inv۰inner 𝑡 γ P).

  Definition waiter_spsc۰producer t : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    oneshot۰pending γ.(metadata۰lstate) (DfracOwn (2/3)) ().

  Definition waiter_spsc۰consumer t : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    excl γ.(metadata۰consumer) ().

  Definition waiter_spsc۰notified t : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    oneshot۰shot γ.(metadata۰lstate) ().

  #[global] Instance waiter_spsc۰invｰcontractive t :
    Contractive (waiter_spsc۰inv t).
  Proof.
    rewrite /waiter_spsc۰inv /inv۰inner. solve_contractive.
  Qed.
  #[global] Instance waiter_spsc۰invｰne t :
    NonExpansive (waiter_spsc۰inv t).
  Proof.
    apply _.
  Qed.
  #[global] Instance waiter_spsc۰invｰproper t :
    Proper ((≡) ==> (≡)) (waiter_spsc۰inv t).
  Proof.
    apply _.
  Qed.

  #[global] Instance waiter_spsc۰producerｰtimeless t :
    Timeless (waiter_spsc۰producer t).
  Proof.
    apply _.
  Qed.
  #[global] Instance waiter_spsc۰consumerｰtimeless t :
    Timeless (waiter_spsc۰consumer t).
  Proof.
    apply _.
  Qed.
  #[global] Instance waiter_spsc۰notifiedｰtimeless t :
    Timeless (waiter_spsc۰notified t).
  Proof.
    apply _.
  Qed.

  #[global] Instance waiter_spsc۰invｰpersistent t P :
    Persistent (waiter_spsc۰inv t P).
  Proof.
    apply _.
  Qed.
  #[global] Instance waiter_spsc۰notifiedｰpersistent t :
    Persistent (waiter_spsc۰notified t).
  Proof.
    apply _.
  Qed.

  Lemma waiter_spsc۰producerｰexclusive t :
    waiter_spsc۰producer t -∗
    waiter_spsc۰producer t -∗
    False.
  Proof.
    iIntros "(%𝑡 & %γ & -> & #Hmeta & Hpending1) (%𝑡_ & %γ_ & %Heq & Hmeta_ & Hpending2)". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (oneshot۰pendingｰvalidｰ2 with "Hpending1 Hpending2") as %(? & _). done.
  Qed.

  Lemma waiter_spsc۰consumerｰexclusive t :
    waiter_spsc۰consumer t -∗
    waiter_spsc۰consumer t -∗
    False.
  Proof.
    iIntros "(%𝑡 & %γ & -> & #Hmeta & Hconsumer1) (%𝑡_ & %γ_ & %Heq & Hmeta_ & Hconsumer2)". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iApply (exclｰexclusive with "Hconsumer1 Hconsumer2").
  Qed.

  Lemma waiter_spsc٠createｰspec P :
    {{{
      True
    }}}
      waiter_spsc٠create ()
    {{{
      t
    , RET t;
      waiter_spsc۰inv t P ∗
      waiter_spsc۰producer t ∗
      waiter_spsc۰consumer t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp۰rec.
    wp۰apply+ (condition٠createｰspec with "[//]") as "%cond #Hcondition_inv".
    wp۰apply+ (mutex٠createｰspec True with "[//]") as "%mtx #Hmutex_inv".
    wp۰block 𝑡 as "Hmeta" "#H𝑡_mutex #H𝑡_condition H𝑡_flag".

    iMod (oneshotｰalloc ()) as "(%γ_lstate & Hpending)".
    iEval (assert (1 = 2/3 + 1/3)%Qp as -> by compute_done) in "Hpending".
    iDestruct "Hpending" as "(Hpending1 & Hpending2)".

    iMod (exclｰalloc (excl۰G := waiter_spsc۰G۰excl۰G) ()) as "(%γ_consumer & Hconsumer)".

    pose γ :=
      {|metadata۰mutex := mtx
      ; metadata۰condition := cond
      ; metadata۰lstate := γ_lstate
      ; metadata۰consumer := γ_consumer
      |}.
    iMod (metaｰset γ with "Hmeta") as "#Hmeta"; first done.

    iSteps.
  Qed.

  Lemma waiter_spsc٠notifyｰspec t P :
    {{{
      waiter_spsc۰inv t P ∗
      waiter_spsc۰producer t ∗
      P
    }}}
      waiter_spsc٠notify t
    {{{
      RET ();
      waiter_spsc۰notified t
    }}}.
  Proof.
    iIntros "%Φ ((%𝑡 & %γ & -> & #Hmeta & #H𝑡_mutex & #Hmutex_inv & #H𝑡_condition & #Hcondition_inv & #Hinv) & (%𝑡_ & %γ_ & %Heq & Hmeta_ & Hpending) & HP) HΦ". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp۰rec. wp۰load.
    pose (Ψ_mtx (_ : val) := (
      oneshot۰shot γ.(metadata۰lstate)  ()
    )%I).
    wp۰apply (mutex٠protectｰspec Ψ_mtx with "[$Hmutex_inv Hpending HP]") as (res) "#Hshot".
    { iIntros "Hmutex_locked _".
      wp۰pures.
      wp۰bind (_ <-{flag} _)%E.
      iInv "Hinv" as "(%b & H𝑡_flag & Hb)".
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

  Lemma waiter_spsc٠try_waitｰspec t P :
    {{{
      waiter_spsc۰inv t P ∗
      waiter_spsc۰consumer t
    }}}
      waiter_spsc٠try_wait t
    {{{
      b
    , RET #b;
      if b then
        P
      else
        waiter_spsc۰consumer t
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
  Lemma waiter_spsc٠try_waitｰspecｰnotified t P :
    {{{
      waiter_spsc۰inv t P ∗
      waiter_spsc۰consumer t ∗
      waiter_spsc۰notified t
    }}}
      waiter_spsc٠try_wait t
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

  Lemma waiter_spsc٠waitｰspec t P :
    {{{
      waiter_spsc۰inv t P ∗
      waiter_spsc۰consumer t
    }}}
      waiter_spsc٠wait t
    {{{
      RET ();
      P
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & Hconsumer) HΦ".

    wp۰rec.
    wp۰apply (waiter_spsc٠try_waitｰspec with "[$Hinv $Hconsumer]") as ([]) "Hconsumer"; first iSteps.

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
End waiter_spsc۰G.

Require zoo_std.waiter_spsc__opaque.

#[global] Opaque waiter_spsc۰inv.
#[global] Opaque waiter_spsc۰producer.
#[global] Opaque waiter_spsc۰consumer.
#[global] Opaque waiter_spsc۰notified.
