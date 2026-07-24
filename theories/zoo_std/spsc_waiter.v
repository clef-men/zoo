Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Import zoo.iris.base_logic.lib.oneshot.
Require Import zoo.iris.base_logic.lib.excl.
Require Import zoo.base.
Require Export zoo_std.spsc_waiter__code.
Require Import zoo_std.condition.
Require Import zoo_std.spsc_waiter__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type 𝑡 : location.

Class SpscWaiterG Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] spsc_waiter۰G۰mutex۰G :: MutexG Σ
  ; #[local] spsc_waiter۰G۰lstate۰G :: OneshotG Σ unit unit
  ; #[local] spsc_waiter۰G۰excl۰G :: ExclG Σ unitO
  }.

Definition spsc_waiter۰Σ :=
  #[mutex۰Σ
  ; oneshot۰Σ unit unit
  ; excl۰Σ unitO
  ].
#[global] Instance subG𑁒spsc_waiter۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG spsc_waiter۰Σ Σ →
  SpscWaiterG Σ .
Proof.
  solve_inG.
Qed.

Section spsc_waiter۰G.
  Context `{spsc_waiter۰G : SpscWaiterG Σ}.

  Record metadata :=
    { metadata۰mutex : val
    ; metadata۰condition : val
    ; metadata۰lstate : gname
    ; metadata۰consumer : gname
    }.
  Implicit Type γ : metadata.

  #[local] Instance metadata𑁒eq_dec : EqDecision metadata :=
    ltac:(solve_decision).
  #[local] Instance metadata𑁒countable :
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
  Definition spsc_waiter۰inv t P : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    𝑡.[mutex] ↦□ γ.(metadata۰mutex) ∗
    mutex۰inv γ.(metadata۰mutex) True ∗
    𝑡.[condition] ↦□ γ.(metadata۰condition) ∗
    condition۰inv γ.(metadata۰condition) ∗
    inv nroot (inv۰inner 𝑡 γ P).

  Definition spsc_waiter۰producer t : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    oneshot۰pending γ.(metadata۰lstate) (DfracOwn (2/3)) ().

  Definition spsc_waiter۰consumer t : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    excl γ.(metadata۰consumer) ().

  Definition spsc_waiter۰notified t : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    oneshot۰shot γ.(metadata۰lstate) ().

  #[global] Instance spsc_waiter۰inv𑁒contractive t :
    Contractive (spsc_waiter۰inv t).
  Proof.
    rewrite /spsc_waiter۰inv /inv۰inner. solve_contractive.
  Qed.
  #[global] Instance spsc_waiter۰inv𑁒ne t :
    NonExpansive (spsc_waiter۰inv t).
  Proof.
    apply _.
  Qed.
  #[global] Instance spsc_waiter۰inv𑁒proper t :
    Proper ((≡) ==> (≡)) (spsc_waiter۰inv t).
  Proof.
    apply _.
  Qed.

  #[global] Instance spsc_waiter۰producer𑁒timeless t :
    Timeless (spsc_waiter۰producer t).
  Proof.
    apply _.
  Qed.
  #[global] Instance spsc_waiter۰consumer𑁒timeless t :
    Timeless (spsc_waiter۰consumer t).
  Proof.
    apply _.
  Qed.
  #[global] Instance spsc_waiter۰notified𑁒timeless t :
    Timeless (spsc_waiter۰notified t).
  Proof.
    apply _.
  Qed.

  #[global] Instance spsc_waiter۰inv𑁒persistent t P :
    Persistent (spsc_waiter۰inv t P).
  Proof.
    apply _.
  Qed.
  #[global] Instance spsc_waiter۰notified𑁒persistent t :
    Persistent (spsc_waiter۰notified t).
  Proof.
    apply _.
  Qed.

  Lemma spsc_waiter۰producer𑁒exclusive t :
    spsc_waiter۰producer t -∗
    spsc_waiter۰producer t -∗
    False.
  Proof.
    iIntros "(%𝑡 & %γ & -> & #Hmeta & Hpending1) (%𝑡_ & %γ_ & %Heq & Hmeta_ & Hpending2)". injection Heq as <-.
    iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (oneshot۰pending𑁒valid𑁒2 with "Hpending1 Hpending2") as %(? & _). done.
  Qed.

  Lemma spsc_waiter۰consumer𑁒exclusive t :
    spsc_waiter۰consumer t -∗
    spsc_waiter۰consumer t -∗
    False.
  Proof.
    iIntros "(%𝑡 & %γ & -> & #Hmeta & Hconsumer1) (%𝑡_ & %γ_ & %Heq & Hmeta_ & Hconsumer2)". injection Heq as <-.
    iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iApply (excl𑁒exclusive with "Hconsumer1 Hconsumer2").
  Qed.

  Lemma spsc_waiter٠create𑁒spec P :
    {{{
      True
    }}}
      spsc_waiter٠create ()
    {{{
      t
    , RET t;
      spsc_waiter۰inv t P ∗
      spsc_waiter۰producer t ∗
      spsc_waiter۰consumer t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp۰rec.
    wp۰apply+ (condition٠create𑁒spec with "[//]") as "%cond #Hcondition_inv".
    wp۰apply+ (mutex٠create𑁒spec True with "[//]") as "%mtx #Hmutex_inv".
    wp۰block 𝑡 as "Hmeta" "(H𝑡_mutex & H𝑡_condition & H𝑡_flag & _)".
    iMod (pointsto𑁒persist with "H𝑡_mutex") as "H𝑡_mutex".
    iMod (pointsto𑁒persist with "H𝑡_condition") as "H𝑡_condition".

    iMod (oneshot𑁒alloc ()) as "(%γ_lstate & Hpending)".
    iEval (assert (1 = 2/3 + 1/3)%Qp as -> by compute_done) in "Hpending".
    iDestruct "Hpending" as "(Hpending1 & Hpending2)".

    iMod (excl𑁒alloc (excl۰G := spsc_waiter۰G۰excl۰G) ()) as "(%γ_consumer & Hconsumer)".

    pose γ :=
      {|metadata۰mutex := mtx
      ; metadata۰condition := cond
      ; metadata۰lstate := γ_lstate
      ; metadata۰consumer := γ_consumer
      |}.
    iMod (meta𑁒set γ with "Hmeta") as "#Hmeta"; first done.

    iSteps.
  Qed.

  Lemma spsc_waiter٠notify𑁒spec t P :
    {{{
      spsc_waiter۰inv t P ∗
      spsc_waiter۰producer t ∗
      P
    }}}
      spsc_waiter٠notify t
    {{{
      RET ();
      spsc_waiter۰notified t
    }}}.
  Proof.
    iIntros "%Φ ((%𝑡 & %γ & -> & #Hmeta & #H𝑡_mutex & #Hmutex_inv & #H𝑡_condition & #Hcondition_inv & #Hinv) & (%𝑡_ & %γ_ & %Heq & Hmeta_ & Hpending) & HP) HΦ". injection Heq as <-.
    iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp۰rec. wp۰load.
    pose (Ψ_mtx (_ : val) := (
      oneshot۰shot γ.(metadata۰lstate)  ()
    )%I).
    wp۰apply (mutex٠protect𑁒spec Ψ_mtx with "[$Hmutex_inv Hpending HP]") as (res) "#Hshot".
    { iIntros "Hmutex_locked _".
      wp۰pures.
      wp۰bind (_ <-{flag} _)%E.
      iInv "Hinv" as "(%b & H𝑡_flag & Hb)".
      wp۰store.
      destruct b.
      { iDestruct "Hb" as "(Hshot & _)".
        iDestruct (oneshot𑁒pending𑁒shot with "Hpending Hshot") as %[].
      }
      iCombine "Hpending Hb" as "Hpending".
      assert (2/3 + 1/3 = 1)%Qp as -> by compute_done.
      iMod (oneshot𑁒update𑁒shot with "Hpending") as "#Hshot".
      iSteps.
    }
    wp۰load.
    wp۰apply (condition٠notify𑁒spec with "Hcondition_inv").
    iSteps.
  Qed.

  Lemma spsc_waiter٠try_wait𑁒spec t P :
    {{{
      spsc_waiter۰inv t P ∗
      spsc_waiter۰consumer t
    }}}
      spsc_waiter٠try_wait t
    {{{
      b
    , RET #b;
      if b then
        P
      else
        spsc_waiter۰consumer t
    }}}.
  Proof.
    iIntros "%Φ ((%𝑡 & %γ & -> & #Hmeta & #H𝑡_mutex & #Hmutex_inv & #H𝑡_condition & #Hcondition_inv & #Hinv) & (%𝑡_ & %γ_ & %Heq & Hmeta_ & Hconsumer)) HΦ". injection Heq as <-.
    iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    wp۰rec. wp۰pures.

    iInv "Hinv" as "(%b & H𝑡_flag & Hb)".
    wp۰load.
    destruct b; last iSteps.
    iDestruct "Hb" as "(Hshot & [HP | Hconsumer'])"; last first.
    { iDestruct (excl𑁒exclusive with "Hconsumer Hconsumer'") as %[]. }
    iSmash.
  Qed.
  Lemma spsc_waiter٠try_wait𑁒spec𑁒notified t P :
    {{{
      spsc_waiter۰inv t P ∗
      spsc_waiter۰consumer t ∗
      spsc_waiter۰notified t
    }}}
      spsc_waiter٠try_wait t
    {{{
      RET true;
      P
    }}}.
  Proof.
    iIntros "%Φ ((%𝑡 & %γ & -> & #Hmeta & #H𝑡_mutex & #Hmutex_inv & #H𝑡_condition & #Hcondition_inv & #Hinv) & (%𝑡1 & %γ1 & %Heq1 & Hmeta_1 & Hconsumer) & (%𝑡2 & %γ2 & %Heq2 & Hmeta_2 & #Hshot)) HΦ". injection Heq1 as <-. injection Heq2 as <-.
    iDestruct (meta𑁒agree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
    iDestruct (meta𑁒agree with "Hmeta Hmeta_2") as %<-. iClear "Hmeta_2".

    wp۰rec. wp۰pures.

    iInv "Hinv" as "(%b & H𝑡_flag & Hb)".
    wp۰load.
    destruct b; last first.
    { iDestruct (oneshot𑁒pending𑁒shot with "Hb Hshot") as %[]. }
    iDestruct "Hb" as "(_ & [HP | Hconsumer'])"; last first.
    { iDestruct (excl𑁒exclusive with "Hconsumer Hconsumer'") as %[]. }
    iSmash.
  Qed.

  Lemma spsc_waiter٠wait𑁒spec t P :
    {{{
      spsc_waiter۰inv t P ∗
      spsc_waiter۰consumer t
    }}}
      spsc_waiter٠wait t
    {{{
      RET ();
      P
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & Hconsumer) HΦ".

    wp۰rec.
    wp۰apply (spsc_waiter٠try_wait𑁒spec with "[$Hinv $Hconsumer]") as ([]) "Hconsumer"; first iSteps.

    iDestruct "Hinv" as "(%𝑡 & %γ & -> & #Hmeta & #H𝑡_mutex & #Hmutex_inv & #H𝑡_condition & #Hcondition_inv & #Hinv)".
    iDestruct "Hconsumer" as "(%𝑡_ & %γ_ & %Heq & Hmeta_ & Hconsumer)". injection Heq as <-.
    iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

    do 2 wp۰load.
    pose Ψ_mtx res := (
      ⌜res = ()%V⌝ ∗
      P
    )%I.
    wp۰apply+ (mutex٠protect𑁒spec Ψ_mtx with "[$Hmutex_inv Hconsumer]"); last iSteps.
    iIntros "Hmutex_locked _".
    pose (Ψ_cond b := (
      if b then
        P
      else
        excl γ.(metadata۰consumer) ()
    )%I).
    wp۰apply+ (condition٠wait_until𑁒spec Ψ_cond with "[$Hcondition_inv $Hmutex_inv $Hmutex_locked $Hconsumer]"); last iSteps.

    iIntros "!> Hmutex_locked _ Hconsumer".
    wp۰pures.

    iInv "Hinv" as "(%b & H𝑡_flag & Hb)".
    wp۰load.
    destruct b; last iSteps.
    iDestruct "Hb" as "(Hshot & [HP | Hconsumer'])"; last first.
    { iDestruct (excl𑁒exclusive with "Hconsumer Hconsumer'") as %[]. }
    iSmash.
  Qed.
End spsc_waiter۰G.

Require zoo_std.spsc_waiter__opaque.

#[global] Opaque spsc_waiter۰inv.
#[global] Opaque spsc_waiter۰producer.
#[global] Opaque spsc_waiter۰consumer.
#[global] Opaque spsc_waiter۰notified.
