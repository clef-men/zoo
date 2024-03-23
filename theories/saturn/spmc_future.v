From zebre Require Import
  prelude.
From zebre.iris.base_logic Require Import
  lib.oneshot
  lib.excl.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Import
  opt
  condition.
From zebre.saturn Require Export
  base.
From zebre Require Import
  options.

Implicit Types b : bool.
Implicit Types l : location.
Implicit Types o : option val.

#[local] Notation "'result'" := (
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

Definition spmc_future_create : val :=
  λ: <>,
    { §None;
      mutex_create ();
      condition_create ()
    }.

Definition spmc_future_set : val :=
  λ: "t" "v",
    "t" <-{result} ‘Some{ "v" } ;;
    condition_broadcast "t".{condition}.

Definition spmc_future_try_get : val :=
  λ: "t",
    "t".{result}.

Definition spmc_future_get : val :=
  λ: "t",
    match: spmc_future_try_get "t" with
    | Some "v" =>
        "v"
    | None =>
        let: "mtx" := "t".{mutex} in
        let: "cond" := "t".{condition} in
        mutex_protect "mtx" (λ: <>,
          condition_wait_while "cond" "mtx" (λ: <>, "t".{result} = §None)
        ) ;;
        let: ‘Some "v" := "t".{result} in
        "v"
    end.

Class SpmcFutureG Σ `{zebre_G : !ZebreG Σ} := {
  #[local] spmc_future_G_mutex_G :: MutexG Σ ;
  #[local] spmc_future_G_lstate_G :: OneshotG Σ unit val ;
}.

Definition spmc_future_Σ := #[
  mutex_Σ ;
  oneshot_Σ unit val
].
#[global] Instance subG_spmc_future_Σ Σ `{zebre_G : !ZebreG Σ} :
  subG spmc_future_Σ Σ →
  SpmcFutureG Σ .
Proof.
  solve_inG.
Qed.

Section spmc_future_G.
  Context `{spmc_future_G : SpmcFutureG Σ}.

  #[local] Definition spmc_future_inv_inner l γ Ψ : iProp Σ :=
    ∃ o,
    l.[result] ↦ o ∗
    match o with
    | Some v =>
        oneshot_shot γ v ∗
        □ Ψ v
    | None =>
        oneshot_pending γ (DfracOwn (1/3)) ()
    end.
  Definition spmc_future_inv t Ψ : iProp Σ :=
    ∃ l γ mtx cond,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    l.[mutex] ↦□ mtx ∗
    mutex_inv mtx True ∗
    l.[condition] ↦□ cond ∗
    condition_inv cond ∗
    inv nroot (spmc_future_inv_inner l γ Ψ).

  Definition spmc_future_producer t : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    oneshot_pending γ (DfracOwn (2/3)) ().

  Definition spmc_future_result t v : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    oneshot_shot γ v.

  #[global] Instance spmc_future_inv_contractive t n :
    Proper ((pointwise_relation _ (dist_later n)) ==> (≡{n}≡)) (spmc_future_inv t).
  Proof.
    rewrite /spmc_future_inv /spmc_future_inv_inner. solve_contractive.
  Qed.
  #[global] Instance spmc_future_inv_proper t :
    Proper ((pointwise_relation _ (≡)) ==> (≡)) (spmc_future_inv t).
  Proof.
    intros Ψ1 Ψ2 HΨ.
    apply equiv_dist => n.
    apply spmc_future_inv_contractive => v.
    dist_later_intro.
    apply equiv_dist, HΨ.
  Qed.

  #[global] Instance spmc_future_inv_persistent t Ψ :
    Persistent (spmc_future_inv t Ψ).
  Proof.
    apply _.
  Qed.
  #[global] Instance spmc_future_result_persistent t v :
    Persistent (spmc_future_result t v).
  Proof.
    apply _.
  Qed.
  #[global] Instance spmc_future_producer_timeless t :
    Timeless (spmc_future_producer t).
  Proof.
    apply _.
  Qed.
  #[global] Instance spmc_future_result_timeless t v :
    Timeless (spmc_future_result t v).
  Proof.
    apply _.
  Qed.

  Lemma spmc_future_producer_exclusive t :
    spmc_future_producer t -∗
    spmc_future_producer t -∗
    False.
  Proof.
    iIntros "(%l & %γ & -> & #Hmeta & Hpending1) (%_l & %_γ & %Heq & _Hmeta & Hpending2)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iDestruct (oneshot_pending_valid_2 with "Hpending1 Hpending2") as %(? & _). done.
  Qed.

  Lemma spmc_future_create_spec Ψ :
    {{{ True }}}
      spmc_future_create ()
    {{{ t,
      RET t;
      spmc_future_inv t Ψ ∗
      spmc_future_producer t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_rec.
    wp_smart_apply (mutex_create_spec True with "[//]") as "%mtx #Hmtx_inv".
    wp_smart_apply (condition_create_spec _ with "[//]") as "%cond #Hcond_inv".
    wp_record l as "Hmeta" "(Hresult & Hmtx & Hcond & _)".
    iMod (pointsto_persist with "Hmtx") as "Hmtx".
    iMod (pointsto_persist with "Hcond") as "Hcond".

    iMod (oneshot_alloc ()) as "(%γ & Hpending)".
    iEval (assert (1 = 2/3 + 1/3)%Qp as -> by compute_done) in "Hpending".
    iDestruct "Hpending" as "(Hpending1 & Hpending2)".

    iMod (meta_set _ _ γ with "Hmeta") as "#Hmeta"; first done.

    iSteps. iExists None. iSteps.
  Qed.

  Lemma spmc_future_set_spec t Ψ v :
    {{{
      spmc_future_inv t Ψ ∗
      spmc_future_producer t ∗
      □ Ψ v
    }}}
      spmc_future_set t v
    {{{
      RET ();
      spmc_future_result t v
    }}}.
  Proof.
    iIntros "%Φ ((%l & %γ & %mtx & %cond & -> & #Hmeta & #Hmtx & #Hmtx_inv & #Hcond & #Hcond_inv & #Hinv) & (%_l & %_γ & %Heq & _Hmeta & Hpending) & HΨ) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".

    wp_rec.
    wp_pures.

    wp_bind (_ <- _)%E.
    iInv "Hinv" as "(%o & Hresult & Ho)".
    wp_store.
    destruct o.
    { iDestruct "Ho" as "(Hshot & _)".
      iDestruct (oneshot_pending_shot with "Hpending Hshot") as %[].
    }
    iCombine "Hpending Ho" as "Hpending".
    assert (2/3 + 1/3 = 1)%Qp as -> by compute_done.
    iMod (oneshot_update_shot with "Hpending") as "#Hshot".
    iSplitR "HΦ". { iExists (Some _). iSteps. }
    iModIntro.

    wp_load.
    wp_apply (condition_signal_spec with "Hcond_inv").
    iSteps.
  Qed.

  Lemma spmc_future_try_get_spec_result t Ψ v :
    {{{
      spmc_future_inv t Ψ ∗
      spmc_future_result t v
    }}}
      spmc_future_try_get t
    {{{
      RET Some v : val;
      Ψ v
    }}}.
  Proof.
    iIntros "%Φ ((%l & %γ & %mtx & %cond & -> & #Hmeta & #Hmtx & #Hmtx_inv & #Hcond & #Hcond_inv & #Hinv) & (%_l & %_γ & %Heq & _Hmeta & #Hshot)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".

    wp_rec.
    wp_pures.

    iInv "Hinv" as "(%o & Hresult & Ho)".
    wp_load.
    destruct o; last first.
    { iDestruct (oneshot_pending_shot with "Ho Hshot") as %[]. }
    iDestruct "Ho" as "(_Hshot & #HΨ)".
    iDestruct (oneshot_shot_agree with "Hshot _Hshot") as %<-. iClear "_Hshot".
    iSplitR "HΦ". { iExists (Some _). iSteps. }
    iSteps.
  Qed.
  Lemma spmc_future_try_get_spec t Ψ :
    {{{
      spmc_future_inv t Ψ
    }}}
      spmc_future_try_get t
    {{{ o,
      RET o : val;
      from_option Ψ True o
    }}}.
  Proof.
    iIntros "%Φ (%l & %γ & %mtx & %cond & -> & #Hmeta & #Hmtx & #Hmtx_inv & #Hcond & #Hcond_inv & #Hinv) HΦ".

    wp_rec.
    wp_pures.

    iInv "Hinv" as "(%o & Hresult & Ho)".
    wp_load.
    destruct o as [v |].

    - iDestruct "Ho" as "(Hshot & #HΨ)".
      iSplitR "HΦ". { iExists (Some _). iSteps. }
      iModIntro.

      iApply ("HΦ" $! (Some _) with "HΨ").

    - iSplitR "HΦ". { iExists None. iSteps. }
      iModIntro.

      iApply ("HΦ" $! None).
      iSteps.
  Qed.

  Lemma spmc_future_get_spec t Ψ :
    {{{
      spmc_future_inv t Ψ
    }}}
      spmc_future_get t
    {{{ v,
      RET v;
      Ψ v
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".

    wp_rec.
    wp_apply (spmc_future_try_get_spec with "Hinv") as ([]) "HΨ"; first iSteps.
    iClear "HΨ".

    iDestruct "Hinv" as "(%l & %γ & %mtx & %cond & -> & #Hmeta & #Hmtx & #Hmtx_inv & #Hcond & #Hcond_inv & #Hinv)".

    do 2 wp_load.
    pose (Ψ_mtx (_ : val) := (
      ∃ v,
      oneshot_shot γ v
    )%I).
    wp_smart_apply (mutex_protect_spec Ψ_mtx with "[$Hmtx_inv]") as (w) "(%v & #Hshot)".
    { iIntros "Hmtx_locked _".
      pose (Ψ_cond b := (
        if b then
          True
        else
          ∃ v,
          oneshot_shot γ v
      )%I).
      wp_smart_apply (condition_wait_while_spec Ψ_cond with "[$Hcond_inv $Hmtx_inv $Hmtx_locked]"); last auto.

      iStep. clear. iIntros "!> %Φ (Hmtx_locked & _) HΦ".
      wp_pures.

      wp_bind (!_)%E.
      iInv "Hinv" as "(%o & Hresult & Ho)".
      wp_load.
      destruct o as [v |].

      - iDestruct "Ho" as "(#Hshot & HΨ)"; last first.
        iSplitR "Hmtx_locked HΦ". { iExists (Some _). iSteps. }
        iSteps.

      - iSplitR "Hmtx_locked HΦ". { iExists None. iSteps. }
        iSteps.
    }
    wp_pures.

    wp_bind (!_)%E.
    iInv "Hinv" as "(%o & Hresult & Ho)".
    wp_load.
    destruct o; last first.
    { iDestruct (oneshot_pending_shot with "Ho Hshot") as %[]. }
    iDestruct "Ho" as "(_Hshot & #HΨ)".
    iDestruct (oneshot_shot_agree with "Hshot _Hshot") as %<-. iClear "_Hshot".
    iSplitR "HΦ". { iExists (Some _). iSteps. }
    iSteps.
  Qed.
End spmc_future_G.

#[global] Opaque spmc_future_create.
#[global] Opaque spmc_future_set.
#[global] Opaque spmc_future_try_get.
#[global] Opaque spmc_future_get.

#[global] Opaque spmc_future_inv.
#[global] Opaque spmc_future_producer.
#[global] Opaque spmc_future_result.
