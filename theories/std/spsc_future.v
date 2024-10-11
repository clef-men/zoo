From zoo Require Import
  prelude.
From zoo.iris.base_logic Require Import
  lib.oneshot
  lib.excl.
From zoo.language Require Import
  notations
  diaframe.
From zoo.std Require Export
  base
  spsc_future__code.
From zoo.std Require Import
  option
  condition
  spsc_future__types.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types l : location.
Implicit Types o : option val.

Class SpscFutureG Σ `{zoo_G : !ZooG Σ} := {
  #[local] spsc_future_G_mutex_G :: MutexG Σ ;
  #[local] spsc_future_G_lstate_G :: OneshotG Σ unit val ;
  #[local] spsc_future_G_excl_G :: ExclG Σ unitO ;
}.

Definition spsc_future_Σ := #[
  mutex_Σ ;
  oneshot_Σ unit val ;
  excl_Σ unitO
].
#[global] Instance subG_spsc_future_Σ Σ `{zoo_G : !ZooG Σ} :
  subG spsc_future_Σ Σ →
  SpscFutureG Σ .
Proof.
  solve_inG.
Qed.

Section spsc_future_G.
  Context `{spsc_future_G : SpscFutureG Σ}.

  Record spsc_future_meta := {
    spsc_future_meta_mutex : val ;
    spsc_future_meta_condition : val ;
    spsc_future_meta_lstate : gname ;
    spsc_future_meta_consumer : gname ;
  }.
  Implicit Types γ : spsc_future_meta.

  #[local] Instance spsc_future_meta_eq_dec : EqDecision spsc_future_meta :=
    ltac:(solve_decision).
  #[local] Instance spsc_future_meta_countable :
    Countable spsc_future_meta.
  Proof.
    pose encode γ := (
      γ.(spsc_future_meta_mutex),
      γ.(spsc_future_meta_condition),
      γ.(spsc_future_meta_lstate),
      γ.(spsc_future_meta_consumer)
    ).
    pose decode := λ '(mtx, cond, γ_lstate, γ_consumer), {|
      spsc_future_meta_mutex := mtx ;
      spsc_future_meta_condition := cond ;
      spsc_future_meta_lstate := γ_lstate ;
      spsc_future_meta_consumer := γ_consumer ;
    |}.
    refine (inj_countable' encode decode _). intros []. done.
  Qed.

  #[local] Definition spsc_future_inv_inner l γ Ψ : iProp Σ :=
    ∃ o,
    l.[result] ↦ o ∗
    match o with
    | Some v =>
        oneshot_shot γ.(spsc_future_meta_lstate) v ∗
        (Ψ v ∨ excl γ.(spsc_future_meta_consumer) ())
    | None =>
        oneshot_pending γ.(spsc_future_meta_lstate) (DfracOwn (1/3)) ()
    end.
  Definition spsc_future_inv t Ψ : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    l.[mutex] ↦□ γ.(spsc_future_meta_mutex) ∗
    mutex_inv γ.(spsc_future_meta_mutex) True ∗
    l.[condition] ↦□ γ.(spsc_future_meta_condition) ∗
    condition_inv γ.(spsc_future_meta_condition) ∗
    inv nroot (spsc_future_inv_inner l γ Ψ).

  Definition spsc_future_producer t : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    oneshot_pending γ.(spsc_future_meta_lstate) (DfracOwn (2/3)) ().

  Definition spsc_future_consumer t : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    excl γ.(spsc_future_meta_consumer) ().

  Definition spsc_future_result t v : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    oneshot_shot γ.(spsc_future_meta_lstate) v.

  #[global] Instance spsc_future_inv_contractive t n :
    Proper ((pointwise_relation _ (dist_later n)) ==> (≡{n}≡)) (spsc_future_inv t).
  Proof.
    rewrite /spsc_future_inv /spsc_future_inv_inner. solve_contractive.
  Qed.
  #[global] Instance spsc_future_inv_proper t :
    Proper ((pointwise_relation _ (≡)) ==> (≡)) (spsc_future_inv t).
  Proof.
    intros Ψ1 Ψ2 HΨ.
    apply equiv_dist => n.
    apply spsc_future_inv_contractive => v.
    dist_later_intro.
    apply equiv_dist, HΨ.
  Qed.

  #[global] Instance spsc_future_inv_persistent t Ψ :
    Persistent (spsc_future_inv t Ψ).
  Proof.
    apply _.
  Qed.
  #[global] Instance spsc_future_result_persistent t v :
    Persistent (spsc_future_result t v).
  Proof.
    apply _.
  Qed.
  #[global] Instance spsc_future_producer_timeless t :
    Timeless (spsc_future_producer t).
  Proof.
    apply _.
  Qed.
  #[global] Instance spsc_future_consumer_timeless t :
    Timeless (spsc_future_consumer t).
  Proof.
    apply _.
  Qed.
  #[global] Instance spsc_future_result_timeless t v :
    Timeless (spsc_future_result t v).
  Proof.
    apply _.
  Qed.

  Lemma spsc_future_producer_exclusive t :
    spsc_future_producer t -∗
    spsc_future_producer t -∗
    False.
  Proof.
    iIntros "(%l & %γ & -> & #Hmeta & Hpending1) (%_l & %_γ & %Heq & _Hmeta & Hpending2)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iDestruct (oneshot_pending_valid_2 with "Hpending1 Hpending2") as %(? & _). done.
  Qed.

  Lemma spsc_future_consumer_exclusive t :
    spsc_future_consumer t -∗
    spsc_future_consumer t -∗
    False.
  Proof.
    iIntros "(%l & %γ & -> & #Hmeta & Hconsumer1) (%_l & %_γ & %Heq & _Hmeta & Hconsumer2)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iApply (excl_exclusive with "Hconsumer1 Hconsumer2").
  Qed.

  Lemma spsc_future_create_spec Ψ :
    {{{
      True
    }}}
      spsc_future_create ()
    {{{ t,
      RET t;
      spsc_future_inv t Ψ ∗
      spsc_future_producer t ∗
      spsc_future_consumer t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_rec.
    wp_smart_apply (condition_create_spec _ with "[//]") as "%cond #Hcond_inv".
    wp_smart_apply (mutex_create_spec True with "[//]") as "%mtx #Hmtx_inv".
    wp_block l as "Hmeta" "(Hresult & Hmtx & Hcond & _)".
    iMod (pointsto_persist with "Hmtx") as "Hmtx".
    iMod (pointsto_persist with "Hcond") as "Hcond".

    iMod (oneshot_alloc ()) as "(%γ_lstate & Hpending)".
    iEval (assert (1 = 2/3 + 1/3)%Qp as -> by compute_done) in "Hpending".
    iDestruct "Hpending" as "(Hpending1 & Hpending2)".

    iMod (excl_alloc (excl_G := spsc_future_G_excl_G) ()) as "(%γ_consumer & Hconsumer)".

    pose γ := {|
      spsc_future_meta_mutex := mtx ;
      spsc_future_meta_condition := cond ;
      spsc_future_meta_lstate := γ_lstate ;
      spsc_future_meta_consumer := γ_consumer ;
    |}.
    iMod (meta_set _ _ γ with "Hmeta") as "#Hmeta"; first done.

    iSteps. iExists None. iSteps.
  Qed.

  Lemma spsc_future_set_spec t Ψ v :
    {{{
      spsc_future_inv t Ψ ∗
      spsc_future_producer t ∗
      Ψ v
    }}}
      spsc_future_set t v
    {{{
      RET ();
      spsc_future_result t v
    }}}.
  Proof.
    iIntros "%Φ ((%l & %γ & -> & #Hmeta & #Hmtx & #Hmtx_inv & #Hcond & #Hcond_inv & #Hinv) & (%_l & %_γ & %Heq & _Hmeta & Hpending) & HΨ) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".

    wp_rec. wp_load.
    pose (Ψ_mtx (_ : val) := (
      oneshot_shot γ.(spsc_future_meta_lstate) v
    )%I).
    wp_apply (mutex_protect_spec Ψ_mtx with "[$Hmtx_inv Hpending HΨ]") as (res) "#Hshot".
    { iIntros "Hmtx_locked _".
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
      iSplitR "Hmtx_locked". { iExists (Some _). iSteps. }
      iSteps.
    }
    wp_load.
    wp_apply (condition_notify_spec with "Hcond_inv").
    iSteps.
  Qed.

  Lemma spsc_future_try_get_spec t Ψ :
    {{{
      spsc_future_inv t Ψ ∗
      spsc_future_consumer t
    }}}
      spsc_future_try_get t
    {{{ o,
      RET o : val;
      match o with
      | None =>
          spsc_future_consumer t
      | Some v =>
          Ψ v
      end
    }}}.
  Proof.
    iIntros "%Φ ((%l & %γ & -> & #Hmeta & #Hmtx & #Hmtx_inv & #Hcond & #Hcond_inv & #Hinv) & (%_l & %_γ & %Heq & _Hmeta & Hconsumer)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".

    wp_rec.
    wp_pures.

    iInv "Hinv" as "(%o & Hresult & Ho)".
    wp_load.
    destruct o as [v |].

    - iDestruct "Ho" as "(Hshot & [HΨ | Hconsumer'])"; last first.
      { iDestruct (excl_exclusive with "Hconsumer Hconsumer'") as %[]. }
      iSplitR "HΨ HΦ". { iExists (Some _). iSteps. }
      iModIntro.

      iApply ("HΦ" $! (Some _) with "HΨ").

    - iSplitR "Hconsumer HΦ". { iExists None. iSteps. }
      iModIntro.

      iApply ("HΦ" $! None).
      iSteps.
  Qed.
  Lemma spsc_future_try_get_spec_result t Ψ v :
    {{{
      spsc_future_inv t Ψ ∗
      spsc_future_consumer t ∗
      spsc_future_result t v
    }}}
      spsc_future_try_get t
    {{{
      RET Some v : val;
      Ψ v
    }}}.
  Proof.
    iIntros "%Φ ((%l & %γ & -> & #Hmeta & #Hmtx & #Hmtx_inv & #Hcond & #Hcond_inv & #Hinv) & (%_l1 & %_γ1 & %Heq1 & _Hmeta1 & Hconsumer) & (%_l2 & %_γ2 & %Heq2 & _Hmeta2 & #Hshot)) HΦ". injection Heq1 as <-. injection Heq2 as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta1") as %<-. iClear "_Hmeta1".
    iDestruct (meta_agree with "Hmeta _Hmeta2") as %<-. iClear "_Hmeta2".

    wp_rec.
    wp_pures.

    iInv "Hinv" as "(%o & Hresult & Ho)".
    wp_load.
    destruct o; last first.
    { iDestruct (oneshot_pending_shot with "Ho Hshot") as %[]. }
    iDestruct "Ho" as "(_Hshot & [HΨ | Hconsumer'])"; last first.
    { iDestruct (excl_exclusive with "Hconsumer Hconsumer'") as %[]. }
    iDestruct (oneshot_shot_agree with "Hshot _Hshot") as %<-. iClear "_Hshot".
    iSplitR "HΨ HΦ". { iExists (Some _). iSteps. }
    iSteps.
  Qed.

  Lemma spsc_future_get_spec t Ψ :
    {{{
      spsc_future_inv t Ψ ∗
      spsc_future_consumer t
    }}}
      spsc_future_get t
    {{{ v,
      RET v;
      Ψ v
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & Hconsumer) HΦ".

    wp_rec.
    wp_apply (spsc_future_try_get_spec with "[$Hinv $Hconsumer]") as ([]) "Hconsumer"; first iSteps.

    iDestruct "Hinv" as "(%l & %γ & -> & #Hmeta & #Hmtx & #Hmtx_inv & #Hcond & #Hcond_inv & #Hinv)".
    iDestruct "Hconsumer" as "(%_l & %_γ & %Heq & _Hmeta & Hconsumer)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".

    do 2 wp_load.
    pose (Ψ_mtx (_ : val) := (
      ∃ v,
      oneshot_shot γ.(spsc_future_meta_lstate) v ∗
      Ψ v
    )%I).
    wp_smart_apply (mutex_protect_spec Ψ_mtx with "[$Hmtx_inv Hconsumer]") as (w) "(%v & #Hshot & HΨ)".
    { iIntros "Hmtx_locked _".
      pose (Ψ_cond b := (
        if b then
          excl γ.(spsc_future_meta_consumer) ()
        else
          ∃ v,
          oneshot_shot γ.(spsc_future_meta_lstate) v ∗
          Ψ v
      )%I).
      wp_smart_apply (condition_wait_while_spec Ψ_cond with "[$Hcond_inv $Hmtx_inv $Hmtx_locked $Hconsumer]"); last iSteps.

      clear. iIntros "!> %Φ (Hmtx_locked & _ & Hconsumer) HΦ".
      wp_pures.

      wp_bind (!_)%E.
      iInv "Hinv" as "(%o & Hresult & Ho)".
      wp_load.
      destruct o as [v |].

      - iDestruct "Ho" as "(#Hshot & [HΨ | Hconsumer'])"; last first.
        { iDestruct (excl_exclusive with "Hconsumer Hconsumer'") as %[]. }
        iSplitR "Hmtx_locked HΨ HΦ". { iExists (Some _). iSteps. }
        iSteps.

      - iSplitR "Hmtx_locked Hconsumer HΦ". { iExists None. iSteps. }
        iSteps.
    }
    wp_pures.

    wp_bind (!_)%E.
    iInv "Hinv" as "(%o & Hresult & Ho)".
    wp_load.
    destruct o; last first.
    { iDestruct (oneshot_pending_shot with "Ho Hshot") as %[]. }
    iDestruct "Ho" as "(_Hshot & Ho)".
    iDestruct (oneshot_shot_agree with "Hshot _Hshot") as %<-. iClear "_Hshot".
    iSplitR "HΨ HΦ". { iExists (Some _). iFrame. iSteps. }
    iSteps.
  Qed.
  Lemma spsc_future_get_spec_result t Ψ v :
    {{{
      spsc_future_inv t Ψ ∗
      spsc_future_consumer t ∗
      spsc_future_result t v
    }}}
      spsc_future_get t
    {{{
      RET v;
      Ψ v
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & Hconsumer & #Hresult) HΦ".

    wp_rec.
    wp_apply (spsc_future_try_get_spec_result with "[$Hinv $Hconsumer $Hresult]").
    iSteps.
  Qed.

  Lemma spsc_future_is_set_spec t Ψ :
    {{{
      spsc_future_inv t Ψ ∗
      spsc_future_consumer t
    }}}
      spsc_future_is_set t
    {{{ b,
      RET #b;
      if b then
        ∃ v, Ψ v
      else
        spsc_future_consumer t
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & Hconsumer) HΦ".

    wp_rec.
    wp_apply (spsc_future_try_get_spec with "[$Hinv $Hconsumer]") as ([v |]) "HΨ"; first iSteps.
    wp_pures.
    iApply "HΦ". naive_solver.
  Qed.
  Lemma spsc_future_is_set_spec_result t Ψ v :
    {{{
      spsc_future_inv t Ψ ∗
      spsc_future_consumer t ∗
      spsc_future_result t v
    }}}
      spsc_future_is_set t
    {{{
      RET #true;
      Ψ v
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & Hconsumer & #Hresult) HΦ".

    wp_rec.
    wp_apply (spsc_future_try_get_spec_result with "[$Hinv $Hconsumer $Hresult]").
    iSteps.
  Qed.
End spsc_future_G.

#[global] Opaque spsc_future_create.
#[global] Opaque spsc_future_set.
#[global] Opaque spsc_future_try_get.
#[global] Opaque spsc_future_get.
#[global] Opaque spsc_future_is_set.

#[global] Opaque spsc_future_inv.
#[global] Opaque spsc_future_producer.
#[global] Opaque spsc_future_consumer.
#[global] Opaque spsc_future_result.
