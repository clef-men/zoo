Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Import zoo.iris.base_logic.lib.oneshot.
Require Import zoo.iris.base_logic.lib.subpreds.
Require Import zoo.base.
Require Export zoo_std.ivar_2__code.
Require Import zoo_std.ivar_2__types.
Require Import zoo_std.option.
Require Import zoo_std.condition.
Require Import zoo.options.

Implicit Types b : bool.
Implicit Types v : val.
Implicit Types o state : option val.

Class Ivar2G Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] ivar_2۰G۰mutex۰G :: MutexG Σ
  ; #[local] ivar_2۰G۰lstate۰G :: OneshotG Σ unit val
  ; #[local] ivar_2۰G۰consumer۰G :: SubpredsG Σ val
  }.

Definition ivar_2۰Σ :=
  #[mutex۰Σ
  ; oneshot۰Σ unit val
  ; subpreds۰Σ val
  ].
#[global] Instance subG𑁒ivar_2۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG ivar_2۰Σ Σ →
  Ivar2G Σ .
Proof.
  solve_inG.
Qed.

Module base.
  Section ivar_2۰G.
    Context `{ivar_2۰G : Ivar2G Σ}.

    Implicit Types t : location.
    Implicit Types Ψ Χ Ξ : val → iProp Σ.

    Record ivar_2۰name :=
      { ivar_2۰name۰mutex : val
      ; ivar_2۰name۰condition : val
      ; ivar_2۰name۰lstate : gname
      ; ivar_2۰name۰consumer : gname
      }.
    Implicit Types γ : ivar_2۰name.

    #[global] Instance ivar_2۰name𑁒eq_dec : EqDecision ivar_2۰name :=
      ltac:(solve_decision).
    #[global] Instance ivar_2۰name𑁒countable :
      Countable ivar_2۰name.
    Proof.
      solve_countable.
    Qed.

    #[local] Definition lstate۰unset₁' γ_lstate :=
      oneshot۰pending γ_lstate (DfracOwn (1/3)) ().
    #[local] Definition lstate۰unset₁ γ :=
      lstate۰unset₁' γ.(ivar_2۰name۰lstate).
    #[local] Definition lstate۰unset₂' γ_lstate :=
      oneshot۰pending γ_lstate (DfracOwn (2/3)) ().
    #[local] Definition lstate۰unset₂ γ :=
      lstate۰unset₂' γ.(ivar_2۰name۰lstate).
    #[local] Definition lstate۰set γ :=
      oneshot۰shot γ.(ivar_2۰name۰lstate).

    #[local] Definition consumer۰auth' :=
      subpreds۰auth.
    #[local] Definition consumer۰auth γ :=
      consumer۰auth' γ.(ivar_2۰name۰consumer).
    #[local] Definition consumer۰frag' :=
      subpreds۰frag.
    #[local] Definition consumer۰frag γ :=
      consumer۰frag' γ.(ivar_2۰name۰consumer).

    #[local] Definition inv۰state۰unset γ :=
      lstate۰unset₁ γ.
    #[local] Instance : CustomIpat "inv۰state۰unset" :=
      " {>;}Hlstate_unset₁
      ".
    #[local] Definition inv۰state۰set γ Ξ v : iProp Σ :=
      lstate۰set γ v ∗
      □ Ξ v.
    #[local] Instance : CustomIpat "inv۰state۰set" :=
      " ( {>;}#Hlstate_set{_{}}
        & #HΞ{_{}}
        )
      ".
    #[local] Definition inv۰state γ Ξ state :=
      match state with
      | None =>
          inv۰state۰unset γ
      | Some v =>
          inv۰state۰set γ Ξ v
      end.

    #[local] Definition inv۰inner t γ Ψ Ξ : iProp Σ :=
      ∃ state,
      t.[result] ↦ state ∗
      consumer۰auth γ Ψ state ∗
      inv۰state γ Ξ state.
    #[local] Instance : CustomIpat "inv۰inner" :=
      " ( %state
        & H𝑡_result
        & Hconsumer_auth
        & Hstate
        )
      ".
    Definition ivar_2۰inv t γ Ψ Ξ : iProp Σ :=
      t.[mutex] ↦□ γ.(ivar_2۰name۰mutex) ∗
      mutex۰inv γ.(ivar_2۰name۰mutex) True ∗
      t.[condition] ↦□ γ.(ivar_2۰name۰condition) ∗
      condition۰inv γ.(ivar_2۰name۰condition) ∗
      inv nroot (inv۰inner t γ Ψ Ξ).
    #[local] Instance : CustomIpat "inv" :=
      " ( #Ht_mutex
        & #Hmutex_inv
        & #Ht_condition
        & #Hcondition_inv
        & #Hinv
        )
      ".

    Definition ivar_2۰producer :=
      lstate۰unset₂.
    #[local] Instance : CustomIpat "producer" :=
      " Hlstate_unset₂{_{}}
      ".

    Definition ivar_2۰consumer :=
      consumer۰frag.
    #[local] Instance : CustomIpat "consumer" :=
      " Hconsumer{}_frag
      ".

    Definition ivar_2۰result :=
      lstate۰set.
    #[local] Instance : CustomIpat "result" :=
      " #Hlstate_set{_{}}
      ".
    Definition ivar_2۰resolved γ : iProp Σ :=
      ∃ v,
      ivar_2۰result γ v.

    Definition ivar_2۰synchronized γ : iProp Σ :=
      True.

    #[global] Instance ivar_2۰inv𑁒contractive t γ n :
      Proper (
        (pointwise_relation _ (dist_later n)) ==>
        (pointwise_relation _ (dist_later n)) ==>
        (≡{n}≡)
      ) (ivar_2۰inv t γ).
    Proof.
      rewrite /ivar_2۰inv /inv۰inner /inv۰state /inv۰state۰unset /inv۰state۰set.
      solve_contractive.
    Qed.
    #[global] Instance ivar_2۰inv𑁒proper t γ :
      Proper (
        (pointwise_relation _ (≡)) ==>
        (pointwise_relation _ (≡)) ==>
        (≡)
      ) (ivar_2۰inv t γ).
    Proof.
      rewrite /ivar_2۰inv /inv۰inner /inv۰state /inv۰state۰unset /inv۰state۰set.
      solve_proper.
    Qed.
    #[global] Instance ivar_2۰consumer𑁒contractive γ n :
      Proper (
        (pointwise_relation _ (dist_later n)) ==>
        (≡{n}≡)
      ) (ivar_2۰consumer γ).
    Proof.
      apply _.
    Qed.
    #[global] Instance ivar_2۰consumer𑁒proper γ :
      Proper (
        (pointwise_relation _ (≡)) ==>
        (≡)
      ) (ivar_2۰consumer γ).
    Proof.
      apply _.
    Qed.

    #[global] Instance ivar_2۰producer𑁒timeless γ :
      Timeless (ivar_2۰producer γ).
    Proof.
      apply _.
    Qed.
    #[global] Instance ivar_2۰result𑁒timeless γ v :
      Timeless (ivar_2۰result γ v).
    Proof.
      apply _.
    Qed.
    #[global] Instance ivar_2۰synchronized𑁒timeless γ :
      Timeless (ivar_2۰synchronized γ).
    Proof.
      apply _.
    Qed.

    #[global] Instance ivar_2۰inv𑁒persistent t γ Ψ Ξ :
      Persistent (ivar_2۰inv t γ Ψ Ξ).
    Proof.
      apply _.
    Qed.
    #[global] Instance ivar_2۰result𑁒persistent γ v :
      Persistent (ivar_2۰result γ v).
    Proof.
      apply _.
    Qed.
    #[global] Instance ivar_2۰synchronized𑁒persistent γ :
      Persistent (ivar_2۰synchronized γ).
    Proof.
      apply _.
    Qed.

    #[local] Lemma lstate𑁒alloc :
      ⊢ |==>
        ∃ γ_lstate,
        lstate۰unset₁' γ_lstate ∗
        lstate۰unset₂' γ_lstate.
    Proof.
      iMod oneshot𑁒alloc as "(%γ_lstate & Hpending)".
      assert (1 = 1/3 + 2/3)%Qp as -> by compute_done.
      iDestruct "Hpending" as "(Hunset₁ & Hpending₂)".
      iSteps.
    Qed.
    #[local] Lemma lstate۰unset₂𑁒exclusive γ :
      lstate۰unset₂ γ -∗
      lstate۰unset₂ γ -∗
      False.
    Proof.
      iIntros "Hpending1 Hpending2".
      iDestruct (oneshot۰pending𑁒valid𑁒2 with "Hpending1 Hpending2") as %(? & _). done.
    Qed.
    #[local] Lemma lstate۰set𑁒agree γ v1 v2 :
      lstate۰set γ v1 -∗
      lstate۰set γ v2 -∗
      ⌜v1 = v2⌝.
    Proof.
      apply oneshot۰shot𑁒agree.
    Qed.
    #[local] Lemma lstate𑁒unset₁𑁒set γ v :
      lstate۰unset₁ γ -∗
      lstate۰set γ v -∗
      False.
    Proof.
      apply oneshot𑁒pending𑁒shot.
    Qed.
    #[local] Lemma lstate𑁒unset₂𑁒set γ v :
      lstate۰unset₂ γ -∗
      lstate۰set γ v -∗
      False.
    Proof.
      apply oneshot𑁒pending𑁒shot.
    Qed.
    #[local] Lemma lstate𑁒update {γ} v :
      lstate۰unset₁ γ -∗
      lstate۰unset₂ γ ==∗
      lstate۰set γ v.
    Proof.
      iIntros "Hpending₁ Hpending₂".
      iCombine "Hpending₁ Hpending₂" as "Hpending".
      assert (1/3 + 2/3 = 1)%Qp as -> by compute_done.
      iApply (oneshot𑁒update𑁒shot with "Hpending").
    Qed.

    #[local] Lemma consumer𑁒alloc Ψ :
      ⊢ |==>
        ∃ γ_consumer,
        consumer۰auth' γ_consumer Ψ None ∗
        consumer۰frag' γ_consumer Ψ.
    Proof.
      apply subpreds𑁒alloc.
    Qed.
    #[local] Lemma consumer𑁒wand {γ Ψ state Χ1} Χ2 E :
      ▷ consumer۰auth γ Ψ state -∗
      consumer۰frag γ Χ1 -∗
      (∀ v, Χ1 v -∗ Χ2 v) ={E}=∗
        ▷ consumer۰auth γ Ψ state ∗
        consumer۰frag γ Χ2.
    Proof.
      apply subpreds𑁒wand.
    Qed.
    #[local] Lemma consumer𑁒divide {γ Ψ state} Χs E :
      ▷ consumer۰auth γ Ψ state -∗
      consumer۰frag γ (λ v, [∗ list] Χ ∈ Χs, Χ v) ={E}=∗
        ▷ consumer۰auth γ Ψ state ∗
        [∗ list] Χ ∈ Χs, consumer۰frag γ Χ.
    Proof.
      apply subpreds𑁒divide.
    Qed.
    #[local] Lemma consumer𑁒produce {γ Ψ} v :
      consumer۰auth γ Ψ None -∗
      Ψ v -∗
      consumer۰auth γ Ψ (Some v).
    Proof.
      apply subpreds𑁒produce.
    Qed.
    #[local] Lemma consumer𑁒consume γ Ψ v Χ E :
      ▷ consumer۰auth γ Ψ (Some v) -∗
      consumer۰frag γ Χ ={E}=∗
        ▷ consumer۰auth γ Ψ (Some v) ∗
        ▷^2 Χ v.
    Proof.
      apply subpreds𑁒consume.
    Qed.

    Lemma ivar_2۰producer𑁒exclusive γ :
      ivar_2۰producer γ -∗
      ivar_2۰producer γ -∗
      False.
    Proof.
      apply lstate۰unset₂𑁒exclusive.
    Qed.

    Lemma ivar_2۰consumer𑁒wand {t γ Ψ Ξ Χ1} Χ2 :
      ivar_2۰inv t γ Ψ Ξ -∗
      ivar_2۰consumer γ Χ1 -∗
      (∀ v, Χ1 v -∗ Χ2 v) ={⊤}=∗
      ivar_2۰consumer γ Χ2.
    Proof.
      iIntros "(:inv) (:consumer) H".
      iInv "Hinv" as "(:inv۰inner)".
      iMod (consumer𑁒wand with "Hconsumer_auth Hconsumer_frag H") as "($ & $)".
      iFrameSteps.
    Qed.
    Lemma ivar_2۰consumer𑁒divide {t γ Ψ Ξ} Χs :
      ivar_2۰inv t γ Ψ Ξ -∗
      ivar_2۰consumer γ (λ v, [∗ list] Χ ∈ Χs, Χ v) ={⊤}=∗
      [∗ list] Χ ∈ Χs, ivar_2۰consumer γ Χ.
    Proof.
      iIntros "(:inv) (:consumer)".
      iInv "Hinv" as "(:inv۰inner)".
      iMod (consumer𑁒divide with "Hconsumer_auth Hconsumer_frag") as "($ & $)".
      iFrameSteps.
    Qed.

    Lemma ivar_2۰result𑁒agree γ v1 v2 :
      ivar_2۰result γ v1 -∗
      ivar_2۰result γ v2 -∗
      ⌜v1 = v2⌝.
    Proof.
      apply lstate۰set𑁒agree.
    Qed.

    Lemma ivar_2𑁒producer𑁒result γ v :
      ivar_2۰producer γ -∗
      ivar_2۰result γ v -∗
      False.
    Proof.
      apply lstate𑁒unset₂𑁒set.
    Qed.

    Lemma ivar_2𑁒inv𑁒result t γ Ψ Ξ v :
      ivar_2۰inv t γ Ψ Ξ -∗
      ivar_2۰result γ v -∗
      ivar_2۰synchronized γ ={⊤}=∗
      ▷ □ Ξ v.
    Proof.
      iIntros "(:inv) (:result) _".
      iInv "Hinv" as "(:inv۰inner)".
      destruct state as [v_ |]; last first.
      { iDestruct "Hstate" as "(:inv۰state۰unset >)".
        iDestruct (lstate𑁒unset₁𑁒set with "Hlstate_unset₁ Hlstate_set") as %[].
      }
      iDestruct "Hstate" as "(:inv۰state۰set =1 >)".
      iDestruct (lstate۰set𑁒agree with "Hlstate_set Hlstate_set_1") as %<-.
      iSplitL. { iFrameSteps. }
      iSteps.
    Qed.
    Lemma ivar_2𑁒inv𑁒result𑁒consumer t γ Ψ Ξ v Χ :
      ivar_2۰inv t γ Ψ Ξ -∗
      ivar_2۰result γ v -∗
      ivar_2۰synchronized γ -∗
      ivar_2۰consumer γ Χ ={⊤}=∗
        ▷^2 Χ v ∗
        ▷ □ Ξ v.
    Proof.
      iIntros "(:inv) (:result) _ (:consumer)".
      iInv "Hinv" as "(:inv۰inner)".
      destruct state as [v_ |]; last first.
      { iDestruct "Hstate" as "(:inv۰state۰unset >)".
        iDestruct (lstate𑁒unset₁𑁒set with "Hlstate_unset₁ Hlstate_set") as %[].
      }
      iDestruct "Hstate" as "(:inv۰state۰set =1 >)".
      iDestruct (lstate۰set𑁒agree with "Hlstate_set Hlstate_set_1") as %<-.
      iMod (consumer𑁒consume with "Hconsumer_auth Hconsumer_frag") as "(Hconsumer_auth & HΧ)".
      iSplitR "HΧ". { iFrameSteps. }
      iSteps.
    Qed.

    Lemma ivar_2٠create𑁒spec Ψ Ξ :
      {{{
        True
      }}}
        ivar_2٠create ()
      {{{
        t γ
      , RET #t;
        meta_token t ⊤ ∗
        ivar_2۰inv t γ Ψ Ξ ∗
        ivar_2۰producer γ ∗
        ivar_2۰consumer γ Ψ
      }}}.
    Proof.
      iIntros "%Φ _ HΦ".

      wp۰rec.
      wp۰apply+ (condition٠create𑁒spec _ with "[//]") as "%cond #Hcondition_inv".
      wp۰apply+ (mutex٠create𑁒spec True with "[//]") as "%mtx #Hmutex_inv".
      wp۰block t as "Hmeta" "(Ht_mutex & Ht_condition & Ht_result & _)".
      iMod (pointsto𑁒persist with "Ht_mutex") as "Ht_mutex".
      iMod (pointsto𑁒persist with "Ht_condition") as "Ht_condition".

      iMod lstate𑁒alloc as "(%γ_lstate & Hlstate_unset₁ & Hlstate_unset₂)".
      iMod consumer𑁒alloc as "(%γ_consumer & Hconsumer_auth & Hconsumer_frag)".

      pose γ :=
        {|ivar_2۰name۰mutex := mtx
        ; ivar_2۰name۰condition := cond
        ; ivar_2۰name۰lstate := γ_lstate
        ; ivar_2۰name۰consumer := γ_consumer
        |}.

      iApply ("HΦ" $! t γ).
      iFrameSteps. iExists None. iSteps.
    Qed.

    Lemma ivar_2٠make𑁒spec Ψ Ξ v :
      {{{
        ▷ Ψ v ∗
        ▷ □ Ξ v
      }}}
        ivar_2٠make v
      {{{
        t γ
      , RET #t;
        meta_token t ⊤ ∗
        ivar_2۰inv t γ Ψ Ξ ∗
        ivar_2۰result γ v ∗
        ivar_2۰synchronized γ ∗
        ivar_2۰consumer γ Ψ
      }}}.
    Proof.
      iIntros "%Φ (HΨ & #HΞ) HΦ".

      wp۰rec.
      wp۰apply+ (condition٠create𑁒spec _ with "[//]") as "%cond #Hcondition_inv".
      wp۰apply+ (mutex٠create𑁒spec True with "[//]") as "%mtx #Hmutex_inv".
      wp۰block t as "Hmeta" "(Ht_mutex & Ht_condition & Ht_result & _)".
      iMod (pointsto𑁒persist with "Ht_mutex") as "Ht_mutex".
      iMod (pointsto𑁒persist with "Ht_condition") as "Ht_condition".

      iMod lstate𑁒alloc as "(%γ_lstate & Hlstate_unset₁ & Hlstate_unset₂)".
      iMod consumer𑁒alloc as "(%γ_consumer & Hconsumer_auth & Hconsumer_frag)".

      pose γ :=
        {|ivar_2۰name۰mutex := mtx
        ; ivar_2۰name۰condition := cond
        ; ivar_2۰name۰lstate := γ_lstate
        ; ivar_2۰name۰consumer := γ_consumer
        |}.

      iMod (lstate𑁒update (γ := γ) v with "Hlstate_unset₁ Hlstate_unset₂") as "#Hlstate_set".
      iDestruct (consumer𑁒produce (γ := γ) v with "Hconsumer_auth HΨ") as "Hconsumer_auth".

      iApply ("HΦ" $! t γ).
      iFrameSteps. iExists (Some v). iSteps.
    Qed.

    Lemma ivar_2٠try_get𑁒spec t γ Ψ Ξ :
      {{{
        ivar_2۰inv t γ Ψ Ξ
      }}}
        ivar_2٠try_get #t
      {{{
        o
      , RET o;
        if o is Some v then
          £ 2 ∗
          ivar_2۰result γ v ∗
          ivar_2۰synchronized γ
        else
          True
      }}}.
    Proof.
      iIntros "%Φ (:inv) HΦ".

      wp۰rec credits:"H£".
      iApply (lc_weaken 2) in "H£"; first done.

      iInv "Hinv" as "(:inv۰inner)".
      wp۰load.
      iSpecialize ("HΦ" $! state).
      destruct state as [v |].

      - iDestruct "Hstate" as "(:inv۰state۰set)".
        iSplitR "H£ HΦ". { iFrameSteps. }
        iSteps.

      - iSplitR "HΦ". { iFrameSteps. }
        iSteps.
    Qed.
    Lemma ivar_2٠try_get𑁒spec𑁒result t γ Ψ Ξ v :
      {{{
        ivar_2۰inv t γ Ψ Ξ ∗
        ivar_2۰result γ v
      }}}
        ivar_2٠try_get #t
      {{{
        RET Some v;
        £ 2 ∗
        ivar_2۰synchronized γ
      }}}.
    Proof.
      iIntros "%Φ ((:inv) & (:result)) HΦ".

      wp۰rec credits:"H£".
      iApply (lc_weaken 2) in "H£"; first done.

      iInv "Hinv" as "(:inv۰inner)".
      wp۰load.
      destruct state as [v_ |]; last first.
      { iDestruct (lstate𑁒unset₁𑁒set with "Hstate Hlstate_set") as %[]. }
      iDestruct "Hstate" as "(:inv۰state۰set =1)".
      iDestruct (lstate۰set𑁒agree with "Hlstate_set Hlstate_set_1") as %<-. iClear "Hlstate_set_1".
      iSplitR "H£ HΦ". { iFrameSteps. }
      iSteps.
    Qed.

    Lemma ivar_2٠is_unset𑁒spec t γ Ψ Ξ :
      {{{
        ivar_2۰inv t γ Ψ Ξ
      }}}
        ivar_2٠is_unset #t
      {{{
        b
      , RET #b;
        if b then
          True
        else
          £ 2 ∗
          ivar_2۰resolved γ
      }}}.
    Proof.
      iIntros "%Φ #Hinv HΦ".

      wp۰rec.
      wp۰apply (ivar_2٠try_get𑁒spec with "Hinv") as ([v |]) "H".
      all: wp۰pures.
      2: iSteps.
      iDestruct "H" as "(H£ & Hresult & Hsynchronized)".
      iSteps.
    Qed.
    Lemma ivar_2٠is_unset𑁒spec𑁒result t γ Ψ Ξ v :
      {{{
        ivar_2۰inv t γ Ψ Ξ ∗
        ivar_2۰result γ v
      }}}
        ivar_2٠is_unset #t
      {{{
        RET false;
        £ 2
      }}}.
    Proof.
      iIntros "%Φ (#Hinv & #Hresult) HΦ".

      wp۰rec.
      wp۰apply (ivar_2٠try_get𑁒spec𑁒result with "[$Hinv $Hresult]").
      iSteps.
    Qed.

    Lemma ivar_2٠is_set𑁒spec t γ Ψ Ξ :
      {{{
        ivar_2۰inv t γ Ψ Ξ
      }}}
        ivar_2٠is_set #t
      {{{
        b
      , RET #b;
        if b then
          £ 2 ∗
          ivar_2۰resolved γ
        else
          True
      }}}.
    Proof.
      iIntros "%Φ #Hinv HΦ".

      wp۰rec.
      wp۰apply (ivar_2٠is_unset𑁒spec with "[$]") as (b) "Hb".
      destruct b; iSteps.
    Qed.
    Lemma ivar_2٠is_set𑁒spec𑁒result t γ Ψ Ξ v :
      {{{
        ivar_2۰inv t γ Ψ Ξ ∗
        ivar_2۰result γ v
      }}}
        ivar_2٠is_set #t
      {{{
        RET true;
        £ 2
      }}}.
    Proof.
      iIntros "%Φ (#Hinv & #Hresult) HΦ".

      wp۰rec.
      wp۰apply (ivar_2٠is_unset𑁒spec𑁒result with "[$]").
      iSteps.
    Qed.

    Lemma ivar_2٠get𑁒spec t γ Ψ Ξ :
      {{{
        ivar_2۰inv t γ Ψ Ξ
      }}}
        ivar_2٠get #t
      {{{
        v
      , RET v;
        £ 2 ∗
        ivar_2۰result γ v ∗
        ivar_2۰synchronized γ
      }}}.
    Proof.
      iIntros "%Φ #Hinv HΦ".

      wp۰rec credits:"H£".
      iApply (lc_weaken 2) in "H£"; first done.
      wp۰apply (ivar_2٠try_get𑁒spec with "Hinv") as (state) "H".
      iDestruct "Hinv" as "(:inv)".
      destruct state; first iSteps.
      do 2 wp۰load.

      pose Ψ_mutex (_ : val) := (
        ∃ v,
        lstate۰set γ v
      )%I.
      wp۰apply+ (mutex٠protect𑁒spec Ψ_mutex with "[$Hmutex_inv]") as (res) "(%v & #Hlstate_set)".
      { iIntros "Hmutex_locked _".
        pose (Ψ_condition b := (
          if b then
            True
          else
            ∃ v,
            lstate۰set γ v
        )%I).
        wp۰apply+ (condition٠wait_while𑁒spec Ψ_condition with "[$Hcondition_inv $Hmutex_inv $Hmutex_locked]") as "(Hmutex_locked & _ & Hlstate_set)"; last iFrameSteps.
        iStep. iIntros "!> Hmutex_locked _ _".
        wp۰pures.

        wp۰bind (_.{result})%E.
        iInv "Hinv" as "(:inv۰inner)".
        wp۰load.
        destruct state as [v |].

        - iDestruct "Hstate" as "(:inv۰state۰set)".
          iSplitR "Hmutex_locked". { iFrameSteps. }
          iSteps.

        - iSplitR "Hmutex_locked". { iFrameSteps. }
          iSteps.
      }
      wp۰pures.

      wp۰bind (_.{result})%E.
      iInv "Hinv" as "(:inv۰inner)".
      wp۰load.
      destruct state as [v_ |]; last first.
      { iDestruct (lstate𑁒unset₁𑁒set with "Hstate Hlstate_set") as %[]. }
      iDestruct "Hstate" as "(:inv۰state۰set =1)".
      iDestruct (lstate۰set𑁒agree with "Hlstate_set Hlstate_set_1") as %<-. iClear "Hlstate_set_1".
      iSplitR "H£ HΦ". { iFrameSteps. }
      iSteps.
    Qed.
    Lemma ivar_2٠get𑁒spec𑁒result t γ Ψ Ξ v :
      {{{
        ivar_2۰inv t γ Ψ Ξ ∗
        ivar_2۰result γ v
      }}}
        ivar_2٠get #t
      {{{
        RET v;
        £ 2 ∗
        ivar_2۰synchronized γ
      }}}.
    Proof.
      iIntros "%Φ (#Hinv & #Hresult) HΦ".

      wp۰apply (ivar_2٠get𑁒spec with "Hinv") as (v_) "(H£ & Hresult_ & Hsynchronized)".
      iDestruct (ivar_2۰result𑁒agree with "Hresult Hresult_")as %<-.
      iSteps.
    Qed.

    Lemma ivar_2٠set𑁒spec t γ Ψ Ξ v :
      {{{
        ivar_2۰inv t γ Ψ Ξ ∗
        ivar_2۰producer γ ∗
        ▷ Ψ v ∗
        ▷ □ Ξ v
      }}}
        ivar_2٠set #t v
      {{{
        RET ();
        ivar_2۰result γ v
      }}}.
    Proof.
      iIntros "%Φ ((:inv) & (:producer) & HΨ & #HΞ) HΦ".

      wp۰rec. wp۰load.

      pose Ψ_mutex (_ : val) :=
        lstate۰set γ v.
      wp۰apply (mutex٠protect𑁒spec Ψ_mutex with "[$Hmutex_inv Hlstate_unset₂ HΨ]") as (res) "#Hlstate_set"; last iSteps.
      iIntros "Hmutex_locked _".
      wp۰pures.

      iInv "Hinv" as "(:inv۰inner)".
      wp۰store.
      destruct state.
      { iDestruct "Hstate" as "(:inv۰state۰set =1)".
        iDestruct (lstate𑁒unset₂𑁒set with "Hlstate_unset₂ Hlstate_set_1") as %[].
      }
      iMod (lstate𑁒update with "Hstate Hlstate_unset₂") as "#Hlstate_set".
      iDestruct (consumer𑁒produce with "Hconsumer_auth HΨ") as "Hconsumer_auth".
      iSplitR "Hmutex_locked". { iFrameSteps. }
      iSteps.
    Qed.
  End ivar_2۰G.

  #[global] Opaque ivar_2۰inv.
  #[global] Opaque ivar_2۰producer.
  #[global] Opaque ivar_2۰consumer.
  #[global] Opaque ivar_2۰result.
  #[global] Opaque ivar_2۰synchronized.
End base.

Require zoo_std.ivar_2__opaque.

Section ivar_2۰G.
  Context `{ivar_2۰G : Ivar2G Σ}.

  Implicit Types 𝑡 : location.
  Implicit Types t : val.
  Implicit Types γ : base.ivar_2۰name.
  Implicit Types Ψ Χ Ξ : val → iProp Σ.

  Definition ivar_2۰inv t Ψ Ξ : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.ivar_2۰inv 𝑡 γ Ψ Ξ.
  #[local] Instance : CustomIpat "inv" :=
    " ( %l{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hinv{_{}}
      )
    ".

  Definition ivar_2۰producer t : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.ivar_2۰producer γ.
  #[local] Instance : CustomIpat "producer" :=
    " ( %l{;_}
      & %γ{;_}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hproducer{_{}}
      )
    ".

  Definition ivar_2۰consumer t Χ : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.ivar_2۰consumer γ Χ.
  #[local] Instance : CustomIpat "consumer" :=
    " ( %l{;_}
      & %γ{;_}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hconsumer{_{}}
      )
    ".

  Definition ivar_2۰result t v : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.ivar_2۰result γ v.
  #[local] Instance : CustomIpat "result" :=
    " ( %l{;_}
      & %γ{;_}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hresult{_{}}
      )
    ".
  Definition ivar_2۰resolved t : iProp Σ :=
    ∃ v,
    ivar_2۰result t v.

  Definition ivar_2۰synchronized t : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.ivar_2۰synchronized γ.
  #[local] Instance : CustomIpat "synchronized" :=
    " ( %l{;_}
      & %γ{;_}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hsynchronized{_{}}
      )
    ".

  #[global] Instance ivar_2۰inv𑁒contractive t n :
    Proper (
      (pointwise_relation _ (dist_later n)) ==>
      (pointwise_relation _ (dist_later n)) ==>
      (≡{n}≡)
    ) (ivar_2۰inv t).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance ivar_2۰inv𑁒proper t :
    Proper (
      (pointwise_relation _ (≡)) ==>
      (pointwise_relation _ (≡)) ==>
      (≡)
    ) (ivar_2۰inv t).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance ivar_2۰consumer𑁒contractive t n :
    Proper (
      (pointwise_relation _ (dist_later n)) ==>
      (≡{n}≡)
    ) (ivar_2۰consumer t).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance ivar_2۰consumer𑁒proper t :
    Proper (
      (pointwise_relation _ (≡)) ==>
      (≡)
    ) (ivar_2۰consumer t).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance ivar_2۰producer𑁒timeless t :
    Timeless (ivar_2۰producer t).
  Proof.
    apply _.
  Qed.
  #[global] Instance ivar_2۰result𑁒timeless t v :
    Timeless (ivar_2۰result t v).
  Proof.
    apply _.
  Qed.
  #[global] Instance ivar_2۰synchronized𑁒timeless t :
    Timeless (ivar_2۰synchronized t).
  Proof.
    apply _.
  Qed.

  #[global] Instance ivar_2۰inv𑁒persistent t Ψ Ξ :
    Persistent (ivar_2۰inv t Ψ Ξ).
  Proof.
    apply _.
  Qed.
  #[global] Instance ivar_2۰result𑁒persistent t v :
    Persistent (ivar_2۰result t v).
  Proof.
    apply _.
  Qed.
  #[global] Instance ivar_2۰synchronized𑁒persistent t :
    Persistent (ivar_2۰synchronized t).
  Proof.
    apply _.
  Qed.

  Lemma ivar_2۰producer𑁒exclusive t :
    ivar_2۰producer t -∗
    ivar_2۰producer t -∗
    False.
  Proof.
    iIntros "(:producer =1) (:producer =2)". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.ivar_2۰producer𑁒exclusive with "Hproducer_1 Hproducer_2").
  Qed.

  Lemma ivar_2۰consumer𑁒wand {t Ψ Ξ Χ1} Χ2 :
    ivar_2۰inv t Ψ Ξ -∗
    ivar_2۰consumer t Χ1 -∗
    (∀ v, Χ1 v -∗ Χ2 v) ={⊤}=∗
    ivar_2۰consumer t Χ2.
  Proof.
    iIntros "(:inv =1) (:consumer =2) H". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->.
    iDestruct (base.ivar_2۰consumer𑁒wand with "Hinv_1 Hconsumer_2 H") as "H".
    iSteps.
  Qed.
  Lemma ivar_2۰consumer𑁒divide {t Ψ Ξ} Χs :
    ivar_2۰inv t Ψ Ξ -∗
    ivar_2۰consumer t (λ v, [∗ list] Χ ∈ Χs, Χ v) ={⊤}=∗
    [∗ list] Χ ∈ Χs, ivar_2۰consumer t Χ.
  Proof.
    iIntros "(:inv =1) (:consumer =2)". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->.
    iDestruct (base.ivar_2۰consumer𑁒divide with "Hinv_1 Hconsumer_2") as "H".
    iApply (big_sepL_impl with "H").
    iSteps.
  Qed.
  Lemma ivar_2۰consumer𑁒split {t Ψ Ξ} Χ1 Χ2 :
    ivar_2۰inv t Ψ Ξ -∗
    ivar_2۰consumer t (λ v, Χ1 v ∗ Χ2 v) ={⊤}=∗
      ivar_2۰consumer t Χ1 ∗
      ivar_2۰consumer t Χ2.
  Proof.
    iIntros "Hinv Hconsumer".
    iMod (ivar_2۰consumer𑁒divide [Χ1;Χ2] with "Hinv [Hconsumer]") as "($ & $ & _)" => //.
    { simpl. setoid_rewrite bi.sep_emp => //. }
  Qed.

  Lemma ivar_2۰result𑁒agree t v1 v2 :
    ivar_2۰result t v1 -∗
    ivar_2۰result t v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    iIntros "(:result =1) (:result =2)". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.ivar_2۰result𑁒agree with "Hresult_1 Hresult_2").
  Qed.

  Lemma ivar_2𑁒producer𑁒result t v :
    ivar_2۰producer t -∗
    ivar_2۰result t v -∗
    False.
  Proof.
    iIntros "(:producer =1) (:result =2)". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.ivar_2𑁒producer𑁒result with "Hproducer_1 Hresult_2").
  Qed.

  Lemma ivar_2𑁒inv𑁒result t Ψ Ξ v :
    ivar_2۰inv t Ψ Ξ -∗
    ivar_2۰result t v -∗
    ivar_2۰synchronized t ={⊤}=∗
    ▷ □ Ξ v.
  Proof.
    iIntros "(:inv =1) (:result =2) (:synchronized =3)". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->.
    iDestruct (meta𑁒agree with "Hmeta_2 Hmeta_3") as %<-.
    iApply (base.ivar_2𑁒inv𑁒result with "Hinv_1 Hresult_2 Hsynchronized_3").
  Qed.
  Lemma ivar_2𑁒inv𑁒result' t Ψ Ξ v :
    £ 1 -∗
    ivar_2۰inv t Ψ Ξ -∗
    ivar_2۰result t v -∗
    ivar_2۰synchronized t ={⊤}=∗
    □ Ξ v.
  Proof.
    iIntros "H£ Hinv Hresult Hsynchronized".
    iMod (ivar_2𑁒inv𑁒result with "Hinv Hresult Hsynchronized") as "HΞ".
    iApply (lc_fupd_elim_later with "H£ HΞ").
  Qed.
  Lemma ivar_2𑁒inv𑁒result𑁒consumer t Ψ Ξ v Χ :
    ivar_2۰inv t Ψ Ξ -∗
    ivar_2۰result t v -∗
    ivar_2۰synchronized t -∗
    ivar_2۰consumer t Χ ={⊤}=∗
      ▷^2 Χ v ∗
      ▷ □ Ξ v.
  Proof.
    iIntros "(:inv =1) (:result =2) (:synchronized =3) (:consumer =4)". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->.
    iDestruct (meta𑁒agree with "Hmeta_2 Hmeta_3") as %<-.
    iDestruct (meta𑁒agree with "Hmeta_2 Hmeta_4") as %<-.
    iApply (base.ivar_2𑁒inv𑁒result𑁒consumer with "Hinv_1 Hresult_2 Hsynchronized_3 Hconsumer_4").
  Qed.
  Lemma ivar_2𑁒inv𑁒result𑁒consumer' t Ψ Ξ v Χ :
    £ 2 -∗
    ivar_2۰inv t Ψ Ξ -∗
    ivar_2۰result t v -∗
    ivar_2۰synchronized t -∗
    ivar_2۰consumer t Χ ={⊤}=∗
      Χ v ∗
      □ Ξ v.
  Proof.
    iIntros "(H£1 & H£2) Hinv Hresult Hsynchronized Hconsumer".
    iMod (ivar_2𑁒inv𑁒result𑁒consumer with "Hinv Hresult Hsynchronized Hconsumer") as "H".
    rewrite -bi.later_sep.
    iMod (lc_fupd_elim_later with "H£1 H") as "(HΧ & $)".
    iApply (lc_fupd_elim_later with "H£2 HΧ").
  Qed.

  Lemma ivar_2٠create𑁒spec Ψ Ξ :
    {{{
      True
    }}}
      ivar_2٠create ()
    {{{
      t
    , RET t;
      ivar_2۰inv t Ψ Ξ ∗
      ivar_2۰producer t ∗
      ivar_2۰consumer t Ψ
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    iApply wp𑁒fupd.
    wp۰apply (base.ivar_2٠create𑁒spec with "[//]") as (𝑡 γ) "(Hmeta & Hinv & Hproducer & Hconsumer)".
    iMod (meta𑁒set γ with "Hmeta") as "#Hmeta"; first done.
    iSteps.
  Qed.

  Lemma ivar_2٠make𑁒spec Ψ Ξ v :
    {{{
      ▷ Ψ v ∗
      ▷ □ Ξ v
    }}}
      ivar_2٠make v
    {{{
      t
    , RET t;
      ivar_2۰inv t Ψ Ξ ∗
      ivar_2۰result t v ∗
      ivar_2۰consumer t Ψ
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #HΞ) HΦ".

    iApply wp𑁒fupd.
    wp۰apply (base.ivar_2٠make𑁒spec Ψ with "[$]") as (𝑡 γ) "(Hmeta & Hinv & Hproducer & Hconsumer)".
    iMod (meta𑁒set γ with "Hmeta") as "#Hmeta"; first done.
    iSteps.
  Qed.

  Lemma ivar_2٠try_get𑁒spec t Ψ Ξ :
    {{{
      ivar_2۰inv t Ψ Ξ
    }}}
      ivar_2٠try_get t
    {{{
      o
    , RET o;
      if o is Some v then
        £ 2 ∗
        ivar_2۰result t v ∗
        ivar_2۰synchronized t
      else
        True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰apply (base.ivar_2٠try_get𑁒spec with "[$]") as (o) "Ho".
    iSpecialize ("HΦ" $! o).
    destruct o; iSteps.
  Qed.
  Lemma ivar_2٠try_get𑁒spec𑁒result t Ψ Ξ v :
    {{{
      ivar_2۰inv t Ψ Ξ ∗
      ivar_2۰result t v
    }}}
      ivar_2٠try_get t
    {{{
      RET Some v;
      £ 2 ∗
      ivar_2۰synchronized t
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:result =2)) HΦ". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp۰apply (base.ivar_2٠try_get𑁒spec𑁒result with "[$]").
    iSteps.
  Qed.

  Lemma ivar_2٠is_unset𑁒spec t Ψ Ξ :
    {{{
      ivar_2۰inv t Ψ Ξ
    }}}
      ivar_2٠is_unset t
    {{{
      b
    , RET #b;
      if b then
        True
      else
        £ 2 ∗
        ivar_2۰resolved t
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰apply (base.ivar_2٠is_unset𑁒spec with "[$]") as (b) "Hb".
    rewrite /ivar_2۰resolved. destruct b; iSteps.
  Qed.
  Lemma ivar_2٠is_unset𑁒spec𑁒result t Ψ Ξ v :
    {{{
      ivar_2۰inv t Ψ Ξ ∗
      ivar_2۰result t v
    }}}
      ivar_2٠is_unset t
    {{{
      RET false;
      £ 2
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:result =2)) HΦ". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp۰apply (base.ivar_2٠is_unset𑁒spec𑁒result with "[$] HΦ").
  Qed.

  Lemma ivar_2٠is_set𑁒spec t Ψ Ξ :
    {{{
      ivar_2۰inv t Ψ Ξ
    }}}
      ivar_2٠is_set t
    {{{
      b
    , RET #b;
      if b then
        £ 2 ∗
        ivar_2۰resolved t
      else
        True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰apply (base.ivar_2٠is_set𑁒spec with "[$]") as (b) "Hb".
    rewrite /ivar_2۰resolved. destruct b; iSteps.
  Qed.
  Lemma ivar_2٠is_set𑁒spec𑁒result t Ψ Ξ v :
    {{{
      ivar_2۰inv t Ψ Ξ ∗
      ivar_2۰result t v
    }}}
      ivar_2٠is_set t
    {{{
      RET true;
      £ 2
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:result =2)) HΦ". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp۰apply (base.ivar_2٠is_set𑁒spec𑁒result with "[$] HΦ").
  Qed.

  Lemma ivar_2٠get𑁒spec t Ψ Ξ :
    {{{
      ivar_2۰inv t Ψ Ξ
    }}}
      ivar_2٠get t
    {{{
      v
    , RET v;
      £ 2 ∗
      ivar_2۰result t v ∗
      ivar_2۰synchronized t
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰apply (base.ivar_2٠get𑁒spec with "[$]").
    iSteps.
  Qed.

  Lemma ivar_2٠set𑁒spec t Ψ Ξ v :
    {{{
      ivar_2۰inv t Ψ Ξ ∗
      ivar_2۰producer t ∗
      ▷ Ψ v ∗
      ▷ □ Ξ v
    }}}
      ivar_2٠set t v
    {{{
      RET ();
      ivar_2۰result t v
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:producer =2) & HΨ & HΞ) HΦ". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp۰apply (base.ivar_2٠set𑁒spec _ _ Ψ with "[$]").
    iSteps.
  Qed.
End ivar_2۰G.

#[global] Opaque ivar_2۰inv.
#[global] Opaque ivar_2۰producer.
#[global] Opaque ivar_2۰consumer.
#[global] Opaque ivar_2۰result.
#[global] Opaque ivar_2۰synchronized.
