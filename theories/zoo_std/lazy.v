Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Import zoo.iris.base_logic.lib.oneshot.
Require Import zoo.iris.base_logic.lib.subpreds.
Require Import zoo.base.
Require Export zoo_std.lazy__code.
Require Import zoo_std.lazy__types.
Require Import zoo_std.mutex.
Require Import zoo.options.

Implicit Types b : bool.
Implicit Types v fn mtx : val.

Class LazyG Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] lazy۰G۰mutex۰G :: MutexG Σ
  ; #[local] lazy۰G۰lstate۰G :: OneshotG Σ unit val
  ; #[local] lazy۰G۰consumer۰G :: SubpredsG Σ val
  }.

Definition lazy۰Σ :=
  #[mutex۰Σ
  ; oneshot۰Σ unit val
  ; subpreds۰Σ val
  ].
#[global] Instance subG𑁒lazy۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG lazy۰Σ Σ →
  LazyG Σ .
Proof.
  solve_inG.
Qed.

Module base.
  Section lazy۰G.
    Context `{lazy۰G : LazyG Σ}.

    Implicit Types t : location.
    Implicit Types Ψ Χ Ξ : val → iProp Σ.

    Record lazy۰name :=
      { lazy۰name۰thunk : val
      ; lazy۰name۰lstate : gname
      ; lazy۰name۰consumer : gname
      }.
    Implicit Types γ : lazy۰name.

    #[global] Instance lazy۰name𑁒eq_dec : EqDecision lazy۰name :=
      ltac:(solve_decision).
    #[global] Instance lazy۰name𑁒countable :
      Countable lazy۰name.
    Proof.
      solve_countable.
    Qed.

    Variant state :=
      | Unset
      | Setting mtx
      | Set_ v.
    Implicit Types state : state.

    #[local] Instance state𑁒inhabited : Inhabited state :=
      populate Unset.

    #[local] Definition state۰to_bool state :=
      match state with
      | Set_ _ =>
          true
      | _ =>
          false
      end.
    #[local] Definition state۰to_option state :=
      match state with
      | Set_ v =>
          Some v
      | _ =>
          None
      end.
    #[local] Definition state۰to_val γ state :=
      match state with
      | Unset =>
          ‘Unset( γ.(lazy۰name۰thunk) )
      | Setting mtx =>
          ‘Setting( mtx )
      | Set_ v =>
          ‘Set( v )
      end%V.

    #[local] Definition lstate۰unset₁' γ_lstate :=
      oneshot۰pending γ_lstate (DfracOwn (1/3)) ().
    #[local] Definition lstate۰unset₁ γ :=
      lstate۰unset₁' γ.(lazy۰name۰lstate).
    #[local] Definition lstate۰unset₂' γ_lstate :=
      oneshot۰pending γ_lstate (DfracOwn (2/3)) ().
    #[local] Definition lstate۰unset₂ γ :=
      lstate۰unset₂' γ.(lazy۰name۰lstate).
    #[local] Definition lstate۰set' γ_lstate :=
      oneshot۰shot γ_lstate.
    #[local] Definition lstate۰set γ :=
      lstate۰set' γ.(lazy۰name۰lstate).

    #[local] Definition consumer۰auth' :=
      subpreds۰auth.
    #[local] Definition consumer۰auth γ :=
      consumer۰auth' γ.(lazy۰name۰consumer).
    #[local] Definition consumer۰frag' :=
      subpreds۰frag.
    #[local] Definition consumer۰frag γ :=
      consumer۰frag' γ.(lazy۰name۰consumer).

    Definition lazy۰result :=
      lstate۰set.
    #[local] Instance : CustomIpat "result" :=
      " #Hlstate_set{_{}}
      ".
    Definition lazy۰resolved γ : iProp Σ :=
      ∃ v,
      lazy۰result γ v.

    #[local] Definition inv۰state۰unset γ Ψ Ξ : iProp Σ :=
      lstate۰unset₁ γ ∗
      lstate۰unset₂ γ ∗
      WP γ.(lazy۰name۰thunk) () {{ v,
        ▷ Ψ v ∗
        ▷ □ Ξ v
      }}.
    #[local] Instance : CustomIpat "inv۰state۰unset" :=
      " ( {>;}Hlstate_unset₁{_{}}
        & {>;}Hlstate_unset₂{_{}}
        & Hthunk
        )
      ".
    #[local] Definition inv۰state۰setting γ mtx : iProp Σ :=
      lstate۰unset₁ γ ∗
      mutex۰inv mtx (lazy۰resolved γ).
    #[local] Instance : CustomIpat "inv۰state۰setting" :=
      " ( {>;}Hlstate_unset₁{_{}}
        & #Hmtx_inv{_{}}
        )
      ".
    #[local] Definition inv۰state۰set γ Ξ v : iProp Σ :=
      lstate۰set γ v ∗
      □ Ξ v.
    #[local] Instance : CustomIpat "inv۰state۰set" :=
      " ( {>;}#Hlstate_set{_{}}
        & #HΞ{_{}}
        )
      ".
    #[local] Definition inv۰state γ Ψ Ξ state :=
      match state with
      | Unset =>
          inv۰state۰unset γ Ψ Ξ
      | Setting mtx =>
          inv۰state۰setting γ mtx
      | Set_ v =>
          inv۰state۰set γ Ξ v
      end.

    #[local] Definition inv۰inner t γ Ψ Ξ : iProp Σ :=
      ∃ state,
      t ↦ᵣ state۰to_val γ state ∗
      consumer۰auth γ Ψ (state۰to_option state) ∗
      inv۰state γ Ψ Ξ state.
    #[local] Instance : CustomIpat "inv۰inner" :=
      " ( %state
        & Ht
        & Hconsumer_auth
        & Hstate
        )
      ".
    Definition lazy۰inv t γ Ψ Ξ : iProp Σ :=
      inv nroot (inv۰inner t γ Ψ Ξ).
    #[local] Instance : CustomIpat "inv" :=
      " #Hinv
      ".

    Definition lazy۰consumer :=
      consumer۰frag.
    #[local] Instance : CustomIpat "consumer" :=
      " Hconsumer{}_frag
      ".

    #[global] Instance lazy۰inv𑁒contractive t γ n :
      Proper (
        (pointwise_relation _ (dist_later n)) ==>
        (pointwise_relation _ (dist_later n)) ==>
        (≡{n}≡)
      ) (lazy۰inv t γ).
    Proof.
      rewrite /lazy۰inv /inv۰inner /inv۰state /inv۰state۰unset /inv۰state۰setting /inv۰state۰set.
      intros Ψ1 Ψ2 HΨ Ξ1 Ξ2 HΞ.
      repeat (f_contractive || f_equiv).
      { eapply dist_lt. apply HΨ. done. }
      { eapply dist_lt. apply HΞ. done. }
    Qed.
    #[global] Instance lazy۰inv𑁒proper t γ :
      Proper (
        (pointwise_relation _ (≡)) ==>
        (pointwise_relation _ (≡)) ==>
        (≡)
      ) (lazy۰inv t γ).
    Proof.
      rewrite /lazy۰inv /inv۰inner /inv۰state /inv۰state۰unset /inv۰state۰setting /inv۰state۰set.
      solve_proper.
    Qed.
    #[global] Instance lazy۰consumer𑁒contractive γ n :
      Proper (
        (pointwise_relation _ (dist_later n)) ==>
        (≡{n}≡)
      ) (lazy۰consumer γ).
    Proof.
      apply _.
    Qed.
    #[global] Instance lazy۰consumer𑁒proper γ :
      Proper (
        (pointwise_relation _ (≡)) ==>
        (≡)
      ) (lazy۰consumer γ).
    Proof.
      apply _.
    Qed.

    #[global] Instance lazy۰result𑁒timeless γ v :
      Timeless (lazy۰result γ v).
    Proof.
      apply _.
    Qed.

    #[global] Instance lazy۰inv𑁒persistent t γ Ψ Ξ :
      Persistent (lazy۰inv t γ Ψ Ξ).
    Proof.
      apply _.
    Qed.
    #[global] Instance lazy۰result𑁒persistent γ v :
      Persistent (lazy۰result γ v).
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
      iDestruct "Hpending" as "(Hpending₁ & Hpending₂)".
      iSteps.
    Qed.
    #[local] Lemma lstate۰unset₂𑁒exclusive γ :
      lstate۰unset₂ γ -∗
      lstate۰unset₂ γ -∗
      False.
    Proof.
      iIntros "Hunset1 Hunset2".
      iDestruct (oneshot۰pending𑁒valid𑁒2 with "Hunset1 Hunset2") as %(? & _). done.
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
    #[local] Lemma consumer𑁒wand {γ Ψ} {state : option val} {Χ1} Χ2 E :
      ▷ consumer۰auth γ Ψ state -∗
      consumer۰frag γ Χ1 -∗
      (∀ v, Χ1 v -∗ Χ2 v) ={E}=∗
        ▷ consumer۰auth γ Ψ state ∗
        consumer۰frag γ Χ2.
    Proof.
      apply subpreds𑁒wand.
    Qed.
    #[local] Lemma consumer𑁒divide {γ Ψ} {state : option val} Χs E :
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

    #[local] Lemma inv۰state𑁒lstate۰set γ Ψ Ξ state v :
      ▷ inv۰state γ Ψ Ξ state -∗
      lstate۰set γ v -∗
      ◇ (
        ⌜state = Set_ v⌝ ∗
        ▷ inv۰state۰set γ Ξ v
      ).
    Proof.
      iIntros "Hstate Hlstate_set".
      destruct state as [| mtx | v_].
      - iDestruct "Hstate" as "(:inv۰state۰unset >)".
        iDestruct (lstate𑁒unset₁𑁒set with "Hlstate_unset₁ Hlstate_set") as %[].
      - iDestruct "Hstate" as "(:inv۰state۰setting >)".
        iDestruct (lstate𑁒unset₁𑁒set with "Hlstate_unset₁ Hlstate_set") as %[].
      - iDestruct "Hstate" as "(:inv۰state۰set =1 >)".
        iDestruct (lstate۰set𑁒agree with "Hlstate_set Hlstate_set_1") as %<-.
        iFrame "#∗" => //.
    Qed.

    Lemma lazy۰consumer𑁒wand {t γ Ψ Ξ Χ1} Χ2 :
      lazy۰inv t γ Ψ Ξ -∗
      lazy۰consumer γ Χ1 -∗
      (∀ v, Χ1 v -∗ Χ2 v) ={⊤}=∗
      lazy۰consumer γ Χ2.
    Proof.
      iIntros "(:inv) (:consumer) H".
      iInv "Hinv" as "(:inv۰inner)".
      iMod (consumer𑁒wand with "Hconsumer_auth Hconsumer_frag H") as "($ & $)".
      iFrameSteps.
    Qed.
    Lemma lazy۰consumer𑁒divide {t γ Ψ Ξ} Χs :
      lazy۰inv t γ Ψ Ξ -∗
      lazy۰consumer γ (λ v, [∗ list] Χ ∈ Χs, Χ v) ={⊤}=∗
      [∗ list] Χ ∈ Χs, lazy۰consumer γ Χ.
    Proof.
      iIntros "(:inv) (:consumer)".
      iInv "Hinv" as "(:inv۰inner)".
      iMod (consumer𑁒divide with "Hconsumer_auth Hconsumer_frag") as "($ & $)".
      iFrameSteps.
    Qed.

    Lemma lazy۰result𑁒agree γ v1 v2 :
      lazy۰result γ v1 -∗
      lazy۰result γ v2 -∗
      ⌜v1 = v2⌝.
    Proof.
      apply lstate۰set𑁒agree.
    Qed.

    Lemma lazy𑁒inv𑁒result t γ Ψ Ξ v :
      lazy۰inv t γ Ψ Ξ -∗
      lazy۰result γ v ={⊤}=∗
      ▷ □ Ξ v.
    Proof.
      iIntros "(:inv) (:result)".
      iInv "Hinv" as "(:inv۰inner)".
      iMod (inv۰state𑁒lstate۰set with "Hstate Hlstate_set") as "(-> & (:inv۰state۰set =1 >))".
      iSplitL. { iFrameSteps. }
      iSteps.
    Qed.
    Lemma lazy𑁒inv𑁒result𑁒consumer t γ Ψ Ξ v Χ :
      lazy۰inv t γ Ψ Ξ -∗
      lazy۰result γ v -∗
      lazy۰consumer γ Χ ={⊤}=∗
        ▷^2 Χ v ∗
        ▷ □ Ξ v.
    Proof.
      iIntros "(:inv) (:result) (:consumer)".
      iInv "Hinv" as "(:inv۰inner)".
      iMod (inv۰state𑁒lstate۰set with "Hstate Hlstate_set") as "(-> & (:inv۰state۰set =1 >))".
      iMod (consumer𑁒consume with "Hconsumer_auth Hconsumer_frag") as "(Hconsumer_auth & HΧ)".
      iSplitR "HΧ". { iFrameSteps. }
      iSteps.
    Qed.

    Lemma lazy٠make𑁒spec Ψ Ξ fn :
      {{{
        WP fn () {{ v,
          ▷ Ψ v ∗
          ▷ □ Ξ v
        }}
      }}}
        lazy٠make fn
      {{{
        t γ
      , RET #t;
        meta_token t ⊤ ∗
        lazy۰inv t γ Ψ Ξ ∗
        lazy۰consumer γ Ψ
      }}}.
    Proof.
      iIntros "%Φ Hfn HΦ".

      wp۰rec.
      wp۰ref t as "Hmeta" "Ht".

      iMod lstate𑁒alloc as "(%γ_lstate & Hlstate_unset₁ & Hlstate_unset₂)".
      iMod consumer𑁒alloc as "(%γ_consumer & Hconsumer_auth & Hconsumer_frag)".

      pose γ :=
        {|lazy۰name۰thunk := fn
        ; lazy۰name۰lstate := γ_lstate
        ; lazy۰name۰consumer := γ_consumer
        |}.

      iApply ("HΦ" $! t γ).
      iFrameSteps. iExists Unset. iSteps.
    Qed.

    Lemma lazy٠return𑁒spec Ψ Ξ v :
      {{{
        ▷ Ψ v ∗
        ▷ □ Ξ v
      }}}
        lazy٠return v
      {{{
        t γ
      , RET #t;
        meta_token t ⊤ ∗
        lazy۰inv t γ Ψ Ξ ∗
        lazy۰result γ v ∗
        lazy۰consumer γ Ψ
      }}}.
    Proof.
      iIntros "%Φ (HΨ & #HΞ) HΦ".

      wp۰rec.
      wp۰ref t as "Hmeta" "Ht".

      iMod lstate𑁒alloc as "(%γ_lstate & Hlstate_unset₁ & Hlstate_unset₂)".
      iMod consumer𑁒alloc as "(%γ_consumer & Hconsumer_auth & Hconsumer_frag)".

      pose γ :=
        {|lazy۰name۰thunk := ()
        ; lazy۰name۰lstate := γ_lstate
        ; lazy۰name۰consumer := γ_consumer
        |}.

      iMod (lstate𑁒update (γ := γ) v with "Hlstate_unset₁ Hlstate_unset₂") as "#Hlstate_set".
      iDestruct (consumer𑁒produce (γ := γ) v with "Hconsumer_auth HΨ") as "Hconsumer_auth".

      iApply ("HΦ" $! t γ).
      iFrameSteps. iExists (Set_ v). iSteps.
    Qed.

    Lemma lazy٠is_set𑁒spec t γ Ψ Ξ :
      {{{
        lazy۰inv t γ Ψ Ξ
      }}}
        lazy٠is_set #t
      {{{
        b
      , RET #b;
        if b then
          £ 2 ∗
          lazy۰resolved γ
        else
          True
      }}}.
    Proof.
      iIntros "%Φ (:inv) HΦ".

      wp۰rec credits:"H£".
      iApply (lc_weaken 2) in "H£"; first done.

      wp۰bind (!_)%E.
      iInv "Hinv" as "(:inv۰inner)".
      wp۰load.
      iSpecialize ("HΦ" $! (state۰to_bool state)).
      destruct state as [| mtx | v].

      - iSplitR "HΦ". { iFrameSteps. }
        iSteps.

      - iSplitR "HΦ". { iFrameSteps. }
        iSteps.

      - iDestruct "Hstate" as "(:inv۰state۰set)".
        iSplitR "H£ HΦ". { iFrameSteps. }
        iSteps.
    Qed.
    Lemma lazy٠is_set𑁒spec𑁒result t γ Ψ Ξ v :
      {{{
        lazy۰inv t γ Ψ Ξ ∗
        lazy۰result γ v
      }}}
        lazy٠is_set #t
      {{{
        RET true;
        £ 2
      }}}.
    Proof.
      iIntros "%Φ ((:inv) & (:result)) HΦ".

      wp۰rec credits:"H£".
      iApply (lc_weaken 2) in "H£"; first done.

      wp۰bind (!_)%E.
      iInv "Hinv" as "(:inv۰inner)".
      wp۰load.
      iMod (inv۰state𑁒lstate۰set with "Hstate Hlstate_set") as "(-> & (:inv۰state۰set =1))".
      iSplitR "H£ HΦ". { iFrameSteps. }
      iSteps.
    Qed.

    Lemma lazy٠is_unset𑁒spec t γ Ψ Ξ :
      {{{
        lazy۰inv t γ Ψ Ξ
      }}}
        lazy٠is_unset #t
      {{{
        b
      , RET #b;
        if b then
          True
        else
          £ 2 ∗
          lazy۰resolved γ
      }}}.
    Proof.
      iIntros "%Φ #Hinv HΦ".

      wp۰rec.
      wp۰apply (lazy٠is_set𑁒spec with "[$]") as (b) "Hb".
      destruct b; iSteps.
    Qed.
    Lemma lazy٠is_unset𑁒spec𑁒result t γ Ψ Ξ v :
      {{{
        lazy۰inv t γ Ψ Ξ ∗
        lazy۰result γ v
      }}}
        lazy٠is_unset #t
      {{{
        RET false;
        £ 2
      }}}.
    Proof.
      iIntros "%Φ (#Hinv & #Hresult) HΦ".

      wp۰rec.
      wp۰apply (lazy٠is_set𑁒spec𑁒result with "[$]").
      iSteps.
    Qed.

    Lemma lazy٠get𑁒spec t γ Ψ Ξ :
      {{{
        lazy۰inv t γ Ψ Ξ
      }}}
        lazy٠get #t
      {{{
        v
      , RET v;
        £ 2 ∗
        lazy۰result γ v
      }}}.
    Proof.
      iIntros "%Φ (:inv) HΦ".

      iLöb as "HLöb" forall (Φ).

      wp۰rec credits:"H£".
      iApply (lc_weaken 2) in "H£"; first done.
      iApply (wp𑁒frame𑁒wand with "[H£]"); first iAccu.

      wp۰bind (!_)%E.
      iInv "Hinv" as "(:inv۰inner)".
      wp۰load.
      destruct state as [| mtx | v_].

      - iSplitR "HΦ". { iFrameSteps. }
        iIntros "!> {%}".

        wp۰apply+ (mutex٠create_lock𑁒spec𑁒init with "[//]") as (mtx) "(Hmtx_init & Hmtx_locked)".
        wp۰pures.

        wp۰bind (CAS _ _ _).
        iInv "Hinv" as "(:inv۰inner)".
        wp۰cas as Hcas.

        + iSplitR "Hmtx_init Hmtx_locked HΦ". { iFrameSteps. }
          iIntros "!> {%}".

          wp۰apply+ (mutex٠unlock𑁒spec𑁒init with "[$]") as "_".
          wp۰apply+ "HLöb".
          iSteps.

        + destruct state; zoo_simplify.
          iDestruct "Hstate" as "(:inv۰state۰unset)".
          iMod (mutex۰init𑁒to𑁒inv (lazy۰resolved γ) with "Hmtx_init [//]") as "#Hmtx_inv".
          iSplitR "Hmtx_locked Hlstate_unset₂ Hthunk HΦ".
          { iExists (Setting mtx). iFrameSteps. }
          iIntros "!> {%}".

          wp۰apply+ (wp𑁒wand with "Hthunk") as (v) "(HΨ & #HΞ)".
          wp۰pures.

          wp۰bind (_ <- _)%E.
          iInv "Hinv" as "(:inv۰inner)".
          wp۰store.
          destruct state.

          * iDestruct "Hstate" as "(:inv۰state۰unset =1)".
            iDestruct (lstate۰unset₂𑁒exclusive with "Hlstate_unset₂ Hlstate_unset₂_1") as %[].

          * iDestruct "Hstate" as "(:inv۰state۰setting =1)".
            iMod (lstate𑁒update with "Hlstate_unset₁_1 Hlstate_unset₂") as "#Hlstate_set".
            iDestruct (consumer𑁒produce with "Hconsumer_auth HΨ") as "Hconsumer_auth".
            iSplitR "Hmtx_locked HΦ". { iExists (Set_ v). iFrameSteps. }
            iIntros "!> {%}".

            wp۰apply+ (mutex٠unlock𑁒spec with "[$Hmtx_inv $Hmtx_locked]"); iSteps.

          * iDestruct "Hstate" as "(:inv۰state۰set =1)".
            iDestruct (lstate𑁒unset₂𑁒set with "Hlstate_unset₂ Hlstate_set_1") as %[].

      - iDestruct "Hstate" as "(:inv۰state۰setting)".
        iSplitR "HΦ". { iFrameSteps. }
        iIntros "!> {%}".

        wp۰apply+ (mutex٠synchronize𑁒spec with "[$]") as "_".
        wp۰apply+ "HLöb".
        iSteps.

      - iDestruct "Hstate" as "(:inv۰state۰set)".
        iSplitR "HΦ". { iFrameSteps. }
        iSteps.
    Qed.
    Lemma lazy٠get𑁒spec𑁒result t γ Ψ Ξ v :
      {{{
        lazy۰inv t γ Ψ Ξ ∗
        lazy۰result γ v
      }}}
        lazy٠get #t
      {{{
        RET v;
        £ 2
      }}}.
    Proof.
      iIntros "%Φ ((:inv) & (:result)) HΦ".

      wp۰rec credits:"H£".
      iApply (lc_weaken 2) in "H£"; first done.

      wp۰bind (!_)%E.
      iInv "Hinv" as "(:inv۰inner)".
      wp۰load.
      iMod (inv۰state𑁒lstate۰set with "Hstate Hlstate_set") as "(-> & (:inv۰state۰set =1))".
      iSplitR "H£ HΦ". { iFrameSteps. }
      iSteps.
    Qed.
  End lazy۰G.

  #[global] Opaque lazy۰inv.
  #[global] Opaque lazy۰consumer.
  #[global] Opaque lazy۰result.
End base.

Require zoo_std.lazy__opaque.

Section lazy۰G.
  Context `{lazy۰G : LazyG Σ}.

  Implicit Types 𝑡 : location.
  Implicit Types t : val.
  Implicit Types γ : base.lazy۰name.
  Implicit Types Ψ Χ Ξ : val → iProp Σ.

  Definition lazy۰inv t Ψ Ξ : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.lazy۰inv 𝑡 γ Ψ Ξ.
  #[local] Instance : CustomIpat "inv" :=
    " ( %l{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hinv{_{}}
      )
    ".

  Definition lazy۰consumer t Χ : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.lazy۰consumer γ Χ.
  #[local] Instance : CustomIpat "consumer" :=
    " ( %l{;_}
      & %γ{;_}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hconsumer{_{}}
      )
    ".

  Definition lazy۰result t v : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.lazy۰result γ v.
  #[local] Instance : CustomIpat "result" :=
    " ( %l{;_}
      & %γ{;_}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hresult{_{}}
      )
    ".
  Definition lazy۰resolved t : iProp Σ :=
    ∃ v,
    lazy۰result t v.

  #[global] Instance lazy۰inv𑁒contractive t n :
    Proper (
      (pointwise_relation _ (dist_later n)) ==>
      (pointwise_relation _ (dist_later n)) ==>
      (≡{n}≡)
    ) (lazy۰inv t).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance lazy۰inv𑁒proper t :
    Proper (
      (pointwise_relation _ (≡)) ==>
      (pointwise_relation _ (≡)) ==>
      (≡)
    ) (lazy۰inv t).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance lazy۰consumer𑁒contractive t n :
    Proper (
      (pointwise_relation _ (dist_later n)) ==>
      (≡{n}≡)
    ) (lazy۰consumer t).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance lazy۰consumer𑁒proper t :
    Proper (
      (pointwise_relation _ (≡)) ==>
      (≡)
    ) (lazy۰consumer t).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance lazy۰result𑁒timeless t v :
    Timeless (lazy۰result t v).
  Proof.
    apply _.
  Qed.

  #[global] Instance lazy۰inv𑁒persistent t Ψ Ξ :
    Persistent (lazy۰inv t Ψ Ξ).
  Proof.
    apply _.
  Qed.
  #[global] Instance lazy۰result𑁒persistent t v :
    Persistent (lazy۰result t v).
  Proof.
    apply _.
  Qed.

  Lemma lazy۰consumer𑁒wand {t Ψ Ξ Χ1} Χ2 :
    lazy۰inv t Ψ Ξ -∗
    lazy۰consumer t Χ1 -∗
    (∀ v, Χ1 v -∗ Χ2 v) ={⊤}=∗
    lazy۰consumer t Χ2.
  Proof.
    iIntros "(:inv =1) (:consumer =2) H". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->.
    iDestruct (base.lazy۰consumer𑁒wand with "Hinv_1 Hconsumer_2 H") as "H".
    iSteps.
  Qed.
  Lemma lazy۰consumer𑁒divide {t Ψ Ξ} Χs :
    lazy۰inv t Ψ Ξ -∗
    lazy۰consumer t (λ v, [∗ list] Χ ∈ Χs, Χ v) ={⊤}=∗
    [∗ list] Χ ∈ Χs, lazy۰consumer t Χ.
  Proof.
    iIntros "(:inv =1) (:consumer =2)". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->.
    iDestruct (base.lazy۰consumer𑁒divide with "Hinv_1 Hconsumer_2") as "H".
    iApply (big_sepL_impl with "H").
    iSteps.
  Qed.
  Lemma lazy۰consumer𑁒split {t Ψ Ξ} Χ1 Χ2 :
    lazy۰inv t Ψ Ξ -∗
    lazy۰consumer t (λ v, Χ1 v ∗ Χ2 v) ={⊤}=∗
      lazy۰consumer t Χ1 ∗
      lazy۰consumer t Χ2.
  Proof.
    iIntros "Hinv Hconsumer".
    iMod (lazy۰consumer𑁒divide [Χ1;Χ2] with "Hinv [Hconsumer]") as "($ & $ & _)" => //.
    { simpl. setoid_rewrite bi.sep_emp => //. }
  Qed.

  Lemma lazy۰result𑁒agree t v1 v2 :
    lazy۰result t v1 -∗
    lazy۰result t v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    iIntros "(:result =1) (:result =2)". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.lazy۰result𑁒agree with "Hresult_1 Hresult_2").
  Qed.

  Lemma lazy𑁒inv𑁒result t Ψ Ξ v :
    lazy۰inv t Ψ Ξ -∗
    lazy۰result t v ={⊤}=∗
    ▷ □ Ξ v.
  Proof.
    iIntros "(:inv =1) (:result =2)". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.lazy𑁒inv𑁒result with "Hinv_1 Hresult_2").
  Qed.
  Lemma lazy𑁒inv_result' t Ψ Ξ v :
    £ 1 -∗
    lazy۰inv t Ψ Ξ -∗
    lazy۰result t v ={⊤}=∗
    □ Ξ v.
  Proof.
    iIntros "H£ Hinv Hresult".
    iMod (lazy𑁒inv𑁒result with "Hinv Hresult") as "HΞ".
    iApply (lc_fupd_elim_later with "H£ HΞ").
  Qed.
  Lemma lazy𑁒inv𑁒result𑁒consumer t Ψ Ξ v Χ :
    lazy۰inv t Ψ Ξ -∗
    lazy۰result t v -∗
    lazy۰consumer t Χ ={⊤}=∗
      ▷^2 Χ v ∗
      ▷ □ Ξ v.
  Proof.
    iIntros "(:inv =1) (:result =2) (:consumer =3)". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->.
    iDestruct (meta𑁒agree with "Hmeta_2 Hmeta_3") as %<-.
    iApply (base.lazy𑁒inv𑁒result𑁒consumer with "Hinv_1 Hresult_2 Hconsumer_3").
  Qed.
  Lemma lazy𑁒inv𑁒result𑁒consumer' t Ψ Ξ v Χ :
    £ 2 -∗
    lazy۰inv t Ψ Ξ -∗
    lazy۰result t v -∗
    lazy۰consumer t Χ ={⊤}=∗
      Χ v ∗
      □ Ξ v.
  Proof.
    iIntros "(H£1 & H£2) Hinv Hresult Hconsumer".
    iMod (lazy𑁒inv𑁒result𑁒consumer with "Hinv Hresult Hconsumer") as "H".
    rewrite -bi.later_sep.
    iMod (lc_fupd_elim_later with "H£1 H") as "(HΧ & $)".
    iApply (lc_fupd_elim_later with "H£2 HΧ").
  Qed.

  Lemma lazy٠make𑁒spec Ψ Ξ fn :
    {{{
      WP fn () {{ v,
        ▷ Ψ v ∗
        ▷ □ Ξ v
      }}
    }}}
      lazy٠make fn
    {{{
      t
    , RET t;
      lazy۰inv t Ψ Ξ ∗
      lazy۰consumer t Ψ
    }}}.
  Proof.
    iIntros "%Φ Hfn HΦ".

    iApply wp𑁒fupd.
    wp۰apply (base.lazy٠make𑁒spec with "Hfn") as (𝑡 γ) "(Hmeta & Hinv & Hconsumer)".
    iMod (meta𑁒set γ with "Hmeta") as "#Hmeta"; first done.
    iSteps.
  Qed.

  Lemma lazy٠return𑁒spec Ψ Ξ v :
    {{{
      ▷ Ψ v ∗
      ▷ □ Ξ v
    }}}
      lazy٠return v
    {{{
      t
    , RET t;
      lazy۰inv t Ψ Ξ ∗
      lazy۰result t v ∗
      lazy۰consumer t Ψ
    }}}.
  Proof.
    iIntros "%Φ (HΨ & HΞ) HΦ".

    iApply wp𑁒fupd.
    wp۰apply (base.lazy٠return𑁒spec Ψ with "[$]") as (𝑡 γ) "(Hmeta & Hinv & Hresult & Hconsumer)".
    iMod (meta𑁒set γ with "Hmeta") as "#Hmeta"; first done.
    iSteps.
  Qed.

  Lemma lazy٠is_set𑁒spec t Ψ Ξ :
    {{{
      lazy۰inv t Ψ Ξ
    }}}
      lazy٠is_set t
    {{{
      b
    , RET #b;
      if b then
        £ 2 ∗
        lazy۰resolved t
      else
        True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰apply (base.lazy٠is_set𑁒spec with "[$]") as (b) "Hb".
    rewrite /lazy۰resolved. destruct b; iSteps.
  Qed.
  Lemma lazy٠is_set𑁒spec𑁒result t Ψ Ξ v :
    {{{
      lazy۰inv t Ψ Ξ ∗
      lazy۰result t v
    }}}
      lazy٠is_set t
    {{{
      RET true;
      £ 2
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:result =2)) HΦ". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp۰apply (base.lazy٠is_set𑁒spec𑁒result with "[$] HΦ").
  Qed.

  Lemma lazy٠is_unset𑁒spec t Ψ Ξ :
    {{{
      lazy۰inv t Ψ Ξ
    }}}
      lazy٠is_unset t
    {{{
      b
    , RET #b;
      if b then
        True
      else
        £ 2 ∗
        lazy۰resolved t
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰apply (base.lazy٠is_unset𑁒spec with "[$]") as (b) "Hb".
    rewrite /lazy۰resolved. destruct b; iSteps.
  Qed.
  Lemma lazy٠is_unset𑁒spec𑁒result t Ψ Ξ v :
    {{{
      lazy۰inv t Ψ Ξ ∗
      lazy۰result t v
    }}}
      lazy٠is_unset t
    {{{
      RET false;
      £ 2
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:result =2)) HΦ". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp۰apply (base.lazy٠is_unset𑁒spec𑁒result with "[$] HΦ").
  Qed.

  Lemma lazy٠get𑁒spec t Ψ Ξ :
    {{{
      lazy۰inv t Ψ Ξ
    }}}
      lazy٠get t
    {{{
      v
    , RET v;
      £ 2 ∗
      lazy۰result t v
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰apply (base.lazy٠get𑁒spec with "[$]").
    iSteps.
  Qed.
  Lemma lazy٠get𑁒spec𑁒result t Ψ Ξ v :
    {{{
      lazy۰inv t Ψ Ξ ∗
      lazy۰result t v
    }}}
      lazy٠get t
    {{{
      RET v;
      £ 2
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:result =2)) HΦ". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp۰apply (base.lazy٠get𑁒spec𑁒result with "[$] HΦ").
  Qed.
End lazy۰G.

#[global] Opaque lazy۰inv.
#[global] Opaque lazy۰consumer.
#[global] Opaque lazy۰result.
