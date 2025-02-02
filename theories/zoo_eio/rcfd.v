From zoo Require Import
  prelude.
From zoo.common Require Import
  countable
  gmultiset.
From zoo.iris.base_logic Require Import
  lib.auth_gmultiset
  lib.auth_mono.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  option
  spsc_waiter.
From unix Require Import
  unix.
From zoo_eio Require Export
  base
  rcfd__code.
From zoo_eio Require Import
  rcfd__types.
From zoo Require Import
  options.

Implicit Types b closing : bool.
Implicit Types ops : Z.
Implicit Types q : Qp.
Implicit Types qs : gmultiset Qp.
Implicit Types l l_state : location.
Implicit Types t v v_state fd fn : val.
Implicit Types o : option val.

Inductive state :=
  | Open
  | Closing fn.
Implicit Types state : state.

#[local] Instance state_inhabited : Inhabited state :=
  populate Open.
#[local] Instance state_eq_dec : EqDecision state :=
  ltac:(solve_decision).

#[local] Definition state_to_val open fd state :=
  match state with
  | Open =>
      ‘Open@open( fd )
  | Closing fn =>
      ‘Closing( fn )
  end%V.
#[local] Arguments state_to_val _ _ !_ / : assert.

#[local] Instance state_to_val_physical open fd state :
  ValPhysical (state_to_val open fd state).
Proof.
  destruct state; done.
Qed.

Inductive lstate :=
  | LOpen
  | LClosingUsers
  | LClosingNoUsers.
Implicit Types lstate : lstate.

#[global] Instance lstate_inhabited : Inhabited lstate :=
  populate LOpen.
#[global] Instance lstate_eq_dec : EqDecision lstate :=
  ltac:(solve_decision).

Inductive lstep : relation lstate :=
  | lstep_close_users :
      lstep LOpen LClosingUsers
  | lstep_close_no_users :
      lstep LClosingUsers LClosingNoUsers.
#[local] Hint Constructors lstep : core.

Class RcfdG Σ `{zoo_G : !ZooG Σ} := {
  #[local] rcfd_G_spsc_waiter_G :: SpscWaiterG Σ ;
  #[local] rcfd_G_tokens_G :: AuthGmultisetG Σ Qp ;
  #[local] rcfd_G_lstate_G :: AuthMonoG Σ (A := leibnizO lstate) lstep ;
}.

Definition rcfd_Σ := #[
  spsc_waiter_Σ ;
  auth_gmultiset_Σ Qp ;
  auth_mono_Σ (A := leibnizO lstate) lstep
].
#[global] Instance subG_rcfd_Σ `{zoo_G : !ZooG Σ} :
  subG rcfd_Σ Σ →
  RcfdG Σ.
Proof.
  solve_inG.
Qed.

Section rcfd_G.
  Context `{rcfd_G : RcfdG Σ}.

  Record metadata := {
    metadata_tokens : gname ;
    metadata_lstate : gname ;
    metadata_open : block_id ;
  }.
  Implicit Types γ : metadata.

  #[global] Instance metadata_eq_dec : EqDecision metadata :=
    ltac:(solve_decision).
  #[global] Instance metadata_countable :
    Countable metadata.
  Proof.
    solve_countable.
  Qed.

  #[local] Definition tokens_auth' γ_tokens qs :=
    auth_gmultiset_auth γ_tokens (DfracOwn 1) qs.
  #[local] Definition tokens_auth γ qs :=
    tokens_auth' γ.(metadata_tokens) qs.
  #[local] Definition tokens_frag γ q :=
    auth_gmultiset_frag γ.(metadata_tokens) {[+q+]}.

  #[local] Definition lstate_auth' γ_lstate lstate :=
    auth_mono_auth _ γ_lstate (DfracOwn 1) lstate.
  #[local] Definition lstate_auth γ lstate :=
    lstate_auth' γ.(metadata_lstate) lstate.
  #[local] Definition lstate_lb γ lstate :=
    auth_mono_lb _ γ.(metadata_lstate) lstate.

  #[local] Definition inv_inner l γ fd chars : iProp Σ :=
    ∃ state lstate ops,
    l.[ops] ↦ #ops ∗
    l.[state] ↦ state_to_val γ.(metadata_open) fd state ∗
    lstate_auth γ lstate ∗
    match lstate with
    | LOpen =>
        ∃ q qs,
        ⌜ops = size qs ∧ set_fold Qp.add q qs = 1%Qp⌝ ∗
        ⌜state = Open⌝ ∗
        tokens_auth γ qs ∗
        unix_fd_model fd (DfracOwn q) chars
    | LClosingUsers =>
        ∃ q qs fn,
        ⌜ops = size qs ∧ 0 < size qs ∧ set_fold Qp.add q qs = 1%Qp⌝ ∗
        ⌜state = Closing fn⌝ ∗
        tokens_auth γ qs ∗
        unix_fd_model fd (DfracOwn q) chars ∗
        (unix_fd_model fd (DfracOwn 1) chars -∗ WP fn () {{ res, ⌜res = ()%V⌝ }})
    | LClosingNoUsers =>
        ∃ fn,
        ⌜state = Closing fn⌝ ∗
        WP fn () {{ res, ⌜res = ()%V⌝ }}
    end.
  Definition rcfd_inv t fd chars : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    inv nroot (inv_inner l γ fd chars).

  Definition rcfd_token t q : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    tokens_frag γ q.

  Definition rcfd_closing t : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    lstate_lb γ LClosingUsers.

  #[global] Instance rcfd_inv_timeless t q :
    Timeless (rcfd_token t q).
  Proof.
    apply _.
  Qed.
  #[global] Instance rcfd_inv_persistent t fd chars :
    Persistent (rcfd_inv t fd chars).
  Proof.
    apply _.
  Qed.

  #[global] Instance rcfd_token_timeless t q :
    Timeless (rcfd_token t q).
  Proof.
    apply _.
  Qed.

  #[global] Instance rcfd_closing_timeless t :
    Timeless (rcfd_closing t).
  Proof.
    apply _.
  Qed.
  #[global] Instance rcfd_closing_persistent t :
    Persistent (rcfd_closing t).
  Proof.
    apply _.
  Qed.

  #[local] Lemma tokens_alloc :
    ⊢ |==>
      ∃ γ_tokens,
      tokens_auth' γ_tokens ∅.
  Proof.
    apply auth_gmultiset_alloc.
  Qed.
  #[local] Lemma tokens_elem_of γ qs q :
    tokens_auth γ qs -∗
    tokens_frag γ q -∗
    ⌜q ∈ qs⌝.
  Proof.
    apply auth_gmultiset_elem_of.
  Qed.
  #[local] Lemma tokens_update_alloc {γ qs} q :
    tokens_auth γ qs ⊢ |==>
      tokens_auth γ (qs ⊎ {[+q+]}) ∗
      tokens_frag γ q.
  Proof.
    apply auth_gmultiset_update_alloc_singleton.
  Qed.
  #[local] Lemma tokens_update_dealloc γ qs q :
    tokens_auth γ qs -∗
    tokens_frag γ q ==∗
    tokens_auth γ (qs ∖ {[+q+]}).
  Proof.
    apply auth_gmultiset_update_dealloc.
  Qed.

  #[local] Lemma lstate_alloc :
    ⊢ |==>
      ∃ γ_lstate,
      lstate_auth' γ_lstate LOpen.
  Proof.
    apply auth_mono_alloc.
  Qed.
  #[local] Lemma lstate_lb_get γ lstate :
    lstate_auth γ lstate ⊢
    lstate_lb γ lstate.
  Proof.
    apply auth_mono_lb_get.
  Qed.
  #[local] Lemma lstate_lb_mono {γ lstate} lstate' :
    lstep lstate' lstate →
    lstate_lb γ lstate ⊢
    lstate_lb γ lstate'.
  Proof.
    apply auth_mono_lb_mono'.
  Qed.
  #[local] Lemma lstate_valid γ lstate lstate' :
    lstate_auth γ lstate -∗
    lstate_lb γ lstate' -∗
    ⌜rtc lstep lstate' lstate⌝.
  Proof.
    apply: auth_mono_lb_valid.
  Qed.
  #[local] Lemma lstate_valid_closing_users γ lstate :
    lstate_auth γ lstate -∗
    lstate_lb γ LClosingUsers -∗
    ⌜lstate = LClosingUsers ∨ lstate = LClosingNoUsers⌝.
  Proof.
    iIntros "Hlstate_auth Hlstate_lb".
    iDestruct (lstate_valid with "Hlstate_auth Hlstate_lb") as %Hlsteps.
    iPureIntro.
    apply rtc_inv in Hlsteps as [<- | (lstate' & Hlstep & Hlsteps)]; first naive_solver.
    invert Hlstep.
    apply rtc_inv in Hlsteps as [<- | (lstate' & Hlstep & Hlsteps)]; first naive_solver.
    invert Hlstep.
  Qed.
  #[local] Lemma lstate_valid_closing_no_users γ lstate :
    lstate_auth γ lstate -∗
    lstate_lb γ LClosingNoUsers -∗
    ⌜lstate = LClosingNoUsers⌝.
  Proof.
    iIntros "Hlstate_auth Hlstate_lb".
    iDestruct (lstate_valid with "Hlstate_auth Hlstate_lb") as %Hlsteps.
    iPureIntro.
    apply rtc_inv in Hlsteps as [<- | (lstate' & Hlstep & Hlsteps)]; first naive_solver.
    invert Hlstep.
  Qed.
  #[local] Lemma lstate_update {γ lstate} lstate' :
    lstep lstate lstate' →
    lstate_auth γ lstate ⊢ |==>
    lstate_auth γ lstate'.
  Proof.
    apply auth_mono_update'.
  Qed.

  Lemma rcfd_make_spec fd chars :
    {{{
      unix_fd_model fd (DfracOwn 1) chars
    }}}
      rcfd_make fd
    {{{ t,
      RET t;
      rcfd_inv t fd chars
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".

    wp_rec.
    wp_reveal open.
    wp_block l as "Hmeta" "(Hops & Hfd & _)".

    iMod tokens_alloc as "(%γ_tokens & Htokens_auth)".
    iMod lstate_alloc as "(%γ_lstate & Hlstate_auth)".
    pose γ := {|
      metadata_tokens := γ_tokens ;
      metadata_lstate := γ_lstate ;
      metadata_open := open ;
    |}.
    iMod (meta_set _ _ γ with "Hmeta") as "Hmeta"; first done.

    iApply "HΦ".
    iStep 2. iApply inv_alloc.
    iExists Open. iStep 4. iExists 1%Qp, ∅. iSteps.
  Qed.

  #[local] Lemma rcfd_put_spec' l γ fd chars :
    {{{
      inv nroot (inv_inner l γ fd chars) ∗
      ( ( ∃ q,
          tokens_frag γ q ∗
          unix_fd_model fd (DfracOwn q) chars
        )
      ∨ lstate_lb γ LClosingNoUsers
      )
    }}}
      rcfd_put #l
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & H) HΦ".

    wp_rec. wp_pures.

    wp_bind (FAA _ _).
    iInv "Hinv" as "(%state1 & %lstate1 & %ops1 & Hops & Hfd & Hlstate_auth & Hlstate1)".
    wp_faa.
    iSplitR "HΦ".
    { iDestruct "H" as "[(%q & Htokens_frag & Hmodel) | #Hlstate_lb]".
      - destruct lstate1.
        + iDestruct "Hlstate1" as "(%q' & %qs & (-> & %Hqs) & -> & Htokens_auth & Hmodel')".
          iDestruct (tokens_elem_of with "Htokens_auth Htokens_frag") as %Hq.
          iExists Open. iStep 3. iExists (q + q')%Qp, (qs ∖ {[+q+]}).
          iSplitR; [iSplitR; iPureIntro | iSplitR; [| iSplitR "Hmodel Hmodel'"]].
          * assert (qs ≠ ∅) as Hqs_size%gmultiset_size_non_empty_iff by multiset_solver.
            rewrite gmultiset_size_difference; first multiset_solver.
            rewrite gmultiset_size_singleton. lia.
          * rewrite (gmultiset_disj_union_difference' q qs) // gmultiset_set_fold_disj_union gmultiset_set_fold_singleton // in Hqs.
          * iSteps.
          * iMod (tokens_update_dealloc with "Htokens_auth Htokens_frag") as "$". iSteps.
          * iCombine "Hmodel Hmodel'" as "$". iSteps.
        + iDestruct "Hlstate1" as "(%q' & %qs & %fn1 & (-> & %Hqs_size & %Hqs) & -> & Htokens_auth & Hmodel' & Hfn1)".
          iDestruct (tokens_elem_of with "Htokens_auth Htokens_frag") as %Hq.
          destruct (decide (size qs = 1)) as [Hqs_size' | Hqs_size'].
          * apply gmultiset_size_1_elem_of in Hqs_size' as (q_ & ->%leibniz_equiv). rewrite gmultiset_set_fold_singleton in Hqs.
            apply gmultiset_elem_of_singleton in Hq as <-.
            iMod (tokens_update_dealloc with "Htokens_auth Htokens_frag") as "Htokens_auth".
            rewrite gmultiset_difference_diag.
            iMod (lstate_update LClosingNoUsers with "Hlstate_auth") as "Hlstate_auth"; first done.
            iCombine "Hmodel Hmodel'" as "Hmodel". rewrite Hqs. iDestruct ("Hfn1" with "Hmodel") as "Hfn1".
            iExists (Closing _). iStep 4. done.
          * iMod (tokens_update_dealloc with "Htokens_auth Htokens_frag") as "Htokens_auth".
            iCombine "Hmodel Hmodel'" as "Hmodel".
            iExists (Closing _). iStep 3. iExists (q + q')%Qp, (qs ∖ {[+q+]}). iSteps; iPureIntro.
            -- rewrite gmultiset_size_difference; first multiset_solver.
               rewrite gmultiset_size_singleton. lia.
            -- rewrite gmultiset_size_difference; first multiset_solver.
               rewrite gmultiset_size_singleton. lia.
            -- rewrite (gmultiset_disj_union_difference' q qs) // gmultiset_set_fold_disj_union gmultiset_set_fold_singleton // in Hqs.
        + iDestruct "Hlstate1" as "(%fn1 & -> & Hfn1)".
          iExists (Closing _). iStep 4. done.
      - iDestruct (lstate_valid_closing_no_users with "Hlstate_auth Hlstate_lb") as %->.
        iDestruct "Hlstate1" as "(%fn1 & -> & Hfn1)".
        iExists (Closing _). iStep 4. done.
    }
    iModIntro. clear.

    wp_pures. destruct (decide (ops1 = 1)) as [-> | Hops]; wp_pures; last iSteps.

    wp_bind (_.{state})%E.
    iInv "Hinv" as "(%state2 & %lstate2 & %ops2 & Hops & Hfd & Hlstate_auth & Hlstate2)".
    wp_load.
    destruct (decide (lstate2 = LOpen)) as [-> | Hlstate2].

    - iDestruct "Hlstate2" as "(%q & %qs & (-> & %Hqs) & -> & Htokens_auth & Hmodel)".
      iSplitR "HΦ". { iExists Open. iSteps. }
      iSteps.

    - iAssert (∃ fn2, ⌜state2 = Closing fn2⌝ ∗ lstate_lb γ LClosingUsers)%I as "(%fn2 & -> & #Hlstate_lb)".
      { destruct lstate2; first done.
        - iDestruct "Hlstate2" as "(%q & %qs & %fn2 & _ & -> & _)".
          iDestruct (lstate_lb_get with "Hlstate_auth") as "$".
          iSteps.
        - iDestruct "Hlstate2" as "(%fn2 & -> & _)".
          iDestruct (lstate_lb_get with "Hlstate_auth") as "Hlstate_lb".
          iDestruct (lstate_lb_mono LClosingUsers with "Hlstate_lb") as "Hlstate_lb"; first done.
          iSteps.
      }
      iSplitR "HΦ". { iExists (Closing _). iSteps. }
      iModIntro. clear.

      wp_pures.

      wp_bind (_.{ops})%E.
      iInv "Hinv" as "(%state3 & %lstate3 & %ops3 & Hops & Hfd & Hlstate_auth & Hlstate3)".
      wp_load.
      iDestruct (lstate_valid_closing_users with "Hlstate_auth Hlstate_lb") as %[-> | ->].

      + iDestruct "Hlstate3" as "(%q & %qs & %fn3 & (-> & %Hqs_size & %Hqs) & -> & Htokens_auth & Hmodel & Hfn3)".
        iSplitR "HΦ". { iExists (Closing _). iSteps. }
        iSteps.

      + iDestruct "Hlstate3" as "(%fn3 & -> & Hfn3)".
        iClear "Hlstate_lb". iDestruct (lstate_lb_get with "Hlstate_auth") as "#Hlstate_lb".
        iSplitR "HΦ". { iExists (Closing _). iStep 4. done. }
        iModIntro. clear.

        wp_pures. case_bool_decide as Hops3; wp_pures; last iSteps.

        wp_bind (CAS _ _ _).
        iInv "Hinv" as "(%state4 & %lstate4 & %ops4 & Hops & Hfd & Hlstate_auth & Hlstate4)".
        wp_cas as _ | Hcas; first iSteps.
        destruct state4; first naive_solver. destruct Hcas as (_ & _ & [= <-]).
        iDestruct (lstate_valid_closing_no_users with "Hlstate_auth Hlstate_lb") as %->.
        iDestruct "Hlstate4" as (fn4 [= <-]) "Hfn4".
        iSplitR "Hfn4 HΦ". { iExists (Closing _). iSteps. }
        iSteps.
  Qed.
  #[local] Lemma rcfd_put_spec t fd chars q :
    {{{
      rcfd_inv t fd chars ∗
      rcfd_token t q ∗
      unix_fd_model fd (DfracOwn q) chars
    }}}
      rcfd_put t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ ((%l & %γ & -> & #Hmeta & #Hinv) & (%_l & %_γ & %Heq & _Hmeta & Htokens_frag) & Hmodel) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iApply (rcfd_put_spec' with "[$Hinv Htokens_frag Hmodel] HΦ").
    iSteps.
  Qed.

  #[local] Lemma rcfd_get_spec t fd chars :
    {{{
      rcfd_inv t fd chars
    }}}
      rcfd_get t
    {{{ o,
      RET (o : val);
      match o with
      | None =>
          True
      | Some fd_ =>
          ∃ q,
          ⌜fd_ = fd⌝ ∗
          rcfd_token t q ∗
          unix_fd_model fd (DfracOwn q) chars
      end
    }}}.
  Proof.
    iIntros "%Φ (%l & %γ & -> & #Hmeta & #Hinv) HΦ".

    wp_rec. wp_pures.

    wp_bind (FAA _ _).
    iInv "Hinv" as "(%state1 & %lstate1 & %ops1 & Hops & Hfd & Hlstate_auth & Hlstate1)".
    wp_faa.
    iAssert (|==>
      inv_inner l γ fd chars ∗
      ( ( ∃ q,
          tokens_frag γ q ∗
          unix_fd_model fd (DfracOwn q) chars
        )
      ∨ lstate_lb γ LClosingNoUsers
      )
    )%I with "[- HΦ]" as ">($ & H)".
    { destruct lstate1.
      - iDestruct "Hlstate1" as "(%q & %qs & (-> & %Hqs) & -> & Htokens_auth & Hmodel)".
        iMod (tokens_update_alloc (q / 2) with "Htokens_auth") as "(Htokens_auth & Htokens_frag)".
        iDestruct "Hmodel" as "(Hmodel1 & Hmodel2)".
        iSplitR "Htokens_frag Hmodel2"; last iSteps.
        iExists Open. iStep 3. iExists (q / 2)%Qp, (qs ⊎ {[+q / 2+]})%Qp. iSteps; iPureIntro.
        + rewrite gmultiset_size_disj_union gmultiset_size_singleton. lia.
        + rewrite (comm (⊎)) gmultiset_set_fold_disj_union gmultiset_set_fold_singleton Qp.div_2 //.
      - iDestruct "Hlstate1" as "(%q & %qs & %fn1 & (-> & %Hqs_size & %Hqs) & -> & Htokens_auth & Hmodel & Hfn1)".
        iMod (tokens_update_alloc (q / 2) with "Htokens_auth") as "(Htokens_auth & Htokens_frag)".
        iDestruct "Hmodel" as "(Hmodel1 & Hmodel2)".
        iSplitR "Htokens_frag Hmodel2"; last iSteps.
        iExists (Closing _). iStep 3. iExists (q / 2)%Qp, (qs ⊎ {[+q / 2+]})%Qp. iSteps; iPureIntro.
        + rewrite gmultiset_size_disj_union gmultiset_size_singleton. lia.
        + rewrite gmultiset_size_disj_union. lia.
        + rewrite (comm (⊎)) gmultiset_set_fold_disj_union gmultiset_set_fold_singleton Qp.div_2 //.
      - iDestruct "Hlstate1" as "(%fn1 & -> & Hfn1)".
        iDestruct (lstate_lb_get with "Hlstate_auth") as "#Hlstate_lb".
        iSplitL; last iSteps.
        iExists (Closing _). iSteps.
    }
    iModIntro. wp_pures. clear.

    wp_bind (_.{state})%E.
    iInv "Hinv" as "(%state2 & %lstate2 & %ops2 & Hops & Hfd & Hlstate_auth & Hlstate2)".
    wp_load.
    destruct (decide (lstate2 = LOpen)) as [-> | Hlstate2].

    - iDestruct "Hlstate2" as "(%q & %qs & (-> & %Hqs) & -> & Htokens_auth & Hmodel)".
      iDestruct "H" as "[(%q' & Htokens_frag & Hmodel') | Hlstate_lb]"; last first.
      { iDestruct (lstate_valid_closing_no_users with "Hlstate_auth Hlstate_lb") as %?. done. }
      iSplitR "Htokens_frag Hmodel' HΦ". { iExists Open. iSteps. }
      iModIntro. clear.

      wp_pures.
      iApply ("HΦ" $! (Some _)). iSteps.

    - iAssert ⌜∃ fn2, state2 = Closing fn2⌝%I as %(fn2 & ->).
      { destruct lstate2; iDecompose "Hlstate2"; iSteps. }
      iSplitR "H HΦ". { iExists (Closing fn2). iSteps. }
      iModIntro. clear.

      wp_smart_apply (rcfd_put_spec' with "[$Hinv $H]") as "_".
      iSteps. iApply ("HΦ" $! None). iSteps.
  Qed.

  #[local] Lemma rcfd_close_spec' closing t fd chars :
    {{{
      rcfd_inv t fd chars ∗
      if closing then
        rcfd_closing t
      else
        True
    }}}
      rcfd_close t
    {{{ b,
      RET #b;
      if closing then
        ⌜b = false⌝
      else
        rcfd_closing t
    }}}.
  Proof.
    iIntros "%Φ ((%l & %γ & -> & #Hmeta & #Hinv) & Hclosing) HΦ".

    wp_rec. wp_pures.

    wp_bind (_.{state})%E.
    iInv "Hinv" as "(%state1 & %lstate1 & %ops1 & Hops & Hfd & Hlstate_auth & Hlstate1)".
    wp_load.
    destruct (decide (lstate1 = LOpen)) as [-> | Hlstate1].

    - iDestruct "Hlstate1" as "(%q & %qs & (-> & %Hqs) & -> & Htokens_auth & Hmodel)".
      destruct closing; last iClear "Hclosing".
      { iDestruct "Hclosing" as "(%_l & %_γ & %Heq & _Hmeta & Hlstate_lb)". injection Heq as <-.
        iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
        iDestruct (lstate_valid_closing_users with "Hlstate_auth Hlstate_lb") as %[[=] | [=]].
      }
      iSplitR "HΦ". { iExists Open. iSteps. }
      iModIntro. clear.

      wp_pures.

      wp_bind (CAS _ _ _).
      iInv "Hinv" as "(%state2 & %lstate2 & %ops2 & Hops & Hfd & Hlstate_auth & Hlstate2)".
      wp_cas as Hcas | Hcas.

      + iAssert (⌜∃ fn2, state2 = Closing fn2⌝ ∗ lstate_lb γ LClosingUsers)%I as "((%fn2 & ->) & #Hlstate_lb)".
        { destruct lstate2; iDecompose "Hlstate2"; first naive_solver.
          - iDestruct (lstate_lb_get with "Hlstate_auth") as "$".
            iSteps.
          - iDestruct (lstate_lb_get with "Hlstate_auth") as "Hlstate_lb".
            iDestruct (lstate_lb_mono with "Hlstate_lb") as "$"; first done.
            iSteps.
        }
        iSplitR "HΦ". { iExists (Closing _). iSteps. }
        iSteps.

      + destruct state2; last naive_solver.
        destruct (decide (lstate2 = LOpen)) as [-> | Hlstate2]; last first.
        { destruct lstate2; iDecompose "Hlstate2"; iSteps. }
        iDestruct "Hlstate2" as "(%q & %qs & (-> & %Hqs) & _ & Htokens_auth & Hmodel)".
        iMod (lstate_update LClosingUsers with "Hlstate_auth") as "Hlstate_auth"; first done.
        iDestruct (lstate_lb_get with "Hlstate_auth") as "#Hlstate_lb".
        iSplitR "HΦ".
        { destruct (decide (size qs = 0)) as [Hqs_size | Hqs_size].
          - apply gmultiset_size_empty_iff in Hqs_size as ->.
            rewrite gmultiset_set_fold_empty in Hqs. rewrite {}Hqs.
            iMod (lstate_update LClosingNoUsers with "Hlstate_auth") as "Hlstate_auth"; first done.
            iExists (Closing _). iSteps. iModIntro.
            wp_apply (unix_close_spec with "[$]").
            iSteps.
          - iExists (Closing _). iSteps. iModIntro.
            wp_apply (unix_close_spec with "[$]").
            iSteps.
        }
        iModIntro. clear.

        wp_pures.

        wp_bind (_.{ops})%E.
        iInv "Hinv" as "(%state3 & %lstate3 & %ops3 & Hops & Hfd & Hlstate_auth & Hlstate3)".
        wp_load.
        destruct (decide (ops3 = 0)) as [-> | Hops3]; last iSteps.
        iDestruct (lstate_valid_closing_users with "Hlstate_auth Hlstate_lb") as %[-> | ->].
        { iDestruct "Hlstate3" as "(%q & %qs & %fn3 & (% & % & _) & _)". lia. }
        iDestruct "Hlstate3" as "(%fn3 & -> & Hfn3)".
        iRename "Hlstate_lb" into "Hlstate_lb'". iDestruct (lstate_lb_get with "Hlstate_auth") as "#Hlstate_lb".
        iSplitR "HΦ". { iExists (Closing _). iStep 4. done. }
        iModIntro. clear.

        wp_pures.

        wp_bind (CAS _ _ _).
        iInv "Hinv" as "(%state4 & %lstate4 & %ops4 & Hops & Hfd & Hlstate_auth & Hlstate4)".
        wp_cas as _ | Hcas; first iSteps.

        iDestruct (lstate_valid_closing_no_users with "Hlstate_auth Hlstate_lb") as %->.
        iDestruct "Hlstate4" as "(%fn4 & -> & Hfn4)".
        destruct Hcas as (_ & _ & [= ->]).
        iSplitR "Hfn4 HΦ". { iExists (Closing _). iSteps. }
        iModIntro. clear.

        wp_smart_apply (wp_wand with "Hfn4").
        iSteps.

    - iAssert (⌜∃ fn1, state1 = Closing fn1⌝ ∗ lstate_lb γ LClosingUsers)%I as "((%fn1 & ->) & #Hlstate_lb)".
      { destruct lstate1; iDecompose "Hlstate1".
        - iDestruct (lstate_lb_get with "Hlstate_auth") as "$".
          iSteps.
        - iDestruct (lstate_lb_get with "Hlstate_auth") as "Hlstate_lb".
          iDestruct (lstate_lb_mono with "Hlstate_lb") as "$"; first done.
          iSteps.
      }
      iSplitR "HΦ". { iExists (Closing _). iSteps. }
      iSteps. destruct closing; iSteps.
  Qed.
  Lemma rcfd_close_spec t fd chars :
    {{{
      rcfd_inv t fd chars
    }}}
      rcfd_close t
    {{{ b,
      RET #b;
      rcfd_closing t
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".
    wp_apply (rcfd_close_spec' false with "[$Hinv]").
    iSteps.
  Qed.
  Lemma rcfd_close_spec_closed t fd chars :
    {{{
      rcfd_inv t fd chars ∗
      rcfd_closing t
    }}}
      rcfd_close t
    {{{
      RET #false;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hclosing) HΦ".
    wp_apply (rcfd_close_spec' true with "[$Hinv $Hclosing]").
    iSteps.
  Qed.

  #[local] Lemma rcfd_remove_spec' closing t fd chars :
    {{{
      rcfd_inv t fd chars ∗
      if closing then
        rcfd_closing t
      else
        True
    }}}
      rcfd_remove t
    {{{ o,
      RET (o : val);
      if closing then
        ⌜o = None⌝
      else
        rcfd_closing t ∗
        match o with
        | None =>
            True
        | Some fd' =>
            ⌜fd' = fd⌝ ∗
            unix_fd_model fd (DfracOwn 1) chars
        end
    }}}.
  Proof.
    iIntros "%Φ ((%l & %γ & -> & #Hmeta & #Hinv) & Hclosing) HΦ".

    wp_rec. wp_pures.

    wp_bind (_.{state})%E.
    iInv "Hinv" as "(%state1 & %lstate1 & %ops1 & Hops & Hfd & Hlstate_auth & Hlstate1)".
    wp_load.
    destruct (decide (lstate1 = LOpen)) as [-> | Hlstate1].

    - iDestruct "Hlstate1" as "(%q & %qs & (-> & %Hqs) & -> & Htokens_auth & Hmodel)".
      destruct closing; last iClear "Hclosing".
      { iDestruct "Hclosing" as "(%_l & %_γ & %Heq & _Hmeta & Hlstate_lb)". injection Heq as <-.
        iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
        iDestruct (lstate_valid_closing_users with "Hlstate_auth Hlstate_lb") as %[[=] | [=]].
      }
      iSplitR "HΦ". { iExists Open. iSteps. }
      iModIntro. clear.

      wp_smart_apply (spsc_waiter_create_spec (unix_fd_model fd (DfracOwn 1) chars) with "[//]") as "%chan (#Hchan_inv & Hchan_producer & Hchan_consumer)".
      wp_pures.

      wp_bind (CAS _ _ _).
      iInv "Hinv" as "(%state2 & %lstate2 & %ops2 & Hops & Hfd & Hlstate_auth & Hlstate2)".
      wp_cas as Hcas | Hcas.

      + iAssert (⌜∃ fn2, state2 = Closing fn2⌝ ∗ lstate_lb γ LClosingUsers)%I as "((%fn2 & ->) & #Hlstate_lb)".
        { destruct lstate2; iDecompose "Hlstate2"; first naive_solver.
          - iDestruct (lstate_lb_get with "Hlstate_auth") as "$".
            iSteps.
          - iDestruct (lstate_lb_get with "Hlstate_auth") as "Hlstate_lb".
            iDestruct (lstate_lb_mono with "Hlstate_lb") as "$"; first done.
            iSteps.
        }
        iSplitR "HΦ". { iExists (Closing _). iSteps. }
        iSteps. iApply ("HΦ" $! None). iSteps.

      + destruct state2; last naive_solver.
        destruct (decide (lstate2 = LOpen)) as [-> | Hlstate2]; last first.
        { destruct lstate2; iDecompose "Hlstate2"; iSteps. }
        iDestruct "Hlstate2" as "(%q & %qs & (-> & %Hqs) & _ & Htokens_auth & Hmodel)".
        iMod (lstate_update LClosingUsers with "Hlstate_auth") as "Hlstate_auth"; first done.
        iDestruct (lstate_lb_get with "Hlstate_auth") as "#Hlstate_lb".
        iSplitR "Hchan_consumer HΦ".
        { destruct (decide (size qs = 0)) as [Hqs_size | Hqs_size].
          - apply gmultiset_size_empty_iff in Hqs_size as ->.
            rewrite gmultiset_set_fold_empty in Hqs. rewrite {}Hqs.
            iMod (lstate_update LClosingNoUsers with "Hlstate_auth") as "Hlstate_auth"; first done.
            iExists (Closing _). iStep 8. iModIntro.
            wp_apply (spsc_waiter_notify_spec with "[$Hchan_inv $Hchan_producer $Hmodel]").
            iSteps.
          - iExists (Closing _). iSteps as "Hmodel". iModIntro.
            wp_apply (spsc_waiter_notify_spec with "[$Hchan_inv $Hchan_producer $Hmodel]").
            iSteps.
        }
        iModIntro. clear.

        wp_smart_apply (spsc_waiter_wait_spec with "[$Hchan_inv $Hchan_consumer]") as "Hmodel".
        iSteps. iApply ("HΦ" $! (Some _)). iSteps.

    - iAssert (⌜∃ fn1, state1 = Closing fn1⌝ ∗ lstate_lb γ LClosingUsers)%I as "((%fn1 & ->) & #Hlstate_lb)".
      { destruct lstate1; iDecompose "Hlstate1".
        - iDestruct (lstate_lb_get with "Hlstate_auth") as "$".
          iSteps.
        - iDestruct (lstate_lb_get with "Hlstate_auth") as "Hlstate_lb".
          iDestruct (lstate_lb_mono with "Hlstate_lb") as "$"; first done.
          iSteps.
      }
      iSplitR "HΦ". { iExists (Closing _). iSteps. }
      iSteps. iApply ("HΦ" $! None). destruct closing; iSteps.
  Qed.
  Lemma rcfd_remove_spec t fd chars :
    {{{
      rcfd_inv t fd chars
    }}}
      rcfd_remove t
    {{{ o,
      RET (o : val);
      rcfd_closing t ∗
      match o with
      | None =>
          True
      | Some fd' =>
          ⌜fd' = fd⌝ ∗
          unix_fd_model fd (DfracOwn 1) chars
      end
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".
    wp_apply (rcfd_remove_spec' false with "[$Hinv]").
    iSteps.
  Qed.
  Lemma rcfd_remove_spec_closing closing t fd chars :
    {{{
      rcfd_inv t fd chars ∗
      rcfd_closing t
    }}}
      rcfd_remove t
    {{{
      RET §None;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hclosing) HΦ".
    wp_apply (rcfd_remove_spec' true with "[$Hinv $Hclosing]").
    iSteps.
  Qed.

  Lemma rcfd_use_spec Ψ t fd chars (closed open : val) :
    {{{
      rcfd_inv t fd chars ∗
      WP closed () {{ res,
        ⌜res = ()%V⌝ ∗
        Ψ false
      }} ∗
      ( ∀ q,
        rcfd_token t q -∗
        unix_fd_model fd (DfracOwn q) chars -∗
        WP open fd {{ res,
          ⌜res = ()%V⌝ ∗
          rcfd_token t q ∗
          unix_fd_model fd (DfracOwn q) chars ∗
          Ψ true
        }}
      )
    }}}
      rcfd_use t closed open
    {{{ b,
      RET ();
      Ψ b
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & Hclosed & Hopen) HΦ".
    wp_rec.
    wp_smart_apply (rcfd_get_spec with "Hinv") as ([]) ""; last iSteps.
    iIntros "(%q & -> & Htoken & Hmodel)".
    wp_smart_apply (wp_wand with "(Hopen Htoken Hmodel)") as "%res (-> & Htoken & Hmodel & HΨ)".
    wp_smart_apply (rcfd_put_spec with "[$Hinv $Htoken $Hmodel]").
    iSteps.
  Qed.

  #[local] Lemma rcfd_is_open_spec' closing t fd chars :
    {{{
      rcfd_inv t fd chars ∗
      if closing then
        rcfd_closing t
      else
        True
    }}}
      rcfd_is_open t
    {{{ b,
      RET #b;
      if closing then
        ⌜b = false⌝
      else if b then
        True
      else
        rcfd_closing t
    }}}.
  Proof.
    iIntros "%Φ ((%l & %γ & -> & #Hmeta & #Hinv) & Hclosing) HΦ".

    wp_rec. wp_pures.

    wp_bind (_.{state})%E.
    iInv "Hinv" as "(%state & %lstate & %ops & Hops & Hfd & Hlstate_auth & Hlstate)".
    wp_load.
    destruct closing; last iClear "Hclosing".

    - iDestruct "Hclosing" as "(%_l & %_γ & %Heq & _Hmeta & Hlstate_lb)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iAssert ⌜∃ fn, state = Closing fn⌝%I as %(fn & ->).
      { iDestruct (lstate_valid_closing_users with "Hlstate_auth Hlstate_lb") as %[-> | ->].
        all: iDecompose "Hlstate"; iSteps.
      }
      iSplitR "HΦ". { iExists (Closing _). iSteps. }
      iSteps.

    - destruct state.

      + iSplitR "HΦ". { iExists Open. iSteps. }
        iSteps.

      + iAssert (lstate_lb γ LClosingUsers) as "#Hlstate_lb".
        { destruct lstate; iDecompose "Hlstate".
          - iApply (lstate_lb_get with "Hlstate_auth").
          - iDestruct (lstate_lb_get with "Hlstate_auth") as "Hlstate_lb".
            iApply (lstate_lb_mono with "Hlstate_lb"); first done.
        }
        iSplitR "HΦ". { iExists (Closing _). iSteps. }
        iSteps.
  Qed.
  Lemma rcfd_is_open_spec t fd chars :
    {{{
      rcfd_inv t fd chars
    }}}
      rcfd_is_open t
    {{{ b,
      RET #b;
      if b then
        True
      else
        rcfd_closing t
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".
    wp_apply (rcfd_is_open_spec' false with "[$Hinv]").
    iSteps.
  Qed.
  Lemma rcfd_is_open_spec_closed t fd chars :
    {{{
      rcfd_inv t fd chars ∗
      rcfd_closing t
    }}}
      rcfd_is_open t
    {{{
      RET #false;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hclosing) HΦ".
    wp_apply (rcfd_is_open_spec' true with "[$Hinv $Hclosing]").
    iSteps.
  Qed.

  #[local] Lemma rcfd_peek_spec' closing t fd chars :
    {{{
      rcfd_inv t fd chars ∗
      if closing then
        rcfd_closing t
      else
        True
    }}}
      rcfd_peek t
    {{{ o,
      RET (o : val);
      if closing then
        ⌜o = None⌝
      else
        match o with
        | None =>
            rcfd_closing t
        | Some fd' =>
            ⌜fd' = fd⌝
        end
    }}}.
  Proof.
    iIntros "%Φ ((%l & %γ & -> & #Hmeta & #Hinv) & Hclosing) HΦ".

    wp_rec. wp_pures.

    wp_bind (_.{state})%E.
    iInv "Hinv" as "(%state & %lstate & %ops & Hops & Hfd & Hlstate_auth & Hlstate)".
    wp_load.
    destruct closing; last iClear "Hclosing".

    - iDestruct "Hclosing" as "(%_l & %_γ & %Heq & _Hmeta & Hlstate_lb)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iAssert ⌜∃ fn, state = Closing fn⌝%I as %(fn & ->).
      { iDestruct (lstate_valid_closing_users with "Hlstate_auth Hlstate_lb") as %[-> | ->].
        all: iDecompose "Hlstate"; iSteps.
      }
      iSplitR "HΦ". { iExists (Closing _). iSteps. }
      iSteps. iApply ("HΦ" $! None). iSteps.

    - destruct state.

      + iSplitR "HΦ". { iExists Open. iSteps. }
        iModIntro. clear.

        wp_pures.
        iApply ("HΦ" $! (Some _)). iSteps.

      + iAssert (lstate_lb γ LClosingUsers) as "#Hlstate_lb".
        { destruct lstate; iDecompose "Hlstate".
          - iApply (lstate_lb_get with "Hlstate_auth").
          - iDestruct (lstate_lb_get with "Hlstate_auth") as "Hlstate_lb".
            iApply (lstate_lb_mono with "Hlstate_lb"); first done.
        }
        iSplitR "HΦ". { iExists (Closing _). iSteps. }
        iSteps. iApply ("HΦ" $! None). iSteps.
  Qed.
  Lemma rcfd_peek_spec t fd chars :
    {{{
      rcfd_inv t fd chars
    }}}
      rcfd_peek t
    {{{ o,
      RET (o : val);
      match o with
      | None =>
          rcfd_closing t
      | Some fd' =>
          ⌜fd' = fd⌝
      end
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".
    wp_apply (rcfd_peek_spec' false with "[$Hinv]").
    iSteps.
  Qed.
  Lemma rcfd_peek_spec_closed t fd chars :
    {{{
      rcfd_inv t fd chars ∗
      rcfd_closing t
    }}}
      rcfd_peek t
    {{{
      RET §None;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hclosing) HΦ".
    wp_apply (rcfd_peek_spec' true with "[$Hinv $Hclosing]").
    iSteps.
  Qed.
End rcfd_G.

#[global] Opaque rcfd_make.
#[global] Opaque rcfd_close.
#[global] Opaque rcfd_use.
#[global] Opaque rcfd_is_open.
#[global] Opaque rcfd_peek.

#[global] Opaque rcfd_inv.
#[global] Opaque rcfd_token.
#[global] Opaque rcfd_closing.
