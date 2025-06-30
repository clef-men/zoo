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
Implicit Types l open : location.
Implicit Types t v v_state fd fn : val.
Implicit Types o : option val.

Record metadata := {
  metadata_fd : val ;
  metadata_open : block_id ;
  metadata_tokens : gname ;
  metadata_lstate : gname ;
}.
Implicit Types γ : metadata.

#[local] Instance metadata_eq_dec : EqDecision metadata :=
  ltac:(solve_decision).
#[local] Instance metadata_countable :
  Countable metadata.
Proof.
  solve_countable.
Qed.

Inductive state :=
  | Open
  | Closing fn.
Implicit Types state : state.

#[local] Instance state_inhabited : Inhabited state :=
  populate Open.
#[local] Instance state_eq_dec : EqDecision state :=
  ltac:(solve_decision).

#[local] Definition state_to_val γ state :=
  match state with
  | Open =>
      ‘Open@γ.(metadata_open)[ γ.(metadata_fd) ]
  | Closing fn =>
      ‘Closing[ fn ]
  end%V.
#[local] Arguments state_to_val _ !_ / : assert.

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

  Implicit Types Ψ : frac → iProp Σ.

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

  #[local] Definition inv_inner_open γ Ψ state ops : iProp Σ :=
    ∃ q qs,
    tokens_auth γ qs ∗
    ⌜state = Open⌝ ∗
    ⌜ops = size qs⌝ ∗
    ⌜set_fold Qp.add q qs = 1%Qp⌝ ∗
    Ψ q.
  #[local] Instance : CustomIpatFormat "inv_inner_open" :=
    "(
      %q{} &
      %qs{} &
      Htokens_auth &
      {%H{eq};->} &
      -> &
      %Hqs{} &
      HΨ{_{!}}
    )".
  #[local] Definition inv_inner_closing_users γ Ψ state ops : iProp Σ :=
    ∃ q qs fn,
    tokens_auth γ qs ∗
    ⌜state = Closing fn⌝ ∗
    ⌜ops = size qs⌝ ∗
    ⌜0 < size qs⌝ ∗
    ⌜set_fold Qp.add q qs = 1%Qp⌝ ∗
    Ψ q ∗
    (Ψ 1%Qp -∗ WP fn () {{ itype_unit }}).
  #[local] Instance : CustomIpatFormat "inv_inner_closing_users" :=
    "(
      %q{} &
      %qs{} &
      %fn{} &
      Htokens_auth &
      {%H{eq};->} &
      {%H{eq_ops};->} &
      %Hqs{}_size &
      %Hqs{} &
      HΨ{_{!}} &
      Hfn{}
    )".
  #[local] Definition inv_inner_closing_no_users state : iProp Σ :=
    ∃ fn,
    ⌜state = Closing fn⌝ ∗
    WP fn () {{ itype_unit }}.
  #[local] Instance : CustomIpatFormat "inv_inner_closing_no_users" :=
    "(
      %fn{} &
      {%H{eq};->} &
      Hfn{}
    )".
  #[local] Definition inv_inner l γ Ψ : iProp Σ :=
    ∃ state lstate ops,
    l.[ops] ↦ #ops ∗
    l.[state] ↦ state_to_val γ state ∗
    lstate_auth γ lstate ∗
    match lstate with
    | LOpen =>
        inv_inner_open γ Ψ state ops
    | LClosingUsers =>
        inv_inner_closing_users γ Ψ state ops
    | LClosingNoUsers =>
        inv_inner_closing_no_users state
    end.
  #[local] Instance : CustomIpatFormat "inv_inner" :=
    "(
      %state{} &
      %lstate{} &
      %ops{} &
      Hl_ops &
      Hl_state &
      Hlstate_auth &
      Hlstate
    )".
  #[local] Definition inv' l γ Ψ :=
    inv nroot (inv_inner l γ Ψ).
  Definition rcfd_inv t fd Ψ : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    ⌜fd = γ.(metadata_fd)⌝ ∗
    meta l nroot γ ∗
    inv' l γ Ψ.
  #[local] Instance : CustomIpatFormat "inv" :=
    "(
      %l &
      %γ &
      -> &
      -> &
      #Hmeta &
      #Hinv
    )".

  Definition rcfd_closing t : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    lstate_lb γ LClosingUsers.
  #[local] Instance : CustomIpatFormat "closing" :=
    "(
      %l_ &
      %γ_ &
      %Heq &
      #Hmeta_ &
      #Hlstate_lb
    )".

  #[global] Instance rcfd_inv_contractive t fd n :
    Proper (
      (pointwise_relation _ (dist_later n)) ==>
      (≡{n}≡)
    ) (rcfd_inv t fd).
  Proof.
    rewrite /rcfd_inv /inv' /inv_inner /inv_inner_open /inv_inner_closing_users.
    solve_contractive.
  Qed.
  #[global] Instance rcfd_inv_proper t fd :
    Proper (
      (pointwise_relation _ (≡)) ==>
      (≡)
    ) (rcfd_inv t fd).
  Proof.
    rewrite /rcfd_inv /inv' /inv_inner /inv_inner_open /inv_inner_closing_users.
    solve_proper.
  Qed.

  #[global] Instance rcfd_closing_timeless t :
    Timeless (rcfd_closing t).
  Proof.
    apply _.
  Qed.
  #[global] Instance rcfd_inv_persistent t fd Ψ :
    Persistent (rcfd_inv t fd Ψ).
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
      tokens_auth γ ({[+q+]} ⊎ qs) ∗
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

  Lemma rcfd_make_spec Ψ fd :
    {{{
      Ψ 1%Qp
    }}}
      rcfd_make fd
    {{{ t,
      RET t;
      rcfd_inv t fd Ψ
    }}}.
  Proof.
    iIntros "%Φ HΨ HΦ".

    wp_rec.
    wp_block_generative open.
    wp_block l as "Hmeta" "(Hl_ops & Hl_fd & _)".

    iMod tokens_alloc as "(%γ_tokens & Htokens_auth)".
    iMod lstate_alloc as "(%γ_lstate & Hlstate_auth)".
    pose γ := {|
      metadata_fd := fd ;
      metadata_open := open ;
      metadata_tokens := γ_tokens ;
      metadata_lstate := γ_lstate ;
    |}.
    iMod (meta_set γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iExists l, γ. iSteps. iExists Open. iSteps.
  Qed.

  #[local] Lemma rcfd_put_spec l γ Ψ `{!Fractional Ψ} :
    {{{
      inv' l γ Ψ ∗
      ( lstate_lb γ LClosingNoUsers
      ∨ ∃ q,
        tokens_frag γ q ∗
        Ψ q
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
    iInv "Hinv" as "(:inv_inner =1)".
    wp_faa.
    iSplitR "HΦ".
    { iDestruct "H" as "[#Hlstate_lb | (%q & Htokens_frag & HΨ)]".
      - iDestruct (lstate_valid_closing_no_users with "Hlstate_auth Hlstate_lb") as %->.
        iDestruct "Hlstate" as "(:inv_inner_closing_no_users =1)".
        iFrameSteps 2.
      - destruct lstate1.
        + iDestruct "Hlstate" as "(:inv_inner_open =1 !=)".
          iDestruct (tokens_elem_of with "Htokens_auth Htokens_frag") as %Hq.
          iMod (tokens_update_dealloc with "Htokens_auth Htokens_frag") as "Htokens_auth".
          iDestruct (fractional with "[$HΨ $HΨ_]") as "HΨ".
          iFrameSteps 2; iPureIntro.
          * assert (qs1 ≠ ∅) as Hqs1_size%gmultiset_size_non_empty_iff by multiset_solver.
            rewrite gmultiset_size_difference; first multiset_solver.
            rewrite gmultiset_size_singleton. lia.
          * rewrite (gmultiset_disj_union_difference' q qs1) // gmultiset_set_fold_disj_union gmultiset_set_fold_singleton // in Hqs1.
        + iDestruct "Hlstate" as "(:inv_inner_closing_users =1 !=)".
          iDestruct (tokens_elem_of with "Htokens_auth Htokens_frag") as %Hq.
          destruct (decide (size qs1 = 1)) as [Hqs_size' | Hqs_size'].
          * apply gmultiset_size_1_elem_of in Hqs_size' as (q_ & ->%leibniz_equiv). rewrite gmultiset_set_fold_singleton in Hqs1.
            apply gmultiset_elem_of_singleton in Hq as <-.
            iMod (tokens_update_dealloc with "Htokens_auth Htokens_frag") as "Htokens_auth".
            rewrite gmultiset_difference_diag.
            iMod (lstate_update LClosingNoUsers with "Hlstate_auth") as "Hlstate_auth"; first done.
            iDestruct (fractional with "[$HΨ $HΨ_]") as "HΨ". rewrite Hqs1.
            iFrameSteps 2.
          * iMod (tokens_update_dealloc with "Htokens_auth Htokens_frag") as "Htokens_auth".
            iDestruct (fractional with "[$HΨ $HΨ_]") as "HΨ".
            iFrameSteps 2; iPureIntro.
            -- rewrite gmultiset_size_difference; first multiset_solver.
               rewrite gmultiset_size_singleton. lia.
            -- rewrite gmultiset_size_difference; first multiset_solver.
               rewrite gmultiset_size_singleton. lia.
            -- rewrite (gmultiset_disj_union_difference' q qs1) // gmultiset_set_fold_disj_union gmultiset_set_fold_singleton // in Hqs1.
        + iDestruct "Hlstate" as "(:inv_inner_closing_no_users =1)".
          iFrameSteps 2.
    }
    iIntros "!> {%}".

    wp_pures.
    destruct (decide (ops1 = 1)) as [-> | Hops]; wp_pures; last iSteps.

    wp_bind (_.{state})%E.
    iInv "Hinv" as "(:inv_inner =2)".
    wp_load.
    destruct (decide (lstate2 = LOpen)) as [-> | Hlstate2].

    - iDestruct "Hlstate" as "(:inv_inner_open =2)".
      iSplitR "HΦ". { iFrameSteps 2. }
      iSteps.

    - iAssert (
        ∃ fn2,
        ⌜state2 = Closing fn2⌝ ∗
        lstate_lb γ LClosingUsers
      )%I as "(%fn2 & -> & #Hlstate_lb)".
      { destruct lstate2; first done.
        - iDestruct "Hlstate" as "(:inv_inner_closing_users =2)".
          iDestruct (lstate_lb_get with "Hlstate_auth") as "$".
          iSteps.
        - iDestruct "Hlstate" as "(:inv_inner_closing_no_users =2)".
          iDestruct (lstate_lb_get with "Hlstate_auth") as "Hlstate_lb".
          iDestruct (lstate_lb_mono LClosingUsers with "Hlstate_lb") as "$"; first done.
          iSteps.
      }

      iSplitR "HΦ". { iFrameSteps 2. }
      iIntros "!> {%}".

      wp_pures.

      wp_bind (_.{ops})%E.
      iInv "Hinv" as "(:inv_inner =3)".
      wp_load.
      iDestruct (lstate_valid_closing_users with "Hlstate_auth Hlstate_lb") as %[-> | ->].

      + iDestruct "Hlstate" as "(:inv_inner_closing_users =3)".
        iSplitR "HΦ". { iFrameSteps 2. }
        iSteps.

      + iDestruct "Hlstate" as "(:inv_inner_closing_no_users =3)".
        iClear "Hlstate_lb". iDestruct (lstate_lb_get with "Hlstate_auth") as "#Hlstate_lb".
        iSplitR "HΦ". { iFrameSteps 2. }
        iIntros "!> {%}".

        wp_pures. case_bool_decide as Hops3; wp_pures; last iSteps.

        wp_bind (CAS _ _ _).
        iInv "Hinv" as "(:inv_inner =4)".
        wp_cas as _ | Hcas; first iSteps.
        destruct state4; first zoo_simpl.
        destruct Hcas as (_ & _ & [= <-]).
        iDestruct (lstate_valid_closing_no_users with "Hlstate_auth Hlstate_lb") as %->.
        iDestruct "Hlstate" as "(:inv_inner_closing_no_users =4 eq)". injection Heq as <-.
        iSplitR "Hfn4 HΦ".
        { iExists (Closing _). iFrameSteps. }
        iSteps.
  Qed.

  #[local] Lemma rcfd_get_spec l γ Ψ `{HΨ : !Fractional Ψ} :
    {{{
      inv' l γ Ψ
    }}}
      rcfd_get #l
    {{{ o,
      RET (o : val);
      match o with
      | None =>
          True
      | Some fd_ =>
          ∃ q,
          ⌜fd_ = γ.(metadata_fd)⌝ ∗
          tokens_frag γ q ∗
          Ψ q
      end
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".

    wp_rec. wp_pures.

    wp_bind (FAA _ _).
    iInv "Hinv" as "(:inv_inner =1)".
    wp_faa.

    iAssert (|==>
      inv_inner l γ Ψ ∗
      ( lstate_lb γ LClosingNoUsers
      ∨ ∃ q,
        tokens_frag γ q ∗
        Ψ q
      )
    )%I with "[- HΦ]" as ">($ & H)".
    { destruct lstate1.
      - iDestruct "Hlstate" as "(:inv_inner_open)".
        iMod (tokens_update_alloc (q / 2) with "Htokens_auth") as "(Htokens_auth & Htokens_frag)".
        iDestruct (fractional_half with "HΨ") as "(HΨ1 & HΨ2)"; first done.
        iSplitR "Htokens_frag HΨ2"; last iSteps.
        iFrameSteps 2; iPureIntro.
        + rewrite gmultiset_size_disj_union gmultiset_size_singleton. lia.
        + rewrite gmultiset_set_fold_disj_union gmultiset_set_fold_singleton Qp.div_2 //.
      - iDestruct "Hlstate" as "(:inv_inner_closing_users)".
        iMod (tokens_update_alloc (q / 2) with "Htokens_auth") as "(Htokens_auth & Htokens_frag)".
        iDestruct (fractional_half with "HΨ") as "(HΨ1 & HΨ2)"; first done.
        iSplitR "Htokens_frag HΨ2"; last iSteps.
        iFrameSteps 2; iPureIntro.
        + rewrite gmultiset_size_disj_union gmultiset_size_singleton. lia.
        + rewrite gmultiset_size_disj_union. lia.
        + rewrite gmultiset_set_fold_disj_union gmultiset_set_fold_singleton Qp.div_2 //.
      - iDestruct "Hlstate" as "(:inv_inner_closing_no_users)".
        iDestruct (lstate_lb_get with "Hlstate_auth") as "#Hlstate_lb".
        iFrameSteps 2.
    }

    iModIntro. wp_pures. clear- HΨ.

    wp_bind (_.{state})%E.
    iInv "Hinv" as "(:inv_inner =2)".
    wp_load.
    destruct (decide (lstate2 = LOpen)) as [-> | Hlstate2].

    - iDestruct "Hlstate" as "(:inv_inner_open)".
      iDestruct "H" as "[#Hlstate_lb | (%q' & Htokens_frag & HΨ_)]".
      { iDestruct (lstate_valid_closing_no_users with "Hlstate_auth Hlstate_lb") as %?. done. }
      iSplitR "Htokens_frag HΨ_ HΦ". { iFrameSteps 2. }
      iIntros "!> {%}".

      wp_pures.
      iApply ("HΦ" $! (Some _)). iSteps.

    - iAssert (
        ∃ fn2,
        ⌜state2 = Closing fn2⌝
      )%I as %(fn2 & ->).
      { destruct lstate2; iDecompose "Hlstate"; iSteps. }

      iSplitR "H HΦ". { iFrameSteps 2. }
      iModIntro. clear- HΨ.

      wp_smart_apply (rcfd_put_spec with "[$]") as "_".
      wp_pures.
      iApply ("HΦ" $! None). iSteps.
  Qed.

  Lemma rcfd_use_spec Χ t fd Ψ `{!Fractional Ψ} (closed open : val) :
    {{{
      rcfd_inv t fd Ψ ∗
      WP closed () {{ Χ false }} ∗
      ( ∀ q,
        Ψ q -∗
        WP open fd {{ res,
          Ψ q ∗
          Χ true res
        }}
      )
    }}}
      rcfd_use t closed open
    {{{ b res,
      RET res;
      Χ b res
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & Hclosed & Hopen) HΦ".
    wp_rec.
    wp_smart_apply (rcfd_get_spec with "Hinv") as ([v |]) ""; last iSteps.
    iIntros "(%q & -> & Htoken & HΨ)".
    wp_smart_apply (wp_wand with "(Hopen HΨ)") as "%res (HΨ & HΧ)".
    wp_smart_apply (rcfd_put_spec with "[Htoken HΨ]"); first iSteps.
    iSteps.
  Qed.

  #[local] Lemma rcfd_close_spec_aux closing t fd Ψ :
    {{{
      rcfd_inv t fd Ψ ∗
      if closing then
        rcfd_closing t
      else
        ( Ψ 1%Qp -∗
            ∃ chars,
            unix_fd_model fd (DfracOwn 1) chars
        )
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
    iIntros "%Φ ((:inv) & Hclosing) HΦ".

    wp_rec. wp_pures.

    wp_bind (_.{state})%E.
    iInv "Hinv" as "(:inv_inner =1)".
    wp_load.
    destruct (decide (lstate1 = LOpen)) as [-> | Hlstate1].

    - iDestruct "Hlstate" as "(:inv_inner_open =1)".
      destruct closing.
      { iDestruct "Hclosing" as "(:closing)". injection Heq as <-.
        iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
        iDestruct (lstate_valid_closing_users with "Hlstate_auth Hlstate_lb") as %[[=] | [=]].
      }

      iSplitR "Hclosing HΦ". { iFrameSteps 2. }
      iIntros "!> {%}".

      wp_pures.

      wp_bind (CAS _ _ _).
      iInv "Hinv" as "(:inv_inner =2)".
      wp_cas as Hcas.

      + iAssert (
          ∃ fn2,
          ⌜state2 = Closing fn2⌝ ∗
          lstate_lb γ LClosingUsers
        )%I as "(%fn2 & -> & #Hlstate_lb)".
        { destruct lstate2; iDecompose "Hlstate".
          - zoo_simpl. naive_solver.
          - iDestruct (lstate_lb_get with "Hlstate_auth") as "$".
            iSteps.
          - iDestruct (lstate_lb_get with "Hlstate_auth") as "Hlstate_lb".
            iDestruct (lstate_lb_mono with "Hlstate_lb") as "$"; first done.
            iSteps.
        }

        iSplitR "HΦ". { iFrameSteps 2. }
        iSteps.

      + destruct state2; last zoo_simpl.
        destruct (decide (lstate2 = LOpen)) as [-> | Hlstate2]; last first.
        { destruct lstate2; iDecompose "Hlstate"; iSteps. }
        iDestruct "Hlstate" as "(:inv_inner_open =2 eq)".
        iMod (lstate_update LClosingUsers with "Hlstate_auth") as "Hlstate_auth"; first done.
        iDestruct (lstate_lb_get with "Hlstate_auth") as "#Hlstate_lb".

        iSplitR "HΦ".
        { destruct (decide (size qs2 = 0)) as [Hqs_size | Hqs_size].
          - apply gmultiset_size_empty_iff in Hqs_size as ->.
            rewrite gmultiset_set_fold_empty in Hqs2. rewrite {}Hqs2.
            iMod (lstate_update LClosingNoUsers with "Hlstate_auth") as "Hlstate_auth"; first done.
            iDestruct ("Hclosing" with "HΨ") as "(%chars & Hfd)".
            iExists (Closing _). iFrameSteps.
          - iExists (Closing _). iFrame. iStep 8 as "HΨ".
            iDestruct ("Hclosing" with "HΨ") as "(%chars & Hfd)".
            iSteps.
        }
        iIntros "!> {%}".

        wp_pures.

        wp_bind (_.{ops})%E.
        iInv "Hinv" as "(:inv_inner =3)".
        wp_load.

        destruct (decide (ops3 = 0)) as [-> | Hops3]; last iSteps.

        iDestruct (lstate_valid_closing_users with "Hlstate_auth Hlstate_lb") as %[-> | ->].
        { iDestruct "Hlstate" as "(:inv_inner_closing_users =3 eq_ops)". lia. }
        iDestruct "Hlstate" as "(:inv_inner_closing_no_users =3)".
        iRename "Hlstate_lb" into "Hlstate_lb'". iDestruct (lstate_lb_get with "Hlstate_auth") as "#Hlstate_lb".
        iSplitR "HΦ". { iFrameSteps 2. }
        iIntros "!> {%}".

        wp_pures.

        wp_bind (CAS _ _ _).
        iInv "Hinv" as "(:inv_inner =4)".
        wp_cas as _ | Hcas; first iSteps.

        iDestruct (lstate_valid_closing_no_users with "Hlstate_auth Hlstate_lb") as %->.
        iDestruct "Hlstate" as "(:inv_inner_closing_no_users =4)".
        destruct Hcas as (_ & _ & [= ->]).
        iSplitR "Hfn4 HΦ".
        { iExists (Closing _). iFrameSteps. }
        iIntros "!> {%}".

        wp_smart_apply (wp_wand with "Hfn4").
        iSteps.

    - iAssert (
        ∃ fn1,
        ⌜state1 = Closing fn1⌝ ∗
        lstate_lb γ LClosingUsers
      )%I as "(%fn1 & -> & #Hlstate_lb)".
      { destruct lstate1; iDecompose "Hlstate".
        - iDestruct (lstate_lb_get with "Hlstate_auth") as "$".
          iSteps.
        - iDestruct (lstate_lb_get with "Hlstate_auth") as "Hlstate_lb".
          iDestruct (lstate_lb_mono with "Hlstate_lb") as "$"; first done.
          iSteps.
      }

      iSplitR "HΦ". { iFrameSteps 2. }
      iIntros "!> {%}".

      wp_pures.
      destruct closing; iSteps.
  Qed.
  Lemma rcfd_close_spec t fd Ψ :
    {{{
      rcfd_inv t fd Ψ ∗
      ( Ψ 1%Qp -∗
          ∃ chars,
          unix_fd_model fd (DfracOwn 1) chars
      )
    }}}
      rcfd_close t
    {{{ b,
      RET #b;
      rcfd_closing t
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & H) HΦ".
    wp_apply (rcfd_close_spec_aux false with "[$] HΦ").
  Qed.
  Lemma rcfd_close_spec_closing t fd Ψ :
    {{{
      rcfd_inv t fd Ψ ∗
      rcfd_closing t
    }}}
      rcfd_close t
    {{{
      RET #false;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hclosing) HΦ".
    wp_apply (rcfd_close_spec_aux true with "[$]").
    iSteps.
  Qed.

  #[local] Lemma rcfd_remove_spec_aux closing t fd Ψ :
    {{{
      rcfd_inv t fd Ψ ∗
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
        | Some fd_ =>
            ⌜fd_ = fd⌝ ∗
            Ψ 1%Qp
        end
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & Hclosing) HΦ".

    wp_rec. wp_pures.

    wp_bind (_.{state})%E.
    iInv "Hinv" as "(:inv_inner =1)".
    wp_load.
    destruct (decide (lstate1 = LOpen)) as [-> | Hlstate1].

    - iDestruct "Hlstate" as "(:inv_inner_open =1)".
      destruct closing; last iClear "Hclosing".
      { iDestruct "Hclosing" as "(:closing)". injection Heq as <-.
        iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
        iDestruct (lstate_valid_closing_users with "Hlstate_auth Hlstate_lb") as %[[=] | [=]].
      }

      iSplitR "HΦ". { iFrameSteps 2. }
      iIntros "!> {%}".

      wp_smart_apply (spsc_waiter_create_spec (Ψ 1%Qp) with "[//]") as "%waiter (#Hwaiter_inv & Hwaiter_producer & Hwaiter_consumer)".
      wp_pures.

      wp_bind (CAS _ _ _).
      iInv "Hinv" as "(:inv_inner =2)".
      wp_cas as Hcas.

      + iAssert (
          ∃ fn2,
          ⌜state2 = Closing fn2⌝ ∗
          lstate_lb γ LClosingUsers
        )%I as "(%fn2 & -> & #Hlstate_lb)".
        { destruct lstate2; iDecompose "Hlstate".
          - zoo_simpl. naive_solver.
          - iDestruct (lstate_lb_get with "Hlstate_auth") as "$".
            iSteps.
          - iDestruct (lstate_lb_get with "Hlstate_auth") as "Hlstate_lb".
            iDestruct (lstate_lb_mono with "Hlstate_lb") as "$"; first done.
            iSteps.
        }

        iSplitR "HΦ". { iFrameSteps 2. }
        iIntros "!> {%}".

        wp_pures.
        iApply ("HΦ" $! None). iSteps.

      + destruct state2; last zoo_simpl.
        destruct (decide (lstate2 = LOpen)) as [-> | Hlstate2]; last first.
        { destruct lstate2; iDecompose "Hlstate"; iSteps. }
        iDestruct "Hlstate" as "(:inv_inner_open =2 eq)".
        iMod (lstate_update LClosingUsers with "Hlstate_auth") as "Hlstate_auth"; first done.
        iDestruct (lstate_lb_get with "Hlstate_auth") as "#Hlstate_lb".
        iSplitR "Hwaiter_consumer HΦ".
        { destruct (decide (size qs2 = 0)) as [Hqs_size | Hqs_size].
          - apply gmultiset_size_empty_iff in Hqs_size as ->.
            rewrite gmultiset_set_fold_empty in Hqs2. rewrite {}Hqs2.
            iMod (lstate_update LClosingNoUsers with "Hlstate_auth") as "Hlstate_auth"; first done.
            iExists (Closing _). iFrameStep 8.
            wp_apply (spsc_waiter_notify_spec with "[$Hwaiter_inv $Hwaiter_producer $HΨ]").
            iSteps.
          - iExists (Closing _). iFrame. iSteps as "HΨ".
            wp_apply (spsc_waiter_notify_spec with "[$Hwaiter_inv $Hwaiter_producer $HΨ]").
            iSteps.
        }
        iIntros "!> {%}".

        wp_smart_apply (spsc_waiter_wait_spec with "[$Hwaiter_inv $Hwaiter_consumer]") as "HΨ".
        wp_pures.
        iApply ("HΦ" $! (Some _)). iSteps.

    - iAssert (
        ∃ fn1,
        ⌜state1 = Closing fn1⌝ ∗
        lstate_lb γ LClosingUsers
      )%I as "(%fn1 & -> & #Hlstate_lb)".
      { destruct lstate1; iDecompose "Hlstate".
        - iDestruct (lstate_lb_get with "Hlstate_auth") as "$".
          iSteps.
        - iDestruct (lstate_lb_get with "Hlstate_auth") as "Hlstate_lb".
          iDestruct (lstate_lb_mono with "Hlstate_lb") as "$"; first done.
          iSteps.
      }

      iSplitR "HΦ". { iFrameSteps 2. }
      iIntros "!> {%}".

      wp_pures.
      iApply ("HΦ" $! None). destruct closing; iSteps.
  Qed.
  Lemma rcfd_remove_spec t fd Ψ :
    {{{
      rcfd_inv t fd Ψ
    }}}
      rcfd_remove t
    {{{ o,
      RET (o : val);
      rcfd_closing t ∗
      match o with
      | None =>
          True
      | Some fd_ =>
          ⌜fd_ = fd⌝ ∗
          Ψ 1%Qp
      end
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".
    wp_apply (rcfd_remove_spec_aux false with "[$Hinv] HΦ").
  Qed.
  Lemma rcfd_remove_spec_closing closing t fd Ψ :
    {{{
      rcfd_inv t fd Ψ ∗
      rcfd_closing t
    }}}
      rcfd_remove t
    {{{
      RET §None;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hclosing) HΦ".
    wp_apply (rcfd_remove_spec_aux true with "[$Hinv $Hclosing]").
    iSteps.
  Qed.

  #[local] Lemma rcfd_is_open_spec_aux closing t fd Ψ :
    {{{
      rcfd_inv t fd Ψ ∗
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
    iIntros "%Φ ((:inv) & Hclosing) HΦ".

    wp_rec. wp_pures.

    wp_bind (_.{state})%E.
    iInv "Hinv" as "(:inv_inner)".
    wp_load.
    destruct closing.

    - iDestruct "Hclosing" as "(:closing)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

      iAssert (
        ∃ fn,
        ⌜state = Closing fn⌝
      )%I as "(%fn & ->)".
      { iDestruct (lstate_valid_closing_users with "Hlstate_auth Hlstate_lb") as %[-> | ->].
        all: iDecompose "Hlstate"; iSteps.
      }

      iSplitR "HΦ". { iFrameSteps 2. }
      iSteps.

    - destruct state.

      + iSplitR "HΦ". { iFrameSteps 2. }
        iSteps.

      + iAssert (lstate_lb γ LClosingUsers) as "#Hlstate_lb".
        { destruct lstate; iDecompose "Hlstate".
          - iApply (lstate_lb_get with "Hlstate_auth").
          - iDestruct (lstate_lb_get with "Hlstate_auth") as "Hlstate_lb".
            iApply (lstate_lb_mono with "Hlstate_lb"); first done.
        }

        iSplitR "HΦ". { iFrameSteps 2. }
        iSteps.
  Qed.
  Lemma rcfd_is_open_spec t fd Ψ :
    {{{
      rcfd_inv t fd Ψ
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
    wp_apply (rcfd_is_open_spec_aux false with "[$Hinv] HΦ").
  Qed.
  Lemma rcfd_is_open_spec_closing t fd Ψ :
    {{{
      rcfd_inv t fd Ψ ∗
      rcfd_closing t
    }}}
      rcfd_is_open t
    {{{
      RET #false;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hclosing) HΦ".
    wp_apply (rcfd_is_open_spec_aux true with "[$Hinv $Hclosing]").
    iSteps.
  Qed.

  #[local] Lemma rcfd_peek_spec_aux closing t fd Ψ :
    {{{
      rcfd_inv t fd Ψ ∗
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
        | Some fd_ =>
            ⌜fd_ = fd⌝
        end
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & Hclosing) HΦ".

    wp_rec. wp_pures.

    wp_bind (_.{state})%E.
    iInv "Hinv" as "(:inv_inner)".
    wp_load.
    destruct closing.

    - iDestruct "Hclosing" as "(:closing)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".

      iAssert (
        ∃ fn,
        ⌜state = Closing fn⌝
      )%I as "(%fn & ->)".
      { iDestruct (lstate_valid_closing_users with "Hlstate_auth Hlstate_lb") as %[-> | ->].
        all: iDecompose "Hlstate"; iSteps.
      }

      iSplitR "HΦ". { iFrameSteps 2. }
      iIntros "!> {%}".

      wp_pures.
      iApply ("HΦ" $! None). iSteps.

    - destruct state.

      + iSplitR "HΦ". { iFrameSteps 2. }
        iIntros "!> {%}".

        wp_pures.
        iApply ("HΦ" $! (Some _)). iSteps.

      + iAssert (lstate_lb γ LClosingUsers) as "#Hlstate_lb".
        { destruct lstate; iDecompose "Hlstate".
          - iApply (lstate_lb_get with "Hlstate_auth").
          - iDestruct (lstate_lb_get with "Hlstate_auth") as "Hlstate_lb".
            iApply (lstate_lb_mono with "Hlstate_lb"); first done.
        }

        iSplitR "HΦ". { iFrameSteps 2. }
        iIntros "!> {%}".

        wp_pures.
        iApply ("HΦ" $! None). iSteps.
  Qed.
  Lemma rcfd_peek_spec t fd Ψ :
    {{{
      rcfd_inv t fd Ψ
    }}}
      rcfd_peek t
    {{{ o,
      RET (o : val);
      match o with
      | None =>
          rcfd_closing t
      | Some fd_ =>
          ⌜fd_ = fd⌝
      end
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".
    wp_apply (rcfd_peek_spec_aux false with "[$Hinv] HΦ").
  Qed.
  Lemma rcfd_peek_spec_closing t fd Ψ :
    {{{
      rcfd_inv t fd Ψ ∗
      rcfd_closing t
    }}}
      rcfd_peek t
    {{{
      RET §None;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hclosing) HΦ".
    wp_apply (rcfd_peek_spec_aux true with "[$Hinv $Hclosing]").
    iSteps.
  Qed.
End rcfd_G.

From zoo_eio Require
  rcfd__opaque.

#[global] Opaque rcfd_inv.
#[global] Opaque rcfd_closing.
