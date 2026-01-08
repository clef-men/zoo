From zoo Require Import
  prelude.
From zoo.common Require Import
  countable
  gmultiset
  relations.
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

Implicit Types b owned closing : bool.
Implicit Types ops : Z.
Implicit Types q stock : Qp.
Implicit Types qs : gmultiset Qp.
Implicit Types l open : location.
Implicit Types t v v_state fd fn : val.
Implicit Types o : option val.

Record metadata := {
  metadata_fd : val ;
  metadata_open : block_id ;
  metadata_owned : bool ;
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

#[local] Definition lstate_measure lstate :=
  match lstate with
  | LOpen =>
      0
  | LClosingUsers =>
      1
  | LClosingNoUsers =>
      2
  end.

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

#[local] Lemma lstep_measure lstate1 lstate2 :
  lstep lstate1 lstate2 →
  lstate_measure lstate1 < lstate_measure lstate2.
Proof.
  intros []; simpl; lia.
Qed.
#[local] Lemma lstep_tc_measure lstate1 lstate2 :
  tc lstep lstate1 lstate2 →
  lstate_measure lstate1 < lstate_measure lstate2.
Proof.
  intros Hlsteps.
  apply transitive_tc; first apply _.
  eapply (tc_congruence lstate_measure); last done.
  apply lstep_measure.
Qed.
#[local] Lemma lstep_rtc_measure lstate1 lstate2 :
  rtc lstep lstate1 lstate2 →
  lstate_measure lstate1 ≤ lstate_measure lstate2.
Proof.
  intros [<- | Hlsteps%lstep_tc_measure]%rtc_tc; lia.
Qed.

#[local] Instance lsteps_antisymm :
  AntiSymm (=) (rtc lstep).
Proof.
  intros lstate1 lstate2 Hlsteps1 Hlsteps2%lstep_rtc_measure.
  apply rtc_tc in Hlsteps1 as [<- | Hlsteps1%lstep_tc_measure]; first done.
  lia.
Qed.

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

  #[local] Definition tokens_auth' γ_tokens Ψ ops : iProp Σ :=
    ∃ stock qs,
    ⌜ops = size qs⌝ ∗
    ⌜set_fold Qp.add stock qs = 1%Qp⌝ ∗
    auth_gmultiset_auth γ_tokens (DfracOwn 1) qs ∗
    Ψ stock.
  #[local] Definition tokens_auth γ :=
    tokens_auth' γ.(metadata_tokens).
  #[local] Instance : CustomIpatFormat "tokens_auth" :=
    " ( %stock &
        %qs &
        {{lazy}%Hops;->} &
        %Hqs &
        Hauth &
        HΨ_stock
      )
    ".
  #[local] Definition tokens_frag γ q :=
    auth_gmultiset_frag γ.(metadata_tokens) {[+q+]}.

  #[local] Definition lstate_auth_frac owned lstate :=
    match lstate with
    | LOpen =>
        if owned then 1/4 else 1
    | _ =>
        1
    end%Qp.
  #[local] Definition lstate_auth' γ_lstate owned lstate :=
    auth_mono_auth _ γ_lstate (DfracOwn $ lstate_auth_frac owned lstate) lstate.
  #[local] Definition lstate_auth γ :=
    lstate_auth' γ.(metadata_lstate) γ.(metadata_owned).
  #[local] Definition lstate_lb γ lstate :=
    auth_mono_lb _ γ.(metadata_lstate) lstate.

  #[local] Definition owner' γ_lstate :=
    auth_mono_auth _ γ_lstate (DfracOwn (3/4)%Qp) LOpen.
  #[local] Definition owner γ :=
    owner' γ.(metadata_lstate).

  #[local] Definition inv_lstate_open γ Ψ state ops : iProp Σ :=
    tokens_auth γ Ψ ops ∗
    ⌜state = Open⌝.
  #[local] Instance : CustomIpatFormat "inv_lstate_open" :=
    " ( Htokens_auth &
        {%H{eq};->}
      )
    ".
  #[local] Definition inv_lstate_closing_users γ Ψ state ops : iProp Σ :=
    ∃ fn,
    tokens_auth γ Ψ ops ∗
    ⌜state = Closing fn⌝ ∗
    ⌜0 < ops⌝%Z ∗
    (Ψ 1%Qp -∗ WP fn () {{ itype_unit }}).
  #[local] Instance : CustomIpatFormat "inv_lstate_closing_users" :=
    " ( %fn{} &
        Htokens_auth &
        {%H{eq};->} &
        %Hops{} &
        Hfn{}
      )
    ".
  #[local] Definition inv_lstate_closing_no_users state : iProp Σ :=
    ∃ fn,
    ⌜state = Closing fn⌝ ∗
    WP fn () {{ itype_unit }}.
  #[local] Instance : CustomIpatFormat "inv_lstate_closing_no_users" :=
    " ( %fn{} &
        {%H{eq};->} &
        Hfn{}
      )
    ".
  #[local] Definition inv_lstate γ Ψ state lstate ops :=
    match lstate with
    | LOpen =>
        inv_lstate_open γ Ψ state ops
    | LClosingUsers =>
        inv_lstate_closing_users γ Ψ state ops
    | LClosingNoUsers =>
        inv_lstate_closing_no_users state
    end.

  #[local] Definition inv_inner l γ Ψ : iProp Σ :=
    ∃ state lstate ops,
    l.[ops] ↦ #ops ∗
    l.[state] ↦ state_to_val γ state ∗
    lstate_auth γ lstate ∗
    inv_lstate γ Ψ state lstate ops.
  #[local] Instance : CustomIpatFormat "inv_inner" :=
    " ( %state{} &
        %lstate{} &
        %ops{} &
        Hl_ops &
        Hl_state &
        Hlstate_auth &
        Hlstate
      )
    ".
  #[local] Definition inv' l γ Ψ :=
    inv nroot (inv_inner l γ Ψ).
  Definition rcfd_inv t owned fd Ψ : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    ⌜owned = γ.(metadata_owned)⌝ ∗
    ⌜fd = γ.(metadata_fd)⌝ ∗
    meta l nroot γ ∗
    inv' l γ Ψ.
  #[local] Instance : CustomIpatFormat "inv" :=
    " ( %l &
        %γ &
        -> &
        -> &
        -> &
        #Hmeta &
        #Hinv
      )
    ".

  Definition rcfd_owner t : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    owner γ.
  #[local] Instance : CustomIpatFormat "owner" :=
    " ( %l{;_} &
        %γ{;_} &
        %Heq{} &
        #Hmeta_{} &
        Howner{_{}}
      )
    ".

  Definition rcfd_closing t : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    lstate_lb γ LClosingUsers.
  #[local] Instance : CustomIpatFormat "closing" :=
    " ( %l{;_} &
        %γ{;_} &
        %Heq{} &
        #Hmeta_{} &
        #Hlstate_lb{_{}}
      )
    ".

  #[local] Instance tokens_auth'_ne γ_tokens n :
    Proper (
      (pointwise_relation _ (≡{n}≡)) ==>
      (=) ==>
      (≡{n}≡)
    ) (tokens_auth' γ_tokens).
  Proof.
    solve_proper.
  Qed.
  #[local] Instance tokens_auth'_proper γ_tokens :
    Proper (
      (pointwise_relation _ (≡)) ==>
      (=) ==>
      (≡)
    ) (tokens_auth' γ_tokens).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance rcfd_inv_contractive t owned fd n :
    Proper (
      (pointwise_relation _ (dist_later n)) ==>
      (≡{n}≡)
    ) (rcfd_inv t owned fd).
  Proof.
    rewrite /rcfd_inv /inv' /inv_inner /inv_lstate /inv_lstate_open /inv_lstate_closing_users.
    solve_contractive.
  Qed.
  #[global] Instance rcfd_inv_proper t owned fd :
    Proper (
      (pointwise_relation _ (≡)) ==>
      (≡)
    ) (rcfd_inv t owned fd).
  Proof.
    rewrite /rcfd_inv /inv' /inv_inner /inv_lstate /inv_lstate_open /inv_lstate_closing_users.
    solve_proper.
  Qed.

  #[global] Instance rcfd_owner_timeless t :
    Timeless (rcfd_owner t).
  Proof.
    apply _.
  Qed.
  #[global] Instance rcfd_closing_timeless t :
    Timeless (rcfd_closing t).
  Proof.
    apply _.
  Qed.

  #[global] Instance rcfd_inv_persistent t owned fd Ψ :
    Persistent (rcfd_inv t owned fd Ψ).
  Proof.
    apply _.
  Qed.
  #[global] Instance rcfd_closing_persistent t :
    Persistent (rcfd_closing t).
  Proof.
    apply _.
  Qed.

  #[local] Lemma tokens_alloc Ψ :
    Ψ 1%Qp ⊢ |==>
      ∃ γ_tokens,
      tokens_auth' γ_tokens Ψ 0.
  Proof.
    iIntros "HΨ".
    iMod auth_gmultiset_alloc as "(%γ_tokens & $)".
    iSteps.
  Qed.
  #[local] Lemma tokens_auth_valid γ Ψ ops :
    tokens_auth γ Ψ ops ⊢
    ⌜(0 ≤ ops)%Z⌝.
  Proof.
    iSteps.
  Qed.
  #[local] Lemma tokens_auth_consume γ Ψ :
    tokens_auth γ Ψ 0 ⊢
    Ψ 1%Qp.
  Proof.
    iIntros "(:tokens_auth lazy=)".
    opose proof* (gmultiset_size_empty_inv qs) as ->; first lia.
    rewrite gmultiset_set_fold_empty in Hqs.
    rewrite Hqs //.
  Qed.
  #[local] Lemma tokens_update_alloc γ Ψ `{!Fractional Ψ} ops :
    tokens_auth γ Ψ ops ⊢ |==>
      ∃ q,
      tokens_auth γ Ψ (ops + 1) ∗
      tokens_frag γ q ∗
      Ψ q.
  Proof.
    iIntros "(:tokens_auth)".
    iMod (auth_gmultiset_update_alloc_singleton (stock / 2)%Qp with "Hauth") as "($ & $)".
    iDestruct (fractional_half with "HΨ_stock") as "(HΨ_stock & HΨ)"; first done.
    iFrameSteps; iPureIntro.
    - rewrite gmultiset_size_disj_union gmultiset_size_singleton. lia.
    - rewrite gmultiset_set_fold_disj_union gmultiset_set_fold_singleton Qp.div_2 //.
  Qed.
  #[local] Lemma tokens_update_dealloc γ Ψ `{!Fractional Ψ} ops q :
    tokens_auth γ Ψ ops -∗
    tokens_frag γ q -∗
    Ψ q ==∗
    tokens_auth γ Ψ (ops - 1).
  Proof.
    iIntros "(:tokens_auth) Hfrag HΨ".
    iDestruct (auth_gmultiset_elem_of with "Hauth Hfrag") as %Hq.
    iMod (auth_gmultiset_update_dealloc with "Hauth Hfrag") as "$".
    iDestruct (fractional with "[$HΨ $HΨ_stock]") as "HΨ_stock".
    iFrameSteps; iPureIntro.
    - rewrite gmultiset_size_difference; first multiset_solver.
      rewrite gmultiset_size_singleton.
      apply gmultiset_elem_of_size_non_empty in Hq. lia.
    - rewrite (gmultiset_disj_union_difference' q qs) // gmultiset_set_fold_disj_union gmultiset_set_fold_singleton // in Hqs.
  Qed.

  #[local] Lemma lstate_owner_alloc owned :
    ⊢ |==>
      ∃ γ_lstate,
      lstate_auth' γ_lstate owned LOpen ∗
      if owned then
        owner' γ_lstate
      else
        True.
  Proof.
    iMod (auth_mono_alloc (auth_mono_G := rcfd_G_lstate_G) _ LOpen) as "(%γ_lstate & Hauth)".
    destruct owned; last iSteps.
    iEval (rewrite -Qp.quarter_three_quarter) in "Hauth".
    iDestruct "Hauth" as "(Hauth & Howner)".
    iSteps.
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
    ⌜lstate ≠ LOpen⌝.
  Proof.
    iIntros "Hauth Hlb".
    iDestruct (lstate_valid with "Hauth Hlb") as %Hlsteps.
    iPureIntro.
    apply rtc_inv in Hlsteps as [<- | (lstate' & Hlstep & Hlsteps)]; first naive_solver.
    invert Hlstep.
    apply rtc_inv in Hlsteps as [<- | (lstate' & Hlstep & Hlsteps)]; first naive_solver.
    invert Hlstep.
  Qed.
  #[local] Lemma lstate_valid_closing_users' γ lstate :
    lstate_auth γ lstate -∗
    lstate_lb γ LClosingUsers -∗
    ⌜lstate = LClosingUsers ∨ lstate = LClosingNoUsers⌝.
  Proof.
    iIntros "Hauth Hlb".
    iDestruct (lstate_valid_closing_users with "Hauth Hlb") as %Hlstate.
    destruct lstate; iSteps.
  Qed.
  #[local] Lemma lstate_valid_closing_no_users γ lstate :
    lstate_auth γ lstate -∗
    lstate_lb γ LClosingNoUsers -∗
    ⌜lstate = LClosingNoUsers⌝.
  Proof.
    iIntros "Hauth Hlb".
    iDestruct (lstate_valid with "Hauth Hlb") as %Hlsteps.
    iPureIntro.
    apply rtc_inv in Hlsteps as [<- | (lstate' & Hlstep & Hlsteps)]; first naive_solver.
    invert Hlstep.
  Qed.
  #[local] Lemma lstate_update_close_users γ :
    lstate_auth γ LOpen -∗
    (if γ.(metadata_owned) then owner γ else True) ==∗
    lstate_auth γ LClosingUsers.
  Proof.
    iIntros "Hauth Howner".
    iAssert (auth_mono_auth (auth_mono_G := rcfd_G_lstate_G) _ γ.(metadata_lstate) (DfracOwn 1) LOpen) with "[Hauth Howner]" as "Hauth".
    { rewrite /lstate_auth /lstate_auth' /=.
      destruct γ.(metadata_owned); last iSteps.
      iCombine "Hauth Howner" as "Hauth".
      iEval (rewrite Qp.quarter_three_quarter) in "Hauth".
      iSteps.
    }
    iApply (auth_mono_update' with "Hauth"); first done.
  Qed.
  #[local] Lemma lstate_update_close_no_users γ :
    lstate_auth γ LClosingUsers ⊢ |==>
    lstate_auth γ LClosingNoUsers.
  Proof.
    apply auth_mono_update'; first done.
  Qed.

  #[local] Lemma owner_exclusive γ :
    owner γ -∗
    owner γ -∗
    False.
  Proof.
    iIntros "Hauth_1 Hauth_2".
    iDestruct (auth_mono_auth_valid_2 with "Hauth_1 Hauth_2") as "(% & _)". done.
  Qed.
  #[local] Lemma owner_lstate_auth γ lstate :
    owner γ -∗
    lstate_auth γ lstate -∗
    ⌜lstate = LOpen⌝.
  Proof.
    iIntros "Howner Hauth".
    iApply (auth_mono_auth_agree_L with "Hauth Howner").
  Qed.
  #[local] Lemma owner_lstate_lb γ :
    owner γ -∗
    lstate_lb γ LClosingUsers -∗
    False.
  Proof.
    iIntros "Hauth Hlb".
    iDestruct (auth_mono_lb_valid with "Hauth Hlb") as %H%lstep_rtc_measure.
    exfalso. simpl in H. lia.
  Qed.

  Opaque tokens_auth'.

  #[local] Lemma rcfd_owner_elim l γ :
    meta l nroot γ -∗
    rcfd_owner #l -∗
    owner γ.
  Proof.
    iIntros "#Hmeta (:owner)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-.
    iSteps.
  Qed.
  #[local] Lemma rcfd_owner_elim' l γ b :
    meta l nroot γ -∗
    ( if b then
        rcfd_owner #l
      else
        True
    ) -∗
    if b then
      owner γ
    else
      True.
  Proof.
    iIntros "#Hmeta Howner".
    destruct b; last iSteps.
    iApply (rcfd_owner_elim with "Hmeta Howner").
  Qed.
  Lemma rcfd_owner_exclusive t :
    rcfd_owner t -∗
    rcfd_owner t -∗
    False.
  Proof.
    iIntros "(:owner =1) (:owner =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (owner_exclusive with "Howner_1 Howner_2").
  Qed.
  Lemma rcfd_owner_closing t :
    rcfd_owner t -∗
    rcfd_closing t -∗
    False.
  Proof.
    iIntros "(:owner =1) (:closing =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (owner_lstate_lb with "Howner_1 Hlstate_lb_2").
  Qed.

  #[local] Lemma rcfd_closing_elim l γ :
    meta l nroot γ -∗
    rcfd_closing #l -∗
    lstate_lb γ LClosingUsers.
  Proof.
    iIntros "#Hmeta (:closing)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-.
    iSteps.
  Qed.
  #[local] Lemma rcfd_closing_elim' l γ b P :
    meta l nroot γ -∗
    ( if b then
        rcfd_closing #l
      else
        P
    ) -∗
    if b then
      lstate_lb γ LClosingUsers
    else
      P.
  Proof.
    iIntros "#Hmeta Hclosing".
    destruct b; last iSteps.
    iApply (rcfd_closing_elim with "Hmeta Hclosing").
  Qed.

  #[local] Lemma inv_lstate_Open γ Ψ lstate ops :
    inv_lstate γ Ψ Open lstate ops ⊢
    ⌜lstate = LOpen⌝.
  Proof.
    destruct lstate; iSteps.
  Qed.
  #[local] Lemma inv_lstate_Closing γ Ψ state lstate ops :
    state ≠ Open →
    inv_lstate γ Ψ state lstate ops -∗
    lstate_auth γ lstate -∗
      ∃ fn,
      ⌜state = Closing fn⌝ ∗
      ⌜lstate ≠ LOpen ⌝ ∗
      lstate_lb γ LClosingUsers.
  Proof.
    iIntros "%Hlstate Hlstate Hlstate_auth".
    iDestruct (lstate_lb_get with "Hlstate_auth") as "Hlstate_lb".
    destruct lstate.
    - iDestruct "Hlstate" as "(:inv_lstate_open)".
      exfalso. done.
    - iDestruct "Hlstate" as "(:inv_lstate_closing_users)".
      iSteps.
    - iDestruct "Hlstate" as "(:inv_lstate_closing_no_users)".
      iDestruct (lstate_lb_mono with "Hlstate_lb") as "$"; first done.
      iSteps.
  Qed.
  #[local] Lemma inv_lstate_LClosing γ Ψ state lstate ops :
    lstate ≠ LOpen →
    inv_lstate γ Ψ state lstate ops -∗
    lstate_auth γ lstate -∗
      ∃ fn,
      ⌜state = Closing fn⌝ ∗
      lstate_lb γ LClosingUsers.
  Proof.
    iIntros "%Hlstate Hlstate Hlstate_auth".
    iDestruct (lstate_lb_get with "Hlstate_auth") as "Hlstate_lb".
    destruct lstate; first done.
    - iDestruct "Hlstate" as "(:inv_lstate_closing_users)".
      iSteps.
    - iDestruct "Hlstate" as "(:inv_lstate_closing_no_users)".
      iDestruct (lstate_lb_mono with "Hlstate_lb") as "$"; first done.
      iSteps.
  Qed.

  Lemma rcfd_make_spec owned Ψ fd :
    {{{
      Ψ 1%Qp
    }}}
      rcfd_make fd
    {{{ t,
      RET t;
      rcfd_inv t owned fd Ψ ∗
      if owned then
        rcfd_owner t
      else
        True
    }}}.
  Proof.
    iIntros "%Φ HΨ HΦ".

    wp_rec.
    wp_block_generative open.
    wp_block l as "Hmeta" "(Hl_ops & Hl_fd & _)".

    iMod (tokens_alloc with "HΨ") as "(%γ_tokens & Htokens_auth)".
    iMod (lstate_owner_alloc owned) as "(%γ_lstate & Hlstate_auth & Howner)".

    pose γ := {|
      metadata_fd := fd ;
      metadata_open := open ;
      metadata_owned := owned ;
      metadata_tokens := γ_tokens ;
      metadata_lstate := γ_lstate ;
    |}.
    iMod (meta_set γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitR "Howner".
    - iExists l, γ. iSteps. iExists Open. iSteps.
    - destruct owned; iSteps.
  Qed.

  #[local] Lemma rcfd_finish_spec l γ Ψ (close : val) :
    {{{
      inv' l γ Ψ ∗
      lstate_lb γ LClosingUsers
    }}}
      rcfd_finish #l close ’Closing[ close ]
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hlstate_lb) HΦ".

    wp_rec. wp_pures.

    wp_bind (_.{ops})%E.
    iInv "Hinv" as "(:inv_inner =1)".
    wp_load.
    iDestruct (lstate_valid_closing_users' with "Hlstate_auth Hlstate_lb") as %[-> | ->].

    - iDestruct "Hlstate" as "(:inv_lstate_closing_users =1)".
      iSplitR "HΦ". { iFrameSteps 2. }
      iSteps.

    - iDestruct "Hlstate" as "(:inv_lstate_closing_no_users =1)".
      iDestruct (lstate_lb_get with "Hlstate_auth") as "{Hlstate_lb} #Hlstate_lb".
      iSplitR "HΦ". { iFrameSteps 2. }
      iIntros "!> {%}".

      wp_pures.
      case_bool_decide as Hops3; wp_pures; last iSteps.

      wp_bind (CAS _ _ _).
      iInv "Hinv" as "(:inv_inner =2)".
      wp_cas as _ | Hcas; first iSteps.
      destruct state2; first zoo_simplify.
      destruct Hcas as (_ & _ & [= <-]).
      iDestruct (lstate_valid_closing_no_users with "Hlstate_auth Hlstate_lb") as %->.
      iDestruct "Hlstate" as "(:inv_lstate_closing_no_users =2 eq)". injection Heq as <-.
      iSplitR "Hfn2 HΦ".
      { iExists (Closing _). iFrameSteps. }
      iSteps.
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
        iDestruct "Hlstate" as "(:inv_lstate_closing_no_users =1)".
        iFrameSteps 2.
      - destruct lstate1.
        + iDestruct "Hlstate" as "(:inv_lstate_open =1 !=)".
          iMod (tokens_update_dealloc with "Htokens_auth Htokens_frag HΨ") as "Htokens_auth".
          iFrameSteps 2.
        + iDestruct "Hlstate" as "(:inv_lstate_closing_users =1 !=)".
          iMod (tokens_update_dealloc with "Htokens_auth Htokens_frag HΨ") as "Htokens_auth".
          destruct_decide (ops1 = 1) as -> | ?.
          * iDestruct (tokens_auth_consume with "Htokens_auth") as "HΨ".
            iMod (lstate_update_close_no_users with "Hlstate_auth") as "Hlstate_auth".
            iFrameSteps.
          * iFrameSteps 2.
        + iDestruct "Hlstate" as "(:inv_lstate_closing_no_users =1)".
          iFrameSteps 2.
    }
    iIntros "!> {%}".

    wp_pures.
    destruct_decide (ops1 = 1) as -> | Hops; wp_pures; last iSteps.

    wp_bind (_.{state})%E.
    iInv "Hinv" as "(:inv_inner =2)".
    wp_load.
    destruct_decide (lstate2 = LOpen) as -> | Hlstate2.

    - iDestruct "Hlstate" as "(:inv_lstate_open =2)".
      iSplitR "HΦ". { iFrameSteps 2. }
      iSteps.

    - iDestruct (inv_lstate_LClosing with "Hlstate Hlstate_auth") as "(%fn2 & -> & #Hlstate_lb)"; first done.
      iSplitR "HΦ". { iFrameSteps 2. }
      iIntros "!> {%}".

      wp_smart_apply (rcfd_finish_spec with "[$] HΦ").
  Qed.

  Inductive specification :=
    | SpecOwner
    | SpecClosing
    | SpecNormal.
  Implicit Types spec : specification.

  #[local] Instance specification_eq_dec : EqDecision specification :=
    ltac:(solve_decision).

  #[local] Definition specification_pre_1 t spec : iProp Σ :=
    match spec with
    | SpecOwner =>
        rcfd_owner t
    | SpecClosing =>
        rcfd_closing t
    | SpecNormal =>
        True
    end.
  #[local] Definition specification_pre_2 γ spec : iProp Σ :=
    match spec with
    | SpecOwner =>
        owner γ
    | SpecClosing =>
        lstate_lb γ LClosingUsers
    | SpecNormal =>
        True
    end.
  #[local] Lemma specification_pre_1_2 l γ spec :
    meta l nroot γ -∗
    specification_pre_1 #l spec -∗
    specification_pre_2 γ spec.
  Proof.
    iIntros "#Hmeta Hspec".
    destruct spec; last iSteps.
    - iApply (rcfd_owner_elim with "Hmeta Hspec").
    - iApply (rcfd_closing_elim with "Hmeta Hspec").
  Qed.

  #[local] Lemma rcfd_get_spec_aux spec l γ Ψ `{HΨ : !Fractional Ψ} :
    {{{
      inv' l γ Ψ ∗
      specification_pre_2 γ spec
    }}}
      rcfd_get #l
    {{{ o,
      RET o;
      match spec with
      | SpecOwner =>
          ⌜o ≠ None⌝ ∗
          owner γ
      | SpecClosing =>
          ⌜o = None⌝
      | SpecNormal =>
          True
      end ∗
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
    iIntros "%Φ (#Hinv & Hspec) HΦ".

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
    )%I with "[- Hspec HΦ]" as ">($ & H)".
    { destruct lstate1.
      - iDestruct "Hlstate" as "(:inv_lstate_open)".
        iMod (tokens_update_alloc with "Htokens_auth") as "(%q & Htokens_auth & Htokens_frag & HΨ)".
        iSplitR "Htokens_frag HΨ"; last iSteps.
        iFrameSteps 2.
      - iDestruct "Hlstate" as "(:inv_lstate_closing_users)".
        iMod (tokens_update_alloc with "Htokens_auth") as "(%q & Htokens_auth & Htokens_frag & HΨ)".
        iSplitR "Htokens_frag HΨ"; last iSteps.
        iFrameSteps 2.
      - iDestruct "Hlstate" as "(:inv_lstate_closing_no_users)".
        iDestruct (lstate_lb_get with "Hlstate_auth") as "#Hlstate_lb".
        iFrameSteps 2.
    }

    iModIntro. wp_pures. clear- HΨ.

    wp_bind (_.{state})%E.
    iInv "Hinv" as "(:inv_inner =2)".
    wp_load.
    destruct_decide (lstate2 = LOpen) as -> | Hlstate2.

    - iDestruct "Hlstate" as "(:inv_lstate_open)".

      iDestruct "H" as "[#Hlstate_lb | (%q' & Htokens_frag & HΨ_)]".
      { iDestruct (lstate_valid_closing_no_users with "Hlstate_auth Hlstate_lb") as %?. done. }

      iAssert ⌜spec ≠ SpecClosing⌝%I as %Hspec.
      { iIntros (->).
        iDestruct (lstate_valid_closing_users with "Hlstate_auth Hspec") as %?. congruence.
      }

      iSplitR "Hspec Htokens_frag HΨ_ HΦ". { iFrameSteps 2. }
      iModIntro. clear- Hspec.

      wp_pures.
      iApply ("HΦ" $! (Some _)).
      destruct spec; try congruence; iSteps.

    - iDestruct (inv_lstate_LClosing with "Hlstate Hlstate_auth") as "#(%fn2 & -> & _)"; first done.

      iAssert ⌜spec ≠ SpecOwner⌝%I as %Hspec.
      { iIntros (->).
        iDestruct (owner_lstate_auth with "Hspec Hlstate_auth") as %->. congruence.
      }

      iSplitR "H HΦ". { iFrameSteps 2. }
      iModIntro. clear- HΨ Hspec.

      wp_smart_apply (rcfd_put_spec with "[$]") as "_".
      wp_pures.
      iApply ("HΦ" $! None).
      destruct spec; try congruence; iSteps.
  Qed.
  #[local] Lemma rcfd_get_spec l γ Ψ `{HΨ : !Fractional Ψ} :
    {{{
      inv' l γ Ψ
    }}}
      rcfd_get #l
    {{{ o,
      RET o;
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

    wp_apply (rcfd_get_spec_aux SpecNormal with "[$]").
    iSteps.
  Qed.
  #[local] Lemma rcfd_get_spec_owner l γ Ψ `{HΨ : !Fractional Ψ} :
    {{{
      inv' l γ Ψ ∗
      owner γ
    }}}
      rcfd_get #l
    {{{
      RET Some γ.(metadata_fd);
      ∃ q,
      owner γ ∗
      tokens_frag γ q ∗
      Ψ q
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & Howner) HΦ".

    wp_apply (rcfd_get_spec_aux SpecOwner with "[$]") as ([v |]) ""; last iSteps.
    iSteps.
  Qed.
  #[local] Lemma rcfd_get_spec_closing l γ Ψ `{HΨ : !Fractional Ψ} :
    {{{
      inv' l γ Ψ ∗
      lstate_lb γ LClosingUsers
    }}}
      rcfd_get #l
    {{{
      RET None;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hlstate_lb) HΦ".

    wp_apply (rcfd_get_spec_aux SpecClosing with "[$]").
    iSteps.
  Qed.

  #[local] Lemma rcfd_use_spec_aux spec Χ t owned fd Ψ `{!Fractional Ψ} (closed open : val) :
    {{{
      rcfd_inv t owned fd Ψ ∗
      specification_pre_1 t spec ∗
      ( if decide (spec ≠ SpecOwner) then
          WP closed () {{ Χ false }}
        else
          True
      ) ∗
      ( if decide (spec ≠ SpecClosing) then
          ∀ q,
          Ψ q -∗
          WP open fd {{ res,
            Ψ q ∗
            Χ true res
          }}
        else
          True
      )
    }}}
      rcfd_use t closed open
    {{{ b res,
      RET res;
      Χ b res ∗
      match spec with
      | SpecOwner =>
          ⌜b = true⌝ ∗
          rcfd_owner t
      | SpecClosing =>
          ⌜b = false⌝
      | SpecNormal =>
          True
      end
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & Hspec & Hclosed & Hopen) HΦ".
    iDestruct (specification_pre_1_2 with "Hmeta Hspec") as "Hspec".

    wp_rec.
    wp_smart_apply (rcfd_get_spec_aux with "[$]") as ([v |]) "(Hspec & H)".

    - iDestruct "H" as "(%q & -> & Htoken & HΨ)".

      destruct_decide (spec = SpecClosing) as -> | Hspec.
      { iDestruct "Hspec" as %[=]. }
      iEval (rewrite decide_True //) in "Hopen".

      wp_smart_apply (wp_wand with "(Hopen HΨ)") as "%res (HΨ & HΧ)".
      wp_smart_apply (rcfd_put_spec with "[Htoken HΨ]") as "_"; first iSteps.
      wp_pures.
      destruct spec; try congruence; iSteps.

    - destruct_decide (spec = SpecOwner) as -> | Hspec.
      { iDestruct "Hspec" as "(% & _)". congruence. }
      iEval (rewrite decide_True //) in "Hclosed".

      wp_smart_apply (wp_wand with "Hclosed") as "%res HΧ".
      destruct spec; try congruence; iSteps.
  Qed.
  Lemma rcfd_use_spec Χ t owned fd Ψ `{!Fractional Ψ} (closed open : val) :
    {{{
      rcfd_inv t owned fd Ψ ∗
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
    iIntros "%Φ (#Hinv & Hclosed & Hopen) HΦ".

    wp_apply (rcfd_use_spec_aux SpecNormal with "[$]").
    iSteps.
  Qed.
  Lemma rcfd_use_spec_owner Χ t owned fd Ψ `{!Fractional Ψ} (closed open : val) :
    {{{
      rcfd_inv t owned fd Ψ ∗
      rcfd_owner t ∗
      ( ∀ q,
        Ψ q -∗
        WP open fd {{ res,
          Ψ q ∗
          Χ res
        }}
      )
    }}}
      rcfd_use t closed open
    {{{ res,
      RET res;
      Χ res
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & Howner & Hopen) HΦ".

    wp_apply (rcfd_use_spec_aux SpecOwner (const Χ) with "[$]").
    iSteps.
  Qed.
  Lemma rcfd_use_spec_closing Χ t owned fd Ψ `{!Fractional Ψ} (closed open : val) :
    {{{
      rcfd_inv t owned fd Ψ ∗
      rcfd_closing t ∗
      WP closed () {{ Χ }}
    }}}
      rcfd_use t closed open
    {{{ res,
      RET res;
      Χ res
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & Howner & Hclosed) HΦ".

    wp_apply (rcfd_use_spec_aux SpecClosing (const Χ) with "[$]").
    iSteps.
  Qed.

  #[local] Lemma rcfd_close_spec_aux closing t owned fd Ψ :
    {{{
      rcfd_inv t owned fd Ψ ∗
      ( if owned then
          rcfd_owner t
        else
          True
      ) ∗
      ( if closing then
          rcfd_closing t
        else
          Ψ 1%Qp -∗
            ∃ chars,
            unix_fd_model fd (DfracOwn 1) chars
      )
    }}}
      rcfd_close t
    {{{ b,
      RET #b;
      rcfd_closing t ∗
      ( if owned then
          ⌜b = true⌝
        else
          True
      ) ∗
      ( if closing then
          ⌜b = false⌝
        else
          True
      )
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & Howner & Hclosing) HΦ".
    iDestruct (rcfd_owner_elim' with "Hmeta Howner") as "Howner".
    iDestruct (rcfd_closing_elim' with "Hmeta Hclosing") as "Hclosing".

    wp_rec. wp_pures.

    wp_bind (_.{state})%E.
    iInv "Hinv" as "(:inv_inner =1)".
    wp_load.
    destruct_decide (lstate1 = LOpen) as -> | Hlstate1.

    - iDestruct "Hlstate" as "(:inv_lstate_open =1)".

      destruct closing.
      { iDestruct (lstate_valid_closing_users with "Hlstate_auth Hclosing") as %?. congruence. }

      iSplitR "Howner Hclosing HΦ". { iFrameSteps 2. }
      iIntros "!> {%}".

      wp_pures.

      wp_bind (CAS _ _ _).
      iInv "Hinv" as "(:inv_inner =2)".
      wp_cas as Hcas.

      + iDestruct (inv_lstate_Closing with "Hlstate Hlstate_auth") as "(%fn2 & -> & %Hlstate2 & #Hlstate_lb)".
        { intros ->. zoo_simplify in Hcas. naive_solver. }

        destruct γ.(metadata_owned).
        { iDestruct (owner_lstate_auth with "Howner Hlstate_auth") as %->. congruence. }

        iSplitR "HΦ". { iFrameSteps 2. }
        iSteps.

      + destruct state2; last zoo_simplify.
        iDestruct (inv_lstate_Open with "Hlstate") as %->.
        iDestruct "Hlstate" as "(:inv_lstate_open =2 eq)".

        iMod (lstate_update_close_users with "Hlstate_auth Howner") as "Hlstate_auth".
        iDestruct (lstate_lb_get with "Hlstate_auth") as "#Hlstate_lb".
        iSplitR "HΦ".
        { destruct_decide (ops2 = 0) as -> | Hops.
          - iDestruct (tokens_auth_consume with "Htokens_auth") as "HΨ".
            iMod (lstate_update_close_no_users with "Hlstate_auth") as "Hlstate_auth".
            iDestruct ("Hclosing" with "HΨ") as "(%chars & Hfd)".
            iExists (Closing _). iFrameSteps.
          - iDestruct (tokens_auth_valid with "Htokens_auth") as %?.
            iExists (Closing _). iFrame. iStep 6 as "HΨ".
            iDestruct ("Hclosing" with "HΨ") as "(%chars & Hfd)".
            iSteps.
        }
        iIntros "!> {%}".

        wp_smart_apply (rcfd_finish_spec with "[$]").
        destruct γ.(metadata_owned); iSteps.

    - iDestruct (inv_lstate_LClosing with "Hlstate Hlstate_auth") as "(%fn1 & -> & #Hlstate_lb)"; first done.

      destruct γ.(metadata_owned).
      { iDestruct (owner_lstate_auth with "Howner Hlstate_auth") as %->. congruence. }

      iSplitR "HΦ". { iFrameSteps 2. }
      iIntros "!> {%}".

      wp_pures.
      destruct closing; iSteps.
  Qed.
  Lemma rcfd_close_spec t owned fd Ψ :
    {{{
      rcfd_inv t owned fd Ψ ∗
      ( if owned then
          rcfd_owner t
        else
          True
      ) ∗
      ( Ψ 1%Qp -∗
          ∃ chars,
          unix_fd_model fd (DfracOwn 1) chars
      )
    }}}
      rcfd_close t
    {{{ b,
      RET #b;
      rcfd_closing t ∗
      if owned then
        ⌜b = true⌝
      else
        True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & Howner & H) HΦ".

    wp_apply (rcfd_close_spec_aux false with "[$]").
    iSteps.
  Qed.
  Lemma rcfd_close_spec_closing t fd Ψ :
    {{{
      rcfd_inv t false fd Ψ ∗
      rcfd_closing t
    }}}
      rcfd_close t
    {{{
      RET false;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hclosing) HΦ".

    wp_apply (rcfd_close_spec_aux true with "[$]").
    iSteps.
  Qed.

  #[local] Lemma rcfd_remove_spec_aux closing t owned fd Ψ :
    {{{
      rcfd_inv t owned fd Ψ ∗
      ( if owned then
          rcfd_owner t
        else
          True
      ) ∗
      ( if closing then
          rcfd_closing t
        else
          True
      )
    }}}
      rcfd_remove t
    {{{ o,
      RET o;
      rcfd_closing t ∗
      ( if owned then
          ⌜o = Some fd⌝ ∗
          Ψ 1%Qp
        else
          match o with
          | None =>
              True
          | Some fd_ =>
              ⌜fd_ = fd⌝ ∗
              Ψ 1%Qp
          end
      ) ∗
      ( if closing then
          ⌜o = None⌝
        else
          True
      )
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & Howner & Hclosing) HΦ".
    iDestruct (rcfd_owner_elim' with "Hmeta Howner") as "Howner".
    iDestruct (rcfd_closing_elim' with "Hmeta Hclosing") as "Hclosing".

    wp_rec. wp_pures.

    wp_bind (_.{state})%E.
    iInv "Hinv" as "(:inv_inner =1)".
    wp_load.
    destruct_decide (lstate1 = LOpen) as -> | Hlstate1.

    - iDestruct "Hlstate" as "(:inv_lstate_open =1)".

      destruct closing.
      { iDestruct (lstate_valid_closing_users with "Hlstate_auth Hclosing") as %?. congruence. }

      iSplitR "Howner HΦ". { iFrameSteps 2. }
      iIntros "!> {%}".

      wp_smart_apply (spsc_waiter_create_spec (Ψ 1%Qp) with "[//]") as "%waiter (#Hwaiter_inv & Hwaiter_producer & Hwaiter_consumer)".
      wp_pures.

      wp_bind (CAS _ _ _).
      iInv "Hinv" as "(:inv_inner =2)".
      wp_cas as Hcas.

      + iDestruct (inv_lstate_Closing with "Hlstate Hlstate_auth") as "(%fn2 & -> & %Hlstate2 & #Hlstate_lb)".
        { intros ->. zoo_simplify in Hcas. naive_solver. }

        destruct γ.(metadata_owned).
        { iDestruct (owner_lstate_auth with "Howner Hlstate_auth") as %->. congruence. }

        iSplitR "HΦ". { iFrameSteps 2. }
        iIntros "!> {%}".

        wp_pures.
        iApply ("HΦ" $! None).
        iSteps.

      + destruct state2; last zoo_simplify.
        iDestruct (inv_lstate_Open with "Hlstate") as %->.
        iDestruct "Hlstate" as "(:inv_lstate_open =2 eq)".

        iMod (lstate_update_close_users with "Hlstate_auth Howner") as "Hlstate_auth".
        iDestruct (lstate_lb_get with "Hlstate_auth") as "#Hlstate_lb".
        iSplitR "Hwaiter_consumer HΦ".
        { destruct_decide (ops2 = 0) as -> | ?.
          - iDestruct (tokens_auth_consume with "Htokens_auth") as "HΨ".
            iMod (lstate_update_close_no_users with "Hlstate_auth") as "Hlstate_auth".
            iExists (Closing _). iFrameStep 8.
            wp_apply (spsc_waiter_notify_spec with "[$Hwaiter_inv $Hwaiter_producer $HΨ]").
            iSteps.
          - iDestruct (tokens_auth_valid with "Htokens_auth") as %?.
            iExists (Closing _). iFrame. iSteps as "HΨ".
            wp_apply (spsc_waiter_notify_spec with "[$Hwaiter_inv $Hwaiter_producer $HΨ]").
            iSteps.
        }
        iIntros "!> {%}".

        wp_smart_apply (spsc_waiter_wait_spec with "[$Hwaiter_inv $Hwaiter_consumer]") as "HΨ".
        wp_pures.
        iApply ("HΦ" $! (Some _)).
        destruct γ.(metadata_owned); iSteps.

    - iDestruct (inv_lstate_LClosing with "Hlstate Hlstate_auth") as "(%fn1 & -> & #Hlstate_lb)"; first done.

      destruct γ.(metadata_owned).
      { iDestruct (owner_lstate_auth with "Howner Hlstate_auth") as %->. congruence. }

      iSplitR "HΦ". { iFrameSteps 2. }
      iIntros "!> {%}".

      wp_pures.
      iApply ("HΦ" $! None).
      destruct closing; iSteps.
  Qed.
  Lemma rcfd_remove_spec t owned fd Ψ :
    {{{
      rcfd_inv t owned fd Ψ ∗
      if owned then
        rcfd_owner t
      else
        True
    }}}
      rcfd_remove t
    {{{ o,
      RET o;
      rcfd_closing t ∗
      if owned then
        ⌜o = Some fd⌝ ∗
        Ψ 1%Qp
      else
        match o with
        | None =>
            True
        | Some fd_ =>
            ⌜fd_ = fd⌝ ∗
            Ψ 1%Qp
        end
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & Howner) HΦ".

    wp_apply (rcfd_remove_spec_aux false with "[$]").
    iSteps.
  Qed.
  Lemma rcfd_remove_spec_closing t fd Ψ :
    {{{
      rcfd_inv t false fd Ψ ∗
      rcfd_closing t
    }}}
      rcfd_remove t
    {{{
      RET §None;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hclosing) HΦ".

    wp_apply (rcfd_remove_spec_aux true with "[$]").
    iSteps.
  Qed.

  #[local] Lemma rcfd_is_open_spec_aux spec t owned fd Ψ :
    {{{
      rcfd_inv t owned fd Ψ ∗
      specification_pre_1 t spec
    }}}
      rcfd_is_open t
    {{{ b,
      RET #b;
      match spec with
      | SpecOwner =>
          ⌜b = true⌝ ∗
          rcfd_owner t
      | SpecClosing =>
          ⌜b = false⌝
      | SpecNormal =>
          if b then
            True
          else
            rcfd_closing t
      end
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & Hspec) HΦ".
    iDestruct (specification_pre_1_2 with "Hmeta Hspec") as "Hspec".

    wp_rec. wp_pures.

    wp_bind (_.{state})%E.
    iInv "Hinv" as "(:inv_inner)".
    wp_load.
    destruct state as [| fn].

    - iDestruct (inv_lstate_Open with "Hlstate") as %->.

      destruct_decide (spec = SpecClosing) as -> | Hspec.
      { iDestruct (lstate_valid_closing_users with "Hlstate_auth Hspec") as %?. congruence. }

      iSplitR "Hspec HΦ". { iFrameSteps 2. }
      iModIntro. clear- Hspec.

      wp_pures.
      destruct spec; try congruence; iSteps.

    - iDestruct (inv_lstate_Closing with "Hlstate Hlstate_auth") as "#(%fn_ & _ & %Hlstate & #Hlstate_lb)"; first done.

      destruct_decide (spec = SpecOwner) as -> | Hspec.
      { iDestruct (owner_lstate_auth with "Hspec Hlstate_auth") as %->. congruence. }

      iSplitR "HΦ". { iFrameSteps 2. }
      iModIntro. clear- Hspec.

      wp_pures.
      destruct spec; try congruence; iSteps.
  Qed.
  Lemma rcfd_is_open_spec t owned fd Ψ :
    {{{
      rcfd_inv t owned fd Ψ
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

    wp_apply (rcfd_is_open_spec_aux SpecNormal with "[$]").
    iSteps.
  Qed.
  Lemma rcfd_is_open_spec_owner t owned fd Ψ :
    {{{
      rcfd_inv t owned fd Ψ ∗
      rcfd_owner t
    }}}
      rcfd_is_open t
    {{{
      RET true;
      rcfd_owner t
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & Howner) HΦ".

    wp_apply (rcfd_is_open_spec_aux SpecOwner with "[$]").
    iSteps.
  Qed.
  Lemma rcfd_is_open_spec_closing t owned fd Ψ :
    {{{
      rcfd_inv t false fd Ψ ∗
      rcfd_closing t
    }}}
      rcfd_is_open t
    {{{
      RET false;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hclosing) HΦ".

    wp_apply (rcfd_is_open_spec_aux SpecClosing with "[$]").
    iSteps.
  Qed.

  #[local] Lemma rcfd_peek_spec_aux spec t owned fd Ψ :
    {{{
      rcfd_inv t owned fd Ψ ∗
      specification_pre_1 t spec
    }}}
      rcfd_peek t
    {{{ o,
      RET o;
      match spec with
      | SpecOwner =>
          ⌜o = Some fd⌝ ∗
          rcfd_owner t
      | SpecClosing =>
          ⌜o = None⌝
      | SpecNormal =>
          match o with
          | None =>
              rcfd_closing t
          | Some fd_ =>
              ⌜fd_ = fd⌝
          end
      end
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & Hspec) HΦ".
    iDestruct (specification_pre_1_2 with "Hmeta Hspec") as "Hspec".

    wp_rec. wp_pures.

    wp_bind (_.{state})%E.
    iInv "Hinv" as "(:inv_inner)".
    wp_load.
    destruct state as [| fn].

    - iDestruct (inv_lstate_Open with "Hlstate") as %->.

      destruct_decide (spec = SpecClosing) as -> | Hspec.
      { iDestruct (lstate_valid_closing_users with "Hlstate_auth Hspec") as %?. congruence. }

      iSplitR "Hspec HΦ". { iFrameSteps 2. }
      iModIntro. clear- Hspec.

      wp_pures.
      iApply ("HΦ" $! (Some _)).
      destruct spec; try congruence; iSteps.

    - iDestruct (inv_lstate_Closing with "Hlstate Hlstate_auth") as "#(%fn_ & _ & %Hlstate & #Hlstate_lb)"; first done.

      destruct_decide (spec = SpecOwner) as -> | Hspec.
      { iDestruct (owner_lstate_auth with "Hspec Hlstate_auth") as %->. congruence. }

      iSplitR "HΦ". { iFrameSteps 2. }
      iModIntro. clear- Hspec.

      wp_pures.
      iApply ("HΦ" $! None).
      destruct spec; try congruence; iSteps.
  Qed.
  Lemma rcfd_peek_spec t owned fd Ψ :
    {{{
      rcfd_inv t owned fd Ψ
    }}}
      rcfd_peek t
    {{{ o,
      RET o;
      match o with
      | None =>
          rcfd_closing t
      | Some fd_ =>
          ⌜fd_ = fd⌝
      end
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".

    wp_apply (rcfd_peek_spec_aux SpecNormal with "[$]").
    iSteps.
  Qed.
  Lemma rcfd_peek_spec_owner t owned fd Ψ :
    {{{
      rcfd_inv t owned fd Ψ ∗
      rcfd_owner t
    }}}
      rcfd_peek t
    {{{
      RET Some fd;
      rcfd_owner t
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & Howner) HΦ".

    wp_apply (rcfd_peek_spec_aux SpecOwner with "[$]").
    iSteps.
  Qed.
  Lemma rcfd_peek_spec_closing t owned fd Ψ :
    {{{
      rcfd_inv t owned fd Ψ ∗
      rcfd_closing t
    }}}
      rcfd_peek t
    {{{
      RET §None;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hclosing) HΦ".

    wp_apply (rcfd_peek_spec_aux SpecClosing with "[$]").
    iSteps.
  Qed.
End rcfd_G.

From zoo_eio Require
  rcfd__opaque.

#[global] Opaque rcfd_inv.
#[global] Opaque rcfd_owner.
#[global] Opaque rcfd_closing.
