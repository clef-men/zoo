Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Import zoo.common.gmultiset.
Require Import zoo.common.relations.
Require Import zoo.iris.base_logic.lib.auth_gmultiset.
Require Import zoo.iris.base_logic.lib.auth_mono.
Require Import zoo.base.
Require Import zoo_std.option.
Require Import zoo_std.spsc_waiter.
Require Import unix.unix.
Require Export zoo_eio.rcfd__code.
Require Import zoo_eio.rcfd__types.
Require Import zoo.options.

Implicit Type b owned closing : bool.
Implicit Type ops : Z.
Implicit Type q stock : Qp.
Implicit Type qs : gmultiset Qp.
Implicit Type l open : location.
Implicit Type t v v_state fd fn : val.
Implicit Type o : option val.

Record metadata :=
  { metadata۰fd : val
  ; metadata۰open : block_id
  ; metadata۰owned : bool
  ; metadata۰tokens : gname
  ; metadata۰lstate : gname
  }.
Implicit Type γ : metadata.

#[local] Instance metadata𑁒eq_dec : EqDecision metadata :=
  ltac:(solve_decision).
#[local] Instance metadata𑁒countable :
  Countable metadata.
Proof.
  solve_countable.
Qed.

Variant state :=
  | Open
  | Closing fn.
Implicit Type state : state.

#[local] Instance state𑁒inhabited : Inhabited state :=
  populate Open.
#[local] Instance state𑁒eq_dec : EqDecision state :=
  ltac:(solve_decision).

#[local] Definition state۰to_val γ state :=
  match state with
  | Open =>
      ‘Open@γ.(metadata۰open)[ γ.(metadata۰fd) ]
  | Closing fn =>
      ‘Closing[ fn ]
  end%V.
#[local] Arguments state۰to_val _ !_ / : assert.

Variant lstate :=
  | LOpen
  | LClosingUsers
  | LClosingNoUsers.
Implicit Type lstate : lstate.

#[local] Definition lstate۰measure lstate :=
  match lstate with
  | LOpen =>
      0
  | LClosingUsers =>
      1
  | LClosingNoUsers =>
      2
  end.

#[global] Instance lstate𑁒inhabited : Inhabited lstate :=
  populate LOpen.
#[global] Instance lstate𑁒eq_dec : EqDecision lstate :=
  ltac:(solve_decision).

Variant lstep : relation lstate :=
  | lstep𑁒close𑁒users :
      lstep LOpen LClosingUsers
  | lstep𑁒close𑁒no𑁒users :
      lstep LClosingUsers LClosingNoUsers.
#[local] Hint Constructors lstep : core.

#[local] Lemma lstep𑁒measure lstate1 lstate2 :
  lstep lstate1 lstate2 →
  lstate۰measure lstate1 < lstate۰measure lstate2.
Proof.
  intros []; simpl; lia.
Qed.
#[local] Lemma lstep𑁒tc𑁒measure lstate1 lstate2 :
  tc lstep lstate1 lstate2 →
  lstate۰measure lstate1 < lstate۰measure lstate2.
Proof.
  intros Hlsteps.
  apply transitive𑁒tc; first apply _.
  eapply (tc_congruence lstate۰measure); last done.
  apply lstep𑁒measure.
Qed.
#[local] Lemma lstep𑁒rtc𑁒measure lstate1 lstate2 :
  rtc lstep lstate1 lstate2 →
  lstate۰measure lstate1 ≤ lstate۰measure lstate2.
Proof.
  intros [<- | Hlsteps%lstep𑁒tc𑁒measure]%rtc_tc; lia.
Qed.

#[local] Instance lstep𑁒rtc𑁒antisymm :
  AntiSymm (=) (rtc lstep).
Proof.
  intros lstate1 lstate2 Hlsteps1 Hlsteps2%lstep𑁒rtc𑁒measure.
  apply rtc_tc in Hlsteps1 as [<- | Hlsteps1%lstep𑁒tc𑁒measure]; first done.
  lia.
Qed.

Class RcfdG Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] rcfd۰G۰spsc_waiter۰G :: SpscWaiterG Σ
  ; #[local] rcfd۰G۰tokens۰G :: AuthGmultisetG Σ Qp
  ; #[local] rcfd۰G۰lstate۰G :: AuthMonoG Σ (A := leibnizO lstate) lstep
  }.

Definition rcfd۰Σ :=
  #[spsc_waiter۰Σ
  ; auth_gmultiset۰Σ Qp
  ; auth_mono۰Σ (A := leibnizO lstate) lstep
  ].
#[global] Instance subG𑁒rcfd۰Σ `{zoo۰G : !ZooG Σ} :
  subG rcfd۰Σ Σ →
  RcfdG Σ.
Proof.
  solve_inG.
Qed.

Section rcfd۰G.
  Context `{rcfd۰G : RcfdG Σ}.

  Implicit Type Ψ : frac → iProp Σ.

  #[local] Definition tokens۰auth' γ_tokens Ψ ops : iProp Σ :=
    ∃ stock qs,
    ⌜ops = size qs⌝ ∗
    ⌜set_fold Qp.add stock qs = 1%Qp⌝ ∗
    auth_gmultiset۰auth γ_tokens (DfracOwn 1) qs ∗
    Ψ stock.
  #[local] Definition tokens۰auth γ :=
    tokens۰auth' γ.(metadata۰tokens).
  #[local] Instance : CustomIpat "tokens۰auth" :=
    " ( %stock
      & %qs
      & {{lazy}%Hops;->}
      & %Hqs
      & Hauth
      & HΨ_stock
      )
    ".
  #[local] Definition tokens۰frag γ q :=
    auth_gmultiset۰frag γ.(metadata۰tokens) {[+q+]}.

  #[local] Definition lstate۰auth_frac owned lstate :=
    match lstate with
    | LOpen =>
        if owned then 1/4 else 1
    | _ =>
        1
    end%Qp.
  #[local] Definition lstate۰auth' γ_lstate owned lstate :=
    auth_mono۰auth _ γ_lstate (DfracOwn $ lstate۰auth_frac owned lstate) lstate.
  #[local] Definition lstate۰auth γ :=
    lstate۰auth' γ.(metadata۰lstate) γ.(metadata۰owned).
  #[local] Definition lstate۰lb γ lstate :=
    auth_mono۰lb _ γ.(metadata۰lstate) lstate.

  #[local] Definition owner' γ_lstate :=
    auth_mono۰auth _ γ_lstate (DfracOwn (3/4)%Qp) LOpen.
  #[local] Definition owner γ :=
    owner' γ.(metadata۰lstate).

  #[local] Definition inv۰lstate۰open γ Ψ state ops : iProp Σ :=
    tokens۰auth γ Ψ ops ∗
    ⌜state = Open⌝.
  #[local] Instance : CustomIpat "inv۰lstate۰open" :=
    " ( Htokens_auth
      & {%H{eq};->}
      )
    ".
  #[local] Definition inv۰lstate۰closing۰users γ Ψ state ops : iProp Σ :=
    ∃ fn,
    tokens۰auth γ Ψ ops ∗
    ⌜state = Closing fn⌝ ∗
    ⌜0 < ops⌝%Z ∗
    (Ψ 1%Qp -∗ WP fn () {{ itype۰unit }}).
  #[local] Instance : CustomIpat "inv۰lstate۰closing۰users" :=
    " ( %fn{}
      & Htokens_auth
      & {%H{eq};->}
      & %Hops{}
      & Hfn{}
      )
    ".
  #[local] Definition inv۰lstate۰closing۰no_users state : iProp Σ :=
    ∃ fn,
    ⌜state = Closing fn⌝ ∗
    WP fn () {{ itype۰unit }}.
  #[local] Instance : CustomIpat "inv۰lstate۰closing۰no_users" :=
    " ( %fn{}
      & {%H{eq};->}
      & Hfn{}
      )
    ".
  #[local] Definition inv۰lstate γ Ψ state lstate ops :=
    match lstate with
    | LOpen =>
        inv۰lstate۰open γ Ψ state ops
    | LClosingUsers =>
        inv۰lstate۰closing۰users γ Ψ state ops
    | LClosingNoUsers =>
        inv۰lstate۰closing۰no_users state
    end.

  #[local] Definition inv۰inner l γ Ψ : iProp Σ :=
    ∃ state lstate ops,
    l.[ops] ↦ #ops ∗
    l.[state] ↦ state۰to_val γ state ∗
    lstate۰auth γ lstate ∗
    inv۰lstate γ Ψ state lstate ops.
  #[local] Instance : CustomIpat "inv۰inner" :=
    " ( %state{}
      & %lstate{}
      & %ops{}
      & Hl_ops
      & Hl_state
      & Hlstate_auth
      & Hlstate
      )
    ".
  #[local] Definition inv' l γ Ψ :=
    inv nroot (inv۰inner l γ Ψ).
  Definition rcfd۰inv t owned fd Ψ : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    ⌜owned = γ.(metadata۰owned)⌝ ∗
    ⌜fd = γ.(metadata۰fd)⌝ ∗
    l ↪ γ ∗
    inv' l γ Ψ.
  #[local] Instance : CustomIpat "inv" :=
    " ( %l
      & %γ
      & ->
      & ->
      & ->
      & #Hmeta
      & #Hinv
      )
    ".

  Definition rcfd۰owner t : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    l ↪ γ ∗
    owner γ.
  #[local] Instance : CustomIpat "owner" :=
    " ( %l{;_}
      & %γ{;_}
      & %Heq{}
      & #Hmeta_{}
      & Howner{_{}}
      )
    ".

  Definition rcfd۰closing t : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    l ↪ γ ∗
    lstate۰lb γ LClosingUsers.
  #[local] Instance : CustomIpat "closing" :=
    " ( %l{;_}
      & %γ{;_}
      & %Heq{}
      & #Hmeta_{}
      & #Hlstate_lb{_{}}
      )
    ".

  #[local] Instance tokens۰auth'𑁒ne γ_tokens n :
    Proper (
      (pointwise_relation _ (≡{n}≡)) ==>
      (=) ==>
      (≡{n}≡)
    ) (tokens۰auth' γ_tokens).
  Proof.
    solve_proper.
  Qed.
  #[local] Instance tokens۰auth'𑁒proper γ_tokens :
    Proper (
      (pointwise_relation _ (≡)) ==>
      (=) ==>
      (≡)
    ) (tokens۰auth' γ_tokens).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance rcfd۰inv𑁒contractive t owned fd n :
    Proper (
      (pointwise_relation _ (dist_later n)) ==>
      (≡{n}≡)
    ) (rcfd۰inv t owned fd).
  Proof.
    rewrite /rcfd۰inv /inv' /inv۰inner /inv۰lstate /inv۰lstate۰open /inv۰lstate۰closing۰users.
    solve_contractive.
  Qed.
  #[global] Instance rcfd۰inv𑁒proper t owned fd :
    Proper (
      (pointwise_relation _ (≡)) ==>
      (≡)
    ) (rcfd۰inv t owned fd).
  Proof.
    rewrite /rcfd۰inv /inv' /inv۰inner /inv۰lstate /inv۰lstate۰open /inv۰lstate۰closing۰users.
    solve_proper.
  Qed.

  #[global] Instance rcfd۰owner𑁒timeless t :
    Timeless (rcfd۰owner t).
  Proof.
    apply _.
  Qed.
  #[global] Instance rcfd۰closing𑁒timeless t :
    Timeless (rcfd۰closing t).
  Proof.
    apply _.
  Qed.

  #[global] Instance rcfd۰inv𑁒persistent t owned fd Ψ :
    Persistent (rcfd۰inv t owned fd Ψ).
  Proof.
    apply _.
  Qed.
  #[global] Instance rcfd۰closing𑁒persistent t :
    Persistent (rcfd۰closing t).
  Proof.
    apply _.
  Qed.

  #[local] Lemma tokens𑁒alloc Ψ :
    Ψ 1%Qp ⊢ |==>
      ∃ γ_tokens,
      tokens۰auth' γ_tokens Ψ 0.
  Proof.
    iIntros "HΨ".
    iMod auth_gmultiset𑁒alloc as "(%γ_tokens & $)".
    iSteps.
  Qed.
  #[local] Lemma tokens۰auth𑁒valid γ Ψ ops :
    tokens۰auth γ Ψ ops ⊢
    ⌜(0 ≤ ops)%Z⌝.
  Proof.
    iSteps.
  Qed.
  #[local] Lemma tokens۰auth𑁒consume γ Ψ :
    tokens۰auth γ Ψ 0 ⊢
    Ψ 1%Qp.
  Proof.
    iIntros "(:tokens۰auth lazy=)".
    opose proof* (gmultiset_size_empty_inv qs) as ->; first lia.
    rewrite gmultiset_set_fold_empty in Hqs.
    rewrite Hqs //.
  Qed.
  #[local] Lemma tokens𑁒update𑁒alloc γ Ψ `{!Fractional Ψ} ops :
    tokens۰auth γ Ψ ops ⊢ |==>
      ∃ q,
      tokens۰auth γ Ψ (ops + 1) ∗
      tokens۰frag γ q ∗
      Ψ q.
  Proof.
    iIntros "(:tokens۰auth)".
    iMod (auth_gmultiset𑁒update𑁒alloc𑁒singleton (stock / 2)%Qp with "Hauth") as "($ & $)".
    iDestruct (fractional_half with "HΨ_stock") as "(HΨ_stock & HΨ)"; first done.
    iFrameSteps; iPureIntro.
    - rewrite gmultiset_size_disj_union gmultiset_size_singleton. lia.
    - rewrite gmultiset_set_fold_disj_union gmultiset_set_fold_singleton Qp.div_2 //.
  Qed.
  #[local] Lemma tokens𑁒update𑁒dealloc γ Ψ `{!Fractional Ψ} ops q :
    tokens۰auth γ Ψ ops -∗
    tokens۰frag γ q -∗
    Ψ q ==∗
    tokens۰auth γ Ψ (ops - 1).
  Proof.
    iIntros "(:tokens۰auth) Hfrag HΨ".
    iDestruct (auth_gmultiset𑁒elem_of with "Hauth Hfrag") as %Hq.
    iMod (auth_gmultiset𑁒update𑁒dealloc with "Hauth Hfrag") as "$".
    iDestruct (fractional (Φ := Ψ) with "[$HΨ $HΨ_stock]") as "HΨ_stock".
    iFrameSteps; iPureIntro.
    - rewrite gmultiset_size_difference; first multiset_solver.
      rewrite gmultiset_size_singleton.
      apply gmultiset𑁒elem_of𑁒size𑁒non_empty in Hq. lia.
    - rewrite (gmultiset_disj_union_difference' q qs) // gmultiset_set_fold_disj_union gmultiset_set_fold_singleton // in Hqs.
  Qed.

  #[local] Lemma lstate𑁒alloc owned :
    ⊢ |==>
      ∃ γ_lstate,
      lstate۰auth' γ_lstate owned LOpen ∗
      if owned then
        owner' γ_lstate
      else
        True.
  Proof.
    iMod (auth_mono𑁒alloc (auth_mono۰G := rcfd۰G۰lstate۰G) _ LOpen) as "(%γ_lstate & Hauth)".
    destruct owned; last iSteps.
    iEval (rewrite -Qp.quarter_three_quarter) in "Hauth".
    iDestruct "Hauth" as "(Hauth & Howner)".
    iSteps.
  Qed.
  #[local] Lemma lstate۰lb𑁒get γ lstate :
    lstate۰auth γ lstate ⊢
    lstate۰lb γ lstate.
  Proof.
    apply auth_mono۰lb𑁒get.
  Qed.
  #[local] Lemma lstate۰lb𑁒mono {γ lstate} lstate' :
    lstep lstate' lstate →
    lstate۰lb γ lstate ⊢
    lstate۰lb γ lstate'.
  Proof.
    apply auth_mono۰lb𑁒mono'.
  Qed.
  #[local] Lemma lstate𑁒valid γ lstate lstate' :
    lstate۰auth γ lstate -∗
    lstate۰lb γ lstate' -∗
    ⌜rtc lstep lstate' lstate⌝.
  Proof.
    apply: auth_mono۰lb𑁒valid.
  Qed.
  #[local] Lemma lstate𑁒valid𑁒closing𑁒users γ lstate :
    lstate۰auth γ lstate -∗
    lstate۰lb γ LClosingUsers -∗
    ⌜lstate ≠ LOpen⌝.
  Proof.
    iIntros "Hauth Hlb".
    iDestruct (lstate𑁒valid with "Hauth Hlb") as %Hlsteps.
    iPureIntro.
    apply rtc_inv in Hlsteps as [<- | (lstate' & Hlstep & Hlsteps)]; first naive_solver.
    invert Hlstep.
    apply rtc_inv in Hlsteps as [<- | (lstate' & Hlstep & Hlsteps)]; first naive_solver.
    invert Hlstep.
  Qed.
  #[local] Lemma lstate𑁒valid𑁒closing𑁒users' γ lstate :
    lstate۰auth γ lstate -∗
    lstate۰lb γ LClosingUsers -∗
    ⌜lstate = LClosingUsers ∨ lstate = LClosingNoUsers⌝.
  Proof.
    iIntros "Hauth Hlb".
    iDestruct (lstate𑁒valid𑁒closing𑁒users with "Hauth Hlb") as %Hlstate.
    destruct lstate; iSteps.
  Qed.
  #[local] Lemma lstate𑁒valid𑁒closing𑁒no_users γ lstate :
    lstate۰auth γ lstate -∗
    lstate۰lb γ LClosingNoUsers -∗
    ⌜lstate = LClosingNoUsers⌝.
  Proof.
    iIntros "Hauth Hlb".
    iDestruct (lstate𑁒valid with "Hauth Hlb") as %Hlsteps.
    iPureIntro.
    apply rtc_inv in Hlsteps as [<- | (lstate' & Hlstep & Hlsteps)]; first naive_solver.
    invert Hlstep.
  Qed.
  #[local] Lemma lstate𑁒update𑁒close𑁒users γ :
    lstate۰auth γ LOpen -∗
    (if γ.(metadata۰owned) then owner γ else True) ==∗
    lstate۰auth γ LClosingUsers.
  Proof.
    iIntros "Hauth Howner".
    iAssert (auth_mono۰auth (auth_mono۰G := rcfd۰G۰lstate۰G) _ γ.(metadata۰lstate) (DfracOwn 1) LOpen) with "[Hauth Howner]" as "Hauth".
    { rewrite /lstate۰auth /lstate۰auth' /=.
      destruct γ.(metadata۰owned); last iSteps.
      iCombine "Hauth Howner" as "Hauth".
      iEval (rewrite Qp.quarter_three_quarter) in "Hauth".
      iSteps.
    }
    iApply (auth_mono𑁒update' with "Hauth"); first done.
  Qed.
  #[local] Lemma lstate𑁒update𑁒close𑁒no_users γ :
    lstate۰auth γ LClosingUsers ⊢ |==>
    lstate۰auth γ LClosingNoUsers.
  Proof.
    apply auth_mono𑁒update'; first done.
  Qed.

  #[local] Lemma owner𑁒exclusive γ :
    owner γ -∗
    owner γ -∗
    False.
  Proof.
    iIntros "Hauth_1 Hauth_2".
    iDestruct (auth_mono۰auth𑁒valid𑁒2 with "Hauth_1 Hauth_2") as "(% & _)". done.
  Qed.
  #[local] Lemma owner𑁒lstate۰auth γ lstate :
    owner γ -∗
    lstate۰auth γ lstate -∗
    ⌜lstate = LOpen⌝.
  Proof.
    iIntros "Howner Hauth".
    iApply (auth_mono۰auth𑁒agree𑁒L with "Hauth Howner").
  Qed.
  #[local] Lemma owner𑁒lstate۰lb γ :
    owner γ -∗
    lstate۰lb γ LClosingUsers -∗
    False.
  Proof.
    iIntros "Hauth Hlb".
    iDestruct (auth_mono۰lb𑁒valid with "Hauth Hlb") as %H%lstep𑁒rtc𑁒measure.
    exfalso. simpl in H. lia.
  Qed.

  Opaque tokens۰auth'.

  #[local] Lemma rcfd۰owner𑁒elim l γ :
    l ↪ γ -∗
    rcfd۰owner #l -∗
    owner γ.
  Proof.
    iIntros "#Hmeta (:owner)". injection Heq as <-.
    iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-.
    iSteps.
  Qed.
  #[local] Lemma rcfd۰owner𑁒elim' l γ b :
    l ↪ γ -∗
    ( if b then
        rcfd۰owner #l
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
    iApply (rcfd۰owner𑁒elim with "Hmeta Howner").
  Qed.
  Lemma rcfd۰owner𑁒exclusive t :
    rcfd۰owner t -∗
    rcfd۰owner t -∗
    False.
  Proof.
    iIntros "(:owner =1) (:owner =2)". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (owner𑁒exclusive with "Howner_1 Howner_2").
  Qed.
  Lemma rcfd۰owner𑁒closing t :
    rcfd۰owner t -∗
    rcfd۰closing t -∗
    False.
  Proof.
    iIntros "(:owner =1) (:closing =2)". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (owner𑁒lstate۰lb with "Howner_1 Hlstate_lb_2").
  Qed.

  #[local] Lemma rcfd۰closing𑁒elim l γ :
    l ↪ γ -∗
    rcfd۰closing #l -∗
    lstate۰lb γ LClosingUsers.
  Proof.
    iIntros "#Hmeta (:closing)". injection Heq as <-.
    iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-.
    iSteps.
  Qed.
  #[local] Lemma rcfd۰closing𑁒elim' l γ b P :
    l ↪ γ -∗
    ( if b then
        rcfd۰closing #l
      else
        P
    ) -∗
    if b then
      lstate۰lb γ LClosingUsers
    else
      P.
  Proof.
    iIntros "#Hmeta Hclosing".
    destruct b; last iSteps.
    iApply (rcfd۰closing𑁒elim with "Hmeta Hclosing").
  Qed.

  #[local] Lemma inv۰lstate𑁒Open γ Ψ lstate ops :
    inv۰lstate γ Ψ Open lstate ops ⊢
    ⌜lstate = LOpen⌝.
  Proof.
    destruct lstate; iSteps.
  Qed.
  #[local] Lemma inv۰lstate𑁒Closing γ Ψ state lstate ops :
    state ≠ Open →
    inv۰lstate γ Ψ state lstate ops -∗
    lstate۰auth γ lstate -∗
      ∃ fn,
      ⌜state = Closing fn⌝ ∗
      ⌜lstate ≠ LOpen ⌝ ∗
      lstate۰lb γ LClosingUsers.
  Proof.
    iIntros "%Hlstate Hlstate Hlstate_auth".
    iDestruct (lstate۰lb𑁒get with "Hlstate_auth") as "Hlstate_lb".
    destruct lstate.
    - iDestruct "Hlstate" as "(:inv۰lstate۰open)".
      exfalso. done.
    - iDestruct "Hlstate" as "(:inv۰lstate۰closing۰users)".
      iSteps.
    - iDestruct "Hlstate" as "(:inv۰lstate۰closing۰no_users)".
      iDestruct (lstate۰lb𑁒mono with "Hlstate_lb") as "$"; first done.
      iSteps.
  Qed.
  #[local] Lemma inv۰lstate𑁒LClosing γ Ψ state lstate ops :
    lstate ≠ LOpen →
    inv۰lstate γ Ψ state lstate ops -∗
    lstate۰auth γ lstate -∗
      ∃ fn,
      ⌜state = Closing fn⌝ ∗
      lstate۰lb γ LClosingUsers.
  Proof.
    iIntros "%Hlstate Hlstate Hlstate_auth".
    iDestruct (lstate۰lb𑁒get with "Hlstate_auth") as "Hlstate_lb".
    destruct lstate; first done.
    - iDestruct "Hlstate" as "(:inv۰lstate۰closing۰users)".
      iSteps.
    - iDestruct "Hlstate" as "(:inv۰lstate۰closing۰no_users)".
      iDestruct (lstate۰lb𑁒mono with "Hlstate_lb") as "$"; first done.
      iSteps.
  Qed.

  Lemma rcfd٠make𑁒spec owned Ψ fd :
    {{{
      Ψ 1%Qp
    }}}
      rcfd٠make fd
    {{{
      t
    , RET t;
      rcfd۰inv t owned fd Ψ ∗
      if owned then
        rcfd۰owner t
      else
        True
    }}}.
  Proof.
    iIntros "%Φ HΨ HΦ".

    wp۰rec.
    wp۰block۰generative open.
    wp۰block l as "Hmeta" "(Hl_ops & Hl_fd & _)".

    iMod (tokens𑁒alloc with "HΨ") as "(%γ_tokens & Htokens_auth)".
    iMod (lstate𑁒alloc owned) as "(%γ_lstate & Hlstate_auth & Howner)".

    pose γ :=
      {|metadata۰fd := fd
      ; metadata۰open := open
      ; metadata۰owned := owned
      ; metadata۰tokens := γ_tokens
      ; metadata۰lstate := γ_lstate
      |}.
    iMod (meta𑁒set γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitR "Howner".
    - iExists l, γ. iSteps. iExists Open. iSteps.
    - destruct owned; iSteps.
  Qed.

  #[local] Lemma rcfd٠finish𑁒spec l γ Ψ (close : val) :
    {{{
      inv' l γ Ψ ∗
      lstate۰lb γ LClosingUsers
    }}}
      rcfd٠finish #l close ’Closing[ close ]
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hlstate_lb) HΦ".

    wp۰rec. wp۰pures.

    wp۰bind (_.{ops})%E.
    iInv "Hinv" as "(:inv۰inner =1)".
    wp۰load.
    iDestruct (lstate𑁒valid𑁒closing𑁒users' with "Hlstate_auth Hlstate_lb") as %[-> | ->].

    - iDestruct "Hlstate" as "(:inv۰lstate۰closing۰users =1)".
      iSplitR "HΦ". { iFrameSteps 2. }
      iSteps.

    - iDestruct "Hlstate" as "(:inv۰lstate۰closing۰no_users =1)".
      iDestruct (lstate۰lb𑁒get with "Hlstate_auth") as "{Hlstate_lb} #Hlstate_lb".
      iSplitR "HΦ". { iFrameSteps 2. }
      iIntros "!> {%}".

      wp۰pures.
      case_bool_decide as Hops3; wp۰pures; last iSteps.

      wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
      iInv "Hinv" as "(:inv۰inner =2)".
      wp۰cas as _ | Hcas; first iSteps.
      destruct state2; first zoo_simplify.
      destruct Hcas as (_ & _ & [= <-]).
      iDestruct (lstate𑁒valid𑁒closing𑁒no_users with "Hlstate_auth Hlstate_lb") as %->.
      iDestruct "Hlstate" as "(:inv۰lstate۰closing۰no_users =2 eq)". injection Heq as <-.
      iSplitR "Hfn2 HΦ".
      { iExists (Closing _). iFrameSteps. }
      iSteps.
  Qed.

  #[local] Lemma rcfd٠put𑁒spec l γ Ψ `{!Fractional Ψ} :
    {{{
      inv' l γ Ψ ∗
      ( lstate۰lb γ LClosingNoUsers
      ∨ ∃ q,
        tokens۰frag γ q ∗
        Ψ q
      )
    }}}
      rcfd٠put #l
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & H) HΦ".

    wp۰rec. wp۰pures.

    wp۰bind (𝗳𝗮𝗮 _ _)%E.
    iInv "Hinv" as "(:inv۰inner =1)".
    wp۰faa.
    iSplitR "HΦ".
    { iDestruct "H" as "[#Hlstate_lb | (%q & Htokens_frag & HΨ)]".
      - iDestruct (lstate𑁒valid𑁒closing𑁒no_users with "Hlstate_auth Hlstate_lb") as %->.
        iDestruct "Hlstate" as "(:inv۰lstate۰closing۰no_users =1)".
        iFrameSteps 2.
      - destruct lstate1.
        + iDestruct "Hlstate" as "(:inv۰lstate۰open =1 !=)".
          iMod (tokens𑁒update𑁒dealloc with "Htokens_auth Htokens_frag HΨ") as "Htokens_auth".
          iFrameSteps 2.
        + iDestruct "Hlstate" as "(:inv۰lstate۰closing۰users =1 !=)".
          iMod (tokens𑁒update𑁒dealloc with "Htokens_auth Htokens_frag HΨ") as "Htokens_auth".
          destruct_decide (ops1 = 1) as -> | ?.
          * iDestruct (tokens۰auth𑁒consume with "Htokens_auth") as "HΨ".
            iMod (lstate𑁒update𑁒close𑁒no_users with "Hlstate_auth") as "Hlstate_auth".
            iFrameSteps.
          * iFrameSteps 2.
        + iDestruct "Hlstate" as "(:inv۰lstate۰closing۰no_users =1)".
          iFrameSteps 2.
    }
    iIntros "!> {%}".

    wp۰pures.
    destruct_decide (ops1 = 1) as -> | Hops; wp۰pures; last iSteps.

    wp۰bind (_.{state})%E.
    iInv "Hinv" as "(:inv۰inner =2)".
    wp۰load.
    destruct_decide (lstate2 = LOpen) as -> | Hlstate2.

    - iDestruct "Hlstate" as "(:inv۰lstate۰open =2)".
      iSplitR "HΦ". { iFrameSteps 2. }
      iSteps.

    - iDestruct (inv۰lstate𑁒LClosing with "Hlstate Hlstate_auth") as "(%fn2 & -> & #Hlstate_lb)"; first done.
      iSplitR "HΦ". { iFrameSteps 2. }
      iIntros "!> {%}".

      wp۰apply+ (rcfd٠finish𑁒spec with "[$] HΦ").
  Qed.

  Variant specification :=
    | SpecOwner
    | SpecClosing
    | SpecNormal.
  Implicit Type spec : specification.

  #[local] Instance specification𑁒eq_dec : EqDecision specification :=
    ltac:(solve_decision).

  #[local] Definition specification۰pre₁ t spec : iProp Σ :=
    match spec with
    | SpecOwner =>
        rcfd۰owner t
    | SpecClosing =>
        rcfd۰closing t
    | SpecNormal =>
        True
    end.
  #[local] Definition specification۰pre₂ γ spec : iProp Σ :=
    match spec with
    | SpecOwner =>
        owner γ
    | SpecClosing =>
        lstate۰lb γ LClosingUsers
    | SpecNormal =>
        True
    end.
  #[local] Lemma specification𑁒pre₁𑁒pre₂ l γ spec :
    l ↪ γ -∗
    specification۰pre₁ #l spec -∗
    specification۰pre₂ γ spec.
  Proof.
    iIntros "#Hmeta Hspec".
    destruct spec; last iSteps.
    - iApply (rcfd۰owner𑁒elim with "Hmeta Hspec").
    - iApply (rcfd۰closing𑁒elim with "Hmeta Hspec").
  Qed.

  #[local] Lemma rcfd٠get𑁒spec𑁒aux spec l γ Ψ `{HΨ : !Fractional Ψ} :
    {{{
      inv' l γ Ψ ∗
      specification۰pre₂ γ spec
    }}}
      rcfd٠get #l
    {{{
      o
    , RET o;
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
          ⌜fd_ = γ.(metadata۰fd)⌝ ∗
          tokens۰frag γ q ∗
          Ψ q
      end
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & Hspec) HΦ".

    wp۰rec. wp۰pures.

    wp۰bind (𝗳𝗮𝗮 _ _)%E.
    iInv "Hinv" as "(:inv۰inner =1)".
    wp۰faa.

    iAssert (|==>
      inv۰inner l γ Ψ ∗
      ( lstate۰lb γ LClosingNoUsers
      ∨ ∃ q,
        tokens۰frag γ q ∗
        Ψ q
      )
    )%I with "[- Hspec HΦ]" as ">($ & H)".
    { destruct lstate1.
      - iDestruct "Hlstate" as "(:inv۰lstate۰open)".
        iMod (tokens𑁒update𑁒alloc with "Htokens_auth") as "(%q & Htokens_auth & Htokens_frag & HΨ)".
        iSplitR "Htokens_frag HΨ"; last iSteps.
        iFrameSteps 2.
      - iDestruct "Hlstate" as "(:inv۰lstate۰closing۰users)".
        iMod (tokens𑁒update𑁒alloc with "Htokens_auth") as "(%q & Htokens_auth & Htokens_frag & HΨ)".
        iSplitR "Htokens_frag HΨ"; last iSteps.
        iFrameSteps 2.
      - iDestruct "Hlstate" as "(:inv۰lstate۰closing۰no_users)".
        iDestruct (lstate۰lb𑁒get with "Hlstate_auth") as "#Hlstate_lb".
        iFrameSteps 2.
    }

    iModIntro. wp۰pures. clear- HΨ.

    wp۰bind (_.{state})%E.
    iInv "Hinv" as "(:inv۰inner =2)".
    wp۰load.
    destruct_decide (lstate2 = LOpen) as -> | Hlstate2.

    - iDestruct "Hlstate" as "(:inv۰lstate۰open)".

      iDestruct "H" as "[#Hlstate_lb | (%q' & Htokens_frag & HΨ_)]".
      { iDestruct (lstate𑁒valid𑁒closing𑁒no_users with "Hlstate_auth Hlstate_lb") as %?. done. }

      iAssert ⌜spec ≠ SpecClosing⌝%I as %Hspec.
      { iIntros (->).
        iDestruct (lstate𑁒valid𑁒closing𑁒users with "Hlstate_auth Hspec") as %?. congruence.
      }

      iSplitR "Hspec Htokens_frag HΨ_ HΦ". { iFrameSteps 2. }
      iIntros "!> {%- Hspec}".

      wp۰pures.
      iApply ("HΦ" $! (Some _)).
      destruct spec; try congruence; iSteps.

    - iDestruct (inv۰lstate𑁒LClosing with "Hlstate Hlstate_auth") as "#(%fn2 & -> & _)"; first done.

      iAssert ⌜spec ≠ SpecOwner⌝%I as %Hspec.
      { iIntros (->).
        iDestruct (owner𑁒lstate۰auth with "Hspec Hlstate_auth") as %->. congruence.
      }

      iSplitR "H HΦ". { iFrameSteps 2. }
      iIntros "!> {%- HΨ Hspec}".

      wp۰apply+ (rcfd٠put𑁒spec with "[$]") as "_".
      wp۰pures.
      iApply ("HΦ" $! None).
      destruct spec; try congruence; iSteps.
  Qed.
  #[local] Lemma rcfd٠get𑁒spec l γ Ψ `{HΨ : !Fractional Ψ} :
    {{{
      inv' l γ Ψ
    }}}
      rcfd٠get #l
    {{{
      o
    , RET o;
      match o with
      | None =>
          True
      | Some fd_ =>
          ∃ q,
          ⌜fd_ = γ.(metadata۰fd)⌝ ∗
          tokens۰frag γ q ∗
          Ψ q
      end
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".

    wp۰apply (rcfd٠get𑁒spec𑁒aux SpecNormal with "[$]").
    iSteps.
  Qed.
  #[local] Lemma rcfd٠get𑁒spec𑁒owner l γ Ψ `{HΨ : !Fractional Ψ} :
    {{{
      inv' l γ Ψ ∗
      owner γ
    }}}
      rcfd٠get #l
    {{{
      RET Some γ.(metadata۰fd);
      ∃ q,
      owner γ ∗
      tokens۰frag γ q ∗
      Ψ q
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & Howner) HΦ".

    wp۰apply (rcfd٠get𑁒spec𑁒aux SpecOwner with "[$]") as ([v |]) ""; last iSteps.
    iSteps.
  Qed.
  #[local] Lemma rcfd٠get𑁒spec𑁒closing l γ Ψ `{HΨ : !Fractional Ψ} :
    {{{
      inv' l γ Ψ ∗
      lstate۰lb γ LClosingUsers
    }}}
      rcfd٠get #l
    {{{
      RET None;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hlstate_lb) HΦ".

    wp۰apply (rcfd٠get𑁒spec𑁒aux SpecClosing with "[$]").
    iSteps.
  Qed.

  #[local] Lemma rcfd٠use𑁒spec𑁒aux spec Χ t owned fd Ψ `{!Fractional Ψ} (closed open : val) :
    {{{
      rcfd۰inv t owned fd Ψ ∗
      specification۰pre₁ t spec ∗
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
      rcfd٠use t closed open
    {{{
      b res
    , RET res;
      Χ b res ∗
      match spec with
      | SpecOwner =>
          ⌜b = true⌝ ∗
          rcfd۰owner t
      | SpecClosing =>
          ⌜b = false⌝
      | SpecNormal =>
          True
      end
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & Hspec & Hclosed & Hopen) HΦ".
    iDestruct (specification𑁒pre₁𑁒pre₂ with "Hmeta Hspec") as "Hspec".

    wp۰rec.
    wp۰apply+ (rcfd٠get𑁒spec𑁒aux with "[$]") as ([v |]) "(Hspec & H)".

    - iDestruct "H" as "(%q & -> & Htoken & HΨ)".

      destruct_decide (spec = SpecClosing) as -> | Hspec.
      { iDestruct "Hspec" as %[=]. }
      iEval (rewrite decide_True //) in "Hopen".

      wp۰apply+ (wp𑁒wand with "(Hopen HΨ)") as "%res (HΨ & HΧ)".
      wp۰apply+ (rcfd٠put𑁒spec with "[Htoken HΨ]") as "_"; first iSteps.
      wp۰pures.
      destruct spec; try congruence; iSteps.

    - destruct_decide (spec = SpecOwner) as -> | Hspec.
      { iDestruct "Hspec" as "(% & _)". congruence. }
      iEval (rewrite decide_True //) in "Hclosed".

      wp۰apply+ (wp𑁒wand with "Hclosed") as "%res HΧ".
      destruct spec; try congruence; iSteps.
  Qed.
  Lemma rcfd٠use𑁒spec Χ t owned fd Ψ `{!Fractional Ψ} (closed open : val) :
    {{{
      rcfd۰inv t owned fd Ψ ∗
      WP closed () {{ Χ false }} ∗
      ( ∀ q,
        Ψ q -∗
        WP open fd {{ res,
          Ψ q ∗
          Χ true res
        }}
      )
    }}}
      rcfd٠use t closed open
    {{{
      b res
    , RET res;
      Χ b res
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & Hclosed & Hopen) HΦ".

    wp۰apply (rcfd٠use𑁒spec𑁒aux SpecNormal with "[$]").
    iSteps.
  Qed.
  Lemma rcfd٠use𑁒spec𑁒owner Χ t owned fd Ψ `{!Fractional Ψ} (closed open : val) :
    {{{
      rcfd۰inv t owned fd Ψ ∗
      rcfd۰owner t ∗
      ( ∀ q,
        Ψ q -∗
        WP open fd {{ res,
          Ψ q ∗
          Χ res
        }}
      )
    }}}
      rcfd٠use t closed open
    {{{
      res
    , RET res;
      Χ res
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & Howner & Hopen) HΦ".

    wp۰apply (rcfd٠use𑁒spec𑁒aux SpecOwner (const Χ) with "[$]").
    iSteps.
  Qed.
  Lemma rcfd٠use𑁒spec𑁒closing Χ t owned fd Ψ `{!Fractional Ψ} (closed open : val) :
    {{{
      rcfd۰inv t owned fd Ψ ∗
      rcfd۰closing t ∗
      WP closed () {{ Χ }}
    }}}
      rcfd٠use t closed open
    {{{
      res
    , RET res;
      Χ res
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & Howner & Hclosed) HΦ".

    wp۰apply (rcfd٠use𑁒spec𑁒aux SpecClosing (const Χ) with "[$]").
    iSteps.
  Qed.

  #[local] Lemma rcfd٠close𑁒spec𑁒aux closing t owned fd Ψ :
    {{{
      rcfd۰inv t owned fd Ψ ∗
      ( if owned then
          rcfd۰owner t
        else
          True
      ) ∗
      ( if closing then
          rcfd۰closing t
        else
          Ψ 1%Qp -∗
            ∃ chars,
            unix۰fd_model fd (DfracOwn 1) chars
      )
    }}}
      rcfd٠close t
    {{{
      b
    , RET #b;
      rcfd۰closing t ∗
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
    iDestruct (rcfd۰owner𑁒elim' with "Hmeta Howner") as "Howner".
    iDestruct (rcfd۰closing𑁒elim' with "Hmeta Hclosing") as "Hclosing".

    wp۰rec. wp۰pures.

    wp۰bind (_.{state})%E.
    iInv "Hinv" as "(:inv۰inner =1)".
    wp۰load.
    destruct_decide (lstate1 = LOpen) as -> | Hlstate1.

    - iDestruct "Hlstate" as "(:inv۰lstate۰open =1)".

      destruct closing.
      { iDestruct (lstate𑁒valid𑁒closing𑁒users with "Hlstate_auth Hclosing") as %?. congruence. }

      iSplitR "Howner Hclosing HΦ". { iFrameSteps 2. }
      iIntros "!> {%}".

      wp۰pures.

      wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
      iInv "Hinv" as "(:inv۰inner =2)".
      wp۰cas as Hcas.

      + iDestruct (inv۰lstate𑁒Closing with "Hlstate Hlstate_auth") as "(%fn2 & -> & %Hlstate2 & #Hlstate_lb)".
        { intros ->. zoo_simplify in Hcas. naive_solver. }

        destruct γ.(metadata۰owned).
        { iDestruct (owner𑁒lstate۰auth with "Howner Hlstate_auth") as %->. congruence. }

        iSplitR "HΦ". { iFrameSteps 2. }
        iSteps.

      + destruct state2; last zoo_simplify.
        iDestruct (inv۰lstate𑁒Open with "Hlstate") as %->.
        iDestruct "Hlstate" as "(:inv۰lstate۰open =2 eq)".

        iMod (lstate𑁒update𑁒close𑁒users with "Hlstate_auth Howner") as "Hlstate_auth".
        iDestruct (lstate۰lb𑁒get with "Hlstate_auth") as "#Hlstate_lb".
        iSplitR "HΦ".
        { destruct_decide (ops2 = 0) as -> | Hops.
          - iDestruct (tokens۰auth𑁒consume with "Htokens_auth") as "HΨ".
            iMod (lstate𑁒update𑁒close𑁒no_users with "Hlstate_auth") as "Hlstate_auth".
            iDestruct ("Hclosing" with "HΨ") as "(%chars & Hfd)".
            iExists (Closing _). iFrameSteps.
          - iDestruct (tokens۰auth𑁒valid with "Htokens_auth") as %?.
            iExists (Closing _). iFrame. iStep 6 as "HΨ".
            iDestruct ("Hclosing" with "HΨ") as "(%chars & Hfd)".
            iSteps.
        }
        iIntros "!> {%}".

        wp۰apply+ (rcfd٠finish𑁒spec with "[$]").
        destruct γ.(metadata۰owned); iSteps.

    - iDestruct (inv۰lstate𑁒LClosing with "Hlstate Hlstate_auth") as "(%fn1 & -> & #Hlstate_lb)"; first done.

      destruct γ.(metadata۰owned).
      { iDestruct (owner𑁒lstate۰auth with "Howner Hlstate_auth") as %->. congruence. }

      iSplitR "HΦ". { iFrameSteps 2. }
      iIntros "!> {%}".

      wp۰pures.
      destruct closing; iSteps.
  Qed.
  Lemma rcfd٠close𑁒spec t owned fd Ψ :
    {{{
      rcfd۰inv t owned fd Ψ ∗
      ( if owned then
          rcfd۰owner t
        else
          True
      ) ∗
      ( Ψ 1%Qp -∗
          ∃ chars,
          unix۰fd_model fd (DfracOwn 1) chars
      )
    }}}
      rcfd٠close t
    {{{
      b
    , RET #b;
      rcfd۰closing t ∗
      if owned then
        ⌜b = true⌝
      else
        True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & Howner & H) HΦ".

    wp۰apply (rcfd٠close𑁒spec𑁒aux false with "[$]").
    iSteps.
  Qed.
  Lemma rcfd٠close𑁒spec𑁒closing t fd Ψ :
    {{{
      rcfd۰inv t false fd Ψ ∗
      rcfd۰closing t
    }}}
      rcfd٠close t
    {{{
      RET false;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hclosing) HΦ".

    wp۰apply (rcfd٠close𑁒spec𑁒aux true with "[$]").
    iSteps.
  Qed.

  #[local] Lemma rcfd٠remove𑁒spec𑁒aux closing t owned fd Ψ :
    {{{
      rcfd۰inv t owned fd Ψ ∗
      ( if owned then
          rcfd۰owner t
        else
          True
      ) ∗
      ( if closing then
          rcfd۰closing t
        else
          True
      )
    }}}
      rcfd٠remove t
    {{{
      o
    , RET o;
      rcfd۰closing t ∗
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
    iDestruct (rcfd۰owner𑁒elim' with "Hmeta Howner") as "Howner".
    iDestruct (rcfd۰closing𑁒elim' with "Hmeta Hclosing") as "Hclosing".

    wp۰rec. wp۰pures.

    wp۰bind (_.{state})%E.
    iInv "Hinv" as "(:inv۰inner =1)".
    wp۰load.
    destruct_decide (lstate1 = LOpen) as -> | Hlstate1.

    - iDestruct "Hlstate" as "(:inv۰lstate۰open =1)".

      destruct closing.
      { iDestruct (lstate𑁒valid𑁒closing𑁒users with "Hlstate_auth Hclosing") as %?. congruence. }

      iSplitR "Howner HΦ". { iFrameSteps 2. }
      iIntros "!> {%}".

      wp۰apply+ (spsc_waiter٠create𑁒spec (Ψ 1%Qp) with "[//]") as "%waiter (#Hwaiter_inv & Hwaiter_producer & Hwaiter_consumer)".
      wp۰pures.

      wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
      iInv "Hinv" as "(:inv۰inner =2)".
      wp۰cas as Hcas.

      + iDestruct (inv۰lstate𑁒Closing with "Hlstate Hlstate_auth") as "(%fn2 & -> & %Hlstate2 & #Hlstate_lb)".
        { intros ->. zoo_simplify in Hcas. naive_solver. }

        destruct γ.(metadata۰owned).
        { iDestruct (owner𑁒lstate۰auth with "Howner Hlstate_auth") as %->. congruence. }

        iSplitR "HΦ". { iFrameSteps 2. }
        iIntros "!> {%}".

        wp۰pures.
        iApply ("HΦ" $! None).
        iSteps.

      + destruct state2; last zoo_simplify.
        iDestruct (inv۰lstate𑁒Open with "Hlstate") as %->.
        iDestruct "Hlstate" as "(:inv۰lstate۰open =2 eq)".

        iMod (lstate𑁒update𑁒close𑁒users with "Hlstate_auth Howner") as "Hlstate_auth".
        iDestruct (lstate۰lb𑁒get with "Hlstate_auth") as "#Hlstate_lb".
        iSplitR "Hwaiter_consumer HΦ".
        { destruct_decide (ops2 = 0) as -> | ?.
          - iDestruct (tokens۰auth𑁒consume with "Htokens_auth") as "HΨ".
            iMod (lstate𑁒update𑁒close𑁒no_users with "Hlstate_auth") as "Hlstate_auth".
            iExists (Closing _). iFrameStep 8.
            wp۰apply (spsc_waiter٠notify𑁒spec with "[$Hwaiter_inv $Hwaiter_producer $HΨ]").
            iSteps.
          - iDestruct (tokens۰auth𑁒valid with "Htokens_auth") as %?.
            iExists (Closing _). iFrame. iSteps as "HΨ".
            wp۰apply (spsc_waiter٠notify𑁒spec with "[$Hwaiter_inv $Hwaiter_producer $HΨ]").
            iSteps.
        }
        iIntros "!> {%}".

        wp۰apply+ (spsc_waiter٠wait𑁒spec with "[$Hwaiter_inv $Hwaiter_consumer]") as "HΨ".
        wp۰pures.
        iApply ("HΦ" $! (Some _)).
        destruct γ.(metadata۰owned); iSteps.

    - iDestruct (inv۰lstate𑁒LClosing with "Hlstate Hlstate_auth") as "(%fn1 & -> & #Hlstate_lb)"; first done.

      destruct γ.(metadata۰owned).
      { iDestruct (owner𑁒lstate۰auth with "Howner Hlstate_auth") as %->. congruence. }

      iSplitR "HΦ". { iFrameSteps 2. }
      iIntros "!> {%}".

      wp۰pures.
      iApply ("HΦ" $! None).
      destruct closing; iSteps.
  Qed.
  Lemma rcfd٠remove𑁒spec t owned fd Ψ :
    {{{
      rcfd۰inv t owned fd Ψ ∗
      if owned then
        rcfd۰owner t
      else
        True
    }}}
      rcfd٠remove t
    {{{
      o
    , RET o;
      rcfd۰closing t ∗
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

    wp۰apply (rcfd٠remove𑁒spec𑁒aux false with "[$]").
    iSteps.
  Qed.
  Lemma rcfd٠remove𑁒spec𑁒closing t fd Ψ :
    {{{
      rcfd۰inv t false fd Ψ ∗
      rcfd۰closing t
    }}}
      rcfd٠remove t
    {{{
      RET §None;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hclosing) HΦ".

    wp۰apply (rcfd٠remove𑁒spec𑁒aux true with "[$]").
    iSteps.
  Qed.

  #[local] Lemma rcfd٠is_open𑁒spec𑁒aux spec t owned fd Ψ :
    {{{
      rcfd۰inv t owned fd Ψ ∗
      specification۰pre₁ t spec
    }}}
      rcfd٠is_open t
    {{{
      b
    , RET #b;
      match spec with
      | SpecOwner =>
          ⌜b = true⌝ ∗
          rcfd۰owner t
      | SpecClosing =>
          ⌜b = false⌝
      | SpecNormal =>
          if b then
            True
          else
            rcfd۰closing t
      end
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & Hspec) HΦ".
    iDestruct (specification𑁒pre₁𑁒pre₂ with "Hmeta Hspec") as "Hspec".

    wp۰rec. wp۰pures.

    wp۰bind (_.{state})%E.
    iInv "Hinv" as "(:inv۰inner)".
    wp۰load.
    destruct state as [| fn].

    - iDestruct (inv۰lstate𑁒Open with "Hlstate") as %->.

      destruct_decide (spec = SpecClosing) as -> | Hspec.
      { iDestruct (lstate𑁒valid𑁒closing𑁒users with "Hlstate_auth Hspec") as %?. congruence. }

      iSplitR "Hspec HΦ". { iFrameSteps 2. }
      iIntros "!> {%- Hspec}".

      wp۰pures.
      destruct spec; try congruence; iSteps.

    - iDestruct (inv۰lstate𑁒Closing with "Hlstate Hlstate_auth") as "#(%fn_ & _ & %Hlstate & #Hlstate_lb)"; first done.

      destruct_decide (spec = SpecOwner) as -> | Hspec.
      { iDestruct (owner𑁒lstate۰auth with "Hspec Hlstate_auth") as %->. congruence. }

      iSplitR "HΦ". { iFrameSteps 2. }
      iIntros "!> {%- Hspec}".

      wp۰pures.
      destruct spec; try congruence; iSteps.
  Qed.
  Lemma rcfd٠is_open𑁒spec t owned fd Ψ :
    {{{
      rcfd۰inv t owned fd Ψ
    }}}
      rcfd٠is_open t
    {{{
      b
    , RET #b;
      if b then
        True
      else
        rcfd۰closing t
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".

    wp۰apply (rcfd٠is_open𑁒spec𑁒aux SpecNormal with "[$]").
    iSteps.
  Qed.
  Lemma rcfd٠is_open𑁒spec𑁒owner t owned fd Ψ :
    {{{
      rcfd۰inv t owned fd Ψ ∗
      rcfd۰owner t
    }}}
      rcfd٠is_open t
    {{{
      RET true;
      rcfd۰owner t
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & Howner) HΦ".

    wp۰apply (rcfd٠is_open𑁒spec𑁒aux SpecOwner with "[$]").
    iSteps.
  Qed.
  Lemma rcfd٠is_open𑁒spec𑁒closing t owned fd Ψ :
    {{{
      rcfd۰inv t false fd Ψ ∗
      rcfd۰closing t
    }}}
      rcfd٠is_open t
    {{{
      RET false;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hclosing) HΦ".

    wp۰apply (rcfd٠is_open𑁒spec𑁒aux SpecClosing with "[$]").
    iSteps.
  Qed.

  #[local] Lemma rcfd٠peek𑁒spec𑁒aux spec t owned fd Ψ :
    {{{
      rcfd۰inv t owned fd Ψ ∗
      specification۰pre₁ t spec
    }}}
      rcfd٠peek t
    {{{
      o
    , RET o;
      match spec with
      | SpecOwner =>
          ⌜o = Some fd⌝ ∗
          rcfd۰owner t
      | SpecClosing =>
          ⌜o = None⌝
      | SpecNormal =>
          match o with
          | None =>
              rcfd۰closing t
          | Some fd_ =>
              ⌜fd_ = fd⌝
          end
      end
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & Hspec) HΦ".
    iDestruct (specification𑁒pre₁𑁒pre₂ with "Hmeta Hspec") as "Hspec".

    wp۰rec. wp۰pures.

    wp۰bind (_.{state})%E.
    iInv "Hinv" as "(:inv۰inner)".
    wp۰load.
    destruct state as [| fn].

    - iDestruct (inv۰lstate𑁒Open with "Hlstate") as %->.

      destruct_decide (spec = SpecClosing) as -> | Hspec.
      { iDestruct (lstate𑁒valid𑁒closing𑁒users with "Hlstate_auth Hspec") as %?. congruence. }

      iSplitR "Hspec HΦ". { iFrameSteps 2. }
      iIntros "!> {%- Hspec}".

      wp۰pures.
      iApply ("HΦ" $! (Some _)).
      destruct spec; try congruence; iSteps.

    - iDestruct (inv۰lstate𑁒Closing with "Hlstate Hlstate_auth") as "#(%fn_ & _ & %Hlstate & #Hlstate_lb)"; first done.

      destruct_decide (spec = SpecOwner) as -> | Hspec.
      { iDestruct (owner𑁒lstate۰auth with "Hspec Hlstate_auth") as %->. congruence. }

      iSplitR "HΦ". { iFrameSteps 2. }
      iIntros "!> {%- Hspec}".

      wp۰pures.
      iApply ("HΦ" $! None).
      destruct spec; try congruence; iSteps.
  Qed.
  Lemma rcfd٠peek𑁒spec t owned fd Ψ :
    {{{
      rcfd۰inv t owned fd Ψ
    }}}
      rcfd٠peek t
    {{{
      o
    , RET o;
      match o with
      | None =>
          rcfd۰closing t
      | Some fd_ =>
          ⌜fd_ = fd⌝
      end
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".

    wp۰apply (rcfd٠peek𑁒spec𑁒aux SpecNormal with "[$]").
    iSteps.
  Qed.
  Lemma rcfd٠peek𑁒spec𑁒owner t owned fd Ψ :
    {{{
      rcfd۰inv t owned fd Ψ ∗
      rcfd۰owner t
    }}}
      rcfd٠peek t
    {{{
      RET Some fd;
      rcfd۰owner t
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & Howner) HΦ".

    wp۰apply (rcfd٠peek𑁒spec𑁒aux SpecOwner with "[$]").
    iSteps.
  Qed.
  Lemma rcfd٠peek𑁒spec𑁒closing t owned fd Ψ :
    {{{
      rcfd۰inv t owned fd Ψ ∗
      rcfd۰closing t
    }}}
      rcfd٠peek t
    {{{
      RET §None;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hclosing) HΦ".

    wp۰apply (rcfd٠peek𑁒spec𑁒aux SpecClosing with "[$]").
    iSteps.
  Qed.
End rcfd۰G.

Require zoo_eio.rcfd__opaque.

#[global] Opaque rcfd۰inv.
#[global] Opaque rcfd۰owner.
#[global] Opaque rcfd۰closing.
