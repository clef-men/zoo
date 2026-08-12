Require Import iris.base_logic.lib.invariants.

Require Import zoo.prelude.
Require Import zoo.iris.diaframe.
Require Import zoo.language.notations.
Require Export zoo.program_logic.ghost_state.
Require Import zoo.options.

Implicit Type cnt ns nt : nat.
Implicit Type pid : prophet_id.
Implicit Type tid : thread_id.
Implicit Type l : location.
Implicit Type v : val.
Implicit Type vs : list val.
Implicit Type hdr : header.
Implicit Type hdrs : gmap location header.
Implicit Type σ : state.
Implicit Type proph : val * val.
Implicit Type prophs : list (val * val).
Implicit Type prophets : gmap prophet_id (list (val * val)).
Implicit Type κ κs : list observation.

Record state۰wf σ v :=
  { state۰wfｰlocals :
      σ.(state۰locals) = [v]
  ; state۰wfｰcounter :
      σ.(state۰heap) !! zoo_counter = Some 0%V
  }.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Definition state_interp ns nt σ κs : iProp Σ :=
    headers۰auth σ.(state۰headers) ∗
    heap۰auth σ.(state۰heap) ∗
    prophets۰auth κs σ.(state۰prophets) ∗
    steps۰auth ns ∗
    locals۰auth σ.(state۰locals) ∗
    ⌜length σ.(state۰locals) = nt⌝ ∗
    zoo_counter۰inv.

  Definition fork_post (_ : val) : iProp Σ :=
    True.
End zoo۰G.

#[local] Instance : CustomIpat "state_interp" :=
  " ( Hheaders_auth
    & Hheap_auth
    & Hprophets_auth
    & Hsteps_auth
    & Hlocals_auth
    & %Hlocals
    & Hcounter_inv
    )
  ".

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Lemma state_interpｰmono ns nt σ κs :
    state_interp ns nt σ κs ⊢ |==>
    state_interp ˖ns nt σ κs.
  Proof.
    iIntros "(:state_interp)".
    iMod (stepsｰupdate with "Hsteps_auth") as "Hsteps_auth".
    iFrameSteps.
  Qed.

  Lemma state_interpｰzoo_counter۰inv ns nt σ κs :
    state_interp ns nt σ κs ⊢
    zoo_counter۰inv.
  Proof.
    iSteps.
  Qed.
End zoo۰G.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  #[local] Lemma big_sepMｰchunk {A} (Φ : location → A → iProp Σ) l xs :
    ([∗ map] l ↦ x ∈ chunk l xs, Φ l x) ⊢
    [∗ list] i ↦ x ∈ xs, Φ (l +ₗ i) x.
  Proof.
    iInduction xs as [| x xs] "IH" forall (l) => /=. 1: iSteps.
    iIntros "H".
    rewrite big_sepM_insert.
    { clear.
      apply eq_None_ne_Some. intros x (k & Hk & Hl & _)%chunkｰlookup.
      rewrite -{1}(location۰addｰ0 l) in Hl.
      naive_solver lia.
    }
    iEval (rewrite location۰addｰ0).
    iSteps.
    iEval (setoid_rewrite Nat2Z.inj_succ).
    iEval (setoid_rewrite <- Z.add_1_l).
    iEval (setoid_rewrite <- location۰addｰassoc).
    iSteps.
  Qed.

  Lemma state_interpｰalloc {ns nt σ κs} l tag vs :
    σ.(state۰headers) !! l = None →
    ( ∀ i,
      i < length vs →
      σ.(state۰heap) !! (l +ₗ i) = None
    ) →
    state_interp ns nt σ κs ⊢ |==>
      let hdr := Header tag (length vs) in
      state_interp ns nt (state۰alloc l hdr vs σ) κs ∗
      l ↦ₕ hdr ∗
      meta_token l ⊤ ∗
      l ↦∗ vs.
  Proof.
    iIntros "%Hheadersｰlookup %Hheapｰlookup (:state_interp)".
    iMod (headersｰinsert with "Hheaders_auth") as "($ & Hl_header & $)". 1: done.
    iMod (heapｰinsert (chunk _ _) with "Hheap_auth") as "($ & Hl)".
    { apply chunkｰmapｰdisjoint => //. }
    rewrite big_sepMｰchunk. iSteps.
  Qed.

  Lemma state_interpｰheaders۰atｰvalid ns nt σ κs l hdr :
    state_interp ns nt σ κs -∗
    l ↦ₕ hdr -∗
    ⌜σ.(state۰headers) !! l = Some hdr⌝.
  Proof.
    iIntros "(:state_interp) Hl_header".
    iApply (headersｰlookup with "Hheaders_auth Hl_header").
  Qed.

  Lemma state_interpｰpointstoｰvalid ns nt σ κs l dq v :
    state_interp ns nt σ κs -∗
    l ↦{dq} v -∗
    ⌜σ.(state۰heap) !! l = Some v⌝.
  Proof.
    iIntros "(:state_interp) Hl".
    iApply (heapｰlookup with "Hheap_auth Hl").
  Qed.
  Lemma state_interpｰpointstosｰvalid ns nt σ κs l dq vs :
    state_interp ns nt σ κs -∗
    l ↦∗{dq} vs -∗
    ⌜ ∀ (i : nat) v,
      vs !! i = Some v →
      σ.(state۰heap) !! (l +ₗ i) = Some v
    ⌝.
  Proof.
    iIntros "(:state_interp) Hl %i %v %Hvs_lookup".
    iDestruct (big_sepL_lookup with "Hl") as "Hl"; first done.
    iApply (heapｰlookup with "Hheap_auth Hl").
  Qed.
  Lemma state_interpｰpointstoｰupdate {ns nt σ κs l w} v :
    state_interp ns nt σ κs -∗
    l ↦ w ==∗
      state_interp ns nt (state۰set_location l v σ) κs ∗
      l ↦ v.
  Proof.
    iIntros "(:state_interp) Hl".
    iMod (heapｰupdate with "Hheap_auth Hl") as "(Hheap_auth & Hl)".
    iFrameSteps.
  Qed.

  Lemma state_interpｰsteps۰lbｰget ns nt σ κs :
    state_interp ns nt σ κs ⊢
    ⧖ ns.
  Proof.
    iIntros "(:state_interp)".
    iApply (steps۰lbｰget with "Hsteps_auth").
  Qed.
  Lemma state_interpｰsteps۰lbｰvalid ns1 nt σ κs ns2 :
    state_interp ns1 nt σ κs -∗
    ⧖ ns2 -∗
    ⌜ns2 ≤ ns1⌝.
  Proof.
    iIntros "(:state_interp) Hsteps_lb".
    iApply (steps۰lbｰvalid with "Hsteps_auth Hsteps_lb").
  Qed.

  Lemma state_interpｰlocal_pointstoｰvalid ns nt σ κs tid dq v :
    state_interp ns nt σ κs -∗
    tid ↦ₗ{dq} v -∗
    ⌜σ.(state۰locals) !! tid = Some v⌝.
  Proof.
    iIntros "(:state_interp) Htid".
    iApply (localsｰlookup with "Hlocals_auth Htid").
  Qed.
  Lemma state_interpｰfork {ns nt σ κs} v :
    state_interp ns nt σ κs ⊢ |==>
      state_interp ns (nt + 1) (state۰add_local v σ) κs ∗
      nt ↦ₗ v.
  Proof.
    iIntros "(:state_interp)".
    iMod (localsｰupdateｰpush with "Hlocals_auth") as "(Hlocals_auth & Hlocals)".
    rewrite Hlocals. iFrameSteps. iPureIntro.
    simp_length/=. lia.
  Qed.
  Lemma state_interpｰlocal_pointstoｰupdate {ns nt σ κs tid w} v :
    state_interp ns nt σ κs -∗
    tid ↦ₗ w ==∗
      state_interp ns nt (state۰set_local tid v σ) κs ∗
      tid ↦ₗ v.
  Proof.
    iIntros "(:state_interp) Htid".
    iMod (localsｰupdateｰpointsto with "Hlocals_auth Htid") as "(Hlocals_auth & Htid)".
    iFrameSteps. simp_length.
  Qed.

  Lemma state_interpｰprophetｰnew {ns nt σ κs} pid :
    pid ∉ σ.(state۰prophets) →
    state_interp ns nt σ κs ⊢ |==>
      ∃ prophs,
      state_interp ns nt (state۰add_prophet pid σ) κs ∗
      prophet۰model pid prophs.
  Proof.
    iIntros "%Hpid (:state_interp)".
    iMod (prophetsｰnew with "Hprophets_auth") as "(%prophs & Hprophets_auth & Hpid)". 1: done.
    iFrameSteps.
  Qed.
  Lemma state_interpｰprophetｰresolve ns nt σ κs pid proph prophs :
    state_interp ns nt σ ((pid, proph) :: κs) -∗
    prophet۰model pid prophs ==∗
      ∃ prophs',
      ⌜prophs = proph :: prophs'⌝ ∗
      state_interp ns nt σ κs ∗
      prophet۰model pid prophs'.
  Proof.
    iIntros "(:state_interp) Hpid".
    iMod (prophetsｰresolve with "Hprophets_auth Hpid") as "(%prophs' & -> & Hprophets_auth & Hpid)".
    iFrameSteps.
  Qed.
End zoo۰G.

Definition state۰heap۰initial σ :=
  delete zoo_counter σ.(state۰heap).

Lemma state_interpｰinit `{zoo۰Gpre : !ZooGpre Σ} `{inv۰G : !invGS Σ} σ v κs :
  state۰wf σ v →
  ⊢ |={⊤}=>
    ∃ zoo۰G : ZooG Σ,
    ⌜zoo۰G.(zoo۰G۰inv۰G) = inv۰G⌝ ∗
    state_interp 0 1 σ κs ∗
    ([∗ map] l ↦ v ∈ state۰heap۰initial σ, l ↦ v) ∗
    0 ↦ₗ v.
Proof.
  intros Hwf.
  iMod (zooｰinit σ.(state۰headers) σ.(state۰heap) σ.(state۰prophets) σ.(state۰locals) κs) as "(%zoo۰G & $ & $ & $ & $ & $ & $ & $ & $ & Hlocals)".
  { apply Hwf. }
  iEval (rewrite (state۰wfｰlocals _ v) //) in "Hlocals" |- *.
  iDestruct "Hlocals" as "($ & _)" => //.
Qed.

#[global] Opaque state_interp.
