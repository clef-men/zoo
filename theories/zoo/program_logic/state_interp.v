From iris.base_logic Require Import
  lib.invariants.

From zoo Require Import
  prelude.
From zoo.iris Require Import
  diaframe.
From zoo.language Require Import
  notations.
From zoo.program_logic Require Export
  ghost_state.
From zoo Require Import
  options.

Implicit Types cnt ns nt : nat.
Implicit Type pid : prophet_id.
Implicit Types tid : thread_id.
Implicit Types l : location.
Implicit Types v : val.
Implicit Types vs : list val.
Implicit Types hdr : header.
Implicit Types hdrs : gmap location header.
Implicit Types σ : state.
Implicit Type proph : val * val.
Implicit Type prophs : list (val * val).
Implicit Type prophets : gmap prophet_id (list (val * val)).
Implicit Types κ κs : list observation.

Record state_wf σ v :=
  { state_wf_locals :
      σ.(state_locals) = [v]
  ; state_wf_counter :
      σ.(state_heap) !! zoo_counter = Some 0%V
  }.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition state_interp ns nt σ κs : iProp Σ :=
    headers_auth σ.(state_headers) ∗
    heap_auth σ.(state_heap) ∗
    prophets_auth κs σ.(state_prophets) ∗
    steps_auth ns ∗
    locals_auth σ.(state_locals) ∗
    ⌜length σ.(state_locals) = nt⌝ ∗
    zoo_counter_inv.

  Definition fork_post (_ : val) : iProp Σ :=
    True.
End zoo_G.

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

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Lemma state_interp_mono ns nt σ κs :
    state_interp ns nt σ κs ⊢ |==>
    state_interp ˖ns nt σ κs.
  Proof.
    iIntros "(:state_interp)".
    iMod (steps_update with "Hsteps_auth") as "Hsteps_auth".
    iFrameSteps.
  Qed.

  Lemma state_interp_counter_inv ns nt σ κs :
    state_interp ns nt σ κs ⊢
    zoo_counter_inv.
  Proof.
    iSteps.
  Qed.
End zoo_G.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  #[local] Lemma big_sepM_chunk {A} (Φ : location → A → iProp Σ) l xs :
    ([∗ map] l ↦ x ∈ chunk l xs, Φ l x) ⊢
    [∗ list] i ↦ x ∈ xs, Φ (l +ₗ i) x.
  Proof.
    iInduction xs as [| x xs] "IH" forall (l) => /=. 1: iSteps.
    iIntros "H".
    rewrite big_sepM_insert.
    { clear.
      apply eq_None_ne_Some. intros x (k & Hk & Hl & _)%chunk_lookup.
      rewrite -{1}(location_add_0 l) in Hl.
      naive_solver lia.
    }
    iEval (rewrite location_add_0).
    iSteps.
    iEval (setoid_rewrite Nat2Z.inj_succ).
    iEval (setoid_rewrite <- Z.add_1_l).
    iEval (setoid_rewrite <- location_add_assoc).
    iSteps.
  Qed.

  Lemma state_interp_alloc {ns nt σ κs} l tag vs :
    σ.(state_headers) !! l = None →
    ( ∀ i,
      i < length vs →
      σ.(state_heap) !! (l +ₗ i) = None
    ) →
    state_interp ns nt σ κs ⊢ |==>
      let hdr := Header tag (length vs) in
      state_interp ns nt (state_alloc l hdr vs σ) κs ∗
      l ↦ₕ hdr ∗
      meta_token l ⊤ ∗
      l ↦∗ vs.
  Proof.
    iIntros "%Hheaders_lookup %Hheap_lookup (:state_interp)".
    iMod (headers_insert with "Hheaders_auth") as "($ & Hl_header & $)". 1: done.
    iMod (heap_insert (chunk _ _) with "Hheap_auth") as "($ & Hl)".
    { apply chunk_map_disjoint => //. }
    rewrite big_sepM_chunk. iSteps.
  Qed.

  Lemma state_interp_headers_at_valid ns nt σ κs l hdr :
    state_interp ns nt σ κs -∗
    l ↦ₕ hdr -∗
    ⌜σ.(state_headers) !! l = Some hdr⌝.
  Proof.
    iIntros "(:state_interp) Hl_header".
    iApply (headers_lookup with "Hheaders_auth Hl_header").
  Qed.

  Lemma state_interp_pointsto_valid ns nt σ κs l dq v :
    state_interp ns nt σ κs -∗
    l ↦{dq} v -∗
    ⌜σ.(state_heap) !! l = Some v⌝.
  Proof.
    iIntros "(:state_interp) Hl".
    iApply (heap_lookup with "Hheap_auth Hl").
  Qed.
  Lemma state_interp_pointstos_valid ns nt σ κs l dq vs :
    state_interp ns nt σ κs -∗
    l ↦∗{dq} vs -∗
    ⌜ ∀ (i : nat) v,
      vs !! i = Some v →
      σ.(state_heap) !! (l +ₗ i) = Some v
    ⌝.
  Proof.
    iIntros "(:state_interp) Hl %i %v %Hvs_lookup".
    iDestruct (big_sepL_lookup with "Hl") as "Hl"; first done.
    iApply (heap_lookup with "Hheap_auth Hl").
  Qed.
  Lemma state_interp_pointsto_update {ns nt σ κs l w} v :
    state_interp ns nt σ κs -∗
    l ↦ w ==∗
      state_interp ns nt (state_set_location l v σ) κs ∗
      l ↦ v.
  Proof.
    iIntros "(:state_interp) Hl".
    iMod (heap_update with "Hheap_auth Hl") as "(Hheap_auth & Hl)".
    iFrameSteps.
  Qed.

  Lemma state_interp_steps_lb_get ns nt σ κs :
    state_interp ns nt σ κs ⊢
    ⧖ ns.
  Proof.
    iIntros "(:state_interp)".
    iApply (steps_lb_get with "Hsteps_auth").
  Qed.
  Lemma state_interp_steps_lb_valid ns1 nt σ κs ns2 :
    state_interp ns1 nt σ κs -∗
    ⧖ ns2 -∗
    ⌜ns2 ≤ ns1⌝.
  Proof.
    iIntros "(:state_interp) Hsteps_lb".
    iApply (steps_lb_valid with "Hsteps_auth Hsteps_lb").
  Qed.

  Lemma state_interp_local_pointsto_valid ns nt σ κs tid dq v :
    state_interp ns nt σ κs -∗
    tid ↦ₗ{dq} v -∗
    ⌜σ.(state_locals) !! tid = Some v⌝.
  Proof.
    iIntros "(:state_interp) Htid".
    iApply (locals_lookup with "Hlocals_auth Htid").
  Qed.
  Lemma state_interp_fork {ns nt σ κs} v :
    state_interp ns nt σ κs ⊢ |==>
      state_interp ns (nt + 1) (state_add_local v σ) κs ∗
      nt ↦ₗ v.
  Proof.
    iIntros "(:state_interp)".
    iMod (locals_update_push with "Hlocals_auth") as "(Hlocals_auth & Hlocals)".
    rewrite Hlocals. iFrameSteps. iPureIntro.
    simpl_length/=. lia.
  Qed.
  Lemma state_interp_local_pointsto_update {ns nt σ κs tid w} v :
    state_interp ns nt σ κs -∗
    tid ↦ₗ w ==∗
      state_interp ns nt (state_set_local tid v σ) κs ∗
      tid ↦ₗ v.
  Proof.
    iIntros "(:state_interp) Htid".
    iMod (locals_update_pointsto with "Hlocals_auth Htid") as "(Hlocals_auth & Htid)".
    iFrameSteps. simpl_length.
  Qed.

  Lemma state_interp_prophet_new {ns nt σ κs} pid :
    pid ∉ σ.(state_prophets) →
    state_interp ns nt σ κs ⊢ |==>
      ∃ prophs,
      state_interp ns nt (state_add_prophet pid σ) κs ∗
      prophet_model pid prophs.
  Proof.
    iIntros "%Hpid (:state_interp)".
    iMod (prophets_new with "Hprophets_auth") as "(%prophs & Hprophets_auth & Hpid)". 1: done.
    iFrameSteps.
  Qed.
  Lemma state_interp_prophet_resolve ns nt σ κs pid proph prophs :
    state_interp ns nt σ ((pid, proph) :: κs) -∗
    prophet_model pid prophs ==∗
      ∃ prophs',
      ⌜prophs = proph :: prophs'⌝ ∗
      state_interp ns nt σ κs ∗
      prophet_model pid prophs'.
  Proof.
    iIntros "(:state_interp) Hpid".
    iMod (prophets_resolve with "Hprophets_auth Hpid") as "(%prophs' & -> & Hprophets_auth & Hpid)".
    iFrameSteps.
  Qed.
End zoo_G.

Definition state_heap_initial σ :=
  delete zoo_counter σ.(state_heap).

Lemma state_interp_init `{zoo_Gpre : !ZooGpre Σ} `{inv_G : !invGS Σ} σ v κs :
  state_wf σ v →
  ⊢ |={⊤}=>
    ∃ zoo_G : ZooG Σ,
    ⌜zoo_G.(zoo_G_inv_G) = inv_G⌝ ∗
    state_interp 0 1 σ κs ∗
    ([∗ map] l ↦ v ∈ state_heap_initial σ, l ↦ v) ∗
    0 ↦ₗ v.
Proof.
  intros Hwf.
  iMod (zoo_init σ.(state_headers) σ.(state_heap) σ.(state_prophets) σ.(state_locals) κs) as "(%zoo_G & $ & $ & $ & $ & $ & $ & $ & $ & Hlocals)".
  { apply Hwf. }
  iEval (rewrite (state_wf_locals _ v) //) in "Hlocals" |- *.
  iDestruct "Hlocals" as "($ & _)" => //.
Qed.

#[global] Opaque state_interp.
