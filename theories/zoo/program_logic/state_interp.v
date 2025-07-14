From iris.bi Require Export
  lib.fractional.
From iris.base_logic Require Import
  lib.gen_heap
  lib.invariants.

From zoo Require Import
  prelude.
From zoo.iris.bi Require Import
  big_op.
From zoo.iris.base_logic Require Import
  lib.ghost_list
  lib.prophet_map
  lib.mono_list.
From zoo.iris.program_logic Require Export
  wp.
From zoo.iris Require Import
  diaframe.
From zoo.language Require Export
  language.
From zoo.language Require Import
  notations.
From zoo Require Import
  options.

Implicit Types cnt : nat.
Implicit Types tid : thread_id.
Implicit Types l : location.
Implicit Types hdr : header.
Implicit Types σ : state.
Implicit Types κ : list observation.

Parameter zoo_counter : location.

Class ZooGpre Σ := {
  #[global] zoo_Gpre_inv_Gpre :: invGpreS Σ ;
  #[local] zoo_Gpre_headers_G :: gen_heapGpreS location header Σ ;
  #[local] zoo_Gpre_heap_Gpre :: gen_heapGpreS location val Σ ;
  #[local] zoo_Gpre_locals_G :: GhostListG Σ val ;
  #[local] zoo_Gpre_prophecy_Gpre :: ProphetMapGpre Σ prophet_id (val * val) ;
  #[local] zoo_Gpre_counter_G :: MonoListG Σ val ;
}.

Definition zoo_Σ := #[
  invΣ ;
  gen_heapΣ location header ;
  gen_heapΣ location val ;
  ghost_list_Σ val ;
  prophet_map_Σ prophet_id (val * val) ;
  mono_list_Σ val
].
#[global] Instance subG_zoo_Σ Σ :
  subG zoo_Σ Σ →
  ZooGpre Σ.
Proof.
  solve_inG.
Qed.

Class ZooG Σ := {
  zoo_G_inv_G : invGS Σ ;
  #[local] zoo_G_headers_G :: gen_heapGS location header Σ ;
  #[local] zoo_G_heap_G :: gen_heapGS location val Σ ;
  #[local] zoo_G_locals_G :: GhostListG Σ val ;
  zoo_G_locals_name : gname ;
  #[local] zoo_G_prophecy_map_G :: ProphetMapG Σ prophet_id (val * val) ;
  #[local] zoo_G_counter_G :: MonoListG Σ val ;
  zoo_G_counter_name : gname ;
}.
#[global] Arguments Build_ZooG _ {_ _ _ _} _ {_ _} _ : assert.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition has_header l hdr :=
    pointsto l DfracDiscarded hdr.

  Definition meta_token :=
    meta_token (V := header).

  Definition meta :=
    @meta location _ _ header _ _.
  #[global] Arguments meta {_ _ _} _ _ _ : assert.

  Definition pointsto :=
    pointsto (V := val).

  Definition thread_pointsto tid :=
    ghost_list_at zoo_G_locals_name tid.

  Definition prophet_model :=
    prophet_model.
  Definition prophet_model' pid :=
    prophet_model pid (DfracOwn 1).

  Definition zoo_counter_name :=
    zoo_G_counter_name.
  Definition zoo_counter_inv_inner : iProp Σ :=
    ∃ cnt vs,
    pointsto zoo_counter.[contents] (DfracOwn 1) #cnt ∗
    mono_list_auth zoo_counter_name (DfracOwn 1) vs ∗
    ⌜length vs = cnt⌝.
  Definition zoo_counter_inv : iProp Σ :=
    @inv _ _ zoo_G_inv_G nroot zoo_counter_inv_inner.

  Definition zoo_state_interp nt σ κ : iProp Σ :=
    gen_heap_interp σ.(state_headers) ∗
    gen_heap_interp σ.(state_heap) ∗
    ghost_list_auth zoo_G_locals_name σ.(state_locals) ∗
    ⌜length σ.(state_locals) = nt⌝ ∗
    prophet_map_interp κ σ.(state_prophets) ∗
    zoo_counter_inv.

  #[global] Instance zoo_G_iris_G : IrisG zoo Σ := {
    iris_G_inv_G :=
      zoo_G_inv_G ;
    state_interp :=
      zoo_state_interp ;
    fork_post _ :=
      True%I ;
  }.

  Lemma state_interp_counter_inv nt σ κs :
    state_interp nt σ κs ⊢
    inv nroot zoo_counter_inv_inner.
  Proof.
    iSteps.
  Qed.
End zoo_G.

Notation "l ↦ₕ hdr" := (
  has_header l hdr
)(at level 20,
  format "l  ↦ₕ  hdr"
) : bi_scope.

Notation "l ↦ dq v" := (
  pointsto l dq v%V
)(at level 20,
  dq custom dfrac at level 1,
  format "l  ↦ dq  v"
) : bi_scope.
Notation "l ↦-" := (
  (∃ v, l ↦ v)%I
)(at level 20,
  format "l  ↦-"
) : bi_scope.

Notation "l ↦∗ dq vs" :=
  ([∗ list] i ↦ v ∈ vs, (l +ₗ i) ↦{dq} v)%I
( at level 20,
  dq custom dfrac at level 1,
  format "l  ↦∗ dq  vs"
) : bi_scope.
Notation "l ↦∗-" :=
  (∃ vs, l ↦∗ vs)%I
( at level 20,
  format "l  ↦∗-"
) : bi_scope.

Notation "l ↦ᵣ dq v" := (
  pointsto (location_add l (Z.of_nat (in_type "__ref__" 0))) dq v%V
)(at level 20,
  dq custom dfrac at level 1,
  format "l  ↦ᵣ dq  v"
) : bi_scope.
Notation "l ↦ᵣ-" := (
  (∃ v, l ↦ᵣ v)%I
)(at level 20,
  format "l  ↦ᵣ-"
) : bi_scope.

Notation "tid ↦ₗ dq v" := (
  thread_pointsto tid dq v%V
)(at level 20,
  dq custom dfrac at level 1,
  format "tid  ↦ₗ dq  v"
) : bi_scope.
Notation "tid ↦ₗ-" := (
  (∃ v, tid ↦ₗ v)%I
)(at level 20,
  format "tid  ↦ₗ-"
) : bi_scope.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  #[global] Instance has_header_timeless l hdr :
    Timeless (l ↦ₕ hdr).
  Proof.
    apply _.
  Qed.
  #[global] Instance has_header_persistent l hdr :
    Persistent (l ↦ₕ hdr).
  Proof.
    apply _.
  Qed.

  Lemma has_header_agree l hdr1 hdr2 :
    l ↦ₕ hdr1 -∗
    l ↦ₕ hdr2 -∗
    ⌜hdr1 = hdr2⌝.
  Proof.
    apply pointsto_agree.
  Qed.

  #[global] Instance meta_token_timeless l N :
    Timeless (meta_token l N).
  Proof.
    apply _.
  Qed.
  #[global] Instance meta_timeless `{Countable A} l N (x : A) :
    Timeless (meta l N x).
  Proof.
    apply _.
  Qed.
  #[global] Instance meta_persistent `{Countable A} l N (x : A) :
    Persistent (meta l N x).
  Proof.
    apply _.
  Qed.

  Lemma meta_token_difference {l} E1 E2 :
    E1 ⊆ E2 →
    meta_token l E2 ⊣⊢
      meta_token l E1 ∗
      meta_token l (E2 ∖ E1).
  Proof.
    apply meta_token_difference.
  Qed.

  Lemma meta_set `{Countable A} {l E} (x : A) N :
    ↑ N ⊆ E →
    meta_token l E ⊢ |==>
    meta l N x.
  Proof.
    intros. apply bi.wand_entails', meta_set; done.
  Qed.
  Lemma meta_agree `{Countable A} l i (x1 x2 : A) :
    meta l i x1 -∗
    meta l i x2 -∗
    ⌜x1 = x2⌝.
  Proof.
    apply meta_agree.
  Qed.

  #[global] Instance pointsto_timeless l dq v :
    Timeless (l ↦{dq} v).
  Proof.
    apply _.
  Qed.
  #[global] Instance pointsto_persistent l v :
    Persistent (l ↦□ v).
  Proof.
    apply _.
  Qed.

  #[global] Instance pointsto_fractional l v :
    Fractional (λ q, l ↦{#q} v)%I.
  Proof.
    apply _.
  Qed.
  #[global] Instance pointsto_as_fractional l q v :
    AsFractional (l ↦{#q} v) (λ q, l ↦{#q} v)%I q.
  Proof.
    apply _.
  Qed.

  Lemma pointsto_valid l dq v :
    l ↦{dq} v ⊢
    ⌜✓ dq⌝.
  Proof.
    apply bi.wand_entails', pointsto_valid.
  Qed.
  Lemma pointsto_combine l dq1 v1 dq2 v2 :
    l ↦{dq1} v1 -∗
    l ↦{dq2} v2 -∗
      ⌜v1 = v2⌝ ∗
      l ↦{dq1 ⋅ dq2} v1.
  Proof.
    rewrite comm. apply pointsto_combine.
  Qed.
  Lemma pointsto_valid_2 l dq1 v1 dq2 v2 :
    l ↦{dq1} v1 -∗
    l ↦{dq2} v2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜v1 = v2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (pointsto_valid_2 with "H1 H2") as "$".
  Qed.
  Lemma pointsto_agree l dq2 v1 dq1 v2 :
    l ↦{dq1} v1 -∗
    l ↦{dq2} v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    apply pointsto_agree.
  Qed.
  Lemma pointsto_dfrac_ne l1 dq1 v1 l2 dq2 v2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    l1 ↦{dq1} v1 -∗
    l2 ↦{dq2} v2 -∗
    ⌜l1 ≠ l2⌝.
  Proof.
    apply pointsto_frac_ne.
  Qed.
  Lemma pointsto_ne l1 v1 l2 dq2 v2 :
    l1 ↦ v1 -∗
    l2 ↦{dq2} v2 -∗
    ⌜l1 ≠ l2⌝.
  Proof.
    apply pointsto_ne.
  Qed.
  Lemma pointsto_exclusive l v1 dq2 v2 :
    l ↦ v1 -∗
    l ↦{dq2} v2 -∗
    False.
  Proof.
    iIntros "H1 H2".
    iDestruct (pointsto_ne with "H1 H2") as %?. done.
  Qed.
  Lemma pointsto_persist l dq v :
    l ↦{dq} v ⊢ |==>
    l ↦□ v.
  Proof.
    apply bi.wand_entails', pointsto_persist.
  Qed.

  #[global] Instance pointsto_combine_sep_gives l dq1 v1 dq2 v2 :
    CombineSepGives (l ↦{dq1} v1) (l ↦{dq2} v2) ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝
  | 30.
  Proof.
    apply _.
  Qed.
  #[global] Instance pointsto_combine_as l dq1 dq2 v1 v2 :
    CombineSepAs (l ↦{dq1} v1) (l ↦{dq2} v2) (l ↦{dq1 ⋅ dq2} v1)
  | 60.
  Proof.
    apply _.
  Qed.
  #[global] Instance frame_pointsto p l v q1 q2 q :
    FrameFractionalQp q1 q2 q →
    Frame p (l ↦{#q1} v) (l ↦{#q2} v) (l ↦{#q} v)
  | 5.
  Proof.
    apply _.
  Qed.

  Lemma big_sepL2_pointsto_agree ls dq1 vs1 dq2 vs2 :
    ([∗ list] k ↦ l; v ∈ ls; vs1, l ↦{dq1} v) -∗
    ([∗ list] k ↦ l; v ∈ ls; vs2, l ↦{dq2} v) -∗
    ⌜vs1 = vs2⌝.
  Proof.
    iIntros "H1 H2".
    rewrite list_eq_Forall2.
    iApply big_sepL2_Forall2.
    iDestruct (big_sepL2_retract_l with "H1") as "(% & H1)".
    iDestruct (big_sepL2_retract_l with "H2") as "(% & H2)".
    iDestruct (big_sepL2_sepL_2 with "H1 H2") as "H"; first congruence.
    iApply (big_sepL2_impl with "H"). iIntros "!> %k %v1 %v2 _ _ ((%l1 & %Hl1_lookup & Hl1) & (%l2 & %Hl2_lookup & Hl2))". simplify.
    iApply (pointsto_agree with "Hl1 Hl2").
  Qed.
  Lemma big_sepL2_ref_pointsto_agree ls dq1 vs1 dq2 vs2 :
    ([∗ list] k ↦ l; v ∈ ls; vs1, l ↦ᵣ{dq1} v) -∗
    ([∗ list] k ↦ l; v ∈ ls; vs2, l ↦ᵣ{dq2} v) -∗
    ⌜vs1 = vs2⌝.
  Proof.
    setoid_rewrite location_add_0.
    apply big_sepL2_pointsto_agree.
  Qed.

  #[global] Instance thread_pointsto_timeless tid dq v :
    Timeless (tid ↦ₗ{dq} v).
  Proof.
    apply _.
  Qed.
  #[global] Instance thread_pointsto_persistent tid v :
    Persistent (tid ↦ₗ□ v).
  Proof.
    apply _.
  Qed.

  #[global] Instance thread_pointsto_fractional tid v :
    Fractional (λ q, tid ↦ₗ{#q} v)%I.
  Proof.
    apply _.
  Qed.
  #[global] Instance thread_pointsto_as_fractional tid q v :
    AsFractional (tid ↦ₗ{#q} v) (λ q, tid ↦ₗ{#q} v)%I q.
  Proof.
    apply _.
  Qed.

  #[global] Instance prophet_model_timeless pid dq prophs :
    Timeless (prophet_model pid dq prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_model_persistent pid prophs :
    Persistent (prophet_model pid DfracDiscarded prophs).
  Proof.
    apply _.
  Qed.

  Lemma thread_pointsto_valid tid dq v :
    tid ↦ₗ{dq} v ⊢
    ⌜✓ dq⌝.
  Proof.
    apply ghost_list_at_valid.
  Qed.
  Lemma thread_pointsto_combine tid dq1 v1 dq2 v2 :
    tid ↦ₗ{dq1} v1 -∗
    tid ↦ₗ{dq2} v2 -∗
      ⌜v1 = v2⌝ ∗
      tid ↦ₗ{dq1 ⋅ dq2} v1.
  Proof.
    apply ghost_list_at_combine.
  Qed.
  Lemma thread_pointsto_valid_2 tid dq1 v1 dq2 v2 :
    tid ↦ₗ{dq1} v1 -∗
    tid ↦ₗ{dq2} v2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜v1 = v2⌝.
  Proof.
    apply ghost_list_at_valid_2.
  Qed.
  Lemma thread_pointsto_agree tid dq2 v1 dq1 v2 :
    tid ↦ₗ{dq1} v1 -∗
    tid ↦ₗ{dq2} v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    apply ghost_list_at_agree.
  Qed.
  Lemma thread_pointsto_dfrac_ne tid1 dq1 v1 tid2 dq2 v2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    tid1 ↦ₗ{dq1} v1 -∗
    tid2 ↦ₗ{dq2} v2 -∗
    ⌜tid1 ≠ tid2⌝.
  Proof.
    iIntros "% H1 H2".
    iDestruct (ghost_list_at_dfrac_ne with "H1 H2") as %[]; done.
  Qed.
  Lemma thread_pointsto_ne tid1 v1 tid2 dq2 v2 :
    tid1 ↦ₗ v1 -∗
    tid2 ↦ₗ{dq2} v2 -∗
    ⌜tid1 ≠ tid2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_list_at_ne with "H1 H2") as %[]; done.
  Qed.
  Lemma thread_pointsto_exclusive tid v1 dq2 v2 :
    tid ↦ₗ v1 -∗
    tid ↦ₗ{dq2} v2 -∗
    False.
  Proof.
    apply ghost_list_at_exclusive.
  Qed.
  Lemma thread_pointsto_persist tid dq v :
    tid ↦ₗ{dq} v ⊢ |==>
    tid ↦ₗ□ v.
  Proof.
    apply ghost_list_at_persist.
  Qed.

  #[global] Instance prophet_model_fractional pid prophs :
    Fractional (λ q, prophet_model pid (DfracOwn q) prophs).
  Proof.
    apply _.
  Qed.
  #[global] Instance prophet_model_as_fractional pid q prophs :
    AsFractional (prophet_model pid (DfracOwn q) prophs) (λ q, prophet_model pid (DfracOwn q) prophs) q.
  Proof.
    apply _.
  Qed.

  Lemma prophet_model_valid pid dq prophs :
    prophet_model pid dq prophs ⊢
    ⌜✓ dq⌝.
  Proof.
    apply prophet_model_valid.
  Qed.
  Lemma prophet_model_combine pid dq1 prophs1 dq2 prophs2 :
    prophet_model pid dq1 prophs1 -∗
    prophet_model pid dq2 prophs2 -∗
      ⌜prophs1 = prophs2⌝ ∗
      prophet_model pid (dq1 ⋅ dq2) prophs1.
  Proof.
    apply prophet_model_combine.
  Qed.
  Lemma prophet_model_valid_2 pid dq1 prophs1 dq2 prophs2 :
    prophet_model pid dq1 prophs1 -∗
    prophet_model pid dq2 prophs2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜prophs1 = prophs2⌝.
  Proof.
    apply prophet_model_valid_2.
  Qed.
  Lemma prophet_model_agree pid dq1 prophs1 dq2 prophs2 :
    prophet_model pid dq1 prophs1 -∗
    prophet_model pid dq2 prophs2 -∗
    ⌜prophs1 = prophs2⌝.
  Proof.
    apply prophet_model_agree.
  Qed.
  Lemma prophet_model_dfrac_ne pid1 dq1 prophs1 pid2 dq2 prophs2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    prophet_model pid1 dq1 prophs1 -∗
    prophet_model pid2 dq2 prophs2 -∗
    ⌜pid1 ≠ pid2⌝.
  Proof.
    apply prophet_model_dfrac_ne.
  Qed.
  Lemma prophet_model_ne pid1 prophs1 pid2 dq2 prophs2 :
    prophet_model pid1 (DfracOwn 1) prophs1 -∗
    prophet_model pid2 dq2 prophs2 -∗
    ⌜pid1 ≠ pid2⌝.
  Proof.
    apply prophet_model_ne.
  Qed.
  Lemma prophet_model_exclusive pid prophs1 dq2 prophs2 :
    prophet_model pid (DfracOwn 1) prophs1 -∗
    prophet_model pid dq2 prophs2 -∗
    False.
  Proof.
    apply prophet_model_exclusive.
  Qed.
  Lemma prophet_model_persist pid dq prophs :
    prophet_model pid dq prophs ⊢ |==>
    prophet_model pid DfracDiscarded prophs.
  Proof.
    apply prophet_model_persist.
  Qed.

  #[local] Lemma big_sepM_heap_array (Φ : location → val → iProp Σ) l vs :
    ([∗ map] l' ↦ v ∈ heap_array l vs, Φ l' v) ⊢
    [∗ list] i ↦ v ∈ vs, Φ (l +ₗ i) v.
  Proof.
    iInduction vs as [| v vs] "IH" forall (l) => /=; first iSteps.
    iIntros "H".
    rewrite big_sepM_insert.
    { clear. apply eq_None_ne_Some. intros v (k & Hk & Hl & _)%heap_array_lookup.
      rewrite -{1}(location_add_0 l) in Hl. naive_solver lia.
    }
    rewrite location_add_0. iSteps.
    setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <- Z.add_1_l. setoid_rewrite <- location_add_assoc. iSteps.
  Qed.

  #[local] Instance : CustomIpatFormat "state_interp" :=
    "(
      Hheaders_interp &
      Hheap_interp &
      Hlocals_interp &
      %Hlocals &
      Hprophets_interp &
      Hcounter_inv
    )".
  Lemma state_interp_alloc {nt σ κ} l tag vs :
    σ.(state_headers) !! l = None →
    ( ∀ i,
      i < length vs →
      σ.(state_heap) !! (l +ₗ i) = None
    ) →
    state_interp nt σ κ ⊢ |==>
      let hdr := Header tag (length vs) in
      state_interp nt (state_alloc l hdr vs σ) κ ∗
      l ↦ₕ hdr ∗
      meta_token l ⊤ ∗
      l ↦∗ vs.
  Proof.
    iIntros "%Hheaders_lookup %Hheap_lookup (:state_interp)".
    iMod (gen_heap_alloc with "Hheaders_interp") as "($ & Hl_header & $)"; first done.
    iMod (gen_heap.pointsto_persist with "Hl_header") as "$".
    iMod (gen_heap_alloc_big _ (heap_array _ _) with "Hheap_interp") as "($ & Hl & _)".
    { apply heap_array_map_disjoint. done. }
    rewrite big_sepM_heap_array. iSteps.
  Qed.
  Lemma state_interp_has_header_valid nt σ κ l hdr :
    state_interp nt σ κ -∗
    l ↦ₕ hdr -∗
    ⌜σ.(state_headers) !! l = Some hdr⌝.
  Proof.
    iIntros "(:state_interp) Hl_header".
    iApply (gen_heap_valid with "Hheaders_interp Hl_header").
  Qed.
  Lemma state_interp_pointsto_valid nt σ κ l dq v :
    state_interp nt σ κ -∗
    l ↦{dq} v -∗
    ⌜σ.(state_heap) !! l = Some v⌝.
  Proof.
    iIntros "(:state_interp) Hl".
    iApply (gen_heap_valid with "Hheap_interp Hl").
  Qed.
  Lemma state_interp_pointstos_valid nt σ κ l dq vs :
    state_interp nt σ κ -∗
    l ↦∗{dq} vs -∗
    ⌜ ∀ (i : nat) v,
      vs !! i = Some v →
      σ.(state_heap) !! (l +ₗ i) = Some v
    ⌝.
  Proof.
    iIntros "(:state_interp) Hl %i %v %Hvs_lookup".
    iDestruct (big_sepL_lookup with "Hl") as "Hl"; first done.
    iApply (gen_heap_valid with "Hheap_interp Hl").
  Qed.
  Lemma state_interp_pointsto_update {nt σ κ l w} v :
    state_interp nt σ κ -∗
    l ↦ w ==∗
      state_interp nt (state_update_heap (insert l v) σ) κ ∗
      l ↦ v.
  Proof.
    iIntros "(:state_interp) Hl".
    iMod (gen_heap_update with "Hheap_interp Hl") as "(Hheap_interp & Hl)".
    iFrameSteps.
  Qed.
  Lemma state_interp_fork {nt σ κ} v :
    state_interp nt σ κ ⊢ |==>
      state_interp (nt + 1) (state_update_locals (.++ [v]) σ) κ ∗
      nt ↦ₗ v.
  Proof.
    iIntros "(:state_interp)".
    iMod (ghost_list_update_push with "Hlocals_interp") as "(Hlocals_interp & Hlocals)".
    rewrite Hlocals. iFrameSteps. iPureIntro.
    simpl_length/=. lia.
  Qed.
  Lemma state_interp_thread_pointsto_valid nt σ κ tid dq v :
    state_interp nt σ κ -∗
    tid ↦ₗ{dq} v -∗
    ⌜σ.(state_locals) !! tid = Some v⌝.
  Proof.
    iIntros "(:state_interp) Htid".
    iApply (ghost_list_lookup with "Hlocals_interp Htid").
  Qed.
  Lemma state_interp_thread_pointsto_update {nt σ κ tid w} v :
    state_interp nt σ κ -∗
    tid ↦ₗ w ==∗
      state_interp nt (state_update_locals (insert tid v) σ) κ ∗
      tid ↦ₗ v.
  Proof.
    iIntros "(:state_interp) Htid".
    iMod (ghost_list_update_at with "Hlocals_interp Htid") as "(Hlocals_interp & Htid)".
    iFrameSteps. simpl_length.
  Qed.
  Lemma state_interp_prophet_new {nt σ κ} pid :
    pid ∉ σ.(state_prophets) →
    state_interp nt σ κ ⊢ |==>
      ∃ prophs,
      state_interp nt (state_update_prophets ({[pid]} ∪.) σ) κ ∗
      prophet_model pid (DfracOwn 1) prophs.
  Proof.
    iIntros "%Hpid (:state_interp)".
    iMod (prophet_map_new with "Hprophets_interp") as "(Hprophets_interp & Hpid)"; first done.
    iFrameSteps.
  Qed.
  Lemma state_interp_prophet_resolve nt σ κ pid proph prophs :
    state_interp nt σ ((pid, proph) :: κ) -∗
    prophet_model pid (DfracOwn 1) prophs ==∗
      ∃ prophs',
      ⌜prophs = proph :: prophs'⌝ ∗
      state_interp nt σ κ ∗
      prophet_model pid (DfracOwn 1) prophs'.
  Proof.
    iIntros "(:state_interp) Hpid".
    iMod (prophet_map_resolve with "Hprophets_interp Hpid") as "(%prophs' & -> & Hprophets_interp & Hpid)".
    iFrameSteps.
  Qed.
End zoo_G.

Lemma zoo_init `{zoo_Gpre : !ZooGpre Σ} `{inv_G : !invGS Σ} nt σ cnt κ :
  length σ.(state_locals) = nt →
  σ.(state_heap) !! zoo_counter = Some #cnt →
  ⊢ |={⊤}=>
    ∃ zoo_G : ZooG Σ,
    ⌜zoo_G.(zoo_G_inv_G) = inv_G⌝ ∗
    state_interp nt σ κ ∗
    ( [∗ map] l ↦ v ∈ delete zoo_counter σ.(state_heap),
      l ↦ v
    ) ∗
    ( [∗ list] tid ↦ v ∈ σ.(state_locals),
      tid ↦ₗ v
    ).
Proof.
  intros Hlocals Hcounter.

  iMod (gen_heap_init σ.(state_headers)) as (?) "(Hheaders_interp & _)".

  iMod (gen_heap_init σ.(state_heap)) as (?) "(Hheap_interp & Hheap & _)".
  iDestruct (big_sepM_delete with "Hheap") as "(Hcounter & Hheap)"; first done.
  iEval (rewrite -(location_add_0 zoo_counter)) in "Hcounter".

  iMod (ghost_list_alloc σ.(state_locals)) as "(%γ_locals & Hlocals_interp & Hlocals)".

  iMod (prophet_map_init κ σ.(state_prophets)) as "(% & Hprophets_interp)".

  iMod (mono_list_alloc (replicate cnt inhabitant)) as "(%γ_counter & Hcounter_auth)".

  iExists (Build_ZooG Σ γ_locals γ_counter). iFrameSteps.
  iApply inv_alloc. iSteps. simpl_length.
Qed.
Lemma zoo_init' `{zoo_Gpre : !ZooGpre Σ} `{inv_G : !invGS Σ} σ v cnt κ :
  σ.(state_locals) = [v] →
  σ.(state_heap) !! zoo_counter = Some #cnt →
  ⊢ |={⊤}=>
    ∃ zoo_G : ZooG Σ,
    ⌜zoo_G.(zoo_G_inv_G) = inv_G⌝ ∗
    state_interp 1 σ κ ∗
    ( [∗ map] l ↦ v ∈ delete zoo_counter σ.(state_heap),
      l ↦ v
    ) ∗
    0 ↦ₗ v.
Proof.
  intros Hlocals Hcounter.
  iMod (zoo_init 1 σ cnt κ) as "(%zoo_G & $ & $ & Hlocals)".
  all: rewrite ?Hlocals //.
  iSteps.
Qed.

#[global] Opaque zoo_state_interp.
#[global] Opaque has_header.
#[global] Opaque meta_token.
#[global] Opaque meta.
#[global] Opaque pointsto.
#[global] Opaque thread_pointsto.
#[global] Opaque prophet_model.

Inductive ownership :=
  | Own
  | Discard.

Coercion ownership_to_dfrac own :=
  match own with
  | Own =>
      DfracOwn 1
  | Discard =>
      DfracDiscarded
  end.
