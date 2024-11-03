From iris.bi Require Import
  lib.fractional.
From iris.base_logic Require Import
  lib.gen_heap.

From zoo Require Import
  prelude.
From zoo.iris.base_logic Require Import
  lib.prophet_map.
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

Implicit Types hdr : header.
Implicit Types σ : state.
Implicit Types κ : list observation.

Class ZooGpre Σ := {
  #[global] zoo_Gpre_inv_Gpre :: invGpreS Σ ;
  #[local] zoo_Gpre_headers_G :: gen_heapGpreS location header Σ ;
  #[local] zoo_Gpre_heap_Gpre :: gen_heapGpreS location val Σ ;
  #[local] zoo_Gpre_prophecy_Gpre :: ProphetMapGpre Σ prophet_id (val * val) ;
}.

Definition zoo_Σ := #[
  invΣ ;
  gen_heapΣ location header ;
  gen_heapΣ location val ;
  prophet_map_Σ prophet_id (val * val)
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
  #[local] zoo_G_prophecy_map_G :: ProphetMapG Σ prophet_id (val * val) ;
}.
#[global] Arguments Build_ZooG _ {_ _ _ _} : assert.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition zoo_state_interp (_ : nat) σ κ : iProp Σ :=
    gen_heap_interp σ.(state_headers) ∗
    gen_heap_interp σ.(state_heap) ∗
    prophet_map_interp κ σ.(state_prophets).
  #[global] Instance zoo_G_iris_G : IrisG zoo Σ := {
    iris_G_inv_G :=
      zoo_G_inv_G ;
    state_interp :=
      zoo_state_interp ;
    fork_post _ :=
      True%I ;
  }.

  Definition has_header l hdr :=
    pointsto l DfracDiscarded hdr.

  Definition meta_token :=
    meta_token (V := header).

  Definition meta :=
    @meta location _ _ header _ _.
  #[global] Arguments meta {_ _ _} _ _ _ : assert.

  Definition pointsto :=
    pointsto (V := val).

  Definition prophet_model :=
    prophet_model.
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

Notation "l ↦∗ dq vs" :=
  ([∗ list] i ↦ v ∈ vs, (l +ₗ i) ↦{dq} v)%I
( at level 20,
  dq custom dfrac at level 1,
  format "l  ↦∗ dq  vs"
) : bi_scope.

Notation "l ↦ᵣ dq v" := (
  pointsto (location_add l (Z.of_nat (in_type "__ref__" 0))) dq v%V
)(at level 20,
  dq custom dfrac at level 1,
  format "l  ↦ᵣ dq  v"
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

  Lemma meta_token_difference l E1 E2 :
    E1 ⊆ E2 →
    meta_token l E2 ⊣⊢
      meta_token l E1 ∗
      meta_token l (E2 ∖ E1).
  Proof.
    apply meta_token_difference.
  Qed.

  Lemma meta_set `{Countable A} E l (x : A) N :
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
  #[global] Instance pointsto_persistent l v :
    Persistent (l ↦□ v).
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
    ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
  Proof.
    apply pointsto_valid_2.
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
  Lemma pointsto_exclusive l v1 v2 :
    l ↦ v1 -∗
    l ↦ v2 -∗
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

  #[global] Instance prophet_model_timeless pid prophs :
    Timeless (prophet_model pid prophs).
  Proof.
    apply _.
  Qed.

  Lemma prophet_model_exclusive pid prophs1 prophs2 :
    prophet_model pid prophs1 -∗
    prophet_model pid prophs2 -∗
    False.
  Proof.
    apply prophet_model_exclusive.
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
    iIntros "%Hheaders_lookup %Hheap_lookup (Hheaders & Hheap & $)".
    iMod (gen_heap_alloc with "Hheaders") as "($ & Hhdr & $)"; first done.
    iMod (gen_heap.pointsto_persist with "Hhdr") as "$".
    iMod (gen_heap_alloc_big _ (heap_array _ _) with "Hheap") as "($ & Hl & _)".
    { apply heap_array_map_disjoint. done. }
    rewrite big_sepM_heap_array. iSteps.
  Qed.
  Lemma state_interp_has_header_valid nt σ κ l hdr :
    state_interp nt σ κ -∗
    l ↦ₕ hdr -∗
    ⌜σ.(state_headers) !! l = Some hdr⌝.
  Proof.
    iIntros "(Hheaders & _ & _) Hhdr".
    iApply (gen_heap_valid with "Hheaders Hhdr").
  Qed.
  Lemma state_interp_pointsto_valid nt σ κ l dq v :
    state_interp nt σ κ -∗
    l ↦{dq} v -∗
    ⌜σ.(state_heap) !! l = Some v⌝.
  Proof.
    iIntros "(_ & Hheap & _) Hl".
    iApply (gen_heap_valid with "Hheap Hl").
  Qed.
  Lemma state_interp_pointstos_valid nt σ κ l dq vs :
    state_interp nt σ κ -∗
    l ↦∗{dq} vs -∗
    ⌜ ∀ (i : nat) v,
      vs !! i = Some v →
      σ.(state_heap) !! (l +ₗ i) = Some v
    ⌝.
  Proof.
    iIntros "(_ & Hheap & _) Hl %i %v %Hvs_lookup".
    iDestruct (big_sepL_lookup with "Hl") as "Hl"; first done.
    iApply (gen_heap_valid with "Hheap Hl").
  Qed.
  Lemma state_interp_pointsto_update {nt σ κ l w} v :
    state_interp nt σ κ -∗
    l ↦ w ==∗
      state_interp nt (state_update_heap (insert l v) σ) κ ∗
      l ↦ v.
  Proof.
    iIntros "($ & Hheap & $) Hl".
    iApply (gen_heap_update with "Hheap Hl").
  Qed.
  Lemma state_interp_prophet_new {nt σ κ} pid :
    pid ∉ σ.(state_prophets) →
    state_interp nt σ κ ⊢ |==>
      ∃ prophs,
      state_interp nt (state_update_prophets ({[pid]} ∪.) σ) κ ∗
      prophet_model pid prophs.
  Proof.
    iIntros "%Hpid ($ & $ & Hκ)".
    iMod (prophet_map_new with "Hκ") as "(Hκ & Hpid)"; first done.
    iSteps.
  Qed.
  Lemma state_interp_prophet_resolve nt σ κ pid proph prophs :
    state_interp nt σ ((pid, proph) :: κ) -∗
    prophet_model pid prophs ==∗
      ∃ prophs',
      ⌜prophs = proph :: prophs'⌝ ∗
      state_interp nt σ κ ∗
      prophet_model pid prophs'.
  Proof.
    iIntros "($ & $ & Hκ) Hpid".
    iMod (prophet_map_resolve with "Hκ Hpid") as "(%prophs' & -> & Hκ & Hpid)".
    iSteps.
  Qed.
End zoo_G.

Lemma zoo_init `{zoo_Gpre : !ZooGpre Σ} `{inv_G : !invGS Σ} nt σ κ :
  ⊢ |==>
    ∃ zoo_G : ZooG Σ,
    state_interp nt σ κ.
Proof.
  iMod (gen_heap_init σ.(state_headers)) as (?) "(Hheaders & _)".
  iMod (gen_heap_init σ.(state_heap)) as (?) "(Hσ & _)".
  iMod (prophet_map_init κ σ.(state_prophets)) as "(% & Hκ)".
  iExists (Build_ZooG Σ). iFrame. iSteps.
Qed.
Lemma zoo_init' `{zoo_Gpre : !ZooGpre Σ} `{inv_G : !invGS Σ} σ κ :
  ⊢ |==>
    ∃ zoo_G : ZooG Σ,
    state_interp 0 σ κ.
Proof.
  apply zoo_init.
Qed.

#[global] Opaque zoo_state_interp.
#[global] Opaque has_header.
#[global] Opaque meta_token.
#[global] Opaque meta.
#[global] Opaque pointsto.
#[global] Opaque prophet_model.
