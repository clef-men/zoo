Require Export iris.bi.lib.fractional.
Require Import iris.base_logic.lib.ghost_map.
Require Import iris.base_logic.lib.invariants.

Require Import zoo.prelude.
Require Import zoo.iris.bi.big_op.
Require Import zoo.iris.base_logic.lib.auth_nat_max.
Require Import zoo.iris.base_logic.lib.ghost_heap.
Require Import zoo.iris.base_logic.lib.ghost_list.
Require Import zoo.iris.base_logic.lib.mono_list.
Require Import zoo.iris.diaframe.
Require Export zoo.language.language.
Require Import zoo.language.notations.
Require Import zoo.options.

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

Parameter zoo_counter : location.

Class ZooG₀ Σ :=
  { #[local] zoo_G₀_headers_G :: GhostHeapG Σ location header
  ; #[local] zoo_G₀_heap_G :: ghost_mapG Σ location val
  ; #[local] zoo_G_prophets_G :: ghost_mapG Σ prophet_id (list (val * val))
  ; #[local] zoo_G₀_steps_G :: AuthNatMaxG Σ
  ; #[local] zoo_G₀_locals_G :: GhostListG Σ val
  ; #[local] zoo_G₀_counter_G :: MonoListG Σ val
  }.

#[local] Definition zoo_Σ₀ :=
  #[ghost_heap_Σ location header
  ; ghost_mapΣ location val
  ; ghost_mapΣ prophet_id (list (val * val))
  ; auth_nat_max_Σ
  ; ghost_list_Σ val
  ; mono_list_Σ val
  ].
#[local] Instance subG_zoo_Σ₀ Σ :
  subG zoo_Σ₀ Σ →
  ZooG₀ Σ.
Proof.
  solve_inG.
Qed.

Class ZooGpre Σ :=
  { #[global] zoo_Gpre_inv_Gpre :: invGpreS Σ
  ; #[local] zoo_Gpre_G₀ :: ZooG₀ Σ
  }.

Definition zoo_Σ :=
  #[invΣ
  ; zoo_Σ₀
  ].
#[global] Instance subG_zoo_Σ Σ :
  subG zoo_Σ Σ →
  ZooGpre Σ.
Proof.
  solve_inG.
Qed.

Class ZooG Σ :=
  { #[global] zoo_G_inv_G :: invGS Σ
  ; #[local] zoo_G_G₀ :: ZooG₀ Σ
  ; zoo_G_headers_name : ghost_heap_name
  ; zoo_G_heap_name : gname
  ; zoo_G_prophets_name : gname
  ; zoo_G_steps_name : gname
  ; zoo_G_locals_name : gname
  ; zoo_G_counter_name : gname
  }.
#[global] Arguments Build_ZooG {_ _ _} _ _ _ _ _ _ : assert.

Section zoo_G₀.
  Context `{zoo_G₀ : !ZooG₀ Σ}.

  #[local] Definition headers_auth' γ_headers hdrs :=
    ghost_heap_auth γ_headers hdrs.
  #[local] Definition headers_at' γ_headers l hdr :=
    ghost_heap_at γ_headers l DfracDiscarded hdr.

  #[local] Definition meta_token' γ_headers l E :=
    ghost_heap_meta_token γ_headers l E.
  #[local] Definition meta' `{Countable A} γ_headers l ι (x : A) :=
    ghost_heap_meta γ_headers l ι x.

  #[local] Lemma headers_alloc hdrs :
    ⊢ |==>
      ∃ γ_headers,
      headers_auth' γ_headers hdrs.
  Proof.
    iMod (ghost_heap_alloc hdrs) as "(%γ_headers & $ & _)" => //.
  Qed.
End zoo_G₀.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition headers_auth :=
    headers_auth' zoo_G_headers_name.
  Definition headers_at :=
    headers_at' zoo_G_headers_name.

  Definition meta_token :=
    meta_token' zoo_G_headers_name.
  Definition meta `{Countable A} :=
    meta' (A := A) zoo_G_headers_name.
End zoo_G.

Notation "l ↦ₕ hdr" := (
  headers_at l hdr
)(at level 20,
  format "l  ↦ₕ  hdr"
) : bi_scope.

Notation "l ↪[ ι ] x" := (
  meta l ι x
)(at level 20,
  format "l  ↪[ ι ]  x"
) : bi_scope.
Notation "l ↪ x" := (
  meta l nroot x
)(at level 20,
  format "l  ↪  x"
) : bi_scope.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  #[global] Instance headers_at_timeless l hdr :
    Timeless (l ↦ₕ hdr).
  Proof.
    apply _.
  Qed.

  #[global] Instance headers_at_persistent l hdr :
    Persistent (l ↦ₕ hdr).
  Proof.
    apply _.
  Qed.

  Lemma headers_at_agree l hdr1 hdr2 :
    l ↦ₕ hdr1 -∗
    l ↦ₕ hdr2 -∗
    ⌜hdr1 = hdr2⌝.
  Proof.
    apply ghost_heap_at_agree.
  Qed.
End zoo_G.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  #[global] Instance meta_token_timeless l N :
    Timeless (meta_token l N).
  Proof.
    apply _.
  Qed.
  #[global] Instance meta_timeless `{Countable A} l ι (x : A) :
    Timeless (l ↪[ι] x).
  Proof.
    apply _.
  Qed.

  #[global] Instance meta_persistent `{Countable A} l ι (x : A) :
    Persistent (l ↪[ι] x).
  Proof.
    apply _.
  Qed.

  Lemma meta_token_difference {l} E1 E2 :
    E1 ⊆ E2 →
    meta_token l E2 ⊣⊢
      meta_token l E1 ∗
      meta_token l (E2 ∖ E1).
  Proof.
    apply ghost_heap_meta_token_difference.
  Qed.

  Lemma meta_set `{Countable A} {l E} (x : A) ι :
    ↑ ι ⊆ E →
    meta_token l E ⊢ |==>
    l ↪[ι] x.
  Proof.
    apply ghost_heap_meta_set.
  Qed.
  Lemma meta_agree `{Countable A} l ι (x1 x2 : A) :
    l ↪[ι] x1 -∗
    l ↪[ι] x2 -∗
    ⌜x1 = x2⌝.
  Proof.
    apply ghost_heap_meta_agree.
  Qed.

  Lemma headers_lookup hdrs l hdr :
    headers_auth hdrs -∗
    l ↦ₕ hdr -∗
    ⌜hdrs !! l = Some hdr⌝.
  Proof.
    apply ghost_heap_lookup.
  Qed.

  Lemma headers_insert {hdrs} l hdr :
    hdrs !! l = None →
    headers_auth hdrs ⊢ |==>
      headers_auth (<[l := hdr]> hdrs) ∗
      l ↦ₕ hdr ∗
      meta_token l ⊤.
  Proof.
    iIntros "% Hauth".
    iMod (ghost_heap_insert with "Hauth") as "($ & Hat & $)". 1: done.
    iApply (ghost_heap_at_persist with "Hat").
  Qed.
End zoo_G.

#[global] Opaque headers_auth'.
#[global] Opaque headers_at'.
#[global] Opaque meta_token'.
#[global] Opaque meta'.

Section zoo_G₀.
  Context `{zoo_G₀ : !ZooG₀ Σ}.

  #[local] Definition heap_auth' γ_heap h :=
    ghost_map_auth (V := val) γ_heap 1 h.
  #[local] Definition pointsto' γ_heap l dq v :=
    ghost_map_elem (V := val) γ_heap l dq v.

  #[local] Lemma heap_alloc h :
    ⊢ |==>
      ∃ γ_heap,
      heap_auth' γ_heap h ∗
      [∗ map] l ↦ v ∈ h, pointsto' γ_heap l (DfracOwn 1) v.
  Proof.
    apply ghost_map_alloc.
  Qed.
End zoo_G₀.

Section cheriot_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition heap_auth :=
    heap_auth' zoo_G_heap_name.
  Definition pointsto :=
    pointsto' zoo_G_heap_name.
End cheriot_G.

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
  pointsto (location_add l (Z.of_nat (in_type "@ref" 0))) dq v%V
)(at level 20,
  dq custom dfrac at level 1,
  format "l  ↦ᵣ dq  v"
) : bi_scope.
Notation "l ↦ᵣ-" := (
  (∃ v, l ↦ᵣ v)%I
)(at level 20,
  format "l  ↦ᵣ-"
) : bi_scope.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

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
    apply bi.wand_entails', ghost_map_elem_valid.
  Qed.
  Lemma pointsto_combine l dq1 v1 dq2 v2 :
    l ↦{dq1} v1 -∗
    l ↦{dq2} v2 -∗
      ⌜v1 = v2⌝ ∗
      l ↦{dq1 ⋅ dq2} v1.
  Proof.
    rewrite comm. apply ghost_map_elem_combine.
  Qed.
  Lemma pointsto_valid_2 l dq1 v1 dq2 v2 :
    l ↦{dq1} v1 -∗
    l ↦{dq2} v2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜v1 = v2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_map_elem_valid_2 with "H1 H2") as "$".
  Qed.
  Lemma pointsto_agree l dq2 v1 dq1 v2 :
    l ↦{dq1} v1 -∗
    l ↦{dq2} v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    apply ghost_map_elem_agree.
  Qed.
  Lemma pointsto_dfrac_ne l1 dq1 v1 l2 dq2 v2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    l1 ↦{dq1} v1 -∗
    l2 ↦{dq2} v2 -∗
    ⌜l1 ≠ l2⌝.
  Proof.
    apply ghost_map_elem_frac_ne.
  Qed.
  Lemma pointsto_ne l1 v1 l2 dq2 v2 :
    l1 ↦ v1 -∗
    l2 ↦{dq2} v2 -∗
    ⌜l1 ≠ l2⌝.
  Proof.
    apply ghost_map_elem_ne.
  Qed.
  Lemma pointsto_exclusive l v1 dq2 v2 :
    l ↦ v1 -∗
    l ↦{dq2} v2 -∗
    False.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_map_elem_ne with "H1 H2") as %?. done.
  Qed.
  Lemma pointsto_persist l dq v :
    l ↦{dq} v ⊢ |==>
    l ↦□ v.
  Proof.
    apply bi.wand_entails', ghost_map_elem_persist.
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
    apply: frame_fractional.
  Qed.

  Lemma heap_lookup h a dq c :
    heap_auth h -∗
    a ↦{dq} c -∗
    ⌜h !! a = Some c⌝.
  Proof.
    apply ghost_map_lookup.
  Qed.
  Lemma heap_insert {h1} h2 :
    h2 ##ₘ h1 →
    heap_auth h1 ⊢ |==>
      heap_auth (h2 ∪ h1) ∗
      [∗ map] l ↦ v ∈ h2, l ↦ v.
  Proof.
    intros.
    apply bi.wand_entails', ghost_map_insert_big => //.
  Qed.
  Lemma heap_update {h a c1} c2 :
    heap_auth h -∗
    a ↦ c1 ==∗
      heap_auth (<[a := c2]> h) ∗
      a ↦ c2.
  Proof.
    apply ghost_map_update.
  Qed.
End zoo_G.

#[global] Opaque heap_auth'.
#[global] Opaque pointsto'.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Lemma big_sepL2_pointsto_agree ls dq1 vs1 dq2 vs2 :
    ([∗ list] l; v ∈ ls; vs1, l ↦{dq1} v) -∗
    ([∗ list] l; v ∈ ls; vs2, l ↦{dq2} v) -∗
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
    ([∗ list] l; v ∈ ls; vs1, l ↦ᵣ{dq1} v) -∗
    ([∗ list] l; v ∈ ls; vs2, l ↦ᵣ{dq2} v) -∗
    ⌜vs1 = vs2⌝.
  Proof.
    setoid_rewrite location_add_0.
    apply big_sepL2_pointsto_agree.
  Qed.

  Lemma big_sepL2_pointsto_prefix ls1 dq1 vs1 ls2 dq2 vs2 :
    ls1 `prefix_of` ls2 →
    ([∗ list] l; v ∈ ls1; vs1, l ↦{dq1} v) -∗
    ([∗ list] l; v ∈ ls2; vs2, l ↦{dq2} v) -∗
    ⌜vs1 `prefix_of` vs2⌝.
  Proof.
    iIntros ((ls & ->)) "H1 H2".
    iDestruct (big_sepL2_app_inv_l with "H2") as "(%vs & %vs1_ & -> & H1_ & _)".
    iDestruct (big_sepL2_pointsto_agree with "H1 H1_") as %<-.
    iPureIntro. apply prefix_app_r. done.
  Qed.
  Lemma big_sepL2_ref_pointsto_prefix ls1 dq1 vs1 ls2 dq2 vs2 :
    ls1 `prefix_of` ls2 →
    ([∗ list] l; v ∈ ls1; vs1, l ↦ᵣ{dq1} v) -∗
    ([∗ list] l; v ∈ ls2; vs2, l ↦ᵣ{dq2} v) -∗
    ⌜vs1 `prefix_of` vs2⌝.
  Proof.
    setoid_rewrite location_add_0.
    apply big_sepL2_pointsto_prefix.
  Qed.

  Lemma big_sepL2_pointsto_suffix ls1 dq1 vs1 ls2 dq2 vs2 :
    ls1 `suffix_of` ls2 →
    ([∗ list] l; v ∈ ls1; vs1, l ↦{dq1} v) -∗
    ([∗ list] l; v ∈ ls2; vs2, l ↦{dq2} v) -∗
    ⌜vs1 `suffix_of` vs2⌝.
  Proof.
    iIntros ((ls & ->)) "H1 H2".
    iDestruct (big_sepL2_app_inv_l with "H2") as "(%vs & %vs1_ & -> & _ & H1_)".
    iDestruct (big_sepL2_pointsto_agree with "H1 H1_") as %<-.
    iPureIntro. solve_suffix.
  Qed.
  Lemma big_sepL2_ref_pointsto_suffix ls1 dq1 vs1 ls2 dq2 vs2 :
    ls1 `suffix_of` ls2 →
    ([∗ list] l; v ∈ ls1; vs1, l ↦ᵣ{dq1} v) -∗
    ([∗ list] l; v ∈ ls2; vs2, l ↦ᵣ{dq2} v) -∗
    ⌜vs1 `suffix_of` vs2⌝.
  Proof.
    setoid_rewrite location_add_0.
    apply big_sepL2_pointsto_suffix.
  Qed.
End zoo_G.

Section resolve_prophecies.
  #[local] Fixpoint resolve_prophecies κs pid :=
    match κs with
    | [] =>
        []
    | κ :: κs =>
        if decide (pid = κ.1) then
          κ.2 :: resolve_prophecies κs pid
        else
          resolve_prophecies κs pid
    end.

  #[local] Definition resolve_prophets prophets κs :=
    map_Forall (λ pid prophs, prophs = resolve_prophecies κs pid) prophets.

  #[local] Lemma resolve_prophets_insert κs pid prophets :
    resolve_prophets prophets κs →
    pid ∉ dom prophets →
    resolve_prophets (<[pid := resolve_prophecies κs pid]> prophets) κs.
  Proof.
    intros Hprophets Hpid pid' prophs Hlookup.
    destruct_decide (pid = pid') as -> | Hne.
    - rewrite lookup_insert_eq in Hlookup.
      inversion Hlookup. done.
    - rewrite lookup_insert_ne // in Hlookup.
      apply Hprophets. done.
  Qed.
End resolve_prophecies.

Section zoo_G₀.
  Context `{zoo_G₀ : !ZooG₀ Σ}.

  #[local] Definition prophets_auth' γ_prophets κs pids : iProp Σ :=
    ∃ prophets,
    ⌜resolve_prophets prophets κs⌝ ∗
    ⌜dom prophets ⊆ pids⌝ ∗
    ghost_map_auth γ_prophets 1 prophets.
  #[local] Definition prophet_model' γ_prophets pid prophs :=
    ghost_map_elem γ_prophets pid (DfracOwn 1) prophs.

  #[local] Lemma prophets_alloc κs pids :
    ⊢ |==>
      ∃ γ_prophets,
      prophets_auth' γ_prophets κs pids.
  Proof.
    iMod ghost_map_alloc_empty as "(%γ & $)" => //.
  Qed.
End zoo_G₀.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition prophets_auth :=
    prophets_auth' zoo_G_prophets_name.
  Definition prophet_model :=
    prophet_model' zoo_G_prophets_name.

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
    iIntros "H1 H2".
    iDestruct (ghost_map_elem_ne with "H1 H2") as %[] => //.
  Qed.

  Lemma prophets_new {κs pids} pid :
    pid ∉ pids →
    prophets_auth κs pids ⊢ |==>
      ∃ prophs,
      prophets_auth κs ({[pid]} ∪ pids) ∗
      prophet_model pid prophs.
  Proof.
    iIntros "%Hpid (%prophets & %Hprophets & %Hpids & Hauth)".
    iMod (ghost_map_insert pid (resolve_prophecies κs pid) with "Hauth") as "(Hauth & Helem)".
    { apply not_elem_of_dom. set_solver. }
    iFrame. iPureIntro. split.
    - apply resolve_prophets_insert; first done. set_solver.
    - rewrite dom_insert. set_solver.
  Qed.

  Lemma prophets_resolve pid proph κs pids prophs :
    prophets_auth ((pid, proph) :: κs) pids -∗
    prophet_model pid prophs ==∗
      ∃ prophs',
      ⌜prophs = proph :: prophs'⌝ ∗
      prophets_auth κs pids ∗
      prophet_model pid prophs'.
  Proof.
    iIntros "(%prophets & %Hprophets & %Hpids & Hauth) Hp".
    iCombine "Hauth Hp" gives %Hlookup.
    assert (prophs = proph :: resolve_prophecies κs pid) as ->.
    { rewrite (Hprophets pid prophs Hlookup) /= decide_True //. }
    iMod (ghost_map_update (resolve_prophecies κs pid) with "Hauth Hp") as "(Hauth & Helem)".
    iExists (resolve_prophecies κs pid). iFrameSteps; iPureIntro.
    - intros pid' prophs' Hlookup'. destruct_decide (pid = pid') as <- | Hne.
      + rewrite lookup_insert_eq in Hlookup'.
        inversion Hlookup'. done.
      + rewrite lookup_insert_ne // in Hlookup'.
        rewrite (Hprophets pid' prophs' Hlookup') /= decide_False //.
    - assert (pid ∈ dom prophets) by exact: elem_of_dom_2.
      set_solver.
  Qed.
End zoo_G.

#[global] Opaque prophets_auth'.
#[global] Opaque prophet_model'.

Section zoo_G₀.
  Context `{zoo_G₀ : !ZooG₀ Σ}.

  #[local] Definition steps_auth' γ_steps :=
    auth_nat_max_auth γ_steps (DfracOwn 1).
  #[local] Definition steps_lb' :=
    auth_nat_max_lb.

  #[local] Lemma steps_alloc :
    ⊢ |==>
      ∃ γ_steps,
      steps_auth' γ_steps 0.
  Proof.
    apply auth_nat_max_alloc.
  Qed.
End zoo_G₀.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition steps_auth :=
    steps_auth' zoo_G_steps_name.
  Definition steps_lb :=
    auth_nat_max_lb zoo_G_steps_name.
End zoo_G.

Notation "⧖ n" := (
  steps_lb n
)(at level 1,
  format "⧖  n"
) : bi_scope.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  #[global] Instance steps_auth_timeless ns :
    Timeless (steps_auth ns).
  Proof.
    apply _.
  Qed.
  #[global] Instance steps_lb_timeless ns :
    Timeless (⧖ ns).
  Proof.
    apply _.
  Qed.

  #[global] Instance steps_lb_persistent ns :
    Persistent (⧖ ns).
  Proof.
    apply _.
  Qed.

  Lemma steps_lb_0 :
    ⊢ |==>
      ⧖ 0.
  Proof.
    apply auth_nat_max_lb_0.
  Qed.
  Lemma steps_lb_le ns1 ns2 :
    ns2 ≤ ns1 →
    ⧖ ns1 ⊢
    ⧖ ns2.
  Proof.
    apply auth_nat_max_lb_le.
  Qed.
  Lemma steps_lb_max ns1 ns2 :
    ⧖ ns1 -∗
    ⧖ ns2 -∗
    ⧖ (ns1 `max` ns2).
  Proof.
    iIntros "H⧖_1 H⧖_2".
    destruct (Nat.max_spec ns1 ns2) as [(_ & ->) | (_ & ->)] => //.
  Qed.

  Lemma steps_lb_get ns :
    steps_auth ns ⊢
    ⧖ ns.
  Proof.
    apply auth_nat_max_lb_get.
  Qed.
  Lemma steps_lb_valid ns1 ns2 :
    steps_auth ns1 -∗
    ⧖ ns2 -∗
    ⌜ns2 ≤ ns1⌝.
  Proof.
    apply auth_nat_max_lb_valid.
  Qed.

  Lemma steps_update ns :
    steps_auth ns ⊢ |==>
    steps_auth ˖ns.
  Proof.
    apply auth_nat_max_update. lia.
  Qed.

  #[global] Instance hint_steps_lb_le ns1 ns2 :
    SolveSepSideCondition (ns1 ≤ ns2) →
    HINT
      ⧖ ns2
    ✱ [- ;
      emp
    ] ⊫ [id];
      ⧖ ns1
    ✱ [
      emp
    ]
    | 60.
  Proof.
    intros.
    iStep as "H⧖".
    iDestruct (steps_lb_le with "H⧖") as "$"; first done.
  Qed.
  #[global] Instance merge_steps_lbs ns1 ns2 :
    MergableConsume (⧖ ns1) true (λ p Pin Pout,
      TCAnd (
        TCEq Pin (⧖ ns2)%I
      ) (
        TCEq Pout (⧖ (ns1 `max` ns2))%I
      )
    ).
  Proof.
    move=> p Pin Pout [-> ->].
    rewrite bi.intuitionistically_if_elim.
    iIntros "(H⧖_1 & H⧖_2)".
    iApply (steps_lb_max with "H⧖_1 H⧖_2").
  Qed.
End zoo_G.

#[global] Opaque steps_auth'.
#[global] Opaque steps_lb'.

Section zoo_G₀.
  Context `{zoo_G₀ : !ZooG₀ Σ}.

  #[local] Definition locals_auth' γ_locals vs :=
    ghost_list_auth γ_locals vs.
  #[local] Definition local_pointsto' γ_locals tid dq v :=
    ghost_list_at γ_locals tid dq v.

  #[local] Lemma locals_alloc vs :
    ⊢ |==>
      ∃ γ_locals,
      locals_auth' γ_locals vs ∗
      [∗ list] tid ↦ v ∈ vs, local_pointsto' γ_locals tid (DfracOwn 1) v.
  Proof.
    apply: ghost_list_alloc vs.
  Qed.
End zoo_G₀.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition locals_auth :=
    locals_auth' zoo_G_locals_name.
  Definition local_pointsto :=
    local_pointsto' zoo_G_locals_name.
End zoo_G.

Notation "tid ↦ₗ dq v" := (
  local_pointsto tid dq v%V
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

  #[global] Instance local_pointsto_timeless tid dq v :
    Timeless (tid ↦ₗ{dq} v).
  Proof.
    apply _.
  Qed.

  #[global] Instance local_pointsto_persistent tid v :
    Persistent (tid ↦ₗ□ v).
  Proof.
    apply _.
  Qed.

  #[global] Instance local_pointsto_fractional tid v :
    Fractional (λ q, tid ↦ₗ{#q} v)%I.
  Proof.
    apply _.
  Qed.
  #[global] Instance local_pointsto_as_fractional tid q v :
    AsFractional (tid ↦ₗ{#q} v) (λ q, tid ↦ₗ{#q} v)%I q.
  Proof.
    apply _.
  Qed.

  Lemma local_pointsto_valid tid dq v :
    tid ↦ₗ{dq} v ⊢
    ⌜✓ dq⌝.
  Proof.
    apply ghost_list_at_valid.
  Qed.
  Lemma local_pointsto_combine tid dq1 v1 dq2 v2 :
    tid ↦ₗ{dq1} v1 -∗
    tid ↦ₗ{dq2} v2 -∗
      ⌜v1 = v2⌝ ∗
      tid ↦ₗ{dq1 ⋅ dq2} v1.
  Proof.
    apply ghost_list_at_combine.
  Qed.
  Lemma local_pointsto_valid_2 tid dq1 v1 dq2 v2 :
    tid ↦ₗ{dq1} v1 -∗
    tid ↦ₗ{dq2} v2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜v1 = v2⌝.
  Proof.
    apply ghost_list_at_valid_2.
  Qed.
  Lemma local_pointsto_agree tid dq2 v1 dq1 v2 :
    tid ↦ₗ{dq1} v1 -∗
    tid ↦ₗ{dq2} v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    apply ghost_list_at_agree.
  Qed.
  Lemma local_pointsto_dfrac_ne tid1 dq1 v1 tid2 dq2 v2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    tid1 ↦ₗ{dq1} v1 -∗
    tid2 ↦ₗ{dq2} v2 -∗
    ⌜tid1 ≠ tid2⌝.
  Proof.
    iIntros "% H1 H2".
    iDestruct (ghost_list_at_dfrac_ne with "H1 H2") as %[]; done.
  Qed.
  Lemma local_pointsto_ne tid1 v1 tid2 dq2 v2 :
    tid1 ↦ₗ v1 -∗
    tid2 ↦ₗ{dq2} v2 -∗
    ⌜tid1 ≠ tid2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_list_at_ne with "H1 H2") as %[]; done.
  Qed.
  Lemma local_pointsto_exclusive tid v1 dq2 v2 :
    tid ↦ₗ v1 -∗
    tid ↦ₗ{dq2} v2 -∗
    False.
  Proof.
    apply ghost_list_at_exclusive.
  Qed.
  Lemma local_pointsto_persist tid dq v :
    tid ↦ₗ{dq} v ⊢ |==>
    tid ↦ₗ□ v.
  Proof.
    apply ghost_list_at_persist.
  Qed.

  Lemma locals_lookup vs tid dq v :
    locals_auth vs -∗
    tid ↦ₗ{dq} v -∗
    ⌜vs !! tid = Some v⌝.
  Proof.
    apply ghost_list_lookup.
  Qed.

  Lemma locals_update_push {vs} v :
    locals_auth vs ⊢ |==>
      locals_auth (vs ++ [v]) ∗
      length vs ↦ₗ v.
  Proof.
    apply ghost_list_update_push.
  Qed.
  Lemma locals_update_pointsto {vs tid v} v' :
    locals_auth vs -∗
    tid ↦ₗ v ==∗
      locals_auth (<[tid := v']> vs) ∗
      tid ↦ₗ v'.
  Proof.
    apply ghost_list_update_at.
  Qed.
End zoo_G.

#[global] Opaque locals_auth'.
#[global] Opaque local_pointsto'.

Section zoo_G₀.
  Context `{zoo_G₀ : !ZooG₀ Σ}.

  #[local] Definition zoo_counter_auth' γ_counter vs :=
    mono_list_auth γ_counter (DfracOwn 1) vs.
  #[local] Definition zoo_counter_at' γ_counter id v :=
    mono_list_at γ_counter id v.

  #[local] Lemma zoo_counter_alloc :
    ⊢ |==>
      ∃ γ_counter,
      zoo_counter_auth' γ_counter (replicate 0 inhabitant).
  Proof.
    apply mono_list_alloc.
  Qed.
End zoo_G₀.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition zoo_counter_auth :=
    zoo_counter_auth' zoo_G_counter_name.
  Definition zoo_counter_at :=
    zoo_counter_at' zoo_G_counter_name.

  #[global] Instance zoo_counter_auth_timeless vs :
    Timeless (zoo_counter_auth vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance zoo_counter_at_timeless id v :
    Timeless (zoo_counter_at id v).
  Proof.
    apply _.
  Qed.

  #[global] Instance zoo_counter_at_persistent id v :
    Persistent (zoo_counter_at id v).
  Proof.
    apply _.
  Qed.

  Lemma zoo_counter_at_get {vs} id v :
    vs !! id = Some v →
    zoo_counter_auth vs ⊢
    zoo_counter_at id v.
  Proof.
    apply mono_list_at_get.
  Qed.
  Lemma zoo_counter_at_valid vs id v :
    zoo_counter_auth vs -∗
    zoo_counter_at id v -∗
    ⌜vs !! id = Some v⌝.
  Proof.
    apply mono_list_at_valid.
  Qed.
  Lemma zoo_counter_at_agree id v1 v2 :
    zoo_counter_at id v1 -∗
    zoo_counter_at id v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    apply mono_list_at_agree.
  Qed.

  Lemma zoo_counter_update {vs} v :
    zoo_counter_auth vs ⊢ |==>
    zoo_counter_auth (vs ++ [v]).
  Proof.
    apply mono_list_update_snoc.
  Qed.
End zoo_G.

#[global] Opaque zoo_counter_auth'.
#[global] Opaque zoo_counter_at'.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition zoo_counter_name :=
    zoo_G_counter_name.
  Definition zoo_counter_inv_inner : iProp Σ :=
    ∃ cnt vs,
    zoo_counter ↦ᵣ #cnt ∗
    zoo_counter_auth vs ∗
    ⌜length vs = cnt⌝.
  Definition zoo_counter_inv :=
    inv nroot zoo_counter_inv_inner.
End zoo_G.

Lemma zoo_init `{zoo_Gpre : !ZooGpre Σ} `{inv_G : !invGS Σ} hdrs h pids vs κs :
  h !! zoo_counter = Some 0%V →
  ⊢ |={⊤}=>
    ∃ zoo_G : ZooG Σ,
    ⌜zoo_G.(zoo_G_inv_G) = inv_G⌝ ∗
    headers_auth hdrs ∗
    heap_auth h ∗
    prophets_auth κs pids ∗
    steps_auth 0 ∗
    locals_auth vs ∗
    zoo_counter_inv ∗
    ([∗ map] l ↦ v ∈ delete zoo_counter h, l ↦ v) ∗
    ([∗ list] tid ↦ v ∈ vs, tid ↦ₗ v).
Proof.
  intros Hh_lookup_zoo_counter.

  iMod (headers_alloc hdrs) as "(%γ_headers & Hheaders_auth)".

  iMod (heap_alloc h) as "(%γ_heap & Hheap_auth & Hheap)".
  iDestruct (big_sepM_delete with "Hheap") as "(Hcounter & Hheap)". 1: done.
  iEval (rewrite -(location_add_0 zoo_counter)) in "Hcounter".

  iMod (prophets_alloc κs pids) as "(%γ_prophets & Hprophets_interp)".

  iMod steps_alloc as "(%γ_steps & Hsteps_auth)".

  iMod locals_alloc as "(%γ_locals & Hlocals_auth & Hlocals)".

  iMod zoo_counter_alloc as "(%γ_counter & Hcounter_auth)".

  set zoo_G :=
    {|zoo_G_headers_name := γ_headers
    ; zoo_G_heap_name := γ_heap
    ; zoo_G_prophets_name := γ_prophets
    ; zoo_G_steps_name := γ_steps
    ; zoo_G_locals_name := γ_locals
    ; zoo_G_counter_name := γ_counter
    |}.
  iExists zoo_G. iFrameSteps.
  iApply inv_alloc.
  iExists 0. iFrameSteps.
Qed.

#[global] Opaque headers_auth.
#[global] Opaque headers_at.
#[global] Opaque meta_token.
#[global] Opaque meta.
#[global] Opaque heap_auth.
#[global] Opaque pointsto.
#[global] Opaque prophets_auth.
#[global] Opaque prophet_model.
#[global] Opaque steps_auth.
#[global] Opaque steps_lb.
#[global] Opaque locals_auth.
#[global] Opaque local_pointsto.
#[global] Opaque zoo_counter_auth.
#[global] Opaque zoo_counter_at.

Variant ownership :=
  | Own
  | Discard.

Coercion ownership_to_dfrac own :=
  match own with
  | Own =>
      DfracOwn 1
  | Discard =>
      DfracDiscarded
  end.
