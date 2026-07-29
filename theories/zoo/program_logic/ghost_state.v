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

Parameter zoo_counter : location.

Class ZooG₀ Σ :=
  { #[local] zoo۰G₀۰headers۰G :: GhostHeapG Σ location header
  ; #[local] zoo۰G₀۰heap۰G :: ghost_mapG Σ location val
  ; #[local] zoo۰G₀۰prophets۰G :: ghost_mapG Σ prophet_id (list (val * val))
  ; #[local] zoo۰G₀۰steps۰G :: AuthNatMaxG Σ
  ; #[local] zoo۰G₀۰locals۰G :: GhostListG Σ val
  ; #[local] zoo۰G₀۰counter۰G :: MonoListG Σ val
  }.

#[local] Definition zoo۰Σ₀ :=
  #[ghost_heap۰Σ location header
  ; ghost_mapΣ location val
  ; ghost_mapΣ prophet_id (list (val * val))
  ; auth_nat_max۰Σ
  ; ghost_list۰Σ val
  ; mono_list۰Σ val
  ].
#[local] Instance subGｰzoo۰Σ₀ Σ :
  subG zoo۰Σ₀ Σ →
  ZooG₀ Σ.
Proof.
  solve_inG.
Qed.

Class ZooGpre Σ :=
  { #[global] zoo۰Gpre۰inv۰Gpre :: invGpreS Σ
  ; #[local] zoo۰Gpre۰G₀ :: ZooG₀ Σ
  }.

Definition zoo۰Σ :=
  #[invΣ
  ; zoo۰Σ₀
  ].
#[global] Instance subGｰzoo۰Σ Σ :
  subG zoo۰Σ Σ →
  ZooGpre Σ.
Proof.
  solve_inG.
Qed.

Class ZooG Σ :=
  { #[global] zoo۰G۰inv۰G :: invGS Σ
  ; #[local] zoo۰G۰G₀ :: ZooG₀ Σ
  ; zoo۰G۰headers۰name : ghost_heap۰name
  ; zoo۰G۰heap۰name : gname
  ; zoo۰G۰prophets۰name : gname
  ; zoo۰G۰steps۰name : gname
  ; zoo۰G۰locals۰name : gname
  ; zoo۰G۰counter۰name : gname
  }.
#[global] Arguments Build_ZooG {_ _ _} _ _ _ _ _ _ : assert.

Section zoo۰G₀.
  Context `{zoo۰G₀ : !ZooG₀ Σ}.

  #[local] Definition headers۰auth' γ_headers hdrs :=
    ghost_heap۰auth γ_headers hdrs.
  #[local] Definition headers۰at' γ_headers l hdr :=
    ghost_heap۰at γ_headers l DfracDiscarded hdr.

  #[local] Definition meta_token' γ_headers l E :=
    ghost_heap۰meta_token γ_headers l E.
  #[local] Definition meta' `{Countable A} γ_headers l ι (x : A) :=
    ghost_heap۰meta γ_headers l ι x.

  #[local] Lemma headersｰalloc hdrs :
    ⊢ |==>
      ∃ γ_headers,
      headers۰auth' γ_headers hdrs.
  Proof.
    iMod (ghost_heapｰalloc hdrs) as "(%γ_headers & $ & _)" => //.
  Qed.
End zoo۰G₀.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Definition headers۰auth :=
    headers۰auth' zoo۰G۰headers۰name.
  Definition headers۰at :=
    headers۰at' zoo۰G۰headers۰name.

  Definition meta_token :=
    meta_token' zoo۰G۰headers۰name.
  Definition meta `{Countable A} :=
    meta' (A := A) zoo۰G۰headers۰name.
End zoo۰G.

Notation "l ↦ₕ hdr" := (
  headers۰at l hdr
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

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  #[global] Instance headers۰atｰtimeless l hdr :
    Timeless (l ↦ₕ hdr).
  Proof.
    apply _.
  Qed.

  #[global] Instance headers۰atｰpersistent l hdr :
    Persistent (l ↦ₕ hdr).
  Proof.
    apply _.
  Qed.

  Lemma headers۰atｰagree l hdr1 hdr2 :
    l ↦ₕ hdr1 -∗
    l ↦ₕ hdr2 -∗
    ⌜hdr1 = hdr2⌝.
  Proof.
    apply ghost_heap۰atｰagree.
  Qed.
End zoo۰G.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  #[global] Instance meta_tokenｰtimeless l N :
    Timeless (meta_token l N).
  Proof.
    apply _.
  Qed.
  #[global] Instance metaｰtimeless `{Countable A} l ι (x : A) :
    Timeless (l ↪[ι] x).
  Proof.
    apply _.
  Qed.

  #[global] Instance metaｰpersistent `{Countable A} l ι (x : A) :
    Persistent (l ↪[ι] x).
  Proof.
    apply _.
  Qed.

  Lemma meta_tokenｰdifference {l} E1 E2 :
    E1 ⊆ E2 →
    meta_token l E2 ⊣⊢
      meta_token l E1 ∗
      meta_token l (E2 ∖ E1).
  Proof.
    apply ghost_heap۰meta_tokenｰdifference.
  Qed.

  Lemma metaｰset `{Countable A} {l E} (x : A) ι :
    ↑ ι ⊆ E →
    meta_token l E ⊢ |==>
    l ↪[ι] x.
  Proof.
    apply ghost_heap۰metaｰset.
  Qed.
  Lemma metaｰagree `{Countable A} l ι (x1 x2 : A) :
    l ↪[ι] x1 -∗
    l ↪[ι] x2 -∗
    ⌜x1 = x2⌝.
  Proof.
    apply ghost_heap۰metaｰagree.
  Qed.

  Lemma headersｰlookup hdrs l hdr :
    headers۰auth hdrs -∗
    l ↦ₕ hdr -∗
    ⌜hdrs !! l = Some hdr⌝.
  Proof.
    apply ghost_heapｰlookup.
  Qed.

  Lemma headersｰinsert {hdrs} l hdr :
    hdrs !! l = None →
    headers۰auth hdrs ⊢ |==>
      headers۰auth (<[l := hdr]> hdrs) ∗
      l ↦ₕ hdr ∗
      meta_token l ⊤.
  Proof.
    iIntros "% Hauth".
    iMod (ghost_heapｰinsert with "Hauth") as "($ & Hat & $)". 1: done.
    iApply (ghost_heap۰atｰpersist with "Hat").
  Qed.
End zoo۰G.

#[global] Opaque headers۰auth'.
#[global] Opaque headers۰at'.
#[global] Opaque meta_token'.
#[global] Opaque meta'.

Section zoo۰G₀.
  Context `{zoo۰G₀ : !ZooG₀ Σ}.

  #[local] Definition heap۰auth' γ_heap h :=
    ghost_map_auth (V := val) γ_heap 1 h.
  #[local] Definition pointsto' γ_heap l dq v :=
    ghost_map_elem (V := val) γ_heap l dq v.

  #[local] Lemma heapｰalloc h :
    ⊢ |==>
      ∃ γ_heap,
      heap۰auth' γ_heap h ∗
      [∗ map] l ↦ v ∈ h, pointsto' γ_heap l (DfracOwn 1) v.
  Proof.
    apply ghost_map_alloc.
  Qed.
End zoo۰G₀.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Definition heap۰auth :=
    heap۰auth' zoo۰G۰heap۰name.
  Definition pointsto :=
    pointsto' zoo۰G۰heap۰name.
End zoo۰G.

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
  pointsto (location۰add l (Z.of_nat (in_type "@ref" 0))) dq v%V
)(at level 20,
  dq custom dfrac at level 1,
  format "l  ↦ᵣ dq  v"
) : bi_scope.
Notation "l ↦ᵣ-" := (
  (∃ v, l ↦ᵣ v)%I
)(at level 20,
  format "l  ↦ᵣ-"
) : bi_scope.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  #[global] Instance pointstoｰtimeless l dq v :
    Timeless (l ↦{dq} v).
  Proof.
    apply _.
  Qed.

  #[global] Instance pointstoｰpersistent l v :
    Persistent (l ↦□ v).
  Proof.
    apply _.
  Qed.

  #[global] Instance pointstoｰfractional l v :
    Fractional (λ q, l ↦{#q} v)%I.
  Proof.
    apply _.
  Qed.
  #[global] Instance pointstoｰas_fractional l q v :
    AsFractional (l ↦{#q} v) (λ q, l ↦{#q} v)%I q.
  Proof.
    apply _.
  Qed.

  Lemma pointstoｰvalid l dq v :
    l ↦{dq} v ⊢
    ⌜✓ dq⌝.
  Proof.
    apply bi.wand_entails', ghost_map_elem_valid.
  Qed.
  Lemma pointstoｰcombine l dq1 v1 dq2 v2 :
    l ↦{dq1} v1 -∗
    l ↦{dq2} v2 -∗
      ⌜v1 = v2⌝ ∗
      l ↦{dq1 ⋅ dq2} v1.
  Proof.
    rewrite comm. apply ghost_map_elem_combine.
  Qed.
  Lemma pointstoｰvalidｰ2 l dq1 v1 dq2 v2 :
    l ↦{dq1} v1 -∗
    l ↦{dq2} v2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜v1 = v2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_map_elem_valid_2 with "H1 H2") as "$".
  Qed.
  Lemma pointstoｰagree l dq2 v1 dq1 v2 :
    l ↦{dq1} v1 -∗
    l ↦{dq2} v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    apply ghost_map_elem_agree.
  Qed.
  Lemma pointstoｰdfracｰne l1 dq1 v1 l2 dq2 v2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    l1 ↦{dq1} v1 -∗
    l2 ↦{dq2} v2 -∗
    ⌜l1 ≠ l2⌝.
  Proof.
    apply ghost_map_elem_frac_ne.
  Qed.
  Lemma pointstoｰne l1 v1 l2 dq2 v2 :
    l1 ↦ v1 -∗
    l2 ↦{dq2} v2 -∗
    ⌜l1 ≠ l2⌝.
  Proof.
    apply ghost_map_elem_ne.
  Qed.
  Lemma pointstoｰexclusive l v1 dq2 v2 :
    l ↦ v1 -∗
    l ↦{dq2} v2 -∗
    False.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_map_elem_ne with "H1 H2") as %?. done.
  Qed.
  Lemma pointstoｰpersist l dq v :
    l ↦{dq} v ⊢ |==>
    l ↦□ v.
  Proof.
    apply bi.wand_entails', ghost_map_elem_persist.
  Qed.

  #[global] Instance pointstoｰcombine_sep_gives l dq1 v1 dq2 v2 :
    CombineSepGives (l ↦{dq1} v1) (l ↦{dq2} v2) ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝
  | 30.
  Proof.
    apply _.
  Qed.
  #[global] Instance pointstoｰcombine_as l dq1 dq2 v1 v2 :
    CombineSepAs (l ↦{dq1} v1) (l ↦{dq2} v2) (l ↦{dq1 ⋅ dq2} v1)
  | 60.
  Proof.
    apply _.
  Qed.
  #[global] Instance frameｰpointsto p l v q1 q2 q :
    FrameFractionalQp q1 q2 q →
    Frame p (l ↦{#q1} v) (l ↦{#q2} v) (l ↦{#q} v)
  | 5.
  Proof.
    apply: frame_fractional.
  Qed.

  Lemma heapｰlookup h a dq c :
    heap۰auth h -∗
    a ↦{dq} c -∗
    ⌜h !! a = Some c⌝.
  Proof.
    apply ghost_map_lookup.
  Qed.
  Lemma heapｰinsert {h1} h2 :
    h2 ##ₘ h1 →
    heap۰auth h1 ⊢ |==>
      heap۰auth (h2 ∪ h1) ∗
      [∗ map] l ↦ v ∈ h2, l ↦ v.
  Proof.
    intros.
    apply bi.wand_entails', ghost_map_insert_big => //.
  Qed.
  Lemma heapｰupdate {h a c1} c2 :
    heap۰auth h -∗
    a ↦ c1 ==∗
      heap۰auth (<[a := c2]> h) ∗
      a ↦ c2.
  Proof.
    apply ghost_map_update.
  Qed.
End zoo۰G.

#[global] Opaque heap۰auth'.
#[global] Opaque pointsto'.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Lemma big_sepL2ｰpointstoｰagree ls dq1 vs1 dq2 vs2 :
    ([∗ list] l; v ∈ ls; vs1, l ↦{dq1} v) -∗
    ([∗ list] l; v ∈ ls; vs2, l ↦{dq2} v) -∗
    ⌜vs1 = vs2⌝.
  Proof.
    iIntros "H1 H2".
    rewrite list_eq_Forall2.
    iApply big_sepL2ｰForall2.
    iDestruct (big_sepL2ｰretractｰl with "H1") as "(% & H1)".
    iDestruct (big_sepL2ｰretractｰl with "H2") as "(% & H2)".
    iDestruct (big_sepL2_sepL_2 with "H1 H2") as "H"; first congruence.
    iApply (big_sepL2_impl with "H"). iIntros "!> %k %v1 %v2 _ _ ((%l1 & %Hl1_lookup & Hl1) & (%l2 & %Hl2_lookup & Hl2))". simplify.
    iApply (pointstoｰagree with "Hl1 Hl2").
  Qed.
  Lemma big_sepL2ｰrefｰpointstoｰagree ls dq1 vs1 dq2 vs2 :
    ([∗ list] l; v ∈ ls; vs1, l ↦ᵣ{dq1} v) -∗
    ([∗ list] l; v ∈ ls; vs2, l ↦ᵣ{dq2} v) -∗
    ⌜vs1 = vs2⌝.
  Proof.
    setoid_rewrite location۰addｰ0.
    apply big_sepL2ｰpointstoｰagree.
  Qed.

  Lemma big_sepL2ｰpointstoｰprefix ls1 dq1 vs1 ls2 dq2 vs2 :
    ls1 `prefix_of` ls2 →
    ([∗ list] l; v ∈ ls1; vs1, l ↦{dq1} v) -∗
    ([∗ list] l; v ∈ ls2; vs2, l ↦{dq2} v) -∗
    ⌜vs1 `prefix_of` vs2⌝.
  Proof.
    iIntros ((ls & ->)) "H1 H2".
    iDestruct (big_sepL2_app_inv_l with "H2") as "(%vs & %vs1_ & -> & H1_ & _)".
    iDestruct (big_sepL2ｰpointstoｰagree with "H1 H1_") as %<-.
    iPureIntro. apply prefix_app_r. done.
  Qed.
  Lemma big_sepL2ｰrefｰpointstoｰprefix ls1 dq1 vs1 ls2 dq2 vs2 :
    ls1 `prefix_of` ls2 →
    ([∗ list] l; v ∈ ls1; vs1, l ↦ᵣ{dq1} v) -∗
    ([∗ list] l; v ∈ ls2; vs2, l ↦ᵣ{dq2} v) -∗
    ⌜vs1 `prefix_of` vs2⌝.
  Proof.
    setoid_rewrite location۰addｰ0.
    apply big_sepL2ｰpointstoｰprefix.
  Qed.

  Lemma big_sepL2ｰpointstoｰsuffix ls1 dq1 vs1 ls2 dq2 vs2 :
    ls1 `suffix_of` ls2 →
    ([∗ list] l; v ∈ ls1; vs1, l ↦{dq1} v) -∗
    ([∗ list] l; v ∈ ls2; vs2, l ↦{dq2} v) -∗
    ⌜vs1 `suffix_of` vs2⌝.
  Proof.
    iIntros ((ls & ->)) "H1 H2".
    iDestruct (big_sepL2_app_inv_l with "H2") as "(%vs & %vs1_ & -> & _ & H1_)".
    iDestruct (big_sepL2ｰpointstoｰagree with "H1 H1_") as %<-.
    iPureIntro. solve_suffix.
  Qed.
  Lemma big_sepL2ｰrefｰpointstoｰsuffix ls1 dq1 vs1 ls2 dq2 vs2 :
    ls1 `suffix_of` ls2 →
    ([∗ list] l; v ∈ ls1; vs1, l ↦ᵣ{dq1} v) -∗
    ([∗ list] l; v ∈ ls2; vs2, l ↦ᵣ{dq2} v) -∗
    ⌜vs1 `suffix_of` vs2⌝.
  Proof.
    setoid_rewrite location۰addｰ0.
    apply big_sepL2ｰpointstoｰsuffix.
  Qed.
End zoo۰G.

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

  #[local] Lemma resolve_prophetsｰinsert κs pid prophets :
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

Section zoo۰G₀.
  Context `{zoo۰G₀ : !ZooG₀ Σ}.

  #[local] Definition prophets۰auth' γ_prophets κs pids : iProp Σ :=
    ∃ prophets,
    ⌜resolve_prophets prophets κs⌝ ∗
    ⌜dom prophets ⊆ pids⌝ ∗
    ghost_map_auth γ_prophets 1 prophets.
  #[local] Definition prophet۰model' γ_prophets pid prophs :=
    ghost_map_elem γ_prophets pid (DfracOwn 1) prophs.

  #[local] Lemma prophetsｰalloc κs pids :
    ⊢ |==>
      ∃ γ_prophets,
      prophets۰auth' γ_prophets κs pids.
  Proof.
    iMod ghost_map_alloc_empty as "(%γ & $)" => //.
  Qed.
End zoo۰G₀.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Definition prophets۰auth :=
    prophets۰auth' zoo۰G۰prophets۰name.
  Definition prophet۰model :=
    prophet۰model' zoo۰G۰prophets۰name.

  #[global] Instance prophet۰modelｰtimeless pid prophs :
    Timeless (prophet۰model pid prophs).
  Proof.
    apply _.
  Qed.

  Lemma prophet۰modelｰexclusive pid prophs1 prophs2 :
    prophet۰model pid prophs1 -∗
    prophet۰model pid prophs2 -∗
    False.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_map_elem_ne with "H1 H2") as %[] => //.
  Qed.

  Lemma prophetsｰnew {κs pids} pid :
    pid ∉ pids →
    prophets۰auth κs pids ⊢ |==>
      ∃ prophs,
      prophets۰auth κs ({[pid]} ∪ pids) ∗
      prophet۰model pid prophs.
  Proof.
    iIntros "%Hpid (%prophets & %Hprophets & %Hpids & Hauth)".
    iMod (ghost_map_insert pid (resolve_prophecies κs pid) with "Hauth") as "(Hauth & Helem)".
    { apply not_elem_of_dom. set_solver. }
    iFrame. iPureIntro. split.
    - apply resolve_prophetsｰinsert; first done. set_solver.
    - rewrite dom_insert. set_solver.
  Qed.

  Lemma prophetsｰresolve pid proph κs pids prophs :
    prophets۰auth ((pid, proph) :: κs) pids -∗
    prophet۰model pid prophs ==∗
      ∃ prophs',
      ⌜prophs = proph :: prophs'⌝ ∗
      prophets۰auth κs pids ∗
      prophet۰model pid prophs'.
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
End zoo۰G.

#[global] Opaque prophets۰auth'.
#[global] Opaque prophet۰model'.

Section zoo۰G₀.
  Context `{zoo۰G₀ : !ZooG₀ Σ}.

  #[local] Definition steps۰auth' γ_steps :=
    auth_nat_max۰auth γ_steps (DfracOwn 1).
  #[local] Definition steps۰lb' :=
    auth_nat_max۰lb.

  #[local] Lemma stepsｰalloc :
    ⊢ |==>
      ∃ γ_steps,
      steps۰auth' γ_steps 0.
  Proof.
    apply auth_nat_maxｰalloc.
  Qed.
End zoo۰G₀.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Definition steps۰auth :=
    steps۰auth' zoo۰G۰steps۰name.
  Definition steps۰lb :=
    auth_nat_max۰lb zoo۰G۰steps۰name.
End zoo۰G.

Notation "⧖ n" := (
  steps۰lb n
)(at level 1,
  format "⧖  n"
) : bi_scope.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  #[global] Instance steps۰authｰtimeless ns :
    Timeless (steps۰auth ns).
  Proof.
    apply _.
  Qed.
  #[global] Instance steps۰lbｰtimeless ns :
    Timeless (⧖ ns).
  Proof.
    apply _.
  Qed.

  #[global] Instance steps۰lbｰpersistent ns :
    Persistent (⧖ ns).
  Proof.
    apply _.
  Qed.

  Lemma steps۰lbｰ0 :
    ⊢ |==>
      ⧖ 0.
  Proof.
    apply auth_nat_max۰lbｰ0.
  Qed.
  Lemma steps۰lbｰle ns1 ns2 :
    ns2 ≤ ns1 →
    ⧖ ns1 ⊢
    ⧖ ns2.
  Proof.
    apply auth_nat_max۰lbｰle.
  Qed.
  Lemma steps۰lbｰmax ns1 ns2 :
    ⧖ ns1 -∗
    ⧖ ns2 -∗
    ⧖ (ns1 `max` ns2).
  Proof.
    iIntros "H⧖_1 H⧖_2".
    destruct (Nat.max_spec ns1 ns2) as [(_ & ->) | (_ & ->)] => //.
  Qed.

  Lemma steps۰lbｰget ns :
    steps۰auth ns ⊢
    ⧖ ns.
  Proof.
    apply auth_nat_max۰lbｰget.
  Qed.
  Lemma steps۰lbｰvalid ns1 ns2 :
    steps۰auth ns1 -∗
    ⧖ ns2 -∗
    ⌜ns2 ≤ ns1⌝.
  Proof.
    apply auth_nat_max۰lbｰvalid.
  Qed.

  Lemma stepsｰupdate ns :
    steps۰auth ns ⊢ |==>
    steps۰auth ˖ns.
  Proof.
    apply auth_nat_maxｰupdate. lia.
  Qed.

  #[global] Instance hintｰsteps۰lbｰle ns1 ns2 :
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
    iDestruct (steps۰lbｰle with "H⧖") as "$"; first done.
  Qed.
  #[global] Instance mergeｰsteps۰lb ns1 ns2 :
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
    iApply (steps۰lbｰmax with "H⧖_1 H⧖_2").
  Qed.
End zoo۰G.

#[global] Opaque steps۰auth'.
#[global] Opaque steps۰lb'.

Section zoo۰G₀.
  Context `{zoo۰G₀ : !ZooG₀ Σ}.

  #[local] Definition locals۰auth' γ_locals vs :=
    ghost_list۰auth γ_locals vs.
  #[local] Definition local_pointsto' γ_locals tid dq v :=
    ghost_list۰at γ_locals tid dq v.

  #[local] Lemma localsｰalloc vs :
    ⊢ |==>
      ∃ γ_locals,
      locals۰auth' γ_locals vs ∗
      [∗ list] tid ↦ v ∈ vs, local_pointsto' γ_locals tid (DfracOwn 1) v.
  Proof.
    apply: ghost_listｰalloc vs.
  Qed.
End zoo۰G₀.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Definition locals۰auth :=
    locals۰auth' zoo۰G۰locals۰name.
  Definition local_pointsto :=
    local_pointsto' zoo۰G۰locals۰name.
End zoo۰G.

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

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  #[global] Instance local_pointstoｰtimeless tid dq v :
    Timeless (tid ↦ₗ{dq} v).
  Proof.
    apply _.
  Qed.

  #[global] Instance local_pointstoｰpersistent tid v :
    Persistent (tid ↦ₗ□ v).
  Proof.
    apply _.
  Qed.

  #[global] Instance local_pointstoｰfractional tid v :
    Fractional (λ q, tid ↦ₗ{#q} v)%I.
  Proof.
    apply _.
  Qed.
  #[global] Instance local_pointstoｰas_fractional tid q v :
    AsFractional (tid ↦ₗ{#q} v) (λ q, tid ↦ₗ{#q} v)%I q.
  Proof.
    apply _.
  Qed.

  Lemma local_pointstoｰvalid tid dq v :
    tid ↦ₗ{dq} v ⊢
    ⌜✓ dq⌝.
  Proof.
    apply ghost_list۰atｰvalid.
  Qed.
  Lemma local_pointstoｰcombine tid dq1 v1 dq2 v2 :
    tid ↦ₗ{dq1} v1 -∗
    tid ↦ₗ{dq2} v2 -∗
      ⌜v1 = v2⌝ ∗
      tid ↦ₗ{dq1 ⋅ dq2} v1.
  Proof.
    apply ghost_list۰atｰcombine.
  Qed.
  Lemma local_pointstoｰvalidｰ2 tid dq1 v1 dq2 v2 :
    tid ↦ₗ{dq1} v1 -∗
    tid ↦ₗ{dq2} v2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜v1 = v2⌝.
  Proof.
    apply ghost_list۰atｰvalidｰ2.
  Qed.
  Lemma local_pointstoｰagree tid dq2 v1 dq1 v2 :
    tid ↦ₗ{dq1} v1 -∗
    tid ↦ₗ{dq2} v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    apply ghost_list۰atｰagree.
  Qed.
  Lemma local_pointstoｰdfracｰne tid1 dq1 v1 tid2 dq2 v2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    tid1 ↦ₗ{dq1} v1 -∗
    tid2 ↦ₗ{dq2} v2 -∗
    ⌜tid1 ≠ tid2⌝.
  Proof.
    iIntros "% H1 H2".
    iDestruct (ghost_list۰atｰdfracｰne with "H1 H2") as %[]; done.
  Qed.
  Lemma local_pointstoｰne tid1 v1 tid2 dq2 v2 :
    tid1 ↦ₗ v1 -∗
    tid2 ↦ₗ{dq2} v2 -∗
    ⌜tid1 ≠ tid2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_list۰atｰne with "H1 H2") as %[]; done.
  Qed.
  Lemma local_pointstoｰexclusive tid v1 dq2 v2 :
    tid ↦ₗ v1 -∗
    tid ↦ₗ{dq2} v2 -∗
    False.
  Proof.
    apply ghost_list۰atｰexclusive.
  Qed.
  Lemma local_pointstoｰpersist tid dq v :
    tid ↦ₗ{dq} v ⊢ |==>
    tid ↦ₗ□ v.
  Proof.
    apply ghost_list۰atｰpersist.
  Qed.

  Lemma localsｰlookup vs tid dq v :
    locals۰auth vs -∗
    tid ↦ₗ{dq} v -∗
    ⌜vs !! tid = Some v⌝.
  Proof.
    apply ghost_listｰlookup.
  Qed.

  Lemma localsｰupdateｰpush {vs} v :
    locals۰auth vs ⊢ |==>
      locals۰auth (vs ++ [v]) ∗
      length vs ↦ₗ v.
  Proof.
    apply ghost_listｰupdateｰpush.
  Qed.
  Lemma localsｰupdateｰpointsto {vs tid v} v' :
    locals۰auth vs -∗
    tid ↦ₗ v ==∗
      locals۰auth (<[tid := v']> vs) ∗
      tid ↦ₗ v'.
  Proof.
    apply ghost_listｰupdateｰat.
  Qed.
End zoo۰G.

#[global] Opaque locals۰auth'.
#[global] Opaque local_pointsto'.

Section zoo۰G₀.
  Context `{zoo۰G₀ : !ZooG₀ Σ}.

  #[local] Definition zoo_counter۰auth' γ_counter vs :=
    mono_list۰auth γ_counter (DfracOwn 1) vs.
  #[local] Definition zoo_counter۰at' γ_counter id v :=
    mono_list۰at γ_counter id v.

  #[local] Lemma zoo_counterｰalloc :
    ⊢ |==>
      ∃ γ_counter,
      zoo_counter۰auth' γ_counter (replicate 0 inhabitant).
  Proof.
    apply mono_listｰalloc.
  Qed.
End zoo۰G₀.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Definition zoo_counter۰auth :=
    zoo_counter۰auth' zoo۰G۰counter۰name.
  Definition zoo_counter۰at :=
    zoo_counter۰at' zoo۰G۰counter۰name.

  #[global] Instance zoo_counter۰authｰtimeless vs :
    Timeless (zoo_counter۰auth vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance zoo_counter۰atｰtimeless id v :
    Timeless (zoo_counter۰at id v).
  Proof.
    apply _.
  Qed.

  #[global] Instance zoo_counter۰atｰpersistent id v :
    Persistent (zoo_counter۰at id v).
  Proof.
    apply _.
  Qed.

  Lemma zoo_counter۰atｰget {vs} id v :
    vs !! id = Some v →
    zoo_counter۰auth vs ⊢
    zoo_counter۰at id v.
  Proof.
    apply mono_list۰atｰget.
  Qed.
  Lemma zoo_counter۰atｰvalid vs id v :
    zoo_counter۰auth vs -∗
    zoo_counter۰at id v -∗
    ⌜vs !! id = Some v⌝.
  Proof.
    apply mono_list۰atｰvalid.
  Qed.
  Lemma zoo_counter۰atｰagree id v1 v2 :
    zoo_counter۰at id v1 -∗
    zoo_counter۰at id v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    apply mono_list۰atｰagree.
  Qed.

  Lemma zoo_counterｰupdate {vs} v :
    zoo_counter۰auth vs ⊢ |==>
    zoo_counter۰auth (vs ++ [v]).
  Proof.
    apply mono_listｰupdateｰsnoc.
  Qed.
End zoo۰G.

#[global] Opaque zoo_counter۰auth'.
#[global] Opaque zoo_counter۰at'.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Definition zoo_counter۰name :=
    zoo۰G۰counter۰name.
  Definition zoo_counter۰inv۰inner : iProp Σ :=
    ∃ cnt vs,
    zoo_counter ↦ᵣ #cnt ∗
    zoo_counter۰auth vs ∗
    ⌜length vs = cnt⌝.
  Definition zoo_counter۰inv :=
    inv nroot zoo_counter۰inv۰inner.
End zoo۰G.

Lemma zooｰinit `{zoo۰Gpre : !ZooGpre Σ} `{inv۰G : !invGS Σ} hdrs h pids vs κs :
  h !! zoo_counter = Some 0%V →
  ⊢ |={⊤}=>
    ∃ zoo۰G : ZooG Σ,
    ⌜zoo۰G.(zoo۰G۰inv۰G) = inv۰G⌝ ∗
    headers۰auth hdrs ∗
    heap۰auth h ∗
    prophets۰auth κs pids ∗
    steps۰auth 0 ∗
    locals۰auth vs ∗
    zoo_counter۰inv ∗
    ([∗ map] l ↦ v ∈ delete zoo_counter h, l ↦ v) ∗
    ([∗ list] tid ↦ v ∈ vs, tid ↦ₗ v).
Proof.
  intros Hh_lookup_zoo_counter.

  iMod (headersｰalloc hdrs) as "(%γ_headers & Hheaders_auth)".

  iMod (heapｰalloc h) as "(%γ_heap & Hheap_auth & Hheap)".
  iDestruct (big_sepM_delete with "Hheap") as "(Hcounter & Hheap)". 1: done.
  iEval (rewrite -(location۰addｰ0 zoo_counter)) in "Hcounter".

  iMod (prophetsｰalloc κs pids) as "(%γ_prophets & Hprophets_interp)".

  iMod stepsｰalloc as "(%γ_steps & Hsteps_auth)".

  iMod localsｰalloc as "(%γ_locals & Hlocals_auth & Hlocals)".

  iMod zoo_counterｰalloc as "(%γ_counter & Hcounter_auth)".

  set zoo۰G :=
    {|zoo۰G۰headers۰name := γ_headers
    ; zoo۰G۰heap۰name := γ_heap
    ; zoo۰G۰prophets۰name := γ_prophets
    ; zoo۰G۰steps۰name := γ_steps
    ; zoo۰G۰locals۰name := γ_locals
    ; zoo۰G۰counter۰name := γ_counter
    |}.
  iExists zoo۰G. iFrameSteps.
  iApply inv_alloc.
  iExists 0. iFrameSteps.
Qed.

#[global] Opaque headers۰auth.
#[global] Opaque headers۰at.
#[global] Opaque meta_token.
#[global] Opaque meta.
#[global] Opaque heap۰auth.
#[global] Opaque pointsto.
#[global] Opaque prophets۰auth.
#[global] Opaque prophet۰model.
#[global] Opaque steps۰auth.
#[global] Opaque steps۰lb.
#[global] Opaque locals۰auth.
#[global] Opaque local_pointsto.
#[global] Opaque zoo_counter۰auth.
#[global] Opaque zoo_counter۰at.

Variant ownership :=
  | Own
  | Discard.

Coercion ownership۰to_dfrac own :=
  match own with
  | Own =>
      DfracOwn 1
  | Discard =>
      DfracDiscarded
  end.
