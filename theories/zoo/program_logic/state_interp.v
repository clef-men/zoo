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
  lib.auth_nat_max
  lib.ghost_list
  lib.mono_list
  lib.prophet_map.
From zoo.iris Require Import
  diaframe.
From zoo.language Require Export
  language.
From zoo.language Require Import
  notations.
From zoo Require Import
  options.

Implicit Types cnt ns nt : nat.
Implicit Types tid : thread_id.
Implicit Types l : location.
Implicit Types hdr : header.
Implicit Types σ : state.
Implicit Types κ κs : list observation.

Parameter zoo_counter : location.

Record zoo_parameter := {
  zoo_parameter_local : val ;
  zoo_parameter_counter : nat ;
}.

Record state_wf σ param := {
  state_wf_locals :
    σ.(state_locals) = [param.(zoo_parameter_local)] ;
  state_wf_counter :
    σ.(state_heap) !! zoo_counter = Some (ValNat param.(zoo_parameter_counter)) ;
}.

Class ZooG₀ Σ := {
  #[local] zoo_G₀_steps_G :: AuthNatMaxG Σ ;
  #[local] zoo_G₀_locals_G :: GhostListG Σ val ;
  #[local] zoo_G₀_counter_G :: MonoListG Σ val ;
}.

#[local] Definition zoo_Σ₀ := #[
  auth_nat_max_Σ ;
  ghost_list_Σ val ;
  mono_list_Σ val
].
#[local] Instance subG_zoo_Σ₀ Σ :
  subG zoo_Σ₀ Σ →
  ZooG₀ Σ.
Proof.
  solve_inG.
Qed.

Class ZooGpre Σ := {
  #[global] zoo_Gpre_inv_Gpre :: invGpreS Σ ;
  #[local] zoo_Gpre_headers_G :: gen_heapGpreS location header Σ ;
  #[local] zoo_Gpre_heap_Gpre :: gen_heapGpreS location val Σ ;
  #[local] zoo_Gpre_prophecy_Gpre :: ProphetMapGpre Σ prophet_id (val * val) ;
  #[local] zoo_Gpre_G₀ :: ZooG₀ Σ ;
}.

Definition zoo_Σ := #[
  invΣ ;
  gen_heapΣ location header ;
  gen_heapΣ location val ;
  prophet_map_Σ prophet_id (val * val) ;
  zoo_Σ₀
].
#[global] Instance subG_zoo_Σ Σ :
  subG zoo_Σ Σ →
  ZooGpre Σ.
Proof.
  solve_inG.
Qed.

Class ZooG Σ := {
  #[global] zoo_G_inv_G :: invGS Σ ;
  #[local] zoo_G_headers_G :: gen_heapGS location header Σ ;
  #[local] zoo_G_heap_G :: gen_heapGS location val Σ ;
  #[local] zoo_G_prophecy_G :: ProphetMapG Σ prophet_id (val * val) ;
  #[local] zoo_G_G₀ :: ZooG₀ Σ ;
  zoo_G_steps_name : gname ;
  zoo_G_locals_name : gname ;
  zoo_G_counter_name : gname ;
}.
#[global] Arguments Build_ZooG {_ _ _ _ _ _} _ _ _ : assert.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition has_header l hdr :=
    pointsto l DfracDiscarded hdr.

  Definition meta_token :=
    meta_token (V := header).
  Definition meta :=
    @meta location _ _ header _ _.
  #[global] Arguments meta {_ _ _} _ _ _ : assert.
End zoo_G.

Notation "l ↦ₕ hdr" := (
  has_header l hdr
)(at level 20,
  format "l  ↦ₕ  hdr"
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
End zoo_G.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  #[global] Instance meta_token_timeless l N :
    Timeless (meta_token l N).
  Proof.
    apply _.
  Qed.
  #[global] Instance meta_timeless `{Countable A} l ι (x : A) :
    Timeless (meta l ι x).
  Proof.
    apply _.
  Qed.

  #[global] Instance meta_persistent `{Countable A} l ι (x : A) :
    Persistent (meta l ι x).
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

  Lemma meta_set `{Countable A} {l E} (x : A) ι :
    ↑ ι ⊆ E →
    meta_token l E ⊢ |==>
    meta l ι x.
  Proof.
    intros. apply bi.wand_entails', meta_set; done.
  Qed.
  Lemma meta_agree `{Countable A} l ι (x1 x2 : A) :
    meta l ι x1 -∗
    meta l ι x2 -∗
    ⌜x1 = x2⌝.
  Proof.
    apply meta_agree.
  Qed.
End zoo_G.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition pointsto :=
    pointsto (V := val).
End zoo_G.

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

  Lemma big_sepL2_pointsto_prefix ls1 dq1 vs1 ls2 dq2 vs2 :
    ls1 `prefix_of` ls2 →
    ([∗ list] k ↦ l; v ∈ ls1; vs1, l ↦{dq1} v) -∗
    ([∗ list] k ↦ l; v ∈ ls2; vs2, l ↦{dq2} v) -∗
    ⌜vs1 `prefix_of` vs2⌝.
  Proof.
    iIntros ((ls & ->)) "H1 H2".
    iDestruct (big_sepL2_app_inv_l with "H2") as "(%vs & %vs1_ & -> & H1_ & _)".
    iDestruct (big_sepL2_pointsto_agree with "H1 H1_") as %<-.
    iPureIntro. apply prefix_app_r. done.
  Qed.
  Lemma big_sepL2_ref_pointsto_prefix ls1 dq1 vs1 ls2 dq2 vs2 :
    ls1 `prefix_of` ls2 →
    ([∗ list] k ↦ l; v ∈ ls1; vs1, l ↦ᵣ{dq1} v) -∗
    ([∗ list] k ↦ l; v ∈ ls2; vs2, l ↦ᵣ{dq2} v) -∗
    ⌜vs1 `prefix_of` vs2⌝.
  Proof.
    setoid_rewrite location_add_0.
    apply big_sepL2_pointsto_prefix.
  Qed.

  Lemma big_sepL2_pointsto_suffix ls1 dq1 vs1 ls2 dq2 vs2 :
    ls1 `suffix_of` ls2 →
    ([∗ list] k ↦ l; v ∈ ls1; vs1, l ↦{dq1} v) -∗
    ([∗ list] k ↦ l; v ∈ ls2; vs2, l ↦{dq2} v) -∗
    ⌜vs1 `suffix_of` vs2⌝.
  Proof.
    iIntros ((ls & ->)) "H1 H2".
    iDestruct (big_sepL2_app_inv_l with "H2") as "(%vs & %vs1_ & -> & _ & H1_)".
    iDestruct (big_sepL2_pointsto_agree with "H1 H1_") as %<-.
    iPureIntro. solve_suffix.
  Qed.
  Lemma big_sepL2_ref_pointsto_suffix ls1 dq1 vs1 ls2 dq2 vs2 :
    ls1 `suffix_of` ls2 →
    ([∗ list] k ↦ l; v ∈ ls1; vs1, l ↦ᵣ{dq1} v) -∗
    ([∗ list] k ↦ l; v ∈ ls2; vs2, l ↦ᵣ{dq2} v) -∗
    ⌜vs1 `suffix_of` vs2⌝.
  Proof.
    setoid_rewrite location_add_0.
    apply big_sepL2_pointsto_suffix.
  Qed.
End zoo_G.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition prophet_model :=
    prophet_model.
  Definition prophet_model' pid :=
    prophet_model pid (DfracOwn 1).

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
End zoo_G.

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

  #[local] Definition steps_auth :=
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

  #[local] Instance steps_auth_timeless ns :
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

  #[local] Lemma steps_lb_get ns :
    steps_auth ns ⊢
    ⧖ ns.
  Proof.
    apply auth_nat_max_lb_get.
  Qed.
  #[local] Lemma steps_lb_valid ns1 ns2 :
    steps_auth ns1 -∗
    ⧖ ns2 -∗
    ⌜ns2 ≤ ns1⌝.
  Proof.
    apply auth_nat_max_lb_valid.
  Qed.

  #[local] Lemma steps_update ns :
    steps_auth ns ⊢ |==>
    steps_auth (S ns).
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

  #[local] Definition locals_auth' :=
    ghost_list_auth.
  #[local] Definition local_pointsto' :=
    ghost_list_at.

  #[local] Lemma locals_alloc σ param :
    state_wf σ param →
    ⊢ |==>
      ∃ γ_locals,
      locals_auth' γ_locals σ.(state_locals) ∗
      local_pointsto' γ_locals 0 (DfracOwn 1) param.(zoo_parameter_local).
  Proof.
    intros Hwf.
    iMod (ghost_list_alloc σ.(state_locals)) as "(%γ_locals & $ & Hlocals)".
    iEval (erewrite state_wf_locals; last done) in "Hlocals".
    iDestruct "Hlocals" as "($ & _)" => //.
  Qed.
End zoo_G₀.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  #[local] Definition locals_auth locals :=
    locals_auth' zoo_G_locals_name locals.
  Definition local_pointsto tid dq local :=
    local_pointsto' zoo_G_locals_name tid dq local.

  #[local] Lemma locals_lookup locals tid dq local :
    locals_auth locals -∗
    local_pointsto tid dq local -∗
    ⌜locals !! tid = Some local⌝.
  Proof.
    apply ghost_list_lookup.
  Qed.

  #[local] Lemma locals_update_push {locals} local :
    locals_auth locals ⊢ |==>
      locals_auth (locals ++ [local]) ∗
      local_pointsto (length locals) (DfracOwn 1) local.
  Proof.
    apply ghost_list_update_push.
  Qed.
  #[local] Lemma locals_update_pointsto {locals tid local} local' :
    locals_auth locals -∗
    local_pointsto tid (DfracOwn 1) local ==∗
      locals_auth (<[tid := local']> locals) ∗
      local_pointsto tid (DfracOwn 1) local'.
  Proof.
    apply ghost_list_update_at.
  Qed.
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
End zoo_G.

#[global] Opaque locals_auth'.
#[global] Opaque local_pointsto'.

Section zoo_G₀.
  Context `{zoo_G₀ : !ZooG₀ Σ}.

  #[local] Definition zoo_counter_auth' γ_counter vs :=
    mono_list_auth γ_counter (DfracOwn 1) vs.
  #[local] Definition zoo_counter_at' γ_counter id v :=
    mono_list_at γ_counter id v.

  #[local] Lemma zoo_counter_alloc param :
    ⊢ |==>
      ∃ γ_counter,
      zoo_counter_auth' γ_counter (replicate param.(zoo_parameter_counter) inhabitant).
  Proof.
    apply mono_list_alloc.
  Qed.
End zoo_G₀.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  #[local] Definition zoo_counter_auth :=
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

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition state_interp ns nt σ κs : iProp Σ :=
    gen_heap_interp σ.(state_headers) ∗
    gen_heap_interp σ.(state_heap) ∗
    prophet_map_interp κs σ.(state_prophets) ∗
    steps_auth ns ∗
    locals_auth σ.(state_locals) ∗
    ⌜length σ.(state_locals) = nt⌝ ∗
    zoo_counter_inv.

  Definition fork_post (_ : val) : iProp Σ :=
    True.
End zoo_G.

#[local] Instance : CustomIpat "state_interp" :=
  " ( Hheaders_interp &
      Hheap_interp &
      Hprophets_interp &
      Hsteps_auth &
      Hlocals_auth &
      %Hlocals &
      Hcounter_inv
    )
  ".

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Lemma state_interp_mono ns nt σ κs :
    state_interp ns nt σ κs ⊢ |==>
    state_interp (S ns) nt σ κs.
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
    iMod (gen_heap_alloc with "Hheaders_interp") as "($ & Hl_header & $)"; first done.
    iMod (gen_heap.pointsto_persist with "Hl_header") as "$".
    iMod (gen_heap_alloc_big _ (heap_array _ _) with "Hheap_interp") as "($ & Hl & _)".
    { apply heap_array_map_disjoint. done. }
    rewrite big_sepM_heap_array. iSteps.
  Qed.

  Lemma state_interp_has_header_valid ns nt σ κs l hdr :
    state_interp ns nt σ κs -∗
    l ↦ₕ hdr -∗
    ⌜σ.(state_headers) !! l = Some hdr⌝.
  Proof.
    iIntros "(:state_interp) Hl_header".
    iApply (gen_heap_valid with "Hheaders_interp Hl_header").
  Qed.

  Lemma state_interp_pointsto_valid ns nt σ κs l dq v :
    state_interp ns nt σ κs -∗
    l ↦{dq} v -∗
    ⌜σ.(state_heap) !! l = Some v⌝.
  Proof.
    iIntros "(:state_interp) Hl".
    iApply (gen_heap_valid with "Hheap_interp Hl").
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
    iApply (gen_heap_valid with "Hheap_interp Hl").
  Qed.
  Lemma state_interp_pointsto_update {ns nt σ κs l w} v :
    state_interp ns nt σ κs -∗
    l ↦ w ==∗
      state_interp ns nt (state_update_heap (insert l v) σ) κs ∗
      l ↦ v.
  Proof.
    iIntros "(:state_interp) Hl".
    iMod (gen_heap_update with "Hheap_interp Hl") as "(Hheap_interp & Hl)".
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
      state_interp ns (nt + 1) (state_update_locals (.++ [v]) σ) κs ∗
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
      state_interp ns nt (state_update_locals (insert tid v) σ) κs ∗
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
      state_interp ns nt (state_update_prophets ({[pid]} ∪.) σ) κs ∗
      prophet_model pid (DfracOwn 1) prophs.
  Proof.
    iIntros "%Hpid (:state_interp)".
    iMod (prophet_map_new with "Hprophets_interp") as "(Hprophets_interp & Hpid)"; first done.
    iFrameSteps.
  Qed.
  Lemma state_interp_prophet_resolve ns nt σ κs pid proph prophs :
    state_interp ns nt σ ((pid, proph) :: κs) -∗
    prophet_model pid (DfracOwn 1) prophs ==∗
      ∃ prophs',
      ⌜prophs = proph :: prophs'⌝ ∗
      state_interp ns nt σ κs ∗
      prophet_model pid (DfracOwn 1) prophs'.
  Proof.
    iIntros "(:state_interp) Hpid".
    iMod (prophet_map_resolve with "Hprophets_interp Hpid") as "(%prophs' & -> & Hprophets_interp & Hpid)".
    iFrameSteps.
  Qed.
End zoo_G.

Definition state_heap_initial σ :=
  delete zoo_counter σ.(state_heap).

Lemma zoo_init `{zoo_Gpre : !ZooGpre Σ} `{inv_G : !invGS Σ} σ param κs :
  state_wf σ param →
  ⊢ |={⊤}=>
    ∃ zoo_G : ZooG Σ,
    ⌜zoo_G.(zoo_G_inv_G) = inv_G⌝ ∗
    state_interp 0 1 σ κs ∗
    ([∗ map] l ↦ v ∈ state_heap_initial σ, l ↦ v) ∗
    0 ↦ₗ param.(zoo_parameter_local).
Proof.
  intros Hwf.

  iMod (gen_heap_init σ.(state_headers)) as (?) "(Hheaders_interp & _)".

  iMod (gen_heap_init σ.(state_heap)) as (?) "(Hheap_interp & Hheap & _)".
  iDestruct (big_sepM_delete with "Hheap") as "(Hcounter & Hheap)".
  { apply Hwf. }
  iEval (rewrite -(location_add_0 zoo_counter)) in "Hcounter".

  iMod (prophet_map_init κs σ.(state_prophets)) as "(% & Hprophets_interp)".

  iMod steps_alloc as "(%γ_steps & Hsteps_auth)".

  iMod locals_alloc as "(%γ_locals & Hlocals_auth & Hlocals)"; first done.

  iMod (zoo_counter_alloc param) as "(%γ_counter & Hcounter_auth)".

  iExists (Build_ZooG γ_steps γ_locals γ_counter). iFrameSteps.
  - erewrite state_wf_locals; done.
  - iApply inv_alloc. iSteps. simpl_length.
Qed.

#[global] Opaque has_header.
#[global] Opaque meta_token.
#[global] Opaque meta.
#[global] Opaque pointsto.
#[global] Opaque prophet_model.
#[global] Opaque steps_lb.
#[global] Opaque local_pointsto.
#[global] Opaque zoo_counter_auth.
#[global] Opaque zoo_counter_at.
#[global] Opaque state_interp.

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
