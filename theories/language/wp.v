From zoo Require Import
  prelude.
From zoo.iris.bi Require Import
  big_op.
From zoo.iris.base_logic Require Import
  lib.mono_map.
From zoo.iris.program_logic Require Import
  wp_lifting.
From zoo.iris Require Import
  diaframe.
From zoo.language Require Export
  typeclass_instances
  state_interp.
From zoo.language Require Import
  tactics
  notations.
From zoo Require Import
  options.

Implicit Types l : location.
Implicit Types pid : prophet_id.
Implicit Types lit : literal.
Implicit Types e : expr.
Implicit Types es : list expr.
Implicit Types v w : val.
Implicit Types σ : state.
Implicit Types κ : list observation.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Lemma base_reducible_equal v1 v2 σ :
    val_physical v1 →
    val_physical v2 →
    base_reducible (v1 = v2) σ.
  Proof.
    destruct
      v1 as [lit1 | | tag1 []],
      v2 as [lit2 | | tag2 []].
    all:
      try first
      [ destruct (decide (lit1 = lit2)); first subst
      | destruct (decide (tag1 = tag2)); first subst
      ].
    all: auto with zoo.
  Qed.
  Lemma wp_equal v1 v2 E Φ :
    val_physical v1 →
    val_physical v2 →
    ▷ (
      ( ⌜val_neq v1 v2⌝ -∗
        Φ #false
      ) ∧ (
        ⌜v1 = v2⌝ -∗
        Φ #true
      )
    ) ⊢
    WP v1 = v2 @ E {{ Φ }}.
  Proof.
    iIntros "% % HΦ".
    iApply wp_lift_atomic_base_step_nofork; first done. iIntros "%nt %σ1 %κ %κs Hσ !>".
    iSplit. { iPureIntro. apply base_reducible_equal; done. }
    iIntros "%e2 %σ2 %es %Hstep _ !> !> !>".
    destruct
      v1 as [lit1 | | tag1 []],
      v2 as [lit2 | | tag2 []].
    all:
      try first
      [ destruct (decide (lit1 = lit2)); first subst
      | destruct (decide (tag1 = tag2)); first subst
      ].
    all: invert_base_step; last try by exfalso.
    all:
      match goal with |- _ _ ?P =>
        lazymatch P with
        | context [false] =>
            iDestruct "HΦ" as "(HΦ & _)";
            iSteps
        | context [true] =>
            iDestruct "HΦ" as "(_ & HΦ)";
            iSteps
        end
      end.
  Qed.

  Lemma big_sepM_heap_array (Φ : location → val → iProp Σ) l vs :
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

  Lemma wp_block {es tag} vs E :
    0 < length es →
    to_vals es = Some vs →
    {{{ True }}}
      Block Concrete tag es @ E
    {{{ l,
      RET #l;
      l ↦ₕ Header tag (length es) ∗
      meta_token l ⊤ ∗
      l ↦∗ vs
    }}}.
  Proof.
    iIntros (Hlen <-%of_to_vals) "%Φ _ HΦ".
    iApply wp_lift_atomic_base_step_nofork; first done. iIntros "%nt %σ1 %κ %κs (Hheaders & Hheap & Hκs) !>".
    iSplit; first auto with zoo. iIntros "%e2 %σ2 %es %Hstep _ !> !>".
    invert_base_step. rename select (list val) into vs.
    iStep. iFrame.
    iMod (mono_map_insert' with "Hheaders") as "($ & Hhdr)"; first done.
    iMod (gen_heap_alloc_big _ (heap_array _ _) with "Hheap") as "($ & Hl & Hmeta)".
    { apply heap_array_map_disjoint.
      rewrite -> of_vals_length in *. done.
    }
    iApply "HΦ".
    rewrite !big_sepM_heap_array. iFrame.
    destruct vs; first naive_solver lia.
    iDestruct "Hmeta" as "(Hmeta & _)". rewrite location_add_0 //.
  Qed.

  Lemma wp_match {l hdr dq} vs x e brs e' E Φ :
    length vs = hdr.(header_size) →
    match_apply (Some l) hdr.(header_tag) vs x e brs = Some e' →
    ▷ l ↦ₕ hdr -∗
    ▷ l ↦∗{dq} vs -∗
    ▷ (
      l ↦∗{dq} vs -∗
      WP e' @ E {{ Φ }}
    ) -∗
    WP Match #l x e brs @ E {{ Φ }}.
  Proof.
    iIntros "%Hvs %He' >#Hhdr >Hl H".
    iApply wp_lift_base_step_nofork; first done. iIntros "%nt %σ1 %κ %κs (Hheaders & Hheap & Hκs)".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iDestruct (mono_map_elem_valid with "Hheaders Hhdr") as %Hheaders_lookup.
    iAssert ⌜
      ∀ (i : nat) v,
      vs !! i = Some v →
      σ1.(state_heap) !! (l +ₗ i) = Some v
    ⌝%I as %?.
    { iIntros "%i %v %Hvs_lookup".
      iDestruct (big_sepL_lookup with "Hl") as "Hl"; first done.
      iApply (gen_heap_valid with "Hheap Hl").
    }
    iSplit; first eauto with zoo. iIntros "%_e' %_σ %es %Hstep _ !>".
    invert_base_step.
    select (list val) ltac:(fun _vs => assert (vs = _vs) as ->).
    { apply list_eq_Forall2, Forall2_same_length_lookup_2; first congruence.
      naive_solver.
    }
    simplify.
    iFrame. iSteps.
  Qed.

  Lemma wp_alloc n v E :
    (0 < n)%Z →
    {{{ True }}}
      Alloc #n v @ E
    {{{ l,
      RET #l;
      l ↦ₕ Header 0 (Z.to_nat n) ∗
      meta_token l ⊤ ∗
      l ↦∗ replicate (Z.to_nat n) v
    }}}.
  Proof.
    iIntros "%Hn %Φ _ HΦ".
    iApply wp_lift_atomic_base_step_nofork; first done. iIntros "%nt %σ1 %κ %κs (Hheaders & Hheap & Hκs) !>".
    iSplit; first auto with zoo. iIntros "%e2 %σ2 %es %Hstep _ !> !>".
    invert_base_step.
    iStep. iFrame.
    iMod (mono_map_insert' with "Hheaders") as "($ & Hhdr)"; first done.
    iMod (gen_heap_alloc_big _ (heap_array _ _) with "Hheap") as "($ & Hl & Hmeta)".
    { apply heap_array_map_disjoint.
      rewrite replicate_length //.
    }
    iApply "HΦ".
    rewrite !big_sepM_heap_array. iFrame.
    destruct (Nat.lt_exists_pred 0 (Z.to_nat n)) as (n' & -> & _); first lia.
    iDestruct "Hmeta" as "(Hmeta & _)". rewrite location_add_0 //.
  Qed.

  Lemma wp_get_tag l hdr E Φ :
    ▷ l ↦ₕ hdr -∗
    ▷ Φ #hdr.(header_tag) -∗
    WP GetTag #l @ E {{ Φ }}.
  Proof.
    iIntros ">Hhdr HΦ".
    iApply wp_lift_atomic_base_step_nofork; first done. iIntros "%nt %σ1 %κ %κs (Hheaders & Hheap & Hκs)".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iDestruct (mono_map_elem_valid with "Hheaders Hhdr") as %Hheaders_lookup.
    iSplit; first eauto with zoo. iIntros "%e %σ2 %es %Hstep _ !>".
    invert_base_step.
    iFrame. iSteps.
  Qed.

  Lemma wp_get_size l hdr E Φ :
    ▷ l ↦ₕ hdr -∗
    ▷ Φ #hdr.(header_size) -∗
    WP GetSize #l @ E {{ Φ }}.
  Proof.
    iIntros ">Hhdr HΦ".
    iApply wp_lift_atomic_base_step_nofork; first done. iIntros "%nt %σ1 %κ %κs (Hheaders & Hheap & Hκs)".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iDestruct (mono_map_elem_valid with "Hheaders Hhdr") as %Hheaders_lookup.
    iSplit; first eauto with zoo. iIntros "%e %σ2 %es %Hstep _ !>".
    invert_base_step.
    iFrame. iSteps.
  Qed.

  Lemma wp_load l dq v E :
    {{{
      ▷ l ↦{dq} v
    }}}
      !#l @ E
    {{{
      RET v;
      l ↦{dq} v
    }}}.
  Proof.
    iIntros "%Φ >Hl HΦ".
    iApply wp_lift_atomic_base_step_nofork; first done. iIntros "%nt %σ1 %κ %κs (Hheaders & Hheap & Hκs) !>".
    iDestruct (gen_heap_valid with "Hheap Hl") as %Hlookup.
    iSplit; first eauto with zoo. iIntros "%e2 %σ2 %es %Hstep _ !> !> !>".
    invert_base_step.
    iFrame. iSteps.
  Qed.

  Lemma wp_store l w v E :
    {{{
      ▷ l ↦ w
    }}}
      #l <- v @ E
    {{{
      RET ();
      l ↦ v
    }}}.
  Proof.
    iIntros "%Φ >Hl HΦ".
    iApply wp_lift_atomic_base_step_nofork; first done. iIntros "%nt %σ1 %κ %κs (Hheaders & Hheap & Hκs) !>".
    iDestruct (gen_heap_valid with "Hheap Hl") as %Hlookup.
    iSplit; first eauto with zoo. iIntros "%e2 %σ2 %es %Hstep _ !> !>".
    invert_base_step.
    iMod (gen_heap_update with "Hheap Hl") as "($ & Hl)".
    iFrame. iSteps.
  Qed.

  Lemma wp_xchg l w v E :
    {{{
      ▷ l ↦ w
    }}}
      Xchg #l v @ E
    {{{
      RET w;
      l ↦ v
    }}}.
  Proof.
    iIntros "%Φ >Hl HΦ".
    iApply wp_lift_atomic_base_step_nofork; first done. iIntros "%nt %σ1 %κ %κs (Hheader & Hheap & Hκs) !>".
    iDestruct (gen_heap_valid with "Hheap Hl") as %Hlookup.
    iSplit; first eauto with zoo. iIntros "%e2 %σ2 %es %Hstep _ !> !>".
    invert_base_step.
    iMod (gen_heap_update with "Hheap Hl") as "($ & Hl)".
    iFrame. iSteps.
  Qed.

  Lemma base_reducible_cas l v v1 v2 σ :
    σ.(state_heap) !! l = Some v →
    val_physical v →
    val_physical v1 →
    base_reducible (CAS #l v1 v2) σ.
  Proof.
    destruct
      v as [lit1 | | tag1 []],
      v1 as [lit2 | | tag2 []].
    all:
      try first
      [ destruct (decide (lit1 = lit2)); first subst
      | destruct (decide (tag1 = tag2)); first subst
      ].
    all: eauto with zoo.
  Qed.
  Lemma wp_cas l dq v v1 v2 E Φ :
    val_physical v →
    val_physical v1 →
    ▷ l ↦{dq} v -∗
    ▷ (
      ( ⌜val_neq v v1⌝ -∗
        l ↦{dq} v -∗
        Φ #false
      ) ∧ (
        ⌜v = v1⌝ -∗
        l ↦{dq} v -∗
          ⌜dq = DfracOwn 1⌝ ∗
          l ↦{dq} v ∗
          ( l ↦ v2 -∗
            Φ #true
          )
      )
    ) -∗
    WP CAS #l v1 v2 @ E {{ Φ }}.
  Proof.
    iIntros "% % >Hl HΦ".
    iApply wp_lift_atomic_base_step_nofork; first done. iIntros "%nt %σ1 %κ %κs (Hheaders & Hheap & Hκs) !>".
    iDestruct (gen_heap_valid with "Hheap Hl") as %Hlookup.

    iSplit. { iPureIntro. eapply base_reducible_cas; done. }
    iIntros "%e2 %σ2 %es %Hstep _ !> !>".
    destruct
      v as [lit1 | | tag1 []],
      v1 as [lit2 | | tag2 []].
    all:
      try first
      [ destruct (decide (lit1 = lit2)); first subst
      | destruct (decide (tag1 = tag2)); first subst
      ].
    all: invert_base_step; last try by exfalso.
    all:
      match goal with |- _ _ ?P =>
        lazymatch P with
        | context [false] =>
            iDestruct "HΦ" as "(HΦ & _)";
            iFrame; iSteps
        | context [true] =>
            iDestruct "HΦ" as "(_ & HΦ)";
            iDestruct ("HΦ" with "[//] Hl") as "(-> & Hl & HΦ)";
            iMod (gen_heap_update with "Hheap Hl") as "($ & Hl)";
            iFrame; iSteps
        end
      end.
  Qed.
  Lemma wp_cas_suc l lit lit1 v2 E :
    literal_physical lit →
    lit = lit1 →
    {{{
      ▷ l ↦ #lit
    }}}
      CAS #l #lit1 v2 @ E
    {{{
      RET #true;
      l ↦ v2
    }}}.
  Proof.
    iIntros (Hlit ->) "%Φ >Hl HΦ".
    iApply (wp_cas with "Hl"); [done.. |].
    iSteps.
  Qed.

  Lemma wp_faa l (i1 i2 : Z) E :
    {{{
      ▷ l ↦ #i1
    }}}
      FAA #l #i2 @ E
    {{{
      RET #i1;
      l ↦ #(i1 + i2)
    }}}.
  Proof.
    iIntros "%Φ >Hl HΦ".
    iApply wp_lift_atomic_base_step_nofork; first done. iIntros "%nt %σ1 %κ %κs (Hheaders & Hheap & Hκs) !>".
    iDestruct (gen_heap_valid with "Hheap Hl") as %Hlookup.
    iSplit; first eauto with zoo. iIntros "%e2 %σ2 %es %Hstep _ !> !>".
    invert_base_step.
    iMod (gen_heap_update with "Hheap Hl") as "($ & Hl)".
    iFrame. iSteps.
  Qed.

  Lemma wp_fork e E Φ :
    ▷ WP e @ ⊤ {{ _, True }} -∗
    ▷ Φ ()%V -∗
    WP Fork e @ E {{ Φ }}.
  Proof.
    iIntros "H HΦ".
    iApply wp_lift_atomic_base_step; first done. iIntros "%nt %σ1 %κ %κs Hσ !>".
    iSplit; first auto with zoo. iIntros "%v2 %σ2 %es %Hstep _ !> !> !>".
    invert_base_step.
    iFrame.
  Qed.

  Lemma wp_proph E :
    {{{ True }}}
      Proph @ E
    {{{ prophs pid,
      RET #pid;
      prophet_model pid prophs
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    iApply wp_lift_atomic_base_step_nofork; first done. iIntros "%nt %σ1 %κ %κs (Hheaders & Hheap & Hκs) !>".
    iSplit; first eauto with zoo. iIntros "%e2 %σ2 %es %Hstep _ !> !>".
    invert_base_step.
    iMod (prophet_map_new pid with "Hκs") as "(Hκs & Hp)"; first done.
    iFrame. iSteps.
  Qed.

  Lemma resolve_reducible e σ pid v :
    Atomic e →
    reducible e σ →
    reducible (Resolve e #pid v) σ.
  Proof.
    intros A (κ & e' & σ' & es & H).
    exists (κ ++ [(pid, (default v (to_val e'), v))]), e', σ', es.
    eapply (Ectx_step []); try done.
    assert (∃ w, Val w = e') as (w & <-).
    { unfold Atomic in A. apply (A σ e' κ σ' es) in H. unfold is_Some in H.
      destruct H as [w H]. exists w. simpl in H. apply (of_to_val _ _ H).
    }
    simpl. econstructor. apply prim_step_to_val_is_base_step. done.
  Qed.
  Lemma step_resolve e v1 v2 σ1 κ e2 σ2 es :
    Atomic e →
    prim_step (Resolve e v1 v2) σ1 κ e2 σ2 es →
    base_step (Resolve e v1 v2) σ1 κ e2 σ2 es.
  Proof.
    intros A [K e1' e2' Hfill -> step]. simpl in *.
    induction K as [| k K _] using rev_ind.
    - simpl in *. subst. invert_base_step. constructor. done.
    - rewrite fill_app /= in Hfill. destruct k; inversion Hfill; subst; clear Hfill.
      + assert (fill_item k (fill K e1') = fill (K ++ [k]) e1') as Heq1; first by rewrite fill_app.
        assert (fill_item k (fill K e2') = fill (K ++ [k]) e2') as Heq2; first by rewrite fill_app.
        rewrite fill_app /=. rewrite Heq1 in A.
        assert (is_Some (to_val (fill (K ++ [k]) e2'))) as H.
        { eapply (A σ1 _ κ σ2 es), (Ectx_step (K ++ [k])); done. }
        destruct H as [v H]. apply to_val_fill_some in H. destruct H, K; done.
      + rename select (of_val v1 = _) into Hv1.
        assert (to_val (fill K e1') = Some v1) as Hfill_v1 by rewrite -Hv1 //.
        apply to_val_fill_some in Hfill_v1 as (-> & ->).
        invert_base_step.
      + rename select (of_val v2 = _) into Hv2.
        assert (to_val (fill K e1') = Some v2) as Hfill_v2 by rewrite -Hv2 //.
        apply to_val_fill_some in Hfill_v2 as (-> & ->).
        invert_base_step.
  Qed.
  Lemma wp_resolve e pid v prophs E Φ :
    Atomic e →
    to_val e = None →
    prophet_model pid prophs -∗
    WP e @ E {{ res,
      ∀ prophs',
      ⌜prophs = (res, v) :: prophs'⌝ -∗
      prophet_model pid prophs' -∗
      Φ res
    }} -∗
    WP Resolve e #pid v @ E {{ Φ }}.
  Proof.
    iIntros "%Hatomic %He Hpid H".
    rewrite !wp_unfold /wp_pre /= He. simpl in *.
    iIntros "%nt %σ1 %κ %κs Hσ".
    destruct κ as [| (pid' & (w' & v')) κ' _] using rev_ind.
    - iMod ("H" with "Hσ") as "(%Hreducible & H)".
      iSplitR. { iPureIntro. apply resolve_reducible; done. }
      iIntros "!> %e2 %σ2 %es %Hstep".
      exfalso. apply step_resolve in Hstep; last done.
      invert_base_step.
      destruct κ; done.
    - rewrite -assoc.
      iMod ("H" with "Hσ") as "(%Hreducible & H)".
      iSplitR. { iPureIntro. apply resolve_reducible; done. }
      iIntros "!> %e2 %σ2 %es %Hstep H£".
      apply step_resolve in Hstep; last done.
      invert_base_step. simplify_list_eq.
      iMod ("H" $! (Val w') σ2 es with "[%] H£") as "H".
      { eexists [] _ _; done. }
      do 2 iModIntro.
      iMod "H" as "(($ & $ & Hκs) & H)".
      iMod (prophet_map_resolve pid' (w', v') κs with "Hκs Hpid") as (vs' ->) "($ & Hpid')".
      rewrite !wp_unfold /wp_pre /=.
      iDestruct "H" as "(HΦ & $)".
      iSteps.
  Qed.
End zoo_G.
