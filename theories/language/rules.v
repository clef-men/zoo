From iris.program_logic Require Import
  ectx_lifting.

From zebre Require Import
  prelude.
From zebre.iris Require Import
  diaframe.
From zebre.iris.bi Require Import
  big_op.
From zebre.language Require Export
  typeclass_instances
  state_interp.
From zebre.language Require Import
  tactics
  notations.
From zebre Require Import
  options.

Implicit Types l : loc.
Implicit Types p : prophecy_id.
Implicit Types lit : literal.
Implicit Types e : expr.
Implicit Types es : list expr.
Implicit Types v w : val.
Implicit Types σ : state.
Implicit Types κ : list observation.

Section zebre_G.
  Context `{zebre_G : !ZebreG Σ}.

  Lemma base_reducible_equal v1 v2 σ :
    val_physical v1 →
    val_physical v2 →
    base_reducible (v1 = v2) σ.
  Proof.
    destruct
      v1 as [[b1 | i1 | l1 | |] | | (? & tag1) []],
      v2 as [[b2 | i2 | l2 | |] | | (? & tag2) []].
    all:
      try first
      [ destruct (decide (b1 = b2)); first subst
      | destruct (decide (i1 = i2)); first subst
      | destruct (decide (l1 = l2)); first subst
      | destruct (decide (tag1 = tag2)); first subst
      ].
    all: auto with zebre.
  Qed.
  Lemma wp_equal v1 v2 E Φ :
    val_physical v1 →
    val_physical v2 →
    ▷ (
      ( ⌜val_neq v1 v2⌝ -∗
        Φ #false
      ) ∧ (
        ⌜val_eq v1 v2⌝ -∗
        Φ #true
      )
    ) ⊢
    WP v1 = v2 @ E {{ Φ }}.
  Proof.
    iIntros "% % HΦ".
    iApply wp_lift_atomic_base_step_no_fork; first done. iIntros "%σ1 %ns %κ %κ' %nt (Hσ & Hκ) !>".
    iSplit. { iPureIntro. apply base_reducible_equal; done. }
    iIntros "%e2 %σ2 %es %Hstep !> _".
    destruct
      v1 as [[b1 | i1 | l1 | |] | | (? & tag1) []],
      v2 as [[b2 | i2 | l2 | |] | | (? & tag2) []].
    all:
      try first
      [ destruct (decide (b1 = b2)); first subst
      | destruct (decide (i1 = i2)); first subst
      | destruct (decide (l1 = l2)); first subst
      | destruct (decide (tag1 = tag2)); first subst
      ].
    all: invert_base_step; last try by exfalso.
    all:
      match goal with |- _ _ ?P =>
        lazymatch P with
        | context [false] =>
            iDestruct "HΦ" as "(HΦ & _)";
            iFrame; iSteps; naive_solver
        | context [true] =>
            iDestruct "HΦ" as "(_ & HΦ)";
            iFrame; iSteps; naive_solver
        end
      end.
  Qed.

  Lemma big_sepM_heap_array (Φ : loc → val → iProp Σ) l vs :
    ([∗ map] l' ↦ v ∈ heap_array l vs, Φ l' v) ⊢
    [∗ list] i ↦ v ∈ vs, Φ (l +ₗ i) v.
  Proof.
    iInduction vs as [| v vs] "IH" forall (l) => /=; first iSteps.
    iIntros "H".
    rewrite big_sepM_insert.
    { clear. apply eq_None_ne_Some. intros v (k & Hk & Hl & _)%heap_array_lookup.
      rewrite -{1}(loc_add_0 l) in Hl. naive_solver lia.
    }
    rewrite loc_add_0. iSteps.
    setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <- Z.add_1_l. setoid_rewrite <- loc_add_assoc. iSteps.
  Qed.

  Lemma wp_record {es} vs E :
    0 < length es →
    to_vals es = Some vs →
    {{{ True }}}
      Record es @ E
    {{{ l,
      RET #l;
      meta_token l ⊤ ∗
      l ↦∗ vs
    }}}.
  Proof.
    iIntros (Hlen <-%of_to_vals) "%Φ _ HΦ".
    iApply wp_lift_atomic_base_step_no_fork; first done. iIntros "%σ1 %ns %κ %κ' %nt (Hσ1 & Hκ) !>".
    iSplit; first auto with zebre. iIntros "!> %e2 %σ2 %es %Hstep _".
    invert_base_step. rename select (list val) into vs.
    iStep. iFrame.
    iMod (gen_heap_alloc_big _ (heap_array _ _) with "Hσ1") as "($ & Hl & Hmeta)".
    { apply heap_array_map_disjoint. rewrite -> of_vals_length in *. auto. }
    iApply "HΦ".
    rewrite !big_sepM_heap_array. iFrame.
    destruct vs; first naive_solver lia.
    iDestruct "Hmeta" as "(Hmeta & _)". rewrite loc_add_0 //.
  Qed.

  Lemma wp_alloc n v E :
    (0 < n)%Z →
    {{{ True }}}
      Alloc #n v @ E
    {{{ l,
      RET #l;
      meta_token l ⊤ ∗
      l ↦∗ replicate (Z.to_nat n) v
    }}}.
  Proof.
    iIntros "%Hn %Φ _ HΦ".
    iApply wp_lift_atomic_base_step_no_fork; first done. iIntros "%σ1 %ns %κ %κ' %nt (Hσ1 & Hκ) !>".
    iSplit; first auto with zebre. iIntros "!> %e2 %σ2 %es %Hstep _".
    invert_base_step.
    iStep. iFrame.
    iMod (gen_heap_alloc_big _ (heap_array _ _) with "Hσ1") as "($ & Hl & Hmeta)".
    { apply heap_array_map_disjoint. rewrite replicate_length Z2Nat.id; auto with lia. }
    iApply "HΦ".
    rewrite !big_sepM_heap_array. iFrame.
    destruct (Nat.lt_exists_pred 0 (Z.to_nat n)) as (n' & -> & _); first lia.
    iDestruct "Hmeta" as "(Hmeta & _)". rewrite loc_add_0 //.
  Qed.
  Lemma wp_ref v E :
    {{{ True }}}
      ref v @ E
    {{{ l,
      RET #l;
      meta_token l ⊤ ∗
      l ↦ v
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    iApply wp_alloc; [lia | done |].
    iSteps. rewrite loc_add_0 //.
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
    iApply wp_lift_atomic_base_step_no_fork; first done. iIntros "%σ1 %ns %κ %κ' %nt (Hσ & Hκ) !>".
    iDestruct (gen_heap_valid with "Hσ Hl") as %Hlookup.
    iSplit; first eauto with zebre. iIntros "%e2 %σ2 %es %Hstep !> _".
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
    iApply wp_lift_atomic_base_step_no_fork; first done. iIntros "%σ1 %ns %κ %κ' %nt (Hσ & Hκ) !>".
    iDestruct (gen_heap_valid with "Hσ Hl") as %Hlookup.
    iSplit; first eauto with zebre. iIntros "%e2 %σ2 %es %Hstep !> _".
    invert_base_step.
    iMod (gen_heap_update with "Hσ Hl") as "($ & Hl)".
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
    iApply wp_lift_atomic_base_step_no_fork; first done. iIntros "%σ1 %ns %κ %κ' %nt (Hσ & Hκ) !>".
    iDestruct (gen_heap_valid with "Hσ Hl") as %Hlookup.
    iSplit; first eauto with zebre. iIntros "%e2 %σ2 %es %Hstep !> _".
    invert_base_step.
    iMod (gen_heap_update with "Hσ Hl") as "($ & Hl)".
    iFrame. iSteps.
  Qed.

  Lemma base_reducible_cas l v v1 v2 σ :
    σ.(state_heap) !! l = Some v →
    val_physical v →
    val_physical v1 →
    base_reducible (Cas #l v1 v2) σ.
  Proof.
    intros.
    destruct
      v as [[b | i | l' | |] | | (? & tag) []],
      v1 as [[b1 | i1 | l1 | |] | | (? & tag1) []].
    all:
      try first
      [ destruct (decide (b = b1)); first subst
      | destruct (decide (i = i1)); first subst
      | destruct (decide (l' = l1)); first subst
      | destruct (decide (tag = tag1)); first subst
      ].
    all: eauto with zebre.
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
        ⌜val_eq v v1⌝ -∗
        l ↦{dq} v -∗
          ⌜dq = DfracOwn 1⌝ ∗
          l ↦{dq} v ∗
          ( l ↦ v2 -∗
            Φ #true
          )
      )
    ) -∗
    WP Cas #l v1 v2 @ E {{ Φ }}.
  Proof.
    iIntros "% % >Hl HΦ".
    iApply wp_lift_atomic_base_step_no_fork; first done. iIntros "%σ1 %ns %κ %κ' %nt (Hσ & Hκ) !>".
    iDestruct (gen_heap_valid with "Hσ Hl") as %Hlookup.

    iSplit. { iPureIntro. eapply base_reducible_cas; done. }
    iIntros "%e2 %σ2 %es %Hstep !> _".
    destruct
      v as [[b | i | l' | |] | | (? & tag) []],
      v1 as [[b1 | i1 | l1 | |] | | (? & tag1) []].
    all:
      try first
      [ destruct (decide (b = b1)); first subst
      | destruct (decide (i = i1)); first subst
      | destruct (decide (l' = l1)); first subst
      | destruct (decide (tag = tag1)); first subst
      ].
    all: invert_base_step; last try by exfalso.
    all:
      match goal with |- _ _ ?P =>
        lazymatch P with
        | context [false] =>
            iDestruct "HΦ" as "(HΦ & _)";
            iFrame; iSteps; naive_solver
        | context [true] =>
            iDestruct "HΦ" as "(_ & HΦ)";
            iDestruct ("HΦ" with "[//] Hl") as "(-> & Hl & HΦ)";
            iMod (gen_heap_update with "Hσ Hl") as "($ & Hl)";
            iFrame; iSteps; naive_solver
        end
      end.
  Qed.
  Lemma wp_cas_literal l dq lit lit1 v2 E Φ :
    literal_physical lit →
    literal_physical lit1 →
    ▷ l ↦{dq} #lit -∗
    ▷ (
      ( ⌜lit ≠ lit1⌝ -∗
        l ↦{dq} #lit -∗
        Φ #false
      ) ∧ (
        ⌜literal_eq lit lit1⌝ -∗
        l ↦{dq} #lit -∗
          ⌜dq = DfracOwn 1⌝ ∗
          l ↦{dq} #lit ∗
          ( l ↦ v2 -∗
            Φ #true
          )
      )
    ) -∗
    WP Cas #l #lit1 v2 @ E {{ Φ }}.
  Proof.
    iIntros "% % >Hl HΦ".
    iApply (wp_cas with "Hl"); [done.. |].
    iSplit.
    - iDestruct "HΦ" as "($ & _)".
    - iDestruct "HΦ" as "(_ & $)".
  Qed.
  Lemma wp_cas_suc l lit lit1 v2 E :
    literal_physical lit →
    lit = lit1 →
    {{{
      ▷ l ↦ #lit
    }}}
      Cas #l #lit1 v2 @ E
    {{{
      RET #true;
      l ↦ v2
    }}}.
  Proof.
    iIntros (Hlit ->) "%Φ >Hl HΦ".
    iApply (wp_cas_literal with "Hl"); [done.. |].
    iSteps.
  Qed.

  Lemma wp_faa l (i1 i2 : Z) E :
    {{{
      ▷ l ↦ #i1
    }}}
      Faa #l #i2 @ E
    {{{
      RET #i1;
      l ↦ #(i1 + i2)
    }}}.
  Proof.
    iIntros "%Φ >Hl HΦ".
    iApply wp_lift_atomic_base_step_no_fork; first done. iIntros "%σ1 %ns %κ %κ' %nt (Hσ & Hκ) !>".
    iDestruct (gen_heap_valid with "Hσ Hl") as %Hlookup.
    iSplit; first eauto with zebre. iIntros "%e2 %σ2 %es %Hstep !> _".
    invert_base_step.
    iMod (gen_heap_update with "Hσ Hl") as "($ & Hl)".
    iFrame. iSteps.
  Qed.

  Lemma wp_fork e E Φ :
    ▷ WP e @ ⊤ {{ _, True }} -∗
    ▷ Φ ()%V -∗
    WP Fork e @ E {{ Φ }}.
  Proof.
    iIntros "Hwp HΦ".
    iApply wp_lift_atomic_base_step; first done. iIntros "%σ1 %ns %κ %κ' %nt (Hσ1 & Hκ) !>".
    iSplit; first auto with zebre. iIntros "!> %v2 %σ2 %es %Hstep _".
    invert_base_step.
    iFrame. iSteps.
  Qed.

  Lemma wp_proph E :
    {{{ True }}}
      Proph @ E
    {{{ pvs p,
      RET #p;
      proph p pvs
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    iApply wp_lift_atomic_base_step_no_fork; first done. iIntros "%σ1 %ns %κ %κ' %nt (Hσ & Hκ) !>".
    iSplit; first eauto with zebre. iIntros "%e2 %σ2 %es %Hstep !> _".
    invert_base_step.
    iMod (proph_map_new_proph p with "Hκ") as "(Hκ & Hp)"; first done.
    iFrame. iSteps.
  Qed.

  Lemma resolve_reducible e σ p v :
    Atomic StronglyAtomic e →
    reducible e σ →
    reducible (Resolve e #p v) σ.
  Proof.
    intros A (κ & e' & σ' & es & H).
    exists (κ ++ [(p, (default v (to_val e'), v))]), e', σ', es.
    eapply (Ectx_step []); try done.
    assert (∃ w, Val w = e') as (w & <-).
    { unfold Atomic in A. apply (A σ e' κ σ' es) in H. unfold is_Some in H.
      destruct H as [w H]. exists w. simpl in H. by apply (of_to_val _ _ H).
    }
    simpl. constructor. by apply prim_step_to_val_is_base_step.
  Qed.
  Lemma step_resolve e v1 v2 σ1 κ e2 σ2 es :
    Atomic StronglyAtomic e →
    prim_step (Resolve e v1 v2) σ1 κ e2 σ2 es →
    base_step (Resolve e v1 v2) σ1 κ e2 σ2 es.
  Proof.
    intros A [K e1' e2' Hfill -> step]. simpl in *.
    induction K as [| k K _] using rev_ind.
    + simpl in *. subst. invert_base_step. constructor. done.
    + rewrite fill_app /= in Hfill. destruct k; inversion Hfill; subst; clear Hfill.
      - assert (fill_item k (fill K e1') = fill (K ++ [k]) e1') as Heq1; first by rewrite fill_app.
        assert (fill_item k (fill K e2') = fill (K ++ [k]) e2') as Heq2; first by rewrite fill_app.
        rewrite fill_app /=. rewrite Heq1 in A.
        assert (is_Some (to_val (fill (K ++ [k]) e2'))) as H.
        { eapply (A σ1 _ κ σ2 es), (Ectx_step (K ++ [k])); done. }
        destruct H as [v H]. apply to_val_fill_some in H. destruct H, K; done.
      - rename select (of_val v1 = _) into Hv1.
        assert (to_val (fill K e1') = Some v1) as Hfill_v1 by rewrite -Hv1 //.
        apply to_val_fill_some in Hfill_v1 as (-> & ->).
        invert_base_step.
      - rename select (of_val v2 = _) into Hv2.
        assert (to_val (fill K e1') = Some v2) as Hfill_v2 by rewrite -Hv2 //.
        apply to_val_fill_some in Hfill_v2 as (-> & ->).
        invert_base_step.
  Qed.
  Lemma wp_resolve e p v pvs E Φ :
    Atomic StronglyAtomic e →
    to_val e = None →
    proph p pvs -∗
    WP e @ E {{ res,
      ∀ pvs',
      ⌜pvs = (res, v) :: pvs'⌝ -∗
      proph p pvs' -∗
      Φ res
    }} -∗
    WP Resolve e #p v @ E {{ Φ }}.
  Proof.
    iIntros "%Hatomic %He Hp Hwp".
    rewrite !wp_unfold /wp_pre /= He. simpl in *.
    iIntros "%σ1 %ns %κ %κ' %nt (Hσ & Hκ)".
    destruct κ as [| (p' & (w' & v')) κ'' _] using rev_ind.
    - iMod ("Hwp" $! σ1 ns [] κ' nt with "[$Hσ $Hκ]") as "(%Hreducible & Hwp)".
      iSplitR. { iPureIntro. apply resolve_reducible; done. }
      iIntros "!> %e2 %σ2 %es %Hstep".
      exfalso. apply step_resolve in Hstep; last done.
      invert_base_step.
      destruct κ; done.
    - rewrite -assoc.
      iMod ("Hwp" $! σ1 ns _ _ nt with "[$Hσ $Hκ]") as "(%Hreducible & Hwp)".
      iSplitR. { iPureIntro. apply resolve_reducible; done. }
      iIntros "!> %e2 %σ2 %es %Hstep H£".
      apply step_resolve in Hstep; last done.
      invert_base_step. simplify_list_eq.
      iMod ("Hwp" $! (Val w') σ2 es with "[%] H£") as "Hwp".
      { eexists [] _ _; done. }
      do 2 iModIntro.
      iMod "Hwp" as "Hwp".
      iApply (step_fupdN_wand with "Hwp"). iIntros "!> > (($ & Hκ) & Hwp)".
      iMod (proph_map_resolve_proph p' (w', v') κ' with "[$Hκ $Hp]") as (vs' ->) "($ & Hp')".
      rewrite !wp_unfold /wp_pre /=.
      iDestruct "Hwp" as "(HΦ & $)".
      iSteps.
  Qed.
End zebre_G.
