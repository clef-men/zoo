From zoo Require Import
  prelude.
From zoo.common Require Import
  countable.
From zoo.iris.base_logic Require Import
  lib.auth_dgset
  lib.mono_set
  lib.saved_prop
  lib.twins.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  clst.
From zoo_saturn Require Import
  mpmc_stack_2.
From zoo_parabs Require Export
  base
  vertex__code.
From zoo_parabs Require Import
  vertex__types
  pool.
From zoo Require Import
  options.

Implicit Types closed : bool.
Implicit Types preds : nat.
Implicit Types vtx succ : location.
Implicit Types ctx run : val.

Inductive state :=
  | Init
  | Released
  | Running
  | Done.
Implicit Types state : state.

#[local] Instance state_inhabited : Inhabited state :=
  populate Init.
#[local] Instance state_eq_dec : EqDecision state :=
  ltac:(solve_decision).

Class VertexG Σ `{zoo_G : !ZooG Σ} := {
  #[local] vertex_G_stack_G :: MpmcStack2G Σ ;
  #[local] vertex_G_pool_G :: SchedulerG Σ ;
  #[local] vertex_G_saved_prop_G :: SavedPropG Σ ;
  #[local] vertex_G_dependencies_G :: MonoSetG Σ gname ;
  #[local] vertex_G_predecessors_G :: AuthDgsetG Σ gname ;
  #[local] vertex_G_state_G :: TwinsG Σ (leibnizO state) ;
}.

Definition vertex_Σ := #[
  mpmc_stack_2_Σ ;
  pool_Σ ;
  saved_prop_Σ ;
  mono_set_Σ gname ;
  auth_dgset_Σ gname ;
  twins_Σ (leibnizO state)
].
#[global] Instance subG_vertex_Σ Σ `{zoo_G : !ZooG Σ}:
  subG vertex_Σ Σ →
  VertexG Σ.
Proof.
  solve_inG.
Qed.

Section vertex_G.
  Context `{vertex_G : VertexG Σ}.

  Implicit Types P Q : iProp Σ.

  Record metadata := {
    metadata_task : val ;
    metadata_successors : val ;
    metadata_dependencies : gname ;
    metadata_predecessors : gname ;
    metadata_state : gname ;
  }.
  Implicit Types γ : metadata.

  #[local] Instance metadata_eq_dec : EqDecision metadata :=
    ltac:(solve_decision).
  #[local] Instance metadata_countable :
    Countable metadata.
  Proof.
    solve_countable.
  Qed.

  #[local] Definition dependencies' γ_dependencies closed Δ :=
    mono_set_auth γ_dependencies (if closed then DfracDiscarded else DfracOwn 1) Δ.
  #[local] Definition dependencies γ closed Δ :=
    dependencies' γ.(metadata_dependencies) closed Δ.
  #[local] Definition dependency' γ_dependencies δ :=
    mono_set_elem γ_dependencies δ.
  #[local] Definition dependency γ δ :=
    dependency' γ.(metadata_dependencies) δ.

  #[local] Definition predecessors' γ_predecessors Π :=
    auth_dgset_auth γ_predecessors (DfracOwn 1) Π.
  #[local] Definition predecessors γ Π :=
    predecessors' γ.(metadata_predecessors) Π.
  #[local] Definition predecessor' γ_predecessors π :=
    auth_dgset_frag γ_predecessors {[π]}.
  #[local] Definition predecessor γ π :=
    predecessor' γ.(metadata_predecessors) π.

  #[local] Definition state₁' γ_state state :=
    twins_twin1 γ_state (DfracOwn 1) state.
  #[local] Definition state₁ γ state :=
    state₁' γ.(metadata_state) state.
  #[local] Definition state₂' γ_state state :=
    twins_twin2 γ_state state.
  #[local] Definition state₂ γ state :=
    state₂' γ.(metadata_state) state.

  Definition vertex_init t task : iProp Σ :=
    ∃ vtx γ,
    ⌜t = #vtx⌝ ∗
    ⌜task = γ.(metadata_task)⌝ ∗
    meta vtx nroot γ ∗
    state₂ γ Init.

  #[local] Definition input' γ P : iProp Σ :=
    ∃ δ,
    saved_prop δ P ∗
    dependency γ δ ∗
    £ 1.
  Definition vertex_input t P : iProp Σ :=
    ∃ vtx γ,
    ⌜t = #vtx⌝ ∗
    meta vtx nroot γ ∗
    input' γ P.

  #[local] Definition inv_inner' (inv' : location → metadata → iProp Σ → iProp Σ) vtx γ P : iProp Σ :=
    ∃ state preds Δ Π,
    ⌜Δ ## Π⌝ ∗
    vtx.[preds] ↦ #preds ∗
    ([∗ set] δ ∈ Δ, ∃ P, saved_prop δ P ∗ □ P) ∗
    ([∗ set] π ∈ Π, ∃ P, saved_prop π P) ∗
    predecessors γ Π ∗
    state₁ γ state ∗
    match state with
    | Init =>
        ⌜preds = S (size Π)⌝ ∗
        dependencies γ false (Δ ∪ Π)
    | Released =>
        ⌜preds = size Π⌝ ∗
        state₂ γ Released ∗
        dependencies γ false (Δ ∪ Π) ∗
        ( ∀ ctx,
          pool_context_model ctx -∗
          □ (∀ Q E, input' γ Q ={E}=∗ □ Q) -∗
          WP γ.(metadata_task) ctx {{ res,
            pool_context_model ctx ∗
            ▷ □ P
          }}
        )
    | Running =>
        ⌜size Π = 0⌝
    | Done =>
        ⌜size Π = 0⌝ ∗
        □ P
    end ∗
    if decide (state = Done) then
      mpmc_stack_2_model γ.(metadata_successors) None
    else
      ∃ succs,
      mpmc_stack_2_model γ.(metadata_successors) (Some $ #@{location} <$> succs) ∗
      ( [∗ list] succ ∈ succs,
        ∃ γ_succ P_succ π,
        meta succ nroot γ_succ ∗
        inv' succ γ_succ P_succ ∗
        saved_prop π P ∗
        predecessor γ_succ π
      ).
  #[local] Definition inv_pre
  : (location -d> metadata -d> iProp Σ -d> iProp Σ) →
    location -d> metadata -d> iProp Σ -d> iProp Σ
  :=
    λ inv' vtx γ P, (
      vtx.[task] ↦□ γ.(metadata_task) ∗
      vtx.[succs] ↦□ γ.(metadata_successors) ∗
      mpmc_stack_2_inv γ.(metadata_successors) (nroot.@"successors") ∗
      inv (nroot.@"inv") (inv_inner' inv' vtx γ P)
    )%I.
  #[local] Instance inv_pre_contractive :
    Contractive inv_pre.
  Proof.
    rewrite /inv_pre /inv_inner' => n Ψ1 Ψ2 HΨ vtx γ P.
    repeat (apply HΨ || f_contractive || f_equiv).
  Qed.
  #[local] Definition inv' : location → metadata → iProp Σ → iProp Σ :=
    fixpoint inv_pre.
  #[local] Definition inv_inner :=
    inv_inner' inv'.
  Definition vertex_inv t P : iProp Σ :=
    ∃ vtx γ,
    ⌜t = #vtx⌝ ∗
    meta vtx nroot γ ∗
    inv' vtx γ P.

  #[local] Lemma inv'_unfold vtx γ P :
    inv' vtx γ P ⊣⊢
    inv_pre inv' vtx γ P.
  Proof.
    apply (fixpoint_unfold inv_pre).
  Qed.

  #[global] Instance vertex_init_timeless t task :
    Timeless (vertex_init t task).
  Proof.
    apply _.
  Qed.
  #[local] Instance inv'_persistent vtx γ P :
    Persistent (inv' vtx γ P).
  Proof.
    rewrite inv'_unfold. apply _.
  Qed.
  #[global] Instance vertex_inv_persistent t P :
    Persistent (vertex_inv t P).
  Proof.
    apply _.
  Qed.

  #[local] Lemma dependencies_alloc :
    ⊢ |==>
      ∃ γ_dependencies,
      dependencies' γ_dependencies false ∅.
  Proof.
    apply mono_set_alloc.
  Qed.
  #[local] Lemma dependencies_add {γ Δ} δ :
    dependencies γ false Δ ⊢ |==>
      dependencies γ false ({[δ]} ∪ Δ) ∗
      dependency γ δ.
  Proof.
    apply mono_set_insert'.
  Qed.
  #[local] Lemma dependencies_elem_of γ closed Δ δ :
    dependencies γ closed Δ -∗
    dependency γ δ -∗
    ⌜δ ∈ Δ⌝.
  Proof.
    apply mono_set_elem_valid.
  Qed.
  #[local] Lemma dependencies_close γ Δ :
    dependencies γ false Δ ⊢ |==>
    dependencies γ true Δ.
  Proof.
    apply mono_set_auth_persist.
  Qed.

  #[local] Lemma predecessors_alloc :
    ⊢ |==>
      ∃ γ_predecessors,
      predecessors' γ_predecessors ∅.
  Proof.
    apply auth_dgset_alloc_empty.
  Qed.
  #[local] Lemma predecessors_elem_of γ Π π :
    predecessors γ Π -∗
    predecessor γ π -∗
    ⌜π ∈ Π⌝.
  Proof.
    apply auth_dgset_elem_of.
  Qed.
  #[local] Lemma predecessors_add {γ Π} π :
    π ∉ Π →
    predecessors γ Π ⊢ |==>
      predecessors γ ({[π]} ∪ Π) ∗
      predecessor γ π.
  Proof.
    apply auth_dgset_update_alloc_singleton.
  Qed.
  #[local] Lemma predecessors_remove γ Π π :
    predecessors γ Π -∗
    predecessor γ π ==∗
      predecessors γ (Π ∖ {[π]}).
  Proof.
    apply auth_dgset_update_dealloc.
  Qed.

  #[local] Lemma state_alloc :
    ⊢ |==>
      ∃ γ_state,
      state₁' γ_state Init ∗
      state₂' γ_state Init.
  Proof.
    apply twins_alloc'.
  Qed.
  #[local] Lemma state_agree γ state1 state2 :
    state₁ γ state1 -∗
    state₂ γ state2 -∗
    ⌜state1 = state2⌝.
  Proof.
    apply: twins_agree_L.
  Qed.
  #[local] Lemma state_update {γ state1 state2} state :
    state₁ γ state1 -∗
    state₂ γ state2 ==∗
      state₁ γ state ∗
      state₂ γ state.
  Proof.
    apply twins_update'.
  Qed.

  Lemma vertex_create_spec P task :
    {{{
      True
    }}}
      vertex_create task
    {{{ t,
      RET t;
      vertex_inv t P ∗
      vertex_init t task
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_rec.
    wp_apply (mpmc_stack_2_create_spec with "[//]") as (succs) "(#Hsuccs_inv & Hsuccs_model)".
    wp_block vtx as "Hmeta" "(Hvtx_task & Hvtx_preds & Hvtx_succs & _)".
    iMod (pointsto_persist with "Hvtx_task") as "#Hvtx_task".
    iMod (pointsto_persist with "Hvtx_succs") as "#Hvtx_succs".

    iMod (saved_prop_alloc True) as "(%π & #Hπ)".
    iMod dependencies_alloc as "(%γ_dependencies & Hdeps)".
    iMod predecessors_alloc as "(%γ_predecessors & Hpreds)".
    iMod state_alloc as "(%γ_state & Hstate₁ & Hstate₂)".

    pose γ := {|
      metadata_task := task ;
      metadata_successors := succs ;
      metadata_dependencies := γ_dependencies ;
      metadata_predecessors := γ_predecessors ;
      metadata_state := γ_state ;
    |}.
    iMod (meta_set γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitR "Hstate₂".
    - iSteps. rewrite inv'_unfold. iStep 3.
      iApply inv_alloc.
      iExists Init, 1, ∅, ∅. iFrame.
      rewrite !big_sepS_empty size_empty. iStep 5.
      iExists []. iSteps.
    - iSteps. iExists γ. iSteps.
  Qed.

  Lemma vertex_precede_spec t1 P1 t2 P2 task :
    {{{
      vertex_inv t1 P1 ∗
      vertex_inv t2 P2 ∗
      vertex_init t2 task
    }}}
      vertex_precede t1 t2
    {{{
      RET ();
      vertex_init t2 task ∗
      vertex_input t2 P1
    }}}.
  Proof.
    rewrite /vertex_inv. setoid_rewrite inv'_unfold.
    iIntros "%Φ ((%vtx1 & %γ1 & -> & #Hmeta1 & #Hvtx1_task & #Hvtx1_succs & #Hsuccs1_inv & #Hinv1) & (%vtx2 & %γ2 & -> & #Hmeta2 & #Hvtx2_task & #Hvtx2_succs & #Hsuccs2_inv & #Hinv2) & (%_vtx2 & %_γ2 & %Heq & -> & _Hmeta2 & Hstate₂)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta2 _Hmeta2") as %<-. iClear "_Hmeta2".

    wp_rec. wp_load.

    awp_smart_apply (mpmc_stack_2_is_closed_spec with "Hsuccs1_inv") without "Hstate₂ HΦ".
    iInv "Hinv1" as "(%state & %preds & %Δ & %Π & >%HΔ & Hvtx1_preds & HΔ & HΠ & Hpreds & Hstate₁ & Hstate & Hsuccs)".
    case_decide as Hstate; first subst.

    - iDestruct "Hstate" as "(>%HΠ & #HP1)".
      iDestruct "Hsuccs" as ">Hsuccs_model".
      iAaccIntro with "Hsuccs_model"; first iSteps. iIntros "Hsuccs_model !>".
      iSplitL; first iSteps.
      iIntros "{%} H£ (Hstate₂ & HΦ)".

      iApply fupd_wp.
      iInv "Hinv2" as "(%state & %preds & %Δ & %Π & >%HΔ & Hvtx2_preds & HΔ & HΠ & >Hpreds & >Hstate₁ & Hstate & Hsuccs)".
      iDestruct (state_agree with "Hstate₁ Hstate₂") as %->.
      iDestruct "Hstate" as ">(%Hpreds & Hdeps)".
      iMod (saved_prop_alloc_cofinite (Δ ∪ Π) P1) as "(%π & %Hπ & #Hπ)".
      apply not_elem_of_union in Hπ as (Hπ_Δ & Hπ_Π).
      iMod (dependencies_add π with "Hdeps") as "(Hdeps & #Hdep)".
      iSplitR "Hstate₂ H£ HΦ".
      { iExists Init, preds, ({[π]} ∪ Δ), Π.
        rewrite big_sepS_union; first set_solver. rewrite big_sepS_singleton.
        assert ({[π]} ∪ (Δ ∪ Π) = ({[π]} ∪ Δ) ∪ Π) as -> by set_solver.
        iSteps. iPureIntro. set_solver.
      }
      iSteps.

    - iDestruct "Hsuccs" as "(%succs & >Hsuccs_model & Hsuccs)".
      iAaccIntro with "Hsuccs_model"; iIntros "Hsuccs_model !>".
      { iFrame. rewrite decide_False //. iSteps. }
      iSplitL. { iSteps. rewrite decide_False //. iSteps. }
      iIntros "H£ (Hstate₂ & HΦ)". wp_pures. clear.

      wp_bind (FAA _ _).
      iInv "Hinv2" as "(%state & %preds & %Δ & %Π & >%HΔ & Hvtx2_preds & HΔ & HΠ & Hpreds & Hstate₁ & Hstate & Hsuccs)".
      wp_faa.
      iDestruct (state_agree with "Hstate₁ Hstate₂") as %->.
      iDestruct "Hstate" as "(%Hpreds & Hdeps)".
      iMod (saved_prop_alloc_cofinite (Δ ∪ Π) P1) as "(%π & %Hπ & #Hπ)".
      apply not_elem_of_union in Hπ as (Hπ_Δ & Hπ_Π).
      iMod (predecessors_add with "Hpreds") as "(Hpreds & Hpred)"; first done.
      iMod (dependencies_add π with "Hdeps") as "(Hdeps & #Hdep)".
      iSplitR "Hstate₂ Hpred H£ HΦ".
      { iExists Init, (S preds), Δ, ({[π]} ∪ Π).
        rewrite big_sepS_union; first set_solver. rewrite big_sepS_singleton.
        assert ({[π]} ∪ (Δ ∪ Π) = Δ ∪ ({[π]} ∪ Π)) as -> by set_solver.
        iSteps; iPureIntro.
        - set_solver.
        - rewrite size_union; first set_solver.
          rewrite size_singleton. lia.
      }
      iModIntro. wp_pures. clear.

      awp_apply (mpmc_stack_2_push_spec with "Hsuccs1_inv") without "Hstate₂ H£ HΦ".
      iInv "Hinv1" as "(%state & %preds & %Δ & %Π & >%HΔ & Hvtx1_preds & HΔ & HΠ & Hpreds & Hstate₁ & Hstate & Hsuccs)".
      case_decide as Hstate; first subst.

      + iDestruct "Hstate" as "(>%HΠ & #HP1)".
        iDestruct "Hsuccs" as ">Hsuccs_model".
        iAaccIntro with "Hsuccs_model"; first iSteps. iIntros "Hsuccs_model !>".
        iSplitR "Hpred"; first iSteps.
        iIntros "_ (Hstate₂ & H£ & HΦ) {%}".

        wp_pures.

        wp_bind (FAA _ _).
        iInv "Hinv2" as "(%state & %preds & %Δ & %Π & >%HΔ & Hvtx2_preds & HΔ & HΠ & Hpreds & Hstate₁ & Hstate & Hsuccs)".
        wp_faa.
        iDestruct (state_agree with "Hstate₁ Hstate₂") as %->.
        iDestruct "Hstate" as "(%Hpreds & Hdeps)".
        iDestruct (predecessors_elem_of with "Hpreds Hpred") as %Hπ.
        iMod (predecessors_remove with "Hpreds Hpred") as "Hpreds".
        iDestruct (big_sepS_delete with "HΠ") as "(_ & HΠ)"; first done.
        iSplitR "Hstate₂ H£ HΦ".
        { iExists Init, (preds - 1), ({[π]} ∪ Δ), (Π ∖ {[π]}).
          rewrite big_sepS_union; first set_solver. rewrite big_sepS_singleton.
          assert ({[π]} ∪ Δ ∪ Π ∖ {[π]} = Δ ∪ Π) as ->.
          { apply leibniz_equiv. rewrite (comm (∪) {[_]}) -assoc -union_difference_singleton_L //. }
          iSteps; iPureIntro.
          - set_solver.
          - rewrite size_difference; first set_solver. rewrite size_singleton.
            apply non_empty_inhabited in Hπ as ?%size_non_empty_iff. lia.
        }
        iSteps.

      + iDestruct "Hsuccs" as "(%succs & >Hsuccs_model & Hsuccs)".
        iAaccIntro with "Hsuccs_model"; iIntros "Hsuccs_model !>".
        { iFrame. rewrite decide_False //. iSteps. }
        iSplitL.
        { iSteps. rewrite decide_False //. iExists (vtx2 :: succs). iFrame.
          setoid_rewrite inv'_unfold. iSteps.
        }
        iSteps.
  Qed.

  #[local] Lemma vertex_release_run_spec :
    ⊢ (
      ∀ ctx vtx γ P π Q,
      {{{
        pool_context_model ctx ∗
        inv' vtx γ P ∗
        saved_prop π Q ∗
        predecessor γ π ∗
        □ Q
      }}}
        vertex_release ctx #vtx
      {{{
        RET ();
        pool_context_model ctx
      }}}
    ) ∧ (
      ∀ ctx vtx γ P,
      {{{
        pool_context_model ctx ∗
        inv' vtx γ P ∗
        state₂ γ Running ∗
        ( pool_context_model ctx -∗
          WP γ.(metadata_task) ctx {{ res,
            pool_context_model ctx ∗
            ▷ □ P
          }}
        )
      }}}
        vertex_run ctx #vtx
      {{{
        RET ();
        pool_context_model ctx
      }}}
    ).
  Proof.
    iLöb as "HLöb".
    iDestruct "HLöb" as "(IHrelease & IHrun)".
    iSplit.

    { iClear "IHrelease".
      setoid_rewrite inv'_unfold.
      iIntros "%ctx %vtx %γ %P %π %Q !> %Φ (Hctx & (#Hvtx_task & #Hvtx_succs & #Hsuccs_inv & #Hinv) & #Hπ & Hpred & #HQ) HΦ".

      wp_recs. wp_pures.

      wp_bind (FAA _ _).
      iInv "Hinv" as "(%state & %preds & %Δ & %Π & >%HΔ & Hvtx_preds & HΔ & HΠ & Hpreds & Hstate₁ & Hstate & Hsuccs)".
      wp_faa.
      iDestruct (predecessors_elem_of with "Hpreds Hpred") as %Hπ.
      destruct state.
      3: iDestruct "Hstate" as "%HΠ".
      4: iDestruct "Hstate" as "(%HΠ & _)".
      3,4: apply size_empty_inv in HΠ; set_solver.
      all: iMod (predecessors_remove with "Hpreds Hpred") as "Hpreds".
      all: iDestruct (big_sepS_delete with "HΠ") as "(_ & HΠ)"; first done.

      - iDestruct "Hstate" as "(%Hpreds & Hdeps)".
        iSplitR "Hctx HΦ".
        { iExists Init, (preds - 1), ({[π]} ∪ Δ), (Π ∖ {[π]}).
          rewrite big_sepS_union; first set_solver. rewrite big_sepS_singleton.
          assert ({[π]} ∪ Δ ∪ Π ∖ {[π]} = Δ ∪ Π) as ->.
          { apply leibniz_equiv. rewrite (comm (∪) {[_]}) -assoc -union_difference_singleton_L //. }
          iSteps; iPureIntro.
          - set_solver.
          - rewrite size_difference; first set_solver. rewrite size_singleton.
            apply non_empty_inhabited in Hπ as ?%size_non_empty_iff. lia.
        }
        assert (preds ≠ 1).
        { apply non_empty_inhabited in Hπ as ?%size_non_empty_iff. lia. }
        iSteps.

      - iDestruct "Hstate" as "(%Hpreds & Hstate₂ & Hdeps & Htask)".
        destruct (decide (preds = 1)) as [-> | ?].

        + assert (Π = {[π]}) as ->.
          { apply symmetry, size_1_elem_of in Hpreds as (_π & Heq). set_solver. }
          rewrite difference_diag_L.
          iMod (state_update Running with "Hstate₁ Hstate₂") as "(Hstate₁ & Hstate₂)".
          iDestruct "HΔ" as "#HΔ".
          iSplitR "Hctx Hstate₂ Hdeps Htask HΦ".
          { iExists Running, 0, ({[π]} ∪ Δ), ∅.
            rewrite big_sepS_union; first set_solver. rewrite big_sepS_singleton.
            iSteps.
          }
          iDestruct (big_sepS_insert_2' with "[] HΔ") as "HΔ'"; first iSteps.
          iClear "Hπ HQ HΔ". remember (Δ ∪ {[π]}) as Δ'.
          iMod (dependencies_close with "Hdeps") as "#Hdeps".
          iIntros "!> {%}".

          wp_smart_apply (pool_silent_async_spec with "[$Hctx Hstate₂ Hdeps Htask]"); last iSteps. iIntros "{%} %ctx Hctx".
          wp_smart_apply ("IHrun" with "[-]"); last iSteps. iStep 4 as "Hctx".
          wp_apply ("Htask" with "Hctx"). iIntros "!> %Q %E (%δ & #Hδ & #Hdep & H£)".
          iDestruct (dependencies_elem_of with "Hdeps Hdep") as %Hδ.
          iDestruct (big_sepS_elem_of with "HΔ'") as "(%_Q & _Hδ & #HQ)"; first done.
          iDestruct (saved_prop_agree with "Hδ _Hδ") as "-#Heq".
          iMod (lc_fupd_elim_later with "H£ Heq") as "Heq".
          iRewrite "Heq". iSteps.

        + iSplitR "Hctx HΦ".
          { iExists Released, (preds - 1), ({[π]} ∪ Δ), (Π ∖ {[π]}).
            rewrite big_sepS_union; first set_solver. rewrite big_sepS_singleton.
            assert ({[π]} ∪ Δ ∪ Π ∖ {[π]} = Δ ∪ Π) as ->.
            { apply leibniz_equiv. rewrite (comm (∪) {[_]}) -assoc -union_difference_singleton_L //. }
            assert (1 < preds).
            { apply non_empty_inhabited in Hπ as ?%size_non_empty_iff. lia. }
            iFrameSteps; iPureIntro.
            - set_solver.
            - rewrite size_difference; first set_solver. rewrite size_singleton.
              apply non_empty_inhabited in Hπ as ?%size_non_empty_iff. lia.
          }
          iSteps.
    }

    { iClear "IHrun".
      setoid_rewrite inv'_unfold.
      iIntros "%ctx %vtx %γ %P !> %Φ (Hctx & (#Hvtx_task & #Hvtx_succs & #Hsuccs_inv & #Hinv) & Hstate₂ & Htask) HΦ".

      wp_recs. wp_load.
      wp_apply (wp_wand with "(Htask Hctx)") as (res) "(Hctx & #HP)".
      wp_load.

      awp_smart_apply (mpmc_stack_2_close_spec with "Hsuccs_inv") without "Hctx HΦ".
      iInv "Hinv" as "(%state & %preds & %Δ & %Π & >%HΔ & Hvtx_preds & HΔ & HΠ & Hpreds & >Hstate₁ & Hstate & Hsuccs)".
      iDestruct (state_agree with "Hstate₁ Hstate₂") as %->.
      iDestruct "Hstate" as ">%HΠ".
      iDestruct "Hsuccs" as "(%succs & >Hsuccs_model & Hsuccs)".
      iAaccIntro with "Hsuccs_model"; iIntros "Hsuccs_model"; first iFrameSteps.
      iMod (state_update Done with "Hstate₁ Hstate₂") as "(Hstate₁ & _)".
      iSplitR "Hsuccs"; first iSteps.
      iIntros "!> H£ (Hctx & HΦ) {%}".

      iMod (lc_fupd_elim_later with "H£ Hsuccs") as "Hsuccs".
      wp_smart_apply (clst_iter_spec (λ _, pool_context_model ctx) with "[$Hctx Hsuccs]"); [done | | iSteps].
      rewrite big_sepL_fmap.
      iApply (big_sepL_impl with "Hsuccs"). iIntros "!> %i %succ _ (%γ_succ & %P_succ & %π & #Hmeta_succ & #Hinv_succ & #Hπ & Hpred) Hctx".
      wp_smart_apply ("IHrelease" with "[$Hctx $Hπ $Hpred $HP]"); last iSteps.
      iApply (inv'_unfold with "Hinv_succ").
    }
  Qed.
  #[local] Lemma vertex_release_spec' ctx vtx γ P π Q :
    {{{
      pool_context_model ctx ∗
      inv' vtx γ P ∗
      saved_prop π Q ∗
      predecessor γ π ∗
      □ Q
    }}}
      vertex_release ctx #vtx
    {{{
      RET ();
      pool_context_model ctx
    }}}.
  Proof.
    iDestruct vertex_release_run_spec as "(H & _)".
    iApply "H".
  Qed.
  Lemma vertex_release_spec ctx t P task :
    {{{
      pool_context_model ctx ∗
      vertex_inv t P ∗
      vertex_init t task ∗
      ( ∀ ctx,
        pool_context_model ctx -∗
        □ (∀ Q E, vertex_input t Q ={E}=∗ □ Q) -∗
        WP task ctx {{ res,
          pool_context_model ctx ∗
          ▷ □ P
        }}
      )
    }}}
      vertex_release ctx t
    {{{
      RET ();
      pool_context_model ctx
    }}}.
  Proof.
    rewrite /vertex_inv. setoid_rewrite inv'_unfold.
    iIntros "%Φ (Hctx & (%vtx & %γ & -> & #Hmeta & #Hvtx_task & #Hvtx_succs & #Hsuccs_inv & #Hinv) & (%_vtx & %_γ & %Heq & -> & _Hmeta & Hstate₂) & Htask) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".

    iApply fupd_wp.
    iInv "Hinv" as "(%state & %preds & %Δ & %Π & >%HΔ & Hvtx_preds & HΔ & HΠ & >Hpreds & >Hstate₁ & Hstate & Hsuccs)".
    iDestruct (state_agree with "Hstate₁ Hstate₂") as %->.
    iMod (state_update Released with "Hstate₁ Hstate₂") as "(Hstate₁ & Hstate₂)".
    iDestruct "Hstate" as ">(%Hpreds & Hdeps)".
    iMod (saved_prop_alloc_cofinite (Δ ∪ Π) True) as "(%π & %Hπ & #Hπ)".
    apply not_elem_of_union in Hπ as (Hπ_Δ & Hπ_Π).
    iMod (predecessors_add with "Hpreds") as "(Hpreds & Hpred)"; first done.
    iMod (dependencies_add π with "Hdeps") as "(Hdeps & #Hdep_π)".
    iSplitR "Hctx Hpred HΦ".
    { iExists Released, preds, Δ, ({[π]} ∪ Π).
      rewrite big_sepS_union; first set_solver. rewrite big_sepS_singleton.
      assert ({[π]} ∪ (Δ ∪ Π) = Δ ∪ ({[π]} ∪ Π)) as -> by set_solver.
      iFrame. iSplitR.
      { iPureIntro. set_solver. }
      iStep. iSplitR.
      { rewrite size_union; first set_solver. rewrite size_singleton //. }
      iIntros "{%} !> !> %ctx Hctx #H".
      iApply (wp_wand with "(Htask Hctx [])"); last iSteps.
      iIntros "!> %Q %E (%_vtx & %_γ & %Heq & _Hmeta & Hinput)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iApply ("H" with "Hinput").
    }
    iIntros "!> !> {%}".

    wp_smart_apply (vertex_release_spec' with "[$Hctx $Hπ $Hpred] HΦ").
    rewrite inv'_unfold. iSteps.
  Qed.
End vertex_G.

#[global] Opaque vertex_create.
#[global] Opaque vertex_precede.
#[global] Opaque vertex_release.

#[global] Opaque vertex_inv.
#[global] Opaque vertex_init.
#[global] Opaque vertex_input.
