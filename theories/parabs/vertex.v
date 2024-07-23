(* Based on:
   https://inria.hal.science/hal-01409022v1
*)

From zoo Require Import
  prelude.
From zoo.iris.base_logic Require Import
  lib.auth_dgset
  lib.mono_set
  lib.saved_prop
  lib.twins.
From zoo.language Require Import
  notations
  diaframe.
From zoo.std Require Import
  clst.
From zoo.saturn Require Import
  mpmc_stack_2.
From zoo.parabs Require Export
  base.
From zoo.parabs Require Import
  ws_hub
  pool.
From zoo Require Import
  options.

Implicit Types closed : bool.
Implicit Types preds : nat.
Implicit Types vtx succ : location.
Implicit Types run : val.

#[local] Notation "'task'" := (
  in_type "t" 0
)(in custom zoo_field
).
#[local] Notation "'preds'" := (
  in_type "t" 1
)(in custom zoo_field
).
#[local] Notation "'succs'" := (
  in_type "t" 2
)(in custom zoo_field
).

Definition vertex_create : val :=
  λ: "task",
    { "task",
      #1,
      mpmc_stack_create ()
    }.

Definition vertex_precede : val :=
  λ: "t1" "t2",
    let: "succs1" := "t1".{succs} in
    ifnot: mpmc_stack_is_closed "succs1" then (
      Faa "t2".[preds] #1 ;;
      if: mpmc_stack_push "succs1" "t2" then (
        Faa "t2".[preds] #(-1) ;;
        ()
      )
    ).

Section ws_hub.
  Context `{zoo_G : !ZooG Σ}.
  Context (ws_hub : ws_hub Σ).

  #[local] Definition vertex_propagate : val :=
    λ: "ctx" "t" "run",
      if: Faa "t".[preds] #(-1) = #1 then
        pool_silent_async ws_hub "ctx" (λ: "ctx", "run" "ctx" "t").
  #[local] Definition vertex_run : val :=
    rec: "vertex_run" "ctx" "t" :=
      "t".{task} "ctx" ;;
      clst_iter (mpmc_stack_close "t".{succs}) (λ: "t'",
        vertex_propagate "ctx" "t'" "vertex_run"
      ).
  Definition vertex_release : val :=
    λ: "ctx" "t",
      vertex_propagate "ctx" "t" vertex_run.
End ws_hub.

Inductive vertex_state :=
  | VertexInit
  | VertexReleased
  | VertexRunning
  | VertexDone.
Implicit Types state : vertex_state.

#[local] Instance vertex_state_inhabited : Inhabited vertex_state :=
  populate VertexInit.
#[local] Instance vertex_eq_dec : EqDecision vertex_state :=
  ltac:(solve_decision).

Class VertexG Σ `{zoo_G : !ZooG Σ} := {
  #[local] vertex_G_stack_G :: MpmcStackG Σ ;
  #[local] vertex_G_pool_G :: SchedulerG Σ ;
  #[local] vertex_G_saved_prop_G :: SavedPropG Σ ;
  #[local] vertex_G_dependencies_G :: MonoSetG Σ gname ;
  #[local] vertex_G_predecessors_G :: AuthDgsetG Σ gname ;
  #[local] vertex_G_state_G :: TwinsG Σ (leibnizO vertex_state) ;
}.

Definition vertex_Σ := #[
  mpmc_stack_Σ ;
  pool_Σ ;
  saved_prop_Σ ;
  mono_set_Σ gname ;
  auth_dgset_Σ gname ;
  twins_Σ (leibnizO vertex_state)
].
#[global] Instance subG_vertex_Σ Σ `{zoo_G : !ZooG Σ}:
  subG vertex_Σ Σ →
  VertexG Σ.
Proof.
  solve_inG.
Qed.

Section vertex_G.
  Context `{vertex_G : VertexG Σ}.
  Context (ws_hub : ws_hub Σ).

  Implicit Types P Q : iProp Σ.

  Record vertex_meta := {
    vertex_meta_task : val ;
    vertex_meta_successors : val ;
    vertex_meta_dependencies : gname ;
    vertex_meta_predecessors : gname ;
    vertex_meta_state : gname ;
  }.
  Implicit Types γ : vertex_meta.

  #[local] Instance vertex_meta_eq_dec : EqDecision vertex_meta :=
    ltac:(solve_decision).
  #[local] Instance vertex_meta_countable :
    Countable vertex_meta.
  Proof.
    pose encode γ := (
      γ.(vertex_meta_task),
      γ.(vertex_meta_successors),
      γ.(vertex_meta_dependencies),
      γ.(vertex_meta_predecessors),
      γ.(vertex_meta_state)
    ).
    pose decode := λ '(task, succs, γ_dependencies, γ_predecessors, γ_state), {|
      vertex_meta_task := task ;
      vertex_meta_successors := succs ;
      vertex_meta_dependencies := γ_dependencies ;
      vertex_meta_predecessors := γ_predecessors ;
      vertex_meta_state := γ_state ;
    |}.
    refine (inj_countable' encode decode _). intros []. done.
  Qed.

  #[local] Definition vertex_dependencies' γ_dependencies closed Δ :=
    mono_set_auth γ_dependencies (if closed then DfracDiscarded else DfracOwn 1) Δ.
  #[local] Definition vertex_dependencies γ closed Δ :=
    vertex_dependencies' γ.(vertex_meta_dependencies) closed Δ.
  #[local] Definition vertex_dependency' γ_dependencies δ :=
    mono_set_elem γ_dependencies δ.
  #[local] Definition vertex_dependency γ δ :=
    vertex_dependency' γ.(vertex_meta_dependencies) δ.

  #[local] Definition vertex_predecessors' γ_predecessors Π :=
    auth_dgset_auth γ_predecessors (DfracOwn 1) Π.
  #[local] Definition vertex_predecessors γ Π :=
    vertex_predecessors' γ.(vertex_meta_predecessors) Π.
  #[local] Definition vertex_predecessor' γ_predecessors π :=
    auth_dgset_frag γ_predecessors {[π]}.
  #[local] Definition vertex_predecessor γ π :=
    vertex_predecessor' γ.(vertex_meta_predecessors) π.

  #[local] Definition vertex_state₁' γ_state state :=
    twins_twin1 γ_state (DfracOwn 1) state.
  #[local] Definition vertex_state₁ γ state :=
    vertex_state₁' γ.(vertex_meta_state) state.
  #[local] Definition vertex_state₂' γ_state state :=
    twins_twin2 γ_state state.
  #[local] Definition vertex_state₂ γ state :=
    vertex_state₂' γ.(vertex_meta_state) state.

  Definition vertex_init t task : iProp Σ :=
    ∃ vtx γ,
    ⌜t = #vtx⌝ ∗
    ⌜task = γ.(vertex_meta_task)⌝ ∗
    meta vtx nroot γ ∗
    vertex_state₂ γ VertexInit.

  #[local] Definition vertex_input' γ P : iProp Σ :=
    ∃ δ,
    saved_prop δ P ∗
    vertex_dependency γ δ ∗
    £ 1.
  Definition vertex_input t P : iProp Σ :=
    ∃ vtx γ,
    ⌜t = #vtx⌝ ∗
    meta vtx nroot γ ∗
    vertex_input' γ P.

  #[local] Definition vertex_inv_inner' (vertex_inv' : location → vertex_meta → iProp Σ → iProp Σ) vtx γ P : iProp Σ :=
    ∃ state preds Δ Π,
    ⌜Δ ## Π⌝ ∗
    vtx.[preds] ↦ #preds ∗
    ([∗ set] δ ∈ Δ, ∃ P, saved_prop δ P ∗ □ P) ∗
    ([∗ set] π ∈ Π, ∃ P, saved_prop π P) ∗
    vertex_predecessors γ Π ∗
    vertex_state₁ γ state ∗
    match state with
    | VertexInit =>
        ⌜preds = S (size Π)⌝ ∗
        vertex_dependencies γ false (Δ ∪ Π)
    | VertexReleased =>
        ⌜preds = size Π⌝ ∗
        vertex_state₂ γ VertexReleased ∗
        vertex_dependencies γ false (Δ ∪ Π) ∗
        ( ∀ ctx,
          pool_context ws_hub ctx -∗
          □ (∀ Q E, vertex_input' γ Q ={E}=∗ □ Q) -∗
          WP γ.(vertex_meta_task) ctx {{ res,
            pool_context ws_hub ctx ∗
            ▷ □ P
          }}
        )
    | VertexRunning =>
        ⌜size Π = 0⌝
    | VertexDone =>
        ⌜size Π = 0⌝ ∗
        □ P
    end ∗
    if decide (state = VertexDone) then
      mpmc_stack_model γ.(vertex_meta_successors) None
    else
      ∃ succs,
      mpmc_stack_model γ.(vertex_meta_successors) (Some $ #@{location} <$> succs) ∗
      ( [∗ list] succ ∈ succs,
        ∃ γ_succ P_succ π,
        meta succ nroot γ_succ ∗
        vertex_inv' succ γ_succ P_succ ∗
        saved_prop π P ∗
        vertex_predecessor γ_succ π
      ).
  #[local] Definition vertex_inv_pre
  : (location -d> vertex_meta -d> iProp Σ -d> iProp Σ) →
    location -d> vertex_meta -d> iProp Σ -d> iProp Σ
  :=
    λ vertex_inv' vtx γ P, (
      vtx.[task] ↦□ γ.(vertex_meta_task) ∗
      vtx.[succs] ↦□ γ.(vertex_meta_successors) ∗
      mpmc_stack_inv γ.(vertex_meta_successors) (nroot.@"successors") ∗
      inv (nroot.@"inv") (vertex_inv_inner' vertex_inv' vtx γ P)
    )%I.
  #[local] Instance vertex_inv_pre_contractive :
    Contractive vertex_inv_pre.
  Proof.
    rewrite /vertex_inv_pre /vertex_inv_inner' => n Ψ1 Ψ2 HΨ vtx γ P.
    repeat (apply HΨ || f_contractive || f_equiv).
  Qed.
  #[local] Definition vertex_inv' : location → vertex_meta → iProp Σ → iProp Σ :=
    fixpoint vertex_inv_pre.
  #[local] Definition vertex_inv_inner :=
    vertex_inv_inner' vertex_inv'.
  Definition vertex_inv t P : iProp Σ :=
    ∃ vtx γ,
    ⌜t = #vtx⌝ ∗
    meta vtx nroot γ ∗
    vertex_inv' vtx γ P.

  #[local] Lemma vertex_inv'_unfold vtx γ P :
    vertex_inv' vtx γ P ⊣⊢
    vertex_inv_pre vertex_inv' vtx γ P.
  Proof.
    apply (fixpoint_unfold vertex_inv_pre).
  Qed.

  #[global] Instance vertex_init_timeless t task :
    Timeless (vertex_init t task).
  Proof.
    apply _.
  Qed.
  #[local] Instance vertex_inv'_persistent vtx γ P :
    Persistent (vertex_inv' vtx γ P).
  Proof.
    rewrite vertex_inv'_unfold. apply _.
  Qed.
  #[global] Instance vertex_inv_persistent t P :
    Persistent (vertex_inv t P).
  Proof.
    apply _.
  Qed.

  #[local] Lemma vertex_dependencies_alloc :
    ⊢ |==>
      ∃ γ_dependencies,
      vertex_dependencies' γ_dependencies false ∅.
  Proof.
    apply mono_set_alloc.
  Qed.
  #[local] Lemma vertex_dependencies_add {γ Δ} δ :
    vertex_dependencies γ false Δ ⊢ |==>
      vertex_dependencies γ false ({[δ]} ∪ Δ) ∗
      vertex_dependency γ δ.
  Proof.
    apply mono_set_insert'.
  Qed.
  #[local] Lemma vertex_dependencies_elem_of γ closed Δ δ :
    vertex_dependencies γ closed Δ -∗
    vertex_dependency γ δ -∗
    ⌜δ ∈ Δ⌝.
  Proof.
    apply mono_set_elem_valid.
  Qed.
  #[local] Lemma vertex_dependencies_close γ Δ :
    vertex_dependencies γ false Δ ⊢ |==>
    vertex_dependencies γ true Δ.
  Proof.
    apply mono_set_auth_persist.
  Qed.

  #[local] Lemma vertex_predecessors_alloc :
    ⊢ |==>
      ∃ γ_predecessors,
      vertex_predecessors' γ_predecessors ∅.
  Proof.
    apply auth_dgset_alloc.
  Qed.
  #[local] Lemma vertex_predecessors_elem_of γ Π π :
    vertex_predecessors γ Π -∗
    vertex_predecessor γ π -∗
    ⌜π ∈ Π⌝.
  Proof.
    apply auth_dgset_elem_of.
  Qed.
  #[local] Lemma vertex_predecessors_add {γ Π} π :
    π ∉ Π →
    vertex_predecessors γ Π ⊢ |==>
      vertex_predecessors γ ({[π]} ∪ Π) ∗
      vertex_predecessor γ π.
  Proof.
    apply auth_dgset_update_alloc_singleton.
  Qed.
  #[local] Lemma vertex_predecessors_remove γ Π π :
    vertex_predecessors γ Π -∗
    vertex_predecessor γ π ==∗
      vertex_predecessors γ (Π ∖ {[π]}).
  Proof.
    apply auth_dgset_update_dealloc.
  Qed.

  #[local] Lemma vertex_state_alloc :
    ⊢ |==>
      ∃ γ_state,
      vertex_state₁' γ_state VertexInit ∗
      vertex_state₂' γ_state VertexInit.
  Proof.
    apply twins_alloc'.
  Qed.
  #[local] Lemma vertex_state_agree γ state1 state2 :
    vertex_state₁ γ state1 -∗
    vertex_state₂ γ state2 -∗
    ⌜state1 = state2⌝.
  Proof.
    apply: twins_agree_L.
  Qed.
  #[local] Lemma vertex_state_update {γ state1 state2} state :
    vertex_state₁ γ state1 -∗
    vertex_state₂ γ state2 ==∗
      vertex_state₁ γ state ∗
      vertex_state₂ γ state.
  Proof.
    apply twins_update'.
  Qed.

  Lemma vertex_create_spec P task :
    {{{ True }}}
      vertex_create task
    {{{ t,
      RET t;
      vertex_inv t P ∗
      vertex_init t task
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_rec.
    wp_apply (mpmc_stack_create_spec with "[//]") as (succs) "(#Hsuccs_inv & Hsuccs_model)".
    wp_record vtx as "Hmeta" "(Hvtx_task & Hvtx_preds & Hvtx_succs & _)".
    iMod (pointsto_persist with "Hvtx_task") as "#Hvtx_task".
    iMod (pointsto_persist with "Hvtx_succs") as "#Hvtx_succs".

    iMod (saved_prop_alloc True) as "(%π & #Hπ)".
    iMod vertex_dependencies_alloc as "(%γ_dependencies & Hdeps)".
    iMod vertex_predecessors_alloc as "(%γ_predecessors & Hpreds)".
    iMod vertex_state_alloc as "(%γ_state & Hstate₁ & Hstate₂)".

    pose γ := {|
      vertex_meta_task := task ;
      vertex_meta_successors := succs ;
      vertex_meta_dependencies := γ_dependencies ;
      vertex_meta_predecessors := γ_predecessors ;
      vertex_meta_state := γ_state ;
    |}.
    iMod (meta_set _ _ γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitR "Hstate₂".
    - iSteps. rewrite vertex_inv'_unfold. iStep 3.
      iApply inv_alloc.
      iExists VertexInit, 1, ∅, ∅. iFrame.
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
    rewrite /vertex_inv. setoid_rewrite vertex_inv'_unfold.
    iIntros "%Φ ((%vtx1 & %γ1 & -> & #Hmeta1 & #Hvtx1_task & #Hvtx1_succs & #Hsuccs1_inv & #Hinv1) & (%vtx2 & %γ2 & -> & #Hmeta2 & #Hvtx2_task & #Hvtx2_succs & #Hsuccs2_inv & #Hinv2) & (%_vtx2 & %_γ2 & %Heq & -> & _Hmeta2 & Hstate₂)) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta2 _Hmeta2") as %<-. iClear "_Hmeta2".

    wp_rec. wp_load.

    awp_smart_apply (mpmc_stack_is_closed_spec with "Hsuccs1_inv") without "Hstate₂ HΦ".
    iInv "Hinv1" as "(%state & %preds & %Δ & %Π & >%HΔ & Hvtx1_preds & HΔ & HΠ & Hpreds & Hstate₁ & Hstate & Hsuccs)".
    case_decide as Hstate; first subst.

    - iDestruct "Hstate" as "(>%HΠ & #HP1)".
      iDestruct "Hsuccs" as ">Hsuccs_model".
      iAaccIntro with "Hsuccs_model"; first iSteps. iIntros "Hsuccs_model !>".
      iSplitL; first iSteps.
      iIntros "H£ (Hstate₂ & HΦ)". clear.

      iApply fupd_wp.
      iInv "Hinv2" as "(%state & %preds & %Δ & %Π & >%HΔ & Hvtx2_preds & HΔ & HΠ & >Hpreds & >Hstate₁ & Hstate & Hsuccs)".
      iDestruct (vertex_state_agree with "Hstate₁ Hstate₂") as %->.
      iDestruct "Hstate" as ">(%Hpreds & Hdeps)".
      iMod (saved_prop_alloc_cofinite (Δ ∪ Π) P1) as "(%π & %Hπ & #Hπ)".
      apply not_elem_of_union in Hπ as (Hπ_Δ & Hπ_Π).
      iMod (vertex_dependencies_add π with "Hdeps") as "(Hdeps & #Hdep)".
      iSplitR "Hstate₂ H£ HΦ".
      { iExists VertexInit, preds, ({[π]} ∪ Δ), Π.
        rewrite big_sepS_union; first set_solver. rewrite big_sepS_singleton.
        assert ({[π]} ∪ (Δ ∪ Π) = ({[π]} ∪ Δ) ∪ Π) as -> by set_solver.
        iSteps. iPureIntro. set_solver.
      }
      iSteps.

    - iDestruct "Hsuccs" as "(%succs & >Hsuccs_model & Hsuccs)".
      iAaccIntro with "Hsuccs_model"; iIntros "Hsuccs_model !>".
      { iFrame. rewrite right_id. iExists state. rewrite decide_False //. iSteps. }
      iSplitL. { iSteps. rewrite decide_False //. iSteps. }
      iIntros "H£ (Hstate₂ & HΦ)". wp_pures. clear.

      wp_bind (Faa _ _).
      iInv "Hinv2" as "(%state & %preds & %Δ & %Π & >%HΔ & Hvtx2_preds & HΔ & HΠ & Hpreds & Hstate₁ & Hstate & Hsuccs)".
      wp_faa.
      iDestruct (vertex_state_agree with "Hstate₁ Hstate₂") as %->.
      iDestruct "Hstate" as "(%Hpreds & Hdeps)".
      iMod (saved_prop_alloc_cofinite (Δ ∪ Π) P1) as "(%π & %Hπ & #Hπ)".
      apply not_elem_of_union in Hπ as (Hπ_Δ & Hπ_Π).
      iMod (vertex_predecessors_add with "Hpreds") as "(Hpreds & Hpred)"; first done.
      iMod (vertex_dependencies_add π with "Hdeps") as "(Hdeps & #Hdep)".
      iSplitR "Hstate₂ Hpred H£ HΦ".
      { iExists VertexInit, (S preds), Δ, ({[π]} ∪ Π).
        rewrite big_sepS_union; first set_solver. rewrite big_sepS_singleton.
        assert ({[π]} ∪ (Δ ∪ Π) = Δ ∪ ({[π]} ∪ Π)) as -> by set_solver.
        iSteps; iPureIntro.
        - set_solver.
        - rewrite size_union; first set_solver. rewrite size_singleton //.
      }
      iModIntro. wp_pures. clear.

      awp_apply (mpmc_stack_push_spec with "Hsuccs1_inv") without "Hstate₂ H£ HΦ".
      iInv "Hinv1" as "(%state & %preds & %Δ & %Π & >%HΔ & Hvtx1_preds & HΔ & HΠ & Hpreds & Hstate₁ & Hstate & Hsuccs)".
      case_decide as Hstate; first subst.

      + iDestruct "Hstate" as "(>%HΠ & #HP1)".
        iDestruct "Hsuccs" as ">Hsuccs_model".
        iAaccIntro with "Hsuccs_model"; first iSteps. iIntros "Hsuccs_model !>".
        iSplitR "Hpred"; first iSteps.
        iIntros "_ (Hstate₂ & H£ & HΦ)". clear.

        wp_pures.

        wp_bind (Faa _ _).
        iInv "Hinv2" as "(%state & %preds & %Δ & %Π & >%HΔ & Hvtx2_preds & HΔ & HΠ & Hpreds & Hstate₁ & Hstate & Hsuccs)".
        wp_faa.
        iDestruct (vertex_state_agree with "Hstate₁ Hstate₂") as %->.
        iDestruct "Hstate" as "(%Hpreds & Hdeps)".
        iDestruct (vertex_predecessors_elem_of with "Hpreds Hpred") as %Hπ.
        iMod (vertex_predecessors_remove with "Hpreds Hpred") as "Hpreds".
        iDestruct (big_sepS_delete with "HΠ") as "(_ & HΠ)"; first done.
        iSplitR "Hstate₂ H£ HΦ".
        { iExists VertexInit, (preds - 1), ({[π]} ∪ Δ), (Π ∖ {[π]}).
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
        { iFrame. iExists state. rewrite decide_False //. iSteps. }
        iSplitL.
        { iSteps. rewrite decide_False //. iExists (vtx2 :: succs). iFrame.
          setoid_rewrite vertex_inv'_unfold. iSteps.
        }
        iSteps.
  Qed.

  #[local] Lemma vertex_propagate_spec ctx vtx γ P π Q run :
    {{{
      pool_context ws_hub ctx ∗
      vertex_inv' vtx γ P ∗
      saved_prop π Q ∗
      vertex_predecessor γ π ∗
      □ Q ∗
      ( ∀ ctx,
        pool_context ws_hub ctx -∗
        vertex_state₂ γ VertexRunning -∗
        ( pool_context ws_hub ctx -∗
          WP γ.(vertex_meta_task) ctx {{ res,
            pool_context ws_hub ctx ∗
            ▷ □ P
          }}
        ) -∗
        WP run ctx #vtx {{ res,
          pool_context ws_hub ctx
        }}
      )
    }}}
      vertex_propagate ws_hub ctx #vtx run
    {{{
      RET ();
      pool_context ws_hub ctx
    }}}.
  Proof.
    setoid_rewrite vertex_inv'_unfold.
    iIntros "%Φ (Hctx & (#Hvtx_task & #Hvtx_succs & #Hsuccs_inv & #Hinv) & #Hπ & Hpred & #HQ & Hrun) HΦ".

    wp_rec. wp_pures.

    wp_bind (Faa _ _).
    iInv "Hinv" as "(%state & %preds & %Δ & %Π & >%HΔ & Hvtx_preds & HΔ & HΠ & Hpreds & Hstate₁ & Hstate & Hsuccs)".
    wp_faa.
    iDestruct (vertex_predecessors_elem_of with "Hpreds Hpred") as %Hπ.
    destruct state.
    3: iDestruct "Hstate" as "%HΠ".
    4: iDestruct "Hstate" as "(%HΠ & _)".
    3,4: apply size_empty_inv in HΠ; set_solver.
    all: iMod (vertex_predecessors_remove with "Hpreds Hpred") as "Hpreds".
    all: iDestruct (big_sepS_delete with "HΠ") as "(_ & HΠ)"; first done.

    - iClear "Hrun".
      iDestruct "Hstate" as "(%Hpreds & Hdeps)".
      iSplitR "Hctx HΦ".
      { iExists VertexInit, (preds - 1), ({[π]} ∪ Δ), (Π ∖ {[π]}).
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
        iMod (vertex_state_update VertexRunning with "Hstate₁ Hstate₂") as "(Hstate₁ & Hstate₂)".
        iDestruct "HΔ" as "#HΔ".
        iSplitR "Hctx Hrun Hstate₂ Hdeps Htask HΦ".
        { iExists VertexRunning, 0, ({[π]} ∪ Δ), ∅.
          rewrite big_sepS_union; first set_solver. rewrite big_sepS_singleton.
          iSteps.
        }
        iDestruct (big_sepS_insert_2' with "[] HΔ") as "HΔ'"; first iSteps.
        iClear "Hπ HQ HΔ". remember (Δ ∪ {[π]}) as Δ'.
        iMod (vertex_dependencies_close with "Hdeps") as "#Hdeps".
        iModIntro. clear.

        wp_smart_apply (pool_silent_async_spec with "[$Hctx Hrun Hstate₂ Hdeps Htask]"); last iSteps.
        clear ctx. iIntros "%ctx Hctx".
        wp_smart_apply (wp_wand with "(Hrun Hctx Hstate₂ [Hdeps Htask])"); last iSteps. iIntros "Hctx".
        wp_apply ("Htask" with "Hctx"). iIntros "!> %Q %E (%δ & #Hδ & #Hdep & H£)".
        iDestruct (vertex_dependencies_elem_of with "Hdeps Hdep") as %Hδ.
        iDestruct (big_sepS_elem_of with "HΔ'") as "(%_Q & _Hδ & #HQ)"; first done.
        iDestruct (saved_prop_agree with "Hδ _Hδ") as "-#Heq".
        iMod (lc_fupd_elim_later with "H£ Heq") as "Heq".
        iRewrite "Heq". iSteps.

      + iSplitR "Hctx HΦ".
        { iExists VertexReleased, (preds - 1), ({[π]} ∪ Δ), (Π ∖ {[π]}).
          rewrite big_sepS_union; first set_solver. rewrite big_sepS_singleton.
          assert ({[π]} ∪ Δ ∪ Π ∖ {[π]} = Δ ∪ Π) as ->.
          { apply leibniz_equiv. rewrite (comm (∪) {[_]}) -assoc -union_difference_singleton_L //. }
          assert (1 < preds).
          { apply non_empty_inhabited in Hπ as ?%size_non_empty_iff. lia. }
          iFrame. iSteps; iPureIntro.
          - set_solver.
          - rewrite size_difference; first set_solver. rewrite size_singleton.
            apply non_empty_inhabited in Hπ as ?%size_non_empty_iff. lia.
        }
        iSteps.
  Qed.
  #[local] Lemma vertex_run_spec ctx vtx γ P :
    {{{
      pool_context ws_hub ctx ∗
      vertex_inv' vtx γ P ∗
      vertex_state₂ γ VertexRunning ∗
      ( pool_context ws_hub ctx -∗
        WP γ.(vertex_meta_task) ctx {{ res,
          pool_context ws_hub ctx ∗
          ▷ □ P
        }}
      )
    }}}
      vertex_run ws_hub ctx #vtx
    {{{
      RET ();
      pool_context ws_hub ctx
    }}}.
  Proof.
    iLöb as "HLöb" forall (ctx vtx γ P).

    setoid_rewrite vertex_inv'_unfold.
    iIntros "%Φ (Hctx & (#Hvtx_task & #Hvtx_succs & #Hsuccs_inv & #Hinv) & Hstate₂ & Htask) HΦ".

    wp_rec. wp_load.
    wp_apply (wp_wand with "(Htask Hctx)") as (res) "(Hctx & #HP)".
    wp_load.

    awp_smart_apply (mpmc_stack_close_spec with "Hsuccs_inv") without "Hctx HΦ".
    iInv "Hinv" as "(%state & %preds & %Δ & %Π & >%HΔ & Hvtx_preds & HΔ & HΠ & Hpreds & >Hstate₁ & Hstate & Hsuccs)".
    iDestruct (vertex_state_agree with "Hstate₁ Hstate₂") as %->.
    iDestruct "Hstate" as ">%HΠ".
    iDestruct "Hsuccs" as "(%succs & >Hsuccs_model & Hsuccs)".
    iAaccIntro with "Hsuccs_model"; iIntros "Hsuccs_model".
    { iFrame. iSteps. }
    iMod (vertex_state_update VertexDone with "Hstate₁ Hstate₂") as "(Hstate₁ & _)".
    iSplitR "Hsuccs"; first iSteps.
    iIntros "!> H£ (Hctx & HΦ)". clear.

    iMod (lc_fupd_elim_later with "H£ Hsuccs") as "Hsuccs".
    wp_apply (clst_iter_spec (λ _, pool_context ws_hub ctx) with "[$Hctx Hsuccs]"); [done | | iSteps].
    rewrite big_sepL_fmap.
    iApply (big_sepL_impl with "Hsuccs"). iIntros "!> %i %succ _ (%γ_succ & %P_succ & %π & #Hmeta_succ & #Hinv_succ & #Hπ & Hpred) Hctx".
    wp_smart_apply (vertex_propagate_spec with "[$Hinv_succ $Hctx $Hπ $Hpred $HP]"); last iSteps.
    clear. iIntros "%ctx Hctx Hstate₂ Htask".
    wp_apply ("HLöb" with "[$Hctx $Hstate₂ $Htask]"); last iSteps.
    rewrite -vertex_inv'_unfold //.
  Qed.
  Lemma vertex_release_spec ctx t P task :
    {{{
      pool_context ws_hub ctx ∗
      vertex_inv t P ∗
      vertex_init t task ∗
      ( ∀ ctx,
        pool_context ws_hub ctx -∗
        □ (∀ Q E, vertex_input t Q ={E}=∗ □ Q) -∗
        WP task ctx {{ res,
          pool_context ws_hub ctx ∗
          ▷ □ P
        }}
      )
    }}}
      vertex_release ws_hub ctx t
    {{{
      RET ();
      pool_context ws_hub ctx
    }}}.
  Proof.
    rewrite /vertex_inv. setoid_rewrite vertex_inv'_unfold.
    iIntros "%Φ (Hctx & (%vtx & %γ & -> & #Hmeta & #Hvtx_task & #Hvtx_succs & #Hsuccs_inv & #Hinv) & (%_vtx & %_γ & %Heq & -> & _Hmeta & Hstate₂) & Htask) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".

    iApply fupd_wp.
    iInv "Hinv" as "(%state & %preds & %Δ & %Π & >%HΔ & Hvtx_preds & HΔ & HΠ & >Hpreds & >Hstate₁ & Hstate & Hsuccs)".
    iDestruct (vertex_state_agree with "Hstate₁ Hstate₂") as %->.
    iMod (vertex_state_update VertexReleased with "Hstate₁ Hstate₂") as "(Hstate₁ & Hstate₂)".
    iDestruct "Hstate" as ">(%Hpreds & Hdeps)".
    iMod (saved_prop_alloc_cofinite (Δ ∪ Π) True) as "(%π & %Hπ & #Hπ)".
    apply not_elem_of_union in Hπ as (Hπ_Δ & Hπ_Π).
    iMod (vertex_predecessors_add with "Hpreds") as "(Hpreds & Hpred)"; first done.
    iMod (vertex_dependencies_add π with "Hdeps") as "(Hdeps & #Hdep_π)".
    iSplitR "Hctx Hpred HΦ".
    { iExists VertexReleased, preds, Δ, ({[π]} ∪ Π).
      rewrite big_sepS_union; first set_solver. rewrite big_sepS_singleton.
      assert ({[π]} ∪ (Δ ∪ Π) = Δ ∪ ({[π]} ∪ Π)) as -> by set_solver.
      iFrame. iSplitR.
      { iPureIntro. set_solver. }
      iStep. iSplitR.
      { rewrite size_union; first set_solver. rewrite size_singleton //. }
      clear. iIntros "!> !> %ctx Hctx #H".
      iApply (wp_wand with "(Htask Hctx [])"); last iSteps.
      iIntros "!> %Q %E (%_vtx & %_γ & %Heq & _Hmeta & Hinput)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iApply ("H" with "Hinput").
    }
    do 2 iModIntro. clear.

    wp_rec.

    wp_smart_apply (vertex_propagate_spec with "[$Hctx $Hπ $Hpred] HΦ").
    rewrite vertex_inv'_unfold. do 2 iStep.
    clear. iIntros "%ctx Hctx Hstate₂ Htask".
    wp_apply (vertex_run_spec with "[$Hctx $Hstate₂ $Htask]"); last iSteps.
    rewrite vertex_inv'_unfold. iSteps.
  Qed.
End vertex_G.

#[global] Opaque vertex_create.
#[global] Opaque vertex_precede.
#[global] Opaque vertex_release.

#[global] Opaque vertex_inv.
#[global] Opaque vertex_init.
#[global] Opaque vertex_input.
