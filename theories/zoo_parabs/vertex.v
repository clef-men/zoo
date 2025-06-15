From zoo Require Import
  prelude.
From zoo.common Require Import
  countable
  gmultiset.
From zoo.iris.bi Require Import
  big_op.
From zoo.iris.base_logic Require Import
  lib.auth_gmultiset
  lib.mono_gmultiset
  lib.subprops
  lib.twins.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  clst
  option.
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

Implicit Types b finished : bool.
Implicit Types preds : nat.
Implicit Types t succ : location.
Implicit Types task ctx : val.
Implicit Types own : ownership.

Inductive state :=
  | Init
  | Released
  | Running
  | Finished.
Implicit Types state : state.

#[local] Instance state_inhabited : Inhabited state :=
  populate Init.
#[local] Instance state_eq_dec : EqDecision state :=
  ltac:(solve_decision).

Record vertex_name:= {
  vertex_name_successors : val ;
  vertex_name_state : gname ;
  vertex_name_generation : gname ;
  vertex_name_predecessors : gname ;
  vertex_name_output : gname ;
}.
Implicit Types γ δ π : vertex_name.

#[local] Instance vertex_name_eq_dec : EqDecision vertex_name :=
  ltac:(solve_decision).
#[local] Instance vertex_name_countable :
  Countable vertex_name.
Proof.
  solve_countable.
Qed.
Implicit Types Δ Π : gmultiset vertex_name.

Definition vertex_generation :=
  gname.
Implicit Types gen : vertex_generation.

Class VertexG Σ `{zoo_G : !ZooG Σ} := {
  #[local] vertex_G_stack_G :: MpmcStack2G Σ ;
  #[local] vertex_G_pool_G :: SchedulerG Σ ;
  #[local] vertex_G_state_G :: TwinsG Σ (leibnizO state) ;
  #[local] vertex_G_generation_G :: TwinsG Σ (leibnizO vertex_generation) ;
  #[local] vertex_G_dependencies_G :: MonoGmultisetG Σ vertex_name ;
  #[local] vertex_G_predecessors_G :: AuthGmultisetG Σ vertex_name ;
  #[local] vertex_G_output_G :: SubpropsG Σ ;
}.

Definition vertex_Σ := #[
  mpmc_stack_2_Σ ;
  pool_Σ ;
  twins_Σ (leibnizO state) ;
  twins_Σ (leibnizO vertex_generation) ;
  mono_gmultiset_Σ vertex_name ;
  auth_gmultiset_Σ vertex_name ;
  subprops_Σ
].
#[global] Instance subG_vertex_Σ Σ `{zoo_G : !ZooG Σ}:
  subG vertex_Σ Σ →
  VertexG Σ.
Proof.
  solve_inG.
Qed.

Section vertex_G.
  Context `{vertex_G : VertexG Σ}.

  Implicit Types P Q R : iProp Σ.

  #[local] Definition state₁' γ_state own state :=
    twins_twin1 (twins_G := vertex_G_state_G) γ_state own state.
  #[local] Definition state₁ γ :=
    state₁' γ.(vertex_name_state).
  #[local] Definition state₂' γ_state state :=
    twins_twin2 (twins_G := vertex_G_state_G) γ_state state.
  #[local] Definition state₂ γ :=
    state₂' γ.(vertex_name_state).

  #[local] Definition generation₁' γ_generation gen :=
    twins_twin1 γ_generation (DfracOwn 1) gen.
  #[local] Definition generation₁ γ :=
    generation₁' γ.(vertex_name_generation).
  #[local] Definition generation₂' γ_generation gen :=
    twins_twin2 γ_generation gen.
  #[local] Definition generation₂ γ :=
    generation₂' γ.(vertex_name_generation).

  #[local] Definition dependencies_auth gen own :=
    mono_gmultiset_auth gen own.
  #[local] Definition dependencies_elem gen :=
    mono_gmultiset_elem gen.

  #[local] Definition predecessors_auth' γ_predecessors Π :=
    auth_gmultiset_auth γ_predecessors (DfracOwn 1) Π.
  #[local] Definition predecessors_auth γ Π :=
    predecessors_auth' γ.(vertex_name_predecessors) Π.
  #[local] Definition predecessors_elem γ π :=
    auth_gmultiset_frag γ.(vertex_name_predecessors) {[+π+]}.

  #[local] Definition output_auth' γ_output :=
    subprops_auth γ_output.
  #[local] Definition output_auth γ :=
    subprops_auth γ.(vertex_name_output).
  #[local] Definition output_frag' γ_output :=
    subprops_frag γ_output.
  #[local] Definition output_frag γ :=
    output_frag' γ.(vertex_name_output).

  #[local] Definition model' t γ task state gen : iProp Σ :=
    t.[task] ↦ task ∗
    state₁ γ Own state ∗
    generation₁ γ gen.
  #[local] Instance : CustomIpatFormat "model'" :=
    "(
      Ht{which;}_task{_{}} &
      Hstate{which;}₁{_{}} &
      Hgeneration{which;}₁{_{}}
    )".
  Definition vertex_model t γ task gen : iProp Σ :=
    model' t γ task Init gen.
  #[local] Instance : CustomIpatFormat "model" :=
    "(:model' {//} {/which/})".

  Definition vertex_running gen : iProp Σ :=
    ∃ Δ,
    dependencies_auth gen Discard Δ ∗
    [∗ mset] δ ∈ Δ, state₁ δ Discard Finished.
  #[local] Instance : CustomIpatFormat "running" :=
    "(
      %Δ{} &
      #Hdependencies{which;}_auth{_{}} &
      #HΔ{}
    )".

  Definition vertex_finished γ :=
    state₁ γ Discard Finished.
  #[local] Instance : CustomIpatFormat "finished" :=
    "#Hstate{which;}₁{_{}}".

  Definition vertex_wp_body t γ P R body task gen : iProp Σ :=
    ∀ ctx gen',
    pool_context_model ctx -∗
    vertex_running gen -∗
    vertex_model t γ task gen' -∗
    WP task ctx {{ res,
      ∃ b task,
      ⌜res = #b⌝ ∗
      ▷ (
        pool_context_model ctx ∗
        vertex_model t γ task gen' ∗
        if b then
          body task gen'
        else
          P ∗
          □ R
      )
    }}.
  #[local] Definition vertex_wp_pre
  : location → vertex_name → iProp Σ → iProp Σ →
    (val -d> vertex_generation -d> iProp Σ) →
    val -d> vertex_generation -d> iProp Σ
  :=
    vertex_wp_body.
  #[local] Instance vertex_wp_pre_contractive t γ P R :
    Contractive (vertex_wp_pre t γ P R).
  Proof.
    rewrite /vertex_wp_pre /vertex_wp_body.
    solve_contractive.
  Qed.
  #[local] Instance vertex_wp_pre_ne t γ P R :
    NonExpansive (vertex_wp_pre t γ P R).
  Proof.
    apply _.
  Qed.
  Definition vertex_wp t γ P R : val → vertex_generation → iProp Σ :=
    fixpoint (vertex_wp_pre t γ P R).

  Lemma vertex_wp_unfold t γ P R task gen :
    vertex_wp t γ P R task gen ⊣⊢
    vertex_wp_body t γ P R (vertex_wp t γ P R) task gen.
  Proof.
    apply (fixpoint_unfold (vertex_wp_pre t γ P R)).
  Qed.
  #[global] Instance vertex_wp_ne n :
    Proper (
      (=) ==>
      (=) ==>
      (≡{n}≡) ==>
      (≡{n}≡) ==>
      (≡{n}≡) ==>
      (≡{n}≡) ==>
      (≡{n}≡)
    ) vertex_wp.
  Proof.
    intros t t_ <- γ γ_ <-.
    induction (lt_wf n) as [n _ IH] => P1 P2 HP R1 R2 HR task task_ <- gen gen_ <-.
    rewrite !vertex_wp_unfold /vertex_wp_body.
    do 14 f_equiv. f_contractive.
    apply (dist_le _ m) in HP; last lia.
    apply (dist_le _ m) in HR; last lia.
    do 3 f_equiv; last solve_proper.
    apply IH; done.
  Qed.

  #[local] Definition inv_state_init preds gen Π : iProp Σ :=
    ∃ Δ,
    dependencies_auth gen Own (Δ ⊎ Π) ∗
    ⌜preds = S (size Π)⌝ ∗
    [∗ mset] δ ∈ Δ, vertex_finished δ.
  #[local] Instance : CustomIpatFormat "inv_state_init" :=
    "(
      %Δ &
      {>;}Hdependencies{which;}_auth &
      {>;}-> &
      {>;}HΔ
    )".
  #[local] Definition inv_state_released t γ P R preds gen Π : iProp Σ :=
    ∃ task Δ,
    model' t γ task Released gen ∗
    dependencies_auth gen Discard (Δ ⊎ Π) ∗
    ⌜preds = size Π⌝ ∗
    ([∗ mset] δ ∈ Δ, vertex_finished δ) ∗
    vertex_wp t γ P R task gen.
  #[local] Instance : CustomIpatFormat "inv_state_released" :=
    "(
      %task &
      %Δ &
      (:model' {//} {/which/}) &
      {>;}Hdependencies{which;}_auth &
      {>;}-> &
      {>;}HΔ &
      Htask
    )".
  #[local] Definition inv_state_running Π : iProp Σ :=
    ⌜Π = ∅⌝.
  #[local] Instance : CustomIpatFormat "inv_state_running" :=
    "{>;}->".
  #[local] Definition inv_state_finished γ R preds Π : iProp Σ :=
    vertex_finished γ ∗
    ⌜preds = S (size Π)⌝ ∗
    □ R.
  #[local] Instance : CustomIpatFormat "inv_state_finished" :=
    "(
      {>;}#Hstate{which;}₁ &
      {>;}-> &
      #HR{which;}
    )".
  #[local] Definition inv_state t γ P R state preds gen Π : iProp Σ :=
    match state with
    | Init =>
        inv_state_init preds gen Π
    | Released =>
        inv_state_released t γ P R preds gen Π
    | Running =>
        inv_state_running Π
    | Finished =>
        inv_state_finished γ R preds Π
    end.

  #[local] Definition inv_successor (inv : location → vertex_name → iProp Σ → iProp Σ → iProp Σ) γ succ : iProp Σ :=
    ∃ γ_succ P_succ R_succ,
    inv succ γ_succ P_succ R_succ ∗
    predecessors_elem γ_succ γ.
  #[local] Instance : CustomIpatFormat "inv_successor" :=
    "(
      %γ_succ &
      %P_succ &
      %R_succ &
      #Hinv_succ &
      Hpredecessors_elem
    )".
  #[local] Definition inv_successors inv γ finished :=
    if finished then (
      mpmc_stack_2_model γ.(vertex_name_successors) None
    ) else (
      ∃ succs,
      mpmc_stack_2_model γ.(vertex_name_successors) (Some $ #@{location} <$> succs) ∗
      [∗ list] succ ∈ succs, inv_successor inv γ succ
    )%I.
  #[local] Instance : CustomIpatFormat "inv_successors_finished" :=
    ">Hsuccessors{which;}_model".
  #[local] Instance : CustomIpatFormat "inv_successors" :=
    "(
      %succs &
      >Hsuccessors{which;}_model &
      Hsuccs
    )".

  #[local] Definition inv_inner inv t γ P R : iProp Σ :=
    ∃ preds state gen Π,
    t.[preds] ↦ #preds ∗
    state₂ γ state ∗
    generation₂ γ gen ∗
    predecessors_auth γ Π ∗
    output_auth γ P (bool_decide (state = Finished)) ∗
    inv_state t γ P R state preds gen Π ∗
    inv_successors inv γ (bool_decide (state = Finished)).
  #[local] Instance : CustomIpatFormat "inv_inner" :=
    "(
      %preds{} &
      %state{} &
      %gen{} &
      %Π &
      Ht{which;}_preds &
      >Hstate{which;}₂ &
      >Hgeneration{which;}₂ &
      Hpredecessors{which;}_auth &
      Houtput{which;}_auth &
      Hinv_state{which;} &
      Hinv_successors{which;}
    )".
  #[local] Definition inv_pre
  : (location -d> vertex_name -d> iProp Σ -d> iProp Σ -d> iProp Σ) →
    location -d> vertex_name -d> iProp Σ -d> iProp Σ -d> iProp Σ
  :=
    λ inv t γ P R, (
      t.[succs] ↦□ γ.(vertex_name_successors) ∗
      mpmc_stack_2_inv γ.(vertex_name_successors) (nroot.@"successors") ∗
      invariants.inv (nroot.@"inv") (inv_inner inv t γ P R)
    )%I.
  #[local] Instance : CustomIpatFormat "inv_pre" :=
    "(
      #Ht{}_succs &
      #Hsuccessors{}_inv &
      #Hinv{_{}}
    )".
  #[local] Instance inv_pre_contractive_2 :
    Contractive inv_pre.
  Proof.
    rewrite /inv_pre /inv_inner /inv_successors /inv_successor.
    intros n Ψ1 Ψ2 HΨ t γ P R.
    repeat (apply HΨ || f_contractive || f_equiv).
  Qed.
  Definition vertex_inv : location → vertex_name → iProp Σ → iProp Σ → iProp Σ :=
    fixpoint inv_pre.

  #[local] Lemma vertex_inv_unfold t γ P R :
    vertex_inv t γ P R ⊣⊢
    inv_pre vertex_inv t γ P R.
  Proof.
    apply (fixpoint_unfold inv_pre).
  Qed.
  #[local] Instance vertex_inv_contractive t γ n :
    Proper (
      dist_later n ==>
      dist_later n ==>
      (≡{n}≡)
    ) (vertex_inv t γ).
  Proof.
    induction (lt_wf n) as [n _ IH] => P1 P2 HP R1 R2 HR.
    rewrite !vertex_inv_unfold /inv_pre /inv_inner /inv_state /inv_state_released /inv_state_finished /inv_successors /inv_successor.
    solve_contractive.
  Qed.
  #[global] Instance vertex_inv_ne t γ n :
    Proper (
      (≡{n}≡) ==>
      (≡{n}≡) ==>
      (≡{n}≡)
    ) (vertex_inv t γ).
  Proof.
    intros P1 P2 HP R1 R2 HR.
    apply vertex_inv_contractive.
    all: apply dist_dist_later; done.
  Qed.
  #[global] Instance vertex_inv_proper t γ :
    Proper (
      (≡) ==>
      (≡) ==>
      (≡)
    ) (vertex_inv t γ).
  Proof.
    intros P1 P2 HP R1 R2 HR.
    rewrite !equiv_dist in HP HR |- * => n.
    apply vertex_inv_ne; done.
  Qed.

  Definition vertex_output γ Q :=
    output_frag γ Q.
  #[local] Instance : CustomIpatFormat "output" :=
    "Houtput{which;}_frag{_{}}".

  #[global] Instance vertex_output_contractive γ :
    Contractive (vertex_output γ).
  Proof.
    solve_contractive.
  Qed.
  #[global] Instance vertex_output_proper γ :
    Proper ((≡) ==> (≡)) (vertex_output γ).
  Proof.
    solve_proper.
  Qed.

  Definition vertex_predecessor γ gen :=
    dependencies_elem gen γ.
  #[local] Instance : CustomIpatFormat "predecessor" :=
    "#Hdependencies{which;}_elem{_{}}".

  #[global] Instance vertex_model_timeless t γ task gen :
    Timeless (vertex_model t γ task gen).
  Proof.
    apply _.
  Qed.
  #[global] Instance vertex_running_timeless gen :
    Timeless (vertex_running gen).
  Proof.
    apply _.
  Qed.
  #[global] Instance vertex_finished_timeless γ :
    Timeless (vertex_finished γ).
  Proof.
    apply _.
  Qed.
  #[global] Instance vertex_predecessor_timeless γ gen :
    Timeless (vertex_predecessor γ gen).
  Proof.
    apply _.
  Qed.

  #[local] Instance vertex_inv_persistent t γ P R :
    Persistent (vertex_inv t γ P R).
  Proof.
    rewrite vertex_inv_unfold.
    apply _.
  Qed.
  #[global] Instance vertex_running_persistent gen :
    Persistent (vertex_running gen).
  Proof.
    apply _.
  Qed.
  #[global] Instance vertex_finished_persistent γ :
    Persistent (vertex_finished γ).
  Proof.
    apply _.
  Qed.
  #[global] Instance vertex_predecessor_persistent γ gen :
    Persistent (vertex_predecessor γ gen).
  Proof.
    apply _.
  Qed.

  #[local] Lemma state_alloc :
    ⊢ |==>
      ∃ γ_state,
      state₁' γ_state Own Init ∗
      state₂' γ_state Init.
  Proof.
    apply twins_alloc'.
  Qed.
  #[local] Lemma state_agree γ own1 state1 state2 :
    state₁ γ own1 state1 -∗
    state₂ γ state2 -∗
    ⌜state1 = state2⌝.
  Proof.
    apply: twins_agree_L.
  Qed.
  #[local] Lemma state₁_exclusive γ state1 own2 state2 :
    state₁ γ Own state1 -∗
    state₁ γ own2 state2 -∗
    False.
  Proof.
    apply twins_twin1_exclusive.
  Qed.
  #[local] Lemma state_update {γ state1 state2} state :
    state₁ γ Own state1 -∗
    state₂ γ state2 ==∗
      state₁ γ Own state ∗
      state₂ γ state.
  Proof.
    apply twins_update'.
  Qed.
  #[local] Lemma state₁_discard γ state :
    state₁ γ Own state ⊢ |==>
    state₁ γ Discard state.
  Proof.
    apply twins_twin1_persist.
  Qed.

  #[local] Lemma generation_alloc gen :
    ⊢ |==>
      ∃ γ_generation,
      generation₁' γ_generation gen ∗
      generation₂' γ_generation gen.
  Proof.
    apply twins_alloc'.
  Qed.
  #[local] Lemma generation_agree γ generation1 generation2 :
    generation₁ γ generation1 -∗
    generation₂ γ generation2 -∗
    ⌜generation1 = generation2⌝.
  Proof.
    apply: twins_agree_L.
  Qed.
  #[local] Lemma generation₁_exclusive γ generation1 generation2 :
    generation₁ γ generation1 -∗
    generation₁ γ generation2 -∗
    False.
  Proof.
    apply twins_twin1_exclusive.
  Qed.
  #[local] Lemma generation_update {γ generation1 generation2} generation :
    generation₁ γ generation1 -∗
    generation₂ γ generation2 ==∗
      generation₁ γ generation ∗
      generation₂ γ generation.
  Proof.
    apply twins_update'.
  Qed.

  #[local] Lemma dependencies_alloc :
    ⊢ |==>
      ∃ gen,
      dependencies_auth gen Own ∅.
  Proof.
    apply mono_gmultiset_alloc.
  Qed.
  #[local] Lemma dependencies_add {gen Δ} δ :
    dependencies_auth gen Own Δ ⊢ |==>
      dependencies_auth gen Own ({[+δ+]} ⊎ Δ) ∗
      dependencies_elem gen δ.
  Proof.
    apply mono_gmultiset_insert'.
  Qed.
  #[local] Lemma dependencies_elem_of gen own Δ δ :
    dependencies_auth gen own Δ -∗
    dependencies_elem gen δ -∗
    ⌜δ ∈ Δ⌝.
  Proof.
    apply mono_gmultiset_elem_valid.
  Qed.
  #[local] Lemma dependencies_discard gen Δ :
    dependencies_auth gen Own Δ ⊢ |==>
    dependencies_auth gen Discard Δ.
  Proof.
    apply mono_gmultiset_auth_persist.
  Qed.

  #[local] Lemma predecessors_alloc :
    ⊢ |==>
      ∃ γ_predecessors,
      predecessors_auth' γ_predecessors ∅.
  Proof.
    apply auth_gmultiset_alloc.
  Qed.
  #[local] Lemma predecessors_elem_of γ Π π :
    predecessors_auth γ Π -∗
    predecessors_elem γ π -∗
    ⌜π ∈ Π⌝.
  Proof.
    apply auth_gmultiset_elem_of.
  Qed.
  #[local] Lemma predecessors_add {γ Π} π :
    predecessors_auth γ Π ⊢ |==>
      predecessors_auth γ ({[+π+]} ⊎ Π) ∗
      predecessors_elem γ π.
  Proof.
    apply auth_gmultiset_update_alloc_singleton.
  Qed.
  #[local] Lemma predecessors_remove γ Π π :
    predecessors_auth γ Π -∗
    predecessors_elem γ π ==∗
    predecessors_auth γ (Π ∖ {[+π+]}).
  Proof.
    apply auth_gmultiset_update_dealloc.
  Qed.

  #[local] Lemma output_alloc P :
    ⊢ |==>
      ∃ γ_output,
      output_auth' γ_output P false ∗
      output_frag' γ_output P.
  Proof.
    apply subprops_alloc.
  Qed.
  #[local] Lemma output_divide {γ P finished Q} Qs E :
    ▷ output_auth γ P finished -∗
    output_frag γ Q -∗
    (Q -∗ [∗ list] Q ∈ Qs, Q) ={E}=∗
      ▷ output_auth γ P finished ∗
      [∗ list] Q ∈ Qs, output_frag γ Q.
  Proof.
    apply subprops_divide.
  Qed.
  #[local] Lemma output_produce γ P :
    ▷ output_auth γ P false -∗
    P -∗
    ▷ output_auth γ P true.
  Proof.
    iIntros "Hauth HP".
    iApply (subprops_produce with "Hauth [$HP]").
  Qed.
  #[local] Lemma output_consume γ P Q E :
    ▷ output_auth γ P true -∗
    output_frag γ Q ={E}=∗
      ▷ output_auth γ P true ∗
      ▷^2 Q.
  Proof.
    apply subprops_consume.
  Qed.

  Lemma vertex_model_exclusive t γ task1 gen1 task2 gen2 :
    vertex_model t γ task1 gen1 -∗
    vertex_model t γ task2 gen2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)".
    iApply (generation₁_exclusive with "Hgeneration₁_1 Hgeneration₁_2").
  Qed.
  Lemma vertex_model_not_finished t γ task gen :
    vertex_model t γ task gen -∗
    vertex_finished γ -∗
    False.
  Proof.
    iIntros "(:model =1) (:finished =2)".
    iApply (state₁_exclusive with "Hstate₁_1 Hstate₁_2").
  Qed.

  Lemma vertex_output_divide {t γ P R Q} Qs :
    vertex_inv t γ P R -∗
    vertex_output γ Q -∗
    (Q -∗ [∗ list] Q ∈ Qs, Q) ={⊤}=∗
    [∗ list] Q ∈ Qs, vertex_output γ Q.
  Proof.
    rewrite vertex_inv_unfold.
    iIntros "(:inv_pre) (:output) H".
    iInv "Hinv" as "(:inv_inner)".
    iMod (output_divide with "Houtput_auth Houtput_frag H") as "(Houtput_auth & H)".
    iSplitR "H". { iFrameSteps. }
    iApply (big_sepL_impl with "H").
    iSteps.
  Qed.
  Lemma vertex_output_split {t γ P R Q} Q1 Q2 :
    vertex_inv t γ P R -∗
    vertex_output γ Q -∗
    (Q -∗ Q1 ∗ Q2) ={⊤}=∗
      vertex_output γ Q1 ∗
      vertex_output γ Q2.
  Proof.
    iIntros "#Hinv Houtput H".
    iMod (vertex_output_divide [Q1;Q2] with "Hinv Houtput [H]") as "($ & $ & _)"; iSteps.
  Qed.

  Lemma vertex_predecessor_finished γ gen :
    vertex_predecessor γ gen -∗
    vertex_running gen -∗
    vertex_finished γ.
  Proof.
    iIntros "(:predecessor) (:running)".
    iDestruct (dependencies_elem_of with "Hdependencies_auth Hdependencies_elem") as %Hγ.
    iDestruct (big_sepMS_elem_of with "HΔ") as "#Hstate₁"; first done.
    iSteps.
  Qed.

  Lemma vertex_inv_finished t γ P R :
    vertex_inv t γ P R -∗
    vertex_finished γ ={⊤}=∗
    ▷ □ R.
  Proof.
    setoid_rewrite vertex_inv_unfold.
    iIntros "(:inv_pre) (:finished)".
    iInv "Hinv" as "(:inv_inner)".
    iDestruct (state_agree with "Hstate₁ Hstate₂") as %<-.
    iDestruct "Hinv_state" as "{Hstate₁} (:inv_state_finished >)".
    iSplitL. { iFrameSteps. }
    iSteps.
  Qed.
  Lemma vertex_inv_finished' t γ P R :
    £ 1 -∗
    vertex_inv t γ P R -∗
    vertex_finished γ ={⊤}=∗
    □ R.
  Proof.
    iIntros "H£ Hinv Hfinished".
    iMod (vertex_inv_finished with "Hinv Hfinished") as "HR".
    iApply (lc_fupd_elim_later with "H£ HR").
  Qed.
  Lemma vertex_inv_finished_output t γ P R Q :
    vertex_inv t γ P R -∗
    vertex_finished γ -∗
    vertex_output γ Q ={⊤}=∗
    ▷^2 Q.
  Proof.
    setoid_rewrite vertex_inv_unfold.
    iIntros "(:inv_pre) (:finished) (:output)".
    iInv "Hinv" as "(:inv_inner)".
    iDestruct (state_agree with "Hstate₁ Hstate₂") as %<-.
    iMod (output_consume with "Houtput_auth Houtput_frag") as "(Houtput_auth & HP)".
    iSplitR "HP". { iFrameSteps. }
    iSteps.
  Qed.
  Lemma vertex_inv_finished_output' t γ P R Q :
    £ 2 -∗
    vertex_inv t γ P R -∗
    vertex_finished γ -∗
    vertex_output γ Q ={⊤}=∗
    Q.
  Proof.
    iIntros "(H£1 & H£2) Hinv Hfinished Houtput".
    iMod (vertex_inv_finished_output with "Hinv Hfinished Houtput") as "HP".
    iMod (lc_fupd_elim_later with "H£1 HP") as "HP".
    iApply (lc_fupd_elim_later with "H£2 HP").
  Qed.

  Lemma vertex_create_spec P R (task : option val) :
    {{{
      True
    }}}
      vertex_create task
    {{{ t γ gen,
      RET #t;
      vertex_inv t γ P R ∗
      vertex_model t γ (default ()%V task) gen ∗
      vertex_output γ P
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_rec.

    wp_bind (Match _ _ _ _).
    wp_apply (wp_wand (λ res,
      ⌜res = default ()%V task⌝
    )%I) as (res) "->".
    { destruct task; iSteps. }

    wp_smart_apply (mpmc_stack_2_create_spec with "[//]") as (succs) "(#Hsuccessors_inv & Hsuccessors_model)".
    wp_block t as "(Ht_task & Ht_preds & Ht_succs & _)".
    iMod (pointsto_persist with "Ht_succs") as "#Ht_succs".

    iMod state_alloc as "(%γ_state & Hstate₁ & Hstate₂)".
    iMod dependencies_alloc as "(%gen & Hdependencies_auth)".
    iMod (generation_alloc gen) as "(%γ_generation & Hgeneration₁ & Hgeneration₂)".
    iMod predecessors_alloc as "(%γ_predecessors & Hpredecessors_auth)".
    iMod (output_alloc P) as "(%γ_output & Houtput_auth & Houtput_frag)".

    pose γ := {|
      vertex_name_successors := succs ;
      vertex_name_state := γ_state ;
      vertex_name_generation := γ_generation ;
      vertex_name_predecessors := γ_predecessors ;
      vertex_name_output := γ_output ;
    |}.

    iApply ("HΦ" $! t γ).
    iSplitR "Ht_task Hstate₁ Hgeneration₁ Houtput_frag"; last iSteps.
    rewrite vertex_inv_unfold. iStep 2.
    iApply inv_alloc.
    iExists 1, Init, gen, ∅. iFrame. iSplitR "Hsuccessors_model".
    - rewrite /inv_state /inv_state_init.
      iExists ∅. rewrite big_sepMS_empty left_id. iSteps.
    - iExists []. iSteps.
  Qed.

  Lemma vertex_task_spec t γ task gen :
    {{{
      vertex_model t γ task gen
    }}}
      vertex_task #t
    {{{
      RET task;
      vertex_model t γ task gen
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma vertex_set_task_spec t γ task1 gen task2 :
    {{{
      vertex_model t γ task1 gen
    }}}
      vertex_set_task #t task2
    {{{
      RET ();
      vertex_model t γ task2 gen
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma vertex_set_task'_spec t γ task1 gen task2 :
    {{{
      vertex_model t γ task1 gen
    }}}
      vertex_set_task' #t task2
    {{{
      RET ();
      vertex_model t γ (fun: "ctx" => task2 "ctx" ;; #false) gen
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".

    wp_rec.
    wp_smart_apply (vertex_set_task_spec with "Hmodel HΦ").
  Qed.

  Lemma vertex_precede_spec t1 γ1 P1 R1 t2 γ2 P2 R2 task gen :
    {{{
      vertex_inv t1 γ1 P1 R1 ∗
      vertex_inv t2 γ2 P2 R2 ∗
      vertex_model t2 γ2 task gen
    }}}
      vertex_precede #t1 #t2
    {{{
      RET ();
      vertex_model t2 γ2 task gen ∗
      vertex_predecessor γ1 gen
    }}}.
  Proof.
    setoid_rewrite vertex_inv_unfold.
    iIntros "%Φ ((:inv_pre =1) & (:inv_pre =2) & (:model which=2)) HΦ".

    wp_rec.
    iApply (wp_frame_wand with "[Ht2_task HΦ]"); first iAccu.
    wp_load.

    awp_smart_apply (mpmc_stack_2_is_closed_spec with "Hsuccessors1_inv") without "Hstate2₁ Hgeneration2₁".
    iInv "Hinv_1" as "(:inv_inner which=1 =1)".
    case_decide as Hstate1; first subst.

    - iDestruct "Hinv_state1" as "(:inv_state_finished which=1 =1 >) /=".
      iDestruct "Hinv_successors1" as "(:inv_successors_finished which=1 =1)".
      iAaccIntro with "Hsuccessors1_model"; iIntros "Hsuccs1_model !>".
      { iFrameSteps. }
      iSplitL. { iFrameSteps. }
      iIntros "{%} _ (Hstate2₁ & Hgeneration2₁)".

      iApply fupd_wp.
      iInv "Hinv_2" as "(:inv_inner which=2 =1)".
      iDestruct (state_agree with "Hstate2₁ Hstate2₂") as %<-.
      iDestruct (generation_agree with "Hgeneration2₁ Hgeneration2₂") as %<-.
      iDestruct "Hinv_state2" as "(:inv_state_init which=2 =1 >)".
      iMod (dependencies_add γ1 with "Hdependencies2_auth") as "(Hdependencies2_auth & #Hdependencies2_elem)".
      iDestruct (big_sepMS_insert_2 γ1 with "HΔ Hstate1₁") as "HΔ".
      iSplitR "Hstate2₁ Hgeneration2₁".
      { assert ({[+γ1+]} ⊎ (Δ ⊎ Π) = ({[+γ1+]} ⊎ Δ) ⊎ Π) as ->.
        { rewrite assoc //. }
        iFrame. rewrite /inv_state. iFrameSteps.
      }
      iSteps.

    - iDestruct "Hinv_successors1" as "(:inv_successors which=1 =1)".
      iAaccIntro with "Hsuccessors1_model"; iIntros "Hsuccs_model !>".
      { iFrameSteps. rewrite bool_decide_eq_false_2 //. iSteps. }
      iSplitL.
      { iFrameSteps. rewrite bool_decide_eq_false_2 //. iSteps. }
      iIntros "{%} _ (Hstate2₁ & Hgeneration2₁)".

      wp_pures.

      wp_bind (FAA _ _).
      iInv "Hinv_2" as "(:inv_inner which=2 =1)".
      wp_faa.
      iDestruct (state_agree with "Hstate2₁ Hstate2₂") as %<-.
      iDestruct (generation_agree with "Hgeneration2₁ Hgeneration2₂") as %<-.
      iDestruct "Hinv_state2" as "(:inv_state_init which=2 =1)".
      iMod (dependencies_add γ1 with "Hdependencies2_auth") as "(Hdependencies2_auth & #Hdependencies2_elem)".
      iMod (predecessors_add γ1 with "Hpredecessors2_auth") as "(Hpredecessors2_auth & Hpredecessors2_elem )".
      iSplitR "Hstate2₁ Hgeneration2₁ Hpredecessors2_elem".
      { assert ({[+γ1+]} ⊎ (Δ ⊎ Π) = Δ ⊎ ({[+γ1+]} ⊎ Π)) as ->.
        { rewrite assoc (comm _ _ Δ) -assoc //. }
        iFrameSteps. iPureIntro.
        rewrite gmultiset_size_disj_union gmultiset_size_singleton. lia.
      }
      iIntros "!> {%}".

      wp_pures. clear.

      awp_apply (mpmc_stack_2_push_spec with "Hsuccessors1_inv") without "Hstate2₁ Hgeneration2₁".
      iInv "Hinv_1" as "(:inv_inner which=1 =2)".
      case_decide as Hstate2; first subst.

      + iDestruct "Hinv_state1" as "(:inv_state_finished which=1 =2 >) /=".
        iDestruct "Hinv_successors1" as "(:inv_successors_finished which=1 =2)".
        iAaccIntro with "Hsuccessors1_model"; iIntros "Hsuccs1_model !>".
        { iFrameSteps. }
        iSplitR "Hpredecessors2_elem". { iFrameSteps. }
        iIntros "{%} _ (Hstate2₁ & Hgeneration2₁)".

        wp_pures.

        wp_bind (FAA _ _).
        iInv "Hinv_2" as "(:inv_inner which=2 =2)".
        wp_faa.
        iDestruct (state_agree with "Hstate2₁ Hstate2₂") as %<-.
        iDestruct (generation_agree with "Hgeneration2₁ Hgeneration2₂") as %<-.
        iDestruct "Hinv_state2" as "(:inv_state_init which=2 =2)".
        iDestruct (predecessors_elem_of with "Hpredecessors2_auth Hpredecessors2_elem") as %Hγ1.
        iMod (predecessors_remove with "Hpredecessors2_auth Hpredecessors2_elem") as "Hpredecessors2_auth".
        iDestruct (big_sepMS_insert_2 γ1 with "HΔ Hstate1₁") as "HΔ".
        iSplitR "Hstate2₁ Hgeneration2₁".
        { replace (Δ ⊎ Π) with ({[+γ1+]} ⊎ Δ ⊎ Π ∖ {[+γ1+]}) by multiset_solver.
          iFrameSteps. iPureIntro.
          rewrite gmultiset_size_difference; first multiset_solver.
          rewrite gmultiset_size_singleton.
          apply gmultiset_elem_of_size_non_empty in Hγ1.
          lia.
        }
        iSteps.

      + iDestruct "Hinv_successors1" as "(:inv_successors which=1 =2)".
        iAaccIntro with "Hsuccessors1_model"; iIntros "Hsuccs_model !>".
        { iFrameSteps. rewrite bool_decide_eq_false_2 //. iSteps. }
        iSplitL.
        { iFrameSteps. rewrite bool_decide_eq_false_2 //. iSteps.
          iExists (t2 :: succs). iSteps.
          iExists γ2, P2, R2. rewrite vertex_inv_unfold. iSteps.
        }
        iSteps.
  Qed.

  #[local] Lemma vertex_release_run_spec :
    ⊢ (
      ∀ ctx t γ P R task gen,
      {{{
        pool_context_model ctx ∗
        vertex_inv t γ P R ∗
        vertex_model t γ task gen ∗
        vertex_wp t γ P R task gen
      }}}
        vertex_release ctx #t
      {{{
        RET ();
        pool_context_model ctx
      }}}
    ) ∧ (
      ∀ ctx t γ P R π,
      {{{
        pool_context_model ctx ∗
        vertex_inv t γ P R ∗
        predecessors_elem γ π ∗
        vertex_finished π
      }}}
        vertex_release ctx #t
      {{{
        RET ();
        pool_context_model ctx
      }}}
    ) ∧ (
      ∀ ctx t γ gen P R task,
      {{{
        pool_context_model ctx ∗
        vertex_inv t γ P R ∗
        vertex_running gen ∗
        model' t γ task Running gen ∗
        vertex_wp t γ P R task gen
      }}}
        vertex_run ctx #t
      {{{
        RET ();
        pool_context_model ctx
      }}}
    ).
  Proof.
    iLöb as "HLöb".
    iDestruct "HLöb" as "(IHrelease & IHrelease_successor & IHrun)".
    repeat iSplit.

    { iClear "IHrelease IHrelease_successor".
      setoid_rewrite vertex_inv_unfold.
      iIntros "%ctx %t %γ %P %R %task %gen !> %Φ (Hctx & (:inv_pre) & (:model) & Htask) HΦ".

      wp_recs.
      iApply (wp_frame_wand with "HΦ").
      wp_pures.

      wp_bind (FAA _ _).
      iInv "Hinv" as "(:inv_inner =1)".
      wp_faa.
      iDestruct (state_agree with "Hstate₁ Hstate₂") as %<-.
      iDestruct (generation_agree with "Hgeneration₁ Hgeneration₂") as %<-.
      iDestruct "Hinv_state" as "(:inv_state_init =1)".

      destruct (decide (size Π = 0)) as [->%gmultiset_size_empty_inv | HΠ].

      - rewrite gmultiset_size_empty right_id.
        iMod (state_update Running with "Hstate₁ Hstate₂") as "(Hstate₁ & Hstate₂)".
        iMod (dependencies_discard with "Hdependencies_auth") as "#Hdependencies_auth".
        iDestruct "HΔ" as "#HΔ".
        iSplitR "Hctx Ht_task Hstate₁ Hgeneration₁ Htask". { iFrameSteps. }
        iIntros "{%} !>".

        wp_smart_apply ("IHrun" with "[$]").
        iSteps.

      - iMod (state_update Released with "Hstate₁ Hstate₂") as "(Hstate₁ & Hstate₂)".
        iMod (dependencies_discard with "Hdependencies_auth") as "#Hdependencies_auth".
        iSplitR "Hctx". { iFrameSteps. }
        iSteps.
    }

    { iClear "IHrelease IHrelease_successor".
      setoid_rewrite vertex_inv_unfold.
      iIntros "%ctx %t %γ %P %R %π !> %Φ (Hctx & (:inv_pre) & Hpredecessors_elem & #Hπ) HΦ".

      wp_recs.
      iApply (wp_frame_wand with "HΦ").
      wp_pures.

      wp_bind (FAA _ _).
      iInv "Hinv" as "(:inv_inner)".
      wp_faa.
      iDestruct (predecessors_elem_of with "Hpredecessors_auth Hpredecessors_elem") as %Hπ.
      iMod (predecessors_remove with "Hpredecessors_auth Hpredecessors_elem") as "Hpredecessors_auth".

      destruct state.

      - iDestruct "Hinv_state" as "(:inv_state_init)".
        iDestruct (big_sepMS_insert_2 with "HΔ Hπ") as "HΔ".
        apply gmultiset_elem_of_size_non_empty in Hπ as ?.
        iSplitR "Hctx".
        { replace (Δ ⊎ Π) with (({[+π+]} ⊎ Δ) ⊎ (Π ∖ {[+π+]})) by multiset_solver.
          iFrameSteps. iPureIntro.
          rewrite gmultiset_size_difference; first multiset_solver.
          rewrite gmultiset_size_singleton.
          lia.
        }
        iSteps.

      - iDestruct "Hinv_state" as "(:inv_state_released)".
        iDestruct (big_sepMS_insert_2 with "HΔ Hπ") as "-##HΔ".
        iEval (rewrite (comm (⊎))) in "HΔ".
        destruct (decide (size Π = 1)) as [HΠ |].

        + rewrite HΠ.
          assert (Π = {[+π+]}) as ->.
          { apply gmultiset_size_1_elem_of in HΠ as (π_ & ->).
            set_solver.
          }
          rewrite gmultiset_difference_diag.

          iMod (state_update Running with "Hstate₁ Hstate₂") as "(Hstate₁ & Hstate₂)".
          iSplitR "Hctx Hdependencies_auth Ht_task Hstate₁ Hgeneration₁ Htask". { iFrameSteps. }
          iIntros "{%} !>".

          wp_smart_apply ("IHrun" with "[$]").
          iSteps.

        + apply gmultiset_elem_of_size_non_empty in Hπ as ?.
          iSplitR "Hctx".
          { replace (Δ ⊎ Π) with ((Δ ⊎ {[+π+]}) ⊎ (Π ∖ {[+π+]})) by multiset_solver.
            iFrameSteps. iPureIntro.
            rewrite gmultiset_size_difference; first multiset_solver.
            rewrite gmultiset_size_singleton.
            lia.
          }
          iSteps.

      - iDestruct "Hinv_state" as "(:inv_state_running)".
        exfalso. set_solver.

      - iDestruct "Hinv_state" as "(:inv_state_finished)".
        assert (Π ≠ ∅) as ?%gmultiset_size_non_empty_iff by multiset_solver.
        iSplitR "Hctx".
        { iFrameSteps. iPureIntro.
          rewrite gmultiset_size_difference; first multiset_solver.
          rewrite gmultiset_size_singleton.
          lia.
        }
        iSteps.
    }

    { iClear "IHrun".
      setoid_rewrite vertex_inv_unfold.
      iIntros "%ctx %t %γ %gen %P %R %task !> %Φ (Hctx & (:inv_pre) & #Hrunning & (:model') & Htask) HΦ".

      wp_recs.
      wp_smart_apply (pool_silent_async_spec with "[-HΦ $Hctx] HΦ"). iIntros "{%} %ctx Hctx".
      wp_pures.

      wp_bind (_ <-{preds} _)%E.
      iInv "Hinv" as "(:inv_inner =1)".
      wp_store.
      iDestruct (state_agree with "Hstate₁ Hstate₂") as %<-.
      iMod (state_update Init with "Hstate₁ Hstate₂") as "(Hstate₁ & Hstate₂)".
      iDestruct "Hinv_state" as "(:inv_state_running =1)".
      iMod dependencies_alloc as "(%gen' & Hdependencies_auth)".
      iMod (generation_update gen' with "Hgeneration₁ Hgeneration₂") as "(Hgeneration₁ & Hgeneration₂)".
      iSplitR "Hctx Ht_task Hstate₁ Hgeneration₁ Htask".
      { iFrameSteps.
        iExists ∅. rewrite left_id big_sepMS_empty. iSteps.
      }
      iIntros "{%} !>".

      wp_load.

      rewrite vertex_wp_unfold.
      wp_apply (wp_wand with "(Htask Hctx [$] [$])") as (res) "{%} (%b & %task & -> & Hctx & (:model) & Hb)".
      destruct b.

      - wp_smart_apply ("IHrelease" with "[$]").
        iSteps.

      - iDestruct "Hb" as "(HP & #HR)".

        wp_load.

        awp_apply (mpmc_stack_2_close_spec with "Hsuccessors_inv") without "Hctx".
        iInv "Hinv" as "(:inv_inner =2)".
        iDestruct (state_agree with "Hstate₁ Hstate₂") as %<-.
        iDestruct "Hinv_state" as "(:inv_state_init =2 >)".
        iDestruct "Hinv_successors" as "(:inv_successors =2)".
        iAaccIntro with "Hsuccessors_model"; iIntros "Hsuccessors_model"; first iFrameSteps.
        iMod (state_update Finished with "Hstate₁ Hstate₂") as "(Hstate₁ & Hstate₂)".
        iMod (state₁_discard with "Hstate₁") as "#Hstate₁".
        iDestruct (output_produce with "Houtput_auth HP") as "Houtput_auth".
        iSplitR "Hsuccs". { iFrameSteps. }
        iIntros "!> H£ Hctx {%}".

        iMod (lc_fupd_elim_later with "H£ Hsuccs") as "Hsuccs".
        wp_smart_apply (clst_iter_spec (λ _, pool_context_model ctx) with "[$Hctx Hsuccs]"); [done | | iSteps].
        rewrite big_sepL_fmap.
        iApply (big_sepL_impl with "Hsuccs"). iIntros "!> %i %succ _ (:inv_successor) Hctx".
        wp_smart_apply ("IHrelease_successor" with "[$Hctx $Hpredecessors_elem $Hstate₁]"); last iSteps.
        iApply (vertex_inv_unfold with "Hinv_succ").
    }
  Qed.
  Lemma vertex_release_spec ctx t γ P R task gen :
    {{{
      pool_context_model ctx ∗
      vertex_inv t γ P R ∗
      vertex_model t γ task gen ∗
      vertex_wp t γ P R task gen
    }}}
      vertex_release ctx #t
    {{{
      RET ();
      pool_context_model ctx
    }}}.
  Proof.
    iDestruct vertex_release_run_spec as "(H & _)".
    iApply "H".
  Qed.
  Lemma vertex_release_spec' ctx t γ P R task gen :
    {{{
      pool_context_model ctx ∗
      vertex_inv t γ P R ∗
      vertex_model t γ task gen ∗
      ( ∀ ctx,
        pool_context_model ctx -∗
        vertex_running gen -∗
        WP task ctx {{ res,
          ⌜res = #false⌝ ∗
          ▷ pool_context_model ctx ∗
          ▷ P ∗
          ▷ □ R
        }}
      )
    }}}
      vertex_release ctx #t
    {{{
      RET ();
      pool_context_model ctx
    }}}.
  Proof.
    iIntros "%Φ (Hctx & #Hinv & Hmodel & Htask) HΦ".

    wp_apply (vertex_release_spec with "[- HΦ] HΦ").
    rewrite vertex_wp_unfold. iFrameSteps.
  Qed.
End vertex_G.

From zoo_parabs Require
  vertex__opaque.

#[global] Opaque vertex_inv.
#[global] Opaque vertex_model.
#[global] Opaque vertex_output.
#[global] Opaque vertex_running.
#[global] Opaque vertex_finished.
#[global] Opaque vertex_predecessor.
#[global] Opaque vertex_wp.
