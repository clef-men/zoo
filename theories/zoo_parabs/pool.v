From zoo Require Import
  prelude.
From zoo.common Require Import
  countable
  gmultiset.
From zoo.iris.bi Require Import
  big_op.
From zoo.iris.base_logic Require Import
  lib.ghost_list
  lib.mono_gmultiset
  lib.saved_prop
  lib.spsc_prop.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  array
  domain.
From zoo_parabs Require Export
  base
  pool__code.
From zoo_parabs Require Import
  pool__types
  ws_hub_std.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types v ctx hub task pred : val.
Implicit Types empty : emptiness.
Implicit Types own : ownership.
Implicit Types η : spsc_prop_name.

#[local] Definition max_round_noyield :=
  val_to_nat' pool_max_round_noyield.
#[local] Lemma pool_max_round_noyield :
  pool_max_round_noyield = #max_round_noyield.
Proof.
  done.
Qed.
Opaque pool__code.pool_max_round_noyield.
Opaque max_round_noyield.

#[local] Definition max_round_yield :=
  val_to_nat' pool_max_round_yield.
#[local] Lemma pool_max_round_yield :
  pool_max_round_yield = #max_round_yield.
Proof.
  done.
Qed.
Opaque pool__code.pool_max_round_yield.
Opaque max_round_yield.

Record job := {
  job_val : val ;
  job_name : gname ;
}.
Implicit Types job local global : job.

#[local] Instance job_inhabited : Inhabited job :=
  populate {|
    job_val := inhabitant ;
    job_name := inhabitant ;
  |}.
#[local] Instance job_eq_dec : EqDecision job :=
  ltac:(solve_decision).
#[local] Instance job_countable :
  Countable job.
Proof.
  solve_countable.
Qed.

Implicit Types jobs locals ulocals globals : gmultiset job.
Implicit Types localss : list $ gmultiset job.

Definition pool_scope :=
  gmultiset job.

#[global] Instance pool_scope_eq_dec : EqDecision pool_scope :=
  _.
#[global] Instance pool_scope_countable :
  Countable pool_scope.
Proof.
  apply _.
Qed.

Class PoolG Σ `{zoo_G : !ZooG Σ} := {
  #[local] pool_G_domain_G :: DomainG Σ ;
  #[local] pool_G_ws_hub_G :: WsHubStdG Σ ;
  #[local] pool_G_saved_prop_G :: SavedPropG Σ ;
  #[local] pool_G_jobs_G :: MonoGmultisetG Σ job ;
  #[local] pool_G_locals_G :: GhostListG Σ (gmultiset job) ;
  #[local] pool_G_consumer_G :: SpscPropG Σ ;
}.

Definition pool_Σ := #[
  domain_Σ ;
  ws_hub_std_Σ ;
  saved_prop_Σ ;
  mono_gmultiset_Σ job ;
  ghost_list_Σ (gmultiset job) ;
  spsc_prop_Σ
].
#[global] Instance subG_pool_Σ Σ `{zoo_G : !ZooG Σ} :
  subG pool_Σ Σ →
  PoolG Σ.
Proof.
  solve_inG.
Qed.

Module base.
  Section pool_G.
    Context `{pool_G : PoolG Σ}.

    Implicit Types t : location.
    Implicit Types P Q : iProp Σ.
    Implicit Types Ψ : val → iProp Σ.

    Record pool_name := {
      pool_name_size : nat ;
      pool_name_hub : val ;
      pool_name_domains : val ;
      pool_name_jobs : gname ;
      pool_name_locals : gname ;
    }.
    Implicit Types γ : pool_name.
    Implicit Types γ_tokens : list gname.

    #[global] Instance pool_name_eq_dec : EqDecision pool_name :=
      ltac:(solve_decision).
    #[global] Instance pool_name_countable :
      Countable pool_name.
    Proof.
      solve_countable.
    Qed.

    #[local] Definition pool_name_context γ (i : nat) :=
      ( #γ.(pool_name_size),
        γ.(pool_name_hub),
        #i
      )%V.
    #[local] Instance pool_name_context_inj γ :
      Inj (=) (=) (pool_name_context γ).
    Proof.
      rewrite /Inj. naive_solver.
    Qed.

    #[local] Definition jobs_auth' γ_jobs own :=
      mono_gmultiset_auth γ_jobs own.
    #[local] Definition jobs_auth γ :=
      jobs_auth' γ.(pool_name_jobs).
    #[local] Definition jobs_elem γ :=
      mono_gmultiset_elem γ.(pool_name_jobs).

    #[local] Definition jobs_finished jobs : iProp Σ :=
      [∗ mset] job ∈ jobs,
        ∃ P,
        saved_prop job.(job_name) P ∗
        □ P.

    #[local] Definition locals_auth' sz γ_locals ulocals : iProp Σ :=
      ∃ localss,
      ⌜length localss = S sz⌝ ∗
      ghost_list_auth γ_locals localss ∗
      ⌜ulocals = ⋃+ localss⌝.
    #[local] Definition locals_auth γ :=
      locals_auth' γ.(pool_name_size) γ.(pool_name_locals).
    #[local] Instance : CustomIpat "locals_auth" :=
      " ( %localss{} &
          %Hlocalss{} &
          Hauth{_{}} &
          ->
        )
      ".
    #[local] Definition locals_at_running γ_locals i scope : iProp Σ :=
      ∃ locals,
      ghost_list_at γ_locals i Own (scope ⊎ locals) ∗
      jobs_finished locals.
    #[local] Instance : CustomIpat "locals_at_running" :=
      " ( %locals{} &
          Hat{_{}} &
          Hjobs_finished_locals{}
        )
      ".
    #[local] Definition locals_at_finished γ_locals i : iProp Σ :=
      ∃ locals,
      ghost_list_at γ_locals i Own locals.
    #[local] Instance : CustomIpat "locals_at_finished" :=
      " ( %locals{} &
          Hat{_{}}
        )
      ".
    #[local] Definition locals_at' γ_locals i scope : iProp Σ :=
      match scope with
      | Some scope =>
          locals_at_running γ_locals i scope
      | None =>
          locals_at_finished γ_locals i
      end.
    #[local] Definition locals_at γ :=
      locals_at' γ.(pool_name_locals).

    #[local] Definition globals_model_running γ globals : iProp Σ :=
      ∃ jobs ulocals,
      ⌜jobs = globals ⊎ ulocals⌝ ∗
      jobs_auth γ Own jobs ∗
      locals_auth γ ulocals.
    #[local] Instance : CustomIpat "globals_model_running" :=
      " ( %jobs &
          %ulocals &
          -> &
          Hjobs_auth &
          Hlocals_auth
        )
      ".
    #[local] Definition globals_model_finished γ : iProp Σ :=
      [∗ list] i ∈ seq 0 (S γ.(pool_name_size)),
        locals_at γ i None.
    #[local] Instance : CustomIpat "globals_model_finished" :=
      "Hlocals_ats".
    #[local] Definition globals_model γ globals : iProp Σ :=
        globals_model_running γ globals
      ∨ globals_model_finished γ.
    #[local] Instance : CustomIpat "globals_model" :=
      " [ (:globals_model_running)
        | (:globals_model_finished)
        ]
      ".

    #[local] Definition context_1 γ i (scope : pool_scope) : iProp Σ :=
      ∃ empty,
      ws_hub_std_owner γ.(pool_name_hub) i Nonblocked empty ∗
      locals_at γ i (Some scope).
    #[local] Instance : CustomIpat "context_1" :=
      " ( %empty{} &
          Hhub_owner{_{}} &
          Hlocals_at{_{}}
        )
      ".

    #[local] Definition task_model γ task Ψ : iProp Σ :=
      ∀ i scope,
      ⌜i ≤ γ.(pool_name_size)⌝ -∗
      context_1 γ i scope -∗
      WP task (pool_name_context γ i) {{ v,
        context_1 γ i scope ∗
        Ψ v
      }}.

    #[local] Definition inv_inner γ : iProp Σ :=
      ∃ globals 𝑔𝑙𝑜𝑏𝑎𝑙𝑠,
      ⌜𝑔𝑙𝑜𝑏𝑎𝑙𝑠 = gmultiset_map job_val globals⌝ ∗
      globals_model γ globals ∗
      ws_hub_std_model γ.(pool_name_hub) 𝑔𝑙𝑜𝑏𝑎𝑙𝑠 ∗
      [∗ mset] global ∈ globals,
        task_model γ global.(job_val) (λ _,
          ∃ P,
          saved_prop global.(job_name) P ∗
          ▷ □ P
        ).
    #[local] Instance : CustomIpat "inv_inner" :=
      " ( %globals &
          %𝑔𝑙𝑜𝑏𝑎𝑙𝑠 &
          >%H𝑔𝑙𝑜𝑏𝑎𝑙𝑠 &
          >Hglobals_model &
          >Hhub_model &
          Hglobals
        )
      ".
    #[local] Definition inv_1 γ : iProp Σ :=
      inv (nroot.@"inv") (inv_inner γ).
    #[local] Definition inv_2 γ : iProp Σ :=
      ws_hub_std_inv γ.(pool_name_hub) (nroot.@"hub") (S γ.(pool_name_size)) ∗
      inv_1 γ.
    #[local] Instance : CustomIpat "inv_2" :=
      " ( #Hhub_inv{_{}} &
          #Hinv{_{}}
        )
      ".
    Definition pool_inv γ sz : iProp Σ :=
      ⌜sz = γ.(pool_name_size)⌝ ∗
      inv_2 γ.
    #[local] Instance : CustomIpat "inv" :=
      " ( -> &
          {#Hinv_{};(:inv_2)}
        )
      ".

    #[local] Definition context_finished γ i : iProp Σ :=
      ws_hub_std_owner γ.(pool_name_hub) i Nonblocked Empty ∗
      locals_at γ i (Some ∅).
    #[local] Instance : CustomIpat "context_finished" :=
      " ( Hhub_owner{_{}} &
          Hlocals_at{_{}}
        )
      ".
    #[local] Definition context_2 γ i scope : iProp Σ :=
      ⌜i ≤ γ.(pool_name_size)⌝ ∗
      inv_2 γ ∗
      context_1 γ i scope.
    #[local] Instance : CustomIpat "context_2" :=
      " ( %Hi{} &
          {#Hinv_{};(:inv_2)} &
          { {lazy} Hctx{}
          ; {lazy} Hctx
          ; (:context_1 ={})
          ; (:context_1)
          }
        )
      ".
    Definition pool_context γ ctx scope : iProp Σ :=
      ∃ i,
      ⌜ctx = pool_name_context γ i⌝ ∗
      context_2 γ i scope.
    #[local] Instance : CustomIpat "context" :=
      " ( %i{} &
          {%Heq{};->} &
          (:context_2)
        )
      ".

    #[local] Definition worker_post γ i res : iProp Σ :=
      ⌜res = ()%V⌝ ∗
      context_finished γ i.
    #[local] Instance : CustomIpat "worker_post" :=
      " ( -> &
          (:context_finished)
        )
      ".

    Definition pool_model t γ : iProp Σ :=
      ∃ empty doms,
      ⌜length doms = γ.(pool_name_size)⌝ ∗
      t.[size] ↦□ #γ.(pool_name_size) ∗
      t.[hub] ↦□ γ.(pool_name_hub) ∗
      t.[domains] ↦□ γ.(pool_name_domains) ∗
      inv_2 γ ∗
      array_model γ.(pool_name_domains) DfracDiscarded doms ∗
      ( [∗ list] i ↦ dom ∈ doms,
        domain_model dom (worker_post γ (S i))
      ) ∗
      ws_hub_std_owner γ.(pool_name_hub) 0 Blocked empty ∗
      locals_at γ 0 (Some ∅).
    #[local] Instance : CustomIpat "model" :=
      " ( %empty{} &
          %doms{} &
          %Hdoms{} &
          #Hl{}_size &
          #Hl{}_hub &
          #Hl{}_domains &
          {#Hinv{};(:inv_2)} &
          Hdomains{} &
          Hdoms{} &
          Hhub{}_owner &
          Hlocals_at{_{}}
        )
      ".

    Definition pool_finished γ : iProp Σ :=
      ∃ jobs,
      jobs_auth γ Discard jobs ∗
      jobs_finished jobs.
    #[local] Instance : CustomIpat "finished" :=
      " ( %jobs{} &
          Hjobs_auth{_{}} &
          Hjobs_finished{_jobs{}}
        )
      ".

    Definition pool_obligation γ P : iProp Σ :=
      □ (
        pool_finished γ -∗
        ▷ □ P
      ).

    Definition pool_consumer γ P : iProp Σ :=
      pool_finished γ ={⊤}=∗
      P.

    #[local] Instance globals_model_timeless γ globals :
      Timeless (globals_model γ globals).
    Proof.
      apply _.
    Qed.

    #[local] Instance jobs_elem_persistent γ job :
      Persistent (jobs_elem γ job).
    Proof.
      apply _.
    Qed.
    #[local] Instance jobs_finished_persistent jobs :
      Persistent (jobs_finished jobs).
    Proof.
      apply _.
    Qed.
    #[global] Instance pool_inv_persistent γ sz :
      Persistent (pool_inv γ sz).
    Proof.
      apply _.
    Qed.
    #[global] Instance pool_obligation_persistent γ P :
      Persistent (pool_obligation γ P).
    Proof.
      apply _.
    Qed.
    #[global] Instance pool_finished_persistent γ :
      Persistent (pool_finished γ).
    Proof.
      apply _.
    Qed.

    #[local] Lemma jobs_alloc :
      ⊢ |==>
        ∃ γ_jobs,
        jobs_auth' γ_jobs Own ∅.
    Proof.
      apply mono_gmultiset_alloc.
    Qed.
    #[local] Lemma jobs_auth_discard γ jobs :
      jobs_auth γ Own jobs ⊢ |==>
      jobs_auth γ Discard jobs.
    Proof.
      apply mono_gmultiset_auth_persist.
    Qed.
    #[local] Lemma jobs_elem_valid γ own jobs job :
      jobs_auth γ own jobs -∗
      jobs_elem γ job -∗
      ⌜job ∈ jobs⌝.
    Proof.
      apply mono_gmultiset_elem_valid.
    Qed.
    #[local] Lemma jobs_insert {γ jobs} 𝑗𝑜𝑏 P :
      jobs_auth γ Own jobs ⊢ |==>
        ∃ job,
        ⌜job.(job_val) = 𝑗𝑜𝑏⌝ ∗
        jobs_auth γ Own ({[+job+]} ⊎ jobs) ∗
        jobs_elem γ job ∗
        saved_prop job.(job_name) P.
    Proof.
      iIntros "Hauth".
      iMod (saved_prop_alloc P) as "(%η & #Hη)".
      pose job := {|
        job_val := 𝑗𝑜𝑏 ;
        job_name := η ;
      |}.
      iMod (mono_gmultiset_insert job with "Hauth") as "Hauth".
      iDestruct (mono_gmultiset_elem_get job with "Hauth") as "#Helem"; first set_solver.
      iFrameSteps.
    Qed.
    Opaque jobs_elem.

    #[local] Lemma jobs_finished_empty :
      ⊢ jobs_finished ∅.
    Proof.
      iApply (big_sepMS_empty with "[//]").
    Qed.
    #[local] Lemma jobs_finished_elem_of job jobs :
      job ∈ jobs →
      jobs_finished jobs ⊢
        ∃ P,
        saved_prop job.(job_name) P ∗
        □ P.
    Proof.
      apply: big_sepMS_elem_of.
    Qed.
    #[local] Lemma jobs_finished_insert {jobs} job P :
      jobs_finished jobs -∗
      saved_prop job.(job_name) P -∗
      □ P -∗
      jobs_finished ({[+job+]} ⊎ jobs).
    Proof.
      iIntros "Hfinished #Hjob #HP".
      iApply (big_sepMS_insert_2 with "Hfinished").
      iSteps.
    Qed.
    #[local] Lemma jobs_finished_union localss :
      ( [∗ list] locals ∈ localss,
        jobs_finished locals
      ) ⊢
      jobs_finished (⋃+ localss).
    Proof.
      apply big_sepMS_disj_union_list_2.
    Qed.
    Opaque jobs_finished.

    #[local] Lemma locals_alloc sz :
      ⊢ |==>
        ∃ γ_locals,
        locals_auth' sz γ_locals ∅ ∗
        [∗ list] i ∈ seq 0 (S sz),
          locals_at' γ_locals i (Some ∅).
    Proof.
      iMod (ghost_list_alloc (replicate (S sz) ∅)) as "(%γ_locals & $ & Hats)".
      iSplitR.
      - iPureIntro. split.
        + simpl_length.
        + rewrite gmultiset_disj_union_list_replicate_empty //.
      - iApply big_sepL_replicate_1 in "Hats".
        iApply (big_sepL_impl with "Hats"). iIntros "!> !> %i_ %i _ Hat".
        iExists ∅. rewrite right_id. iFrame.
        iApply jobs_finished_empty.
    Qed.
    #[local] Lemma locals_at_exclusive γ i scope1 scope2 :
      locals_at γ i scope1 -∗
      locals_at γ i scope2 -∗
      False.
    Proof.
      all:
        destruct scope1 as [scope1 |];
        [ iIntros "(:locals_at_running =1)"
        | iIntros "(:locals_at_finished =1)"
        ].
      all:
        destruct scope2 as [scope2 |];
        [ iIntros "(:locals_at_running =2)"
        | iIntros "(:locals_at_finished =2)"
        ].
      all: iApply (ghost_list_at_exclusive with "Hat_1 Hat_2").
    Qed.
    #[local] Lemma locals_insert {γ ulocals i scope} local :
      locals_auth γ ulocals -∗
      locals_at γ i (Some scope) ==∗
        locals_auth γ ({[+local+]} ⊎ ulocals) ∗
        locals_at γ i (Some ({[+local+]} ⊎ scope)).
    Proof.
      iIntros "(:locals_auth) (:locals_at_running)".
      iDestruct (ghost_list_lookup with "Hauth Hat") as %Hlookup.
      iMod (ghost_list_update_at ({[+local+]} ⊎ scope ⊎ locals) with "Hauth Hat") as "($ & $)".
      iFrameSteps; iPureIntro.
      { simpl_length. }
      { rewrite -assoc gmultiset_disj_union_list_insert_disj_union_l //. }
    Qed.
    #[local] Lemma locals_at_finish γ i local P scope :
      locals_at γ i (Some ({[+local+]} ⊎ scope)) -∗
      saved_prop local.(job_name) P -∗
      □ P -∗
      locals_at γ i (Some scope).
    Proof.
      iIntros "(:locals_at_running) Hlocal HP".
      iDestruct (jobs_finished_insert with "Hjobs_finished_locals Hlocal HP") as "$".
      rewrite (comm (⊎) {[+_+]} scope) assoc //.
    Qed.
    #[local] Lemma locals_kill γ ulocals :
      locals_auth γ ulocals -∗
      ( [∗ list] i ∈ seq 0 (S γ.(pool_name_size)),
        locals_at γ i (Some ∅)
      ) -∗
        locals_auth γ ulocals ∗
        ( [∗ list] i ∈ seq 0 (S γ.(pool_name_size)),
          locals_at γ i None
        ) ∗
        jobs_finished ulocals.
    Proof.
      iIntros "(:locals_auth) Hats".
      iDestruct (big_sepL_seq_exists with "Hats") as "(%localss_ & %Hlocalss_ & Hats)".
      iDestruct (big_sepL_sep with "Hats") as "(Hats & Hjobs_finisheds)".
      iEval (setoid_rewrite (left_id ∅ (⊎))) in "Hats".
      iDestruct (ghost_list_auth_ats with "Hauth Hats") as %<-; first lia.
      iSplitL "Hauth"; first iFrameSteps.
      iDestruct (jobs_finished_union with "Hjobs_finisheds") as "$".
      iApply big_sepL_to_seq0 in "Hats".
      iEval (rewrite Hlocalss) in "Hats".
      iApply (big_sepL_impl with "Hats"). iIntros "!> %i_ %i _ (%locals & _ & $)".
    Qed.
    Opaque locals_auth'.
    Opaque locals_at'.

    #[local] Lemma globals_model_init γ :
      jobs_auth γ Own ∅ -∗
      locals_auth γ ∅ -∗
      globals_model γ ∅.
    Proof.
      iIntros "Hjobs_auth Hlocals_auth".
      iLeft. iExists ∅, ∅. iFrameSteps.
    Qed.
    #[local] Lemma globals_model_locals_at γ globals i scope :
      i ≤ γ.(pool_name_size) →
      globals_model γ globals -∗
      locals_at γ i scope -∗
        globals_model_running γ globals ∗
        locals_at γ i scope.
    Proof.
      iIntros "%Hi (:globals_model >) Hlocals_at".
      - iFrameSteps.
      - iDestruct (big_sepL_seq_lookup' i with "Hlocals_ats") as "Hlocals_at_"; first lia.
        iDestruct (locals_at_exclusive with "Hlocals_at Hlocals_at_") as %[].
    Qed.
    #[local] Lemma globals_model_push {γ globals} 𝑔𝑙𝑜𝑏𝑎𝑙 P i scope :
      i ≤ γ.(pool_name_size) →
      globals_model γ globals -∗
      locals_at γ i scope ==∗
        ∃ global,
        ⌜global.(job_val) = 𝑔𝑙𝑜𝑏𝑎𝑙⌝ ∗
        globals_model γ ({[+global+]} ⊎ globals) ∗
        locals_at γ i scope ∗
        jobs_elem γ global ∗
        saved_prop global.(job_name) P.
    Proof.
      iIntros "%Hi Hglobals_model Hlocals_at".
      iDestruct (globals_model_locals_at with "Hglobals_model Hlocals_at") as "((:globals_model_running) & $)"; first done.
      iMod (jobs_insert 𝑔𝑙𝑜𝑏𝑎𝑙 P with "Hjobs_auth") as "(%global & % & Hjobs_auth & $ & $)".
      iStep. iLeft. iFrameSteps. iPureIntro.
      set_solver by lia.
    Qed.
    #[local] Lemma globals_model_pop {γ globals} global globals' i scope :
      i ≤ γ.(pool_name_size) →
      globals = {[+global+]} ⊎ globals' →
      globals_model γ globals -∗
      locals_at γ i (Some scope) ==∗
        globals_model γ globals' ∗
        locals_at γ i (Some ({[+global+]} ⊎ scope)).
    Proof.
      iIntros (Hi ->) "Hglobals_model Hlocals_at".
      iDestruct (globals_model_locals_at with "Hglobals_model Hlocals_at") as "((:globals_model_running) & Hlocals_at)"; first done.
      iMod (locals_insert global with "Hlocals_auth Hlocals_at") as "(Hlocals_auth & $)".
      iLeft. iFrameSteps. iPureIntro.
      set_solver by lia.
    Qed.
    #[local] Lemma globals_model_kill γ :
      globals_model γ ∅ -∗
      ( [∗ list] i ∈ seq 0 (S γ.(pool_name_size)),
        locals_at γ i (Some ∅)
      ) ==∗
        ∃ jobs,
        globals_model γ ∅ ∗
        jobs_auth γ Discard jobs ∗
        jobs_finished jobs.
    Proof.
      iIntros "Hglobals_model Hlocals_ats".

      iAssert (
        globals_model_running γ ∅ ∗
        [∗ list] i ∈ seq 0 (S γ.(pool_name_size)),
          locals_at γ i (Some ∅)
      )%I with "[-]" as "((:globals_model_running) & Hlocals_ats)".
      { iDestruct (big_sepL_lookup_acc _ _ 0 with "Hlocals_ats") as "(Hlocals_at & Hlocals_ats)"; first done.
        iDestruct (globals_model_locals_at with "Hglobals_model Hlocals_at") as "($ & Hlocals_at)"; first lia.
        iApply ("Hlocals_ats" with "Hlocals_at").
      }

      rewrite (left_id ∅ (⊎)).

      iDestruct (locals_kill with "Hlocals_auth Hlocals_ats") as "(_ & $ & $)".
      iApply (jobs_auth_discard with "Hjobs_auth").
    Qed.
    Opaque globals_model.

    Lemma pool_inv_agree γ sz1 sz2 :
      pool_inv γ sz1 -∗
      pool_inv γ sz2 -∗
      ⌜sz1 = sz2⌝.
    Proof.
      iSteps.
    Qed.

    Lemma pool_obligation_wand {γ P1} P2 :
      pool_obligation γ P1 -∗
      □ (P1 -∗ P2) -∗
      pool_obligation γ P2.
    Proof.
      iIntros "#Hobligation #H !> #Hfinished".
      iDestruct ("Hobligation" with "Hfinished") as "HP1".
      iSteps.
    Qed.
    Lemma pool_obligation_split γ P1 P2 :
      pool_obligation γ (P1 ∗ P2) ⊢
        pool_obligation γ P1 ∗
        pool_obligation γ P2.
    Proof.
      iIntros "#Hobligation".
      iDestruct (pool_obligation_wand with "Hobligation []") as "$". 1: iSteps.
      iDestruct (pool_obligation_wand with "Hobligation []") as "$". 1: iSteps.
    Qed.
    Lemma pool_obligation_combine γ P1 P2 :
      pool_obligation γ P1 -∗
      pool_obligation γ P2 -∗
      pool_obligation γ (P1 ∗ P2).
    Proof.
      iIntros "#Hobligation_1 #Hobligation_2 !> #Hfinished".
      iDestruct ("Hobligation_1" with "Hfinished") as "HP1".
      iDestruct ("Hobligation_2" with "Hfinished") as "HP2".
      iSteps.
    Qed.
    Lemma pool_obligation_finished γ P :
      pool_obligation γ P -∗
      pool_finished γ -∗
      ▷ □ P.
    Proof.
      iIntros "#Hobligation #Hfinished".
      iApply ("Hobligation" with "Hfinished").
    Qed.

    Lemma pool_consumer_wand {γ P1} P2 :
      pool_consumer γ P1 -∗
      (P1 -∗ P2) -∗
      pool_consumer γ P2.
    Proof.
      iSteps.
    Qed.
    Lemma pool_consumer_combine γ P1 P2 :
      pool_consumer γ P1 -∗
      pool_consumer γ P2 -∗
      pool_consumer γ (P1 ∗ P2).
    Proof.
      iSteps.
    Qed.
    Lemma pool_consumer_finished γ P :
      pool_consumer γ P -∗
      pool_finished γ ={⊤}=∗
      P.
    Proof.
      iSteps.
    Qed.

    #[local] Lemma pool_context_spec {sz : Z} {hub} {i : Z} γ (i_ : nat) :
      sz = γ.(pool_name_size) →
      hub = γ.(pool_name_hub) →
      i = i_ →
      {{{
        True
      }}}
        pool__code.pool_context #sz hub #i
      {{{
        RET pool_name_context γ i_;
        True
      }}}.
    Proof.
      iSteps.
    Qed.

    #[local] Lemma pool_context_main_spec t γ :
      {{{
        t.[size] ↦□ #γ.(pool_name_size) ∗
        t.[hub] ↦□ γ.(pool_name_hub)
      }}}
        pool_context_main #t
      {{{
        RET pool_name_context γ 0;
        True
      }}}.
    Proof.
      iIntros "%Φ (Ht_size & Ht_hub) HΦ".

      wp_rec. do 2 wp_load.
      wp_apply (pool_context_spec with "[//] HΦ"); done.
    Qed.

    #[local] Lemma pool_execute_spec γ i scope task Ψ :
      i ≤ γ.(pool_name_size) →
      {{{
        context_1 γ i scope ∗
        task_model γ task Ψ
      }}}
        pool_execute (pool_name_context γ i) task
      {{{ v,
        RET v;
        context_1 γ i scope ∗
        Ψ v
      }}}.
    Proof.
      iIntros "%Hi %Φ (Hctx & Htask) HΦ".

      wp_rec.
      wp_smart_apply (wp_wand with "(Htask [//] Hctx) HΦ").
    Qed.

    #[local] Lemma pool_worker_spec γ i :
      {{{
        context_2 γ i ∅
      }}}
        pool_worker (pool_name_context γ i)
      {{{ res,
        RET res;
        worker_post γ i res
      }}}.
    Proof.
      iIntros "%Φ (:context_2 lazy=) HΦ".
      iLöb as "HLöb".
      iDestruct "Hctx" as "(:context_1)".

      wp_rec. rewrite pool_max_round_noyield pool_max_round_yield.

      awp_smart_apply (ws_hub_std_pop_steal_spec with "[$Hhub_inv $Hhub_owner]") without "HΦ"; [done | lia.. |].
      iInv "Hinv" as "(:inv_inner)".
      iAaccIntro with "Hhub_model"; first iSteps. iIntros ([𝑔𝑙𝑜𝑏𝑎𝑙 |]) "Hhub_model".

      - iDestruct "Hhub_model" as "(%𝑔𝑙𝑜𝑏𝑎𝑙𝑠' & -> & Hhub_model)".
        apply symmetry, gmultiset_map_disj_union_singleton_l_inv in H𝑔𝑙𝑜𝑏𝑎𝑙𝑠 as (global & globals' & -> & -> & ->).
        iDestruct (big_sepMS_disj_union with "Hglobals") as "(Hglobal & Hglobals')".
        iEval (rewrite big_sepMS_singleton) in "Hglobal".
        iMod (globals_model_pop global with "Hglobals_model Hlocals_at") as "(Hglobals_model & Hlocals_at)"; [done.. |].
        iSplitR "Hglobal Hlocals_at". { iFrameSteps. }
        iIntros "!> {%- Hi} %empty (Hhub_owner & _) HΦ".

        wp_smart_apply (pool_execute_spec with "[$]") as "{%- Hi} %res((:context_1) & (%P & Hglobal & HP))"; first done.
        iDestruct (locals_at_finish with "Hlocals_at Hglobal HP") as "Hlocals_at".
        wp_smart_apply ("HLöb" with "[$] HΦ").

      - iSplitR "Hlocals_at". { iFrameSteps. }
        iIntros "!> {%- Hi} %empty (Hhub_owner & ->) HΦ".

        wp_smart_apply (ws_hub_std_block_spec with "[$Hhub_inv $Hhub_owner]"); first done.
        iSteps.
    Qed.

    #[local] Lemma pool_drain_spec γ i :
      {{{
        context_2 γ i ∅
      }}}
        pool_drain (pool_name_context γ i)
      {{{ res,
        RET res;
        worker_post γ i res
      }}}.
    Proof.
      iIntros "%Φ (:context_2 lazy=) HΦ".
      iLöb as "HLöb".
      iDestruct "Hctx" as "(:context_1)".

      wp_rec.

      awp_smart_apply (ws_hub_std_pop_spec with "[$Hhub_inv $Hhub_owner]") without "HΦ"; first done.
      iInv "Hinv" as "(:inv_inner)".
      iAaccIntro with "Hhub_model"; first iSteps. iIntros ([𝑔𝑙𝑜𝑏𝑎𝑙 |]) "Hhub_model".

      - iDestruct "Hhub_model" as "(%𝑔𝑙𝑜𝑏𝑎𝑙𝑠' & -> & Hhub_model)".
        apply symmetry, gmultiset_map_disj_union_singleton_l_inv in H𝑔𝑙𝑜𝑏𝑎𝑙𝑠 as (global & globals' & -> & -> & ->).
        iDestruct (big_sepMS_disj_union with "Hglobals") as "(Hglobal & Hglobals')".
        iEval (rewrite big_sepMS_singleton) in "Hglobal".
        iMod (globals_model_pop global with "Hglobals_model Hlocals_at") as "(Hglobals_model & Hlocals_at)"; [done.. |].
        iSplitR "Hglobal Hlocals_at". { iFrameSteps. }
        iIntros "!> {%- Hi} Hhub_owner HΦ".

        wp_smart_apply (pool_execute_spec with "[$]") as "{%- Hi} %res ((:context_1) & (%P & Hglobal & HP))"; first done.
        iDestruct (locals_at_finish with "Hlocals_at Hglobal HP") as "Hlocals_at".
        wp_smart_apply ("HLöb" with "[$] HΦ").

      - iSplitR "Hlocals_at". { iFrameSteps. }
        iIntros "!> {%- Hi} Hhub_owner HΦ".

        wp_smart_apply (ws_hub_std_block_spec with "[$Hhub_inv $Hhub_owner]"); first done.
        iSteps.
    Qed.

    Lemma pool_create_spec sz :
      (0 ≤ sz)%Z →
      {{{
        True
      }}}
        pool_create #sz
      {{{ t γ,
        RET #t;
        pool_inv γ ₊sz ∗
        pool_model t γ ∗
        meta_token t ⊤
      }}}.
    Proof.
      iIntros "%Hsz %Φ _ HΦ".

      wp_rec.

      wp_smart_apply (ws_hub_std_create_spec with "[//]") as (hub) "(#Hhub_inv & Hhub_model & Hhub_owners)"; first lia.
      rewrite Z2Nat.inj_add // Nat.add_1_r.
      iDestruct (big_sepL_seq_cons_1 with "Hhub_owners") as "(Hhub_owner & Hhub_owners)".

      wp_smart_apply (ws_hub_std_block_spec with "[$Hhub_inv $Hhub_owner]") as "Hhub_owner"; first done.

      iMod jobs_alloc as "(%γ_jobs & Hjobs_auth)".

      iMod (locals_alloc ₊sz) as "(%γ_locals & Hlocals_auth & Hlocals_ats)".
      iDestruct (big_sepL_seq_cons_1 with "Hlocals_ats") as "(Hlocals_at & Hlocals_ats)".

      pose γ 𝑑𝑜𝑚𝑠 := {|
        pool_name_size := ₊sz ;
        pool_name_hub := hub ;
        pool_name_domains := 𝑑𝑜𝑚𝑠 ;
        pool_name_jobs := γ_jobs ;
        pool_name_locals := γ_locals ;
      |}.

      wp_smart_apply (array_unsafe_initi_spec_disentangled_strong'
        ( λ 𝑑𝑜𝑚𝑠,
          inv_1 (γ 𝑑𝑜𝑚𝑠)
        )
        ( λ 𝑑𝑜𝑚𝑠 i dom,
          domain_model dom (worker_post (γ 𝑑𝑜𝑚𝑠) (S i))
        )
      with "[Hhub_model Hhub_owners Hjobs_auth Hlocals_auth Hlocals_ats]") as (𝑑𝑜𝑚𝑠 doms) "(%Hdoms & Hdomains & #Hinv & Hdoms)"; first done.
      { iSplitR "Hhub_owners Hlocals_ats".

        - iIntros "!> %𝑑𝑜𝑚𝑠".
          iApply inv_alloc.
          iDestruct (globals_model_init (γ 𝑑𝑜𝑚𝑠) with "Hjobs_auth Hlocals_auth") as "$".
          iFrame. rewrite big_sepMS_empty //.

        - iDestruct (big_sepL_sep_2 with "Hhub_owners Hlocals_ats") as "H".
          iApply (big_sepL_impl_strong with "H").
          { simpl_length. }
          iIntros "!>" (k i1 i2 (-> & Hi1)%lookup_seq (-> & Hi2)%lookup_seq) "(Hhub_owner & Hlocals_at) %𝑑𝑜𝑚𝑠 #Hinv".

          wp_smart_apply (domain_spawn_spec with "[Hhub_owner Hlocals_at]"); last iSteps. iIntros "%tid _".
          iApply wp_thread_id_mono.

          wp_smart_apply (pool_context_spec (γ 𝑑𝑜𝑚𝑠) (S k) with "[//]") as "_"; [naive_solver lia.. |].
          wp_apply (pool_worker_spec with "[Hhub_owner Hlocals_at]"); first iFrameSteps.
          iSteps.
      }
      iMod (array_model_persist with "Hdomains") as "#Hdomains".

      wp_block t as "Hmeta" "(Ht_size & Ht_hub & Ht_domains & _)".
      iMod (pointsto_persist with "Ht_size") as "#Ht_size".
      iMod (pointsto_persist with "Ht_hub") as "#Ht_hub".
      iMod (pointsto_persist with "Ht_domains") as "#Ht_domains".

      iApply "HΦ".
      iFrameSteps.
    Qed.

    Lemma pool_run_spec Ψ t γ task :
      {{{
        pool_model t γ ∗
        ( ∀ ctx scope,
          pool_context γ ctx scope -∗
          WP task ctx {{ v,
            pool_context γ ctx scope ∗
            Ψ v
          }}
        )
      }}}
        pool_run #t task
      {{{ v,
        RET v;
        pool_model t γ ∗
        Ψ v
      }}}.
    Proof.
      iIntros "%Φ ((:model) & Htask) HΦ".

      wp_rec. wp_load.
      wp_apply (ws_hub_std_unblock_spec with "[$Hhub_inv $Hhub_owner]") as "Hhub_owner"; first done.
      wp_smart_apply (pool_context_main_spec with "[$]") as "_".

      wp_smart_apply (pool_execute_spec _ _ _ _ Ψ with "[$Hhub_owner $Hlocals_at Htask]").
      { lia. }
      { iIntros "{%} %i %scope %Hi Hctx".
        wp_apply (wp_wand with "(Htask [Hctx])") as (v) "((:context =1) & $)"; first iFrameSteps.
        apply (inj _) in Heq1 as <-. iFrame.
      }
      iIntros "{%- Hdoms} %v ((:context_1) & HΨ)".

      wp_load.
      wp_apply (ws_hub_std_block_spec with "[$Hhub_inv $Hhub_owner]") as "Hhub_owner"; first done.
      iSteps.
    Qed.

    Lemma pool_kill_spec t γ :
      {{{
        pool_model t γ
      }}}
        pool_kill #t
      {{{
        RET ();
        pool_finished γ
      }}}.
    Proof.
      iIntros "%Φ (:model) HΦ".

      wp_rec. wp_load.
      wp_apply (ws_hub_std_unblock_spec with "[$Hhub_inv $Hhub_owner]") as "Hhub_owner"; first done.
      wp_smart_apply (pool_context_main_spec with "[$]") as "_".

      wp_smart_apply (pool_drain_spec with "[$Hhub_owner $Hlocals_at]"); first iSteps.
      iIntros "{%- Hdoms} %res (:worker_post)".

      wp_load.
      wp_smart_apply (ws_hub_std_kill_spec with "Hhub_inv") as "_".
      wp_load.

      iApply wp_fupd.
      wp_smart_apply (array_iter_spec_disentangled' (λ i _, context_finished γ (S i))%I with "[$Hdomains Hdoms]") as "(_ & Hdoms)".
      { iApply (big_sepL_impl with "Hdoms"). iIntros "!> %i %dom _ Hdom".
        wp_apply (domain_join_spec with "Hdom").
        iSteps.
      }

      iApply (big_sepL_seq_index_2 γ.(pool_name_size)) in "Hdoms"; first lia.
      iApply big_sepL_seq_shift1_2 in "Hdoms".
      iDestruct (big_sepL_seq_cons_2 with "Hdoms [$]") as "Hdoms".
      iDestruct (big_sepL_sep with "Hdoms") as "(Hhub_owners & Hlocals_ats)".

      iApply "HΦ".

      iInv "Hinv" as "(:inv_inner)".
      iDestruct (ws_hub_std_model_empty with "Hhub_inv Hhub_model [Hhub_owners]") as %->.
      { iApply (big_sepL_impl with "Hhub_owners").
        iSteps.
      }
      apply symmetry, gmultiset_map_empty_inv in H𝑔𝑙𝑜𝑏𝑎𝑙𝑠 as ->.
      iMod (globals_model_kill _ with "Hglobals_model Hlocals_ats") as "(%jobs & Hglobals_model & #Hjobs_auth & #Hjobs_finished)".
      iSplitL. { iFrameSteps. }
      iSteps.
    Qed.

    Lemma pool_size_spec γ sz ctx scope :
      {{{
        pool_inv γ sz ∗
        pool_context γ ctx scope
      }}}
        pool_size ctx
      {{{
        RET #sz;
        pool_context γ ctx scope
      }}}.
    Proof.
      iSteps.
    Qed.

    Lemma pool_async_spec P Q γ ctx scope task :
      {{{
        pool_context γ ctx scope ∗
        ( ∀ ctx scope,
          pool_context γ ctx scope -∗
          WP task ctx {{ res,
            pool_context γ ctx scope ∗
            ▷ □ P ∗
            ▷ Q
          }}
        )
      }}}
        pool_async ctx task
      {{{
        RET ();
        pool_context γ ctx scope ∗
        pool_obligation γ P ∗
        pool_consumer γ Q
      }}}.
    Proof.
      iIntros "%Φ ((:context) & Htask) HΦ".

      iMod (spsc_prop_alloc nroot Q) as "(%η & #Hη_inv & Hη_producer & Hη_consumer)".
      set R := (
        P ∗
        spsc_prop_resolved η
      )%I.

      wp_rec credits:"H£".

      awp_smart_apply (ws_hub_std_push_spec with "[$Hhub_inv $Hhub_owner]") without "Hη_consumer H£ HΦ"; first done.
      iInv "Hinv" as "(:inv_inner)".
      iAaccIntro with "Hhub_model"; first iFrameSteps. iIntros "Hhub_model".
      iMod (globals_model_push task R with "Hglobals_model Hlocals_at") as "(%global & %Hglobal & Hglobals_model & Hlocals_at & #Hjobs_elem & #Hglobal)"; first done.
      iSplitR "Hlocals_at".
      { iFrame. iSplitR "Htask Hη_producer".
        - iPureIntro.
          rewrite gmultiset_map_disj_union gmultiset_map_singleton.
          congruence.
        - iApply big_sepMS_singleton.
          rewrite Hglobal. iSteps --silent / as "_ _ HP HQ".
          iMod (spsc_prop_produce with "Hη_inv Hη_producer HQ") as "#Hη_resolved". 1: done.
          iFrame "#" => //.
      }
      iIntros "!> Hhub_owner (Hη_consumer & H£ & HΦ)".

      iAssert (pool_obligation γ R) with "[]" as "#Hobligation".
      { iIntros "!> (:finished)".
        iDestruct (jobs_elem_valid with "Hjobs_auth Hjobs_elem") as %Helem.
        iDestruct (jobs_finished_elem_of with "Hjobs_finished") as "(%R_ & Hglobal_ & #HR)". 1: done.
        iDestruct (saved_prop_agree with "Hglobal Hglobal_") as "Heq".
        iModIntro.
        iRewrite "Heq" => //.
      }

      iApply "HΦ".
      iFrame "#∗". iStep. iSplitR.
      { iApply (pool_obligation_wand with "Hobligation").
        iSteps.
      } {
        iIntros "#Hfinished".
        iDestruct (pool_obligation_finished with "Hobligation Hfinished") as "-#HR".
        iDestruct (lc_weaken 2 with "H£") as "H£". 1: done.
        iDestruct "H£" as "(H£_1 & H£_2)".
        iMod (lc_fupd_elim_later with "H£_1 HR") as "(_ & #Hη_resolved)".
        iMod (spsc_prop_consume with "Hη_inv Hη_consumer Hη_resolved") as "HQ". 1: done.
        iApply (lc_fupd_elim_later with "H£_2 HQ").
      }
    Qed.

    Lemma pool_wait_until_spec P Q γ ctx scope pred :
      {{{
        pool_context γ ctx scope ∗
        P ∗
        □ (
          P -∗
          WP pred () {{ res,
            ∃ b,
            ⌜res = #b⌝ ∗
            if b then Q else P
          }}
        )
      }}}
        pool_wait_until ctx pred
      {{{
        RET ();
        pool_context γ ctx scope ∗
        Q
      }}}.
    Proof.
      iIntros "%Φ ((:context lazy=) & HP & #Hpred) HΦ".
      iLöb as "HLöb".
      iDestruct "Hctx" as "(:context_1)".

      wp_rec. rewrite pool_max_round_noyield.
      wp_smart_apply (wp_wand with "(Hpred HP)") as (res) "(%b & -> & H)".
      destruct b; first iSteps.

      awp_smart_apply (ws_hub_std_pop_steal_until_spec P Q with "[$Hhub_inv $Hhub_owner $H $Hpred]") without "HΦ"; [done.. |].
      iInv "Hinv" as "(:inv_inner)".
      iAaccIntro with "Hhub_model"; first iSteps. iIntros ([𝑔𝑙𝑜𝑏𝑎𝑙 |]) "Hhub_model".

      - iDestruct "Hhub_model" as "(%𝑔𝑙𝑜𝑏𝑎𝑙𝑠' & -> & Hhub_model)".
        apply symmetry, gmultiset_map_disj_union_singleton_l_inv in H𝑔𝑙𝑜𝑏𝑎𝑙𝑠 as (global & globals' & -> & -> & ->).
        iDestruct (big_sepMS_disj_union with "Hglobals") as "(Hglobal & Hglobals')".
        iEval (rewrite big_sepMS_singleton) in "Hglobal".
        iMod (globals_model_pop global with "Hglobals_model Hlocals_at") as "(Hglobals_model & Hlocals_at)"; [done.. |].
        iSplitR "Hglobal Hlocals_at". { iFrameSteps. }
        iIntros "!> {%- Hi} %empty (Hhub_owner & HP) HΦ".

        wp_smart_apply (pool_execute_spec with "[$]") as "{%- Hi} %res ((:context_1) & (%R & Hglobal & HR))"; first done.
        iDestruct (locals_at_finish with "Hlocals_at Hglobal HR") as "Hlocals_at".
        wp_smart_apply ("HLöb" with "[$] HP HΦ").

      - iSplitR "Hlocals_at". { iFrameSteps. }
        iSteps.
    Qed.

    Lemma pool_wait_while_spec P Q γ ctx scope pred :
      {{{
        pool_context γ ctx scope ∗
        P ∗
        □ (
          P -∗
          WP pred () {{ res,
            ∃ b,
            ⌜res = #b⌝ ∗
            if b then P else Q
          }}
        )
      }}}
        pool_wait_while ctx pred
      {{{
        RET ();
        pool_context γ ctx scope ∗
        Q
      }}}.
    Proof.
      iIntros "%Φ (Hctx & HP & #Hpred) HΦ".

      wp_rec.
      wp_smart_apply (pool_wait_until_spec P Q with "[$Hctx $HP] HΦ") as "!> HP".
      wp_smart_apply (wp_wand with "(Hpred HP)") as (res) "(%b & -> & H)".
      destruct b; iSteps.
    Qed.
  End pool_G.

  #[global] Opaque pool_scope.
  #[global] Opaque pool_inv.
  #[global] Opaque pool_model.
  #[global] Opaque pool_context.
  #[global] Opaque pool_obligation.
  #[global] Opaque pool_consumer.
  #[global] Opaque pool_finished.
End base.

From zoo_parabs Require
  pool__opaque.

Section pool_G.
  Context `{pool_G : PoolG Σ}.

  Implicit Types 𝑡 : location.
  Implicit Types t : val.

  Definition pool_inv t sz : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.pool_inv γ sz.
  #[local] Instance : CustomIpat "inv" :=
    " ( %𝑡{} &
        %γ{} &
        {%Heq{};->} &
        #Hmeta{_{}} &
        Hinv{_{}}
      )
    ".

  Definition pool_context t ctx scope : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.pool_context γ ctx scope.
  #[local] Instance : CustomIpat "context" :=
    " ( %𝑡{} &
        %γ{} &
        {%Heq{};->} &
        #Hmeta{_{}} &
        Hctx{_{}}
      )
    ".

  Definition pool_model t : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.pool_model 𝑡 γ.
  #[local] Instance : CustomIpat "model" :=
    " ( %𝑡{} &
        %γ{} &
        {%Heq{};->} &
        #Hmeta{_{}} &
        Hmodel{_{}}
      )
    ".

  Definition pool_obligation t P : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.pool_obligation γ P.
  #[local] Instance : CustomIpat "obligation" :=
    " ( %𝑡{} &
        %γ{} &
        {%Heq{};->} &
        #Hmeta{_{}} &
        Hobligation{_{}}
      )
    ".

  Definition pool_consumer t P : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.pool_consumer γ P.
  #[local] Instance : CustomIpat "consumer" :=
    " ( %𝑡{} &
        %γ{} &
        {%Heq{};->} &
        #Hmeta{_{}} &
        Hconsumer{_{}}
      )
    ".

  Definition pool_finished t : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.pool_finished γ.
  #[local] Instance : CustomIpat "finished" :=
    " ( %𝑡{} &
        %γ{} &
        {%Heq{};->} &
        #Hmeta{_{}} &
        Hfinished{_{}}
      )
    ".

  #[global] Instance pool_inv_persistent t sz :
    Persistent (pool_inv t sz).
  Proof.
    apply _.
  Qed.
  #[global] Instance pool_obligation_persistent t P :
    Persistent (pool_obligation t P).
  Proof.
    apply _.
  Qed.
  #[global] Instance pool_finished_persistent t :
    Persistent (pool_finished t).
  Proof.
    apply _.
  Qed.

  Lemma pool_inv_agree t sz1 sz2 :
    pool_inv t sz1 -∗
    pool_inv t sz2 -∗
    ⌜sz1 = sz2⌝.
  Proof.
    iIntros "(:inv =1) (:inv =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.pool_inv_agree with "Hinv_1 Hinv_2").
  Qed.

  Lemma pool_obligation_wand {t P1} P2 :
    pool_obligation t P1 -∗
    □ (P1 -∗ P2) -∗
    pool_obligation t P2.
  Proof.
    iIntros "(:obligation) H".
    iDestruct (base.pool_obligation_wand with "Hobligation H") as "$".
    iSteps.
  Qed.
  Lemma pool_obligation_split t P1 P2 :
    pool_obligation t (P1 ∗ P2) ⊢
      pool_obligation t P1 ∗
      pool_obligation t P2.
  Proof.
    iIntros "(:obligation)".
    iDestruct (base.pool_obligation_split with "Hobligation") as "($ & $)".
    iSteps.
  Qed.
  Lemma pool_obligation_combine t P1 P2 :
    pool_obligation t P1 -∗
    pool_obligation t P2 -∗
    pool_obligation t (P1 ∗ P2).
  Proof.
    iIntros "(:obligation =1) (:obligation =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iDestruct (base.pool_obligation_combine with "Hobligation_1 Hobligation_2") as "$".
    iSteps.
  Qed.
  Lemma pool_obligation_finished t P :
    pool_obligation t P -∗
    pool_finished t -∗
    ▷ □ P.
  Proof.
    iIntros "(:obligation =1) (:finished =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.pool_obligation_finished with "Hobligation_1 Hfinished_2").
  Qed.

  Lemma pool_consumer_wand {t P1} P2 :
    pool_consumer t P1 -∗
    (P1 -∗ P2) -∗
    pool_consumer t P2.
  Proof.
    iIntros "(:consumer) H".
    iDestruct (base.pool_consumer_wand with "Hconsumer H") as "$".
    iSteps.
  Qed.
  Lemma pool_consumer_combine t P1 P2 :
    pool_consumer t P1 -∗
    pool_consumer t P2 -∗
    pool_consumer t (P1 ∗ P2).
  Proof.
    iIntros "(:consumer =1) (:consumer =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iDestruct (base.pool_consumer_combine with "Hconsumer_1 Hconsumer_2") as "$".
    iSteps.
  Qed.
  Lemma pool_consumer_finished t P :
    pool_consumer t P -∗
    pool_finished t ={⊤}=∗
    P.
  Proof.
    iIntros "(:consumer =1) (:finished =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.pool_consumer_finished with "Hconsumer_1 Hfinished_2").
  Qed.

  Lemma pool_create_spec sz :
    (0 ≤ sz)%Z →
    {{{
      True
    }}}
      pool_create #sz
    {{{ t,
      RET t;
      pool_inv t ₊sz ∗
      pool_model t
    }}}.
  Proof.
    iIntros "% %Φ _ HΦ".

    iApply wp_fupd.
    wp_apply (base.pool_create_spec with "[//]") as (𝑡 γ) "(Hinv & Hmodel & Hmeta)"; first done.
    iMod (meta_set γ with "Hmeta") as "#Hmeta"; first done.
    iSteps.
  Qed.

  Lemma pool_run_spec Ψ t task :
    {{{
      pool_model t ∗
      ( ∀ ctx scope,
        pool_context t ctx scope -∗
        WP task ctx {{ v,
          pool_context t ctx scope ∗
          Ψ v
        }}
      )
    }}}
      pool_run t task
    {{{ v,
      RET v;
      pool_model t ∗
      Ψ v
    }}}.
  Proof.
    iIntros "%Φ ((:model) & Htask) HΦ".

    wp_apply (base.pool_run_spec Ψ with "[$Hmodel Htask]").
    { iIntros "%ctx %scope Hctx".
      wp_apply (wp_wand with "(Htask [$Hctx])") as (v) "((:context =1) & $)"; first iSteps.
      simplify.
      iDestruct (meta_agree with "Hmeta Hmeta_1") as %->. iClear "Hmeta".
      iFrame.
    }
    iSteps.
  Qed.

  Lemma pool_kill_spec t :
    {{{
      pool_model t
    }}}
      pool_kill t
    {{{
      RET ();
      pool_finished t
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".

    wp_apply (base.pool_kill_spec with "Hmodel").
    iSteps.
  Qed.

  Lemma pool_size_spec t sz ctx scope :
    {{{
      pool_inv t sz ∗
      pool_context t ctx scope
    }}}
      pool_size ctx
    {{{
      RET #sz;
      pool_context t ctx scope
    }}}.
  Proof.
    iIntros "%Φ ((:model =1) & (:context =2)) HΦ". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp_apply (base.pool_size_spec with "[$]").
    iSteps.
  Qed.

  Lemma pool_async_spec P Q t ctx scope task :
    {{{
      pool_context t ctx scope ∗
      ( ∀ ctx scope,
        pool_context t ctx scope -∗
        WP task ctx {{ res,
          pool_context t ctx scope ∗
          ▷ □ P ∗
          ▷ Q
        }}
      )
    }}}
      pool_async ctx task
    {{{
      RET ();
      pool_context t ctx scope ∗
      pool_obligation t P ∗
      pool_consumer t Q
    }}}.
  Proof.
    iIntros "%Φ ((:context) & Htask) HΦ".

    wp_apply (base.pool_async_spec P Q with "[$Hctx Htask]").
    { iIntros "{%} %ctx %scope Hctx".
      wp_apply (wp_wand with "(Htask [$Hctx])") as (v) "((:context =1) & $)"; first iSteps.
      simplify.
      iDestruct (meta_agree with "Hmeta Hmeta_1") as %->. iClear "Hmeta".
      iFrame.
    }
    iSteps.
  Qed.

  Lemma pool_wait_until_spec P Q t ctx scope pred :
    {{{
      pool_context t ctx scope ∗
      P ∗
      □ (
        P -∗
        WP pred () {{ res,
          ∃ b,
          ⌜res = #b⌝ ∗
          if b then Q else P
        }}
      )
    }}}
      pool_wait_until ctx pred
    {{{
      RET ();
      pool_context t ctx scope ∗
      Q
    }}}.
  Proof.
    iIntros "%Φ ((:context) & HP & Hpred) HΦ".

    wp_apply (base.pool_wait_until_spec with "[$]").
    iSteps.
  Qed.

  Lemma pool_wait_while_spec P Q t ctx scope pred :
    {{{
      pool_context t ctx scope ∗
      P ∗
      □ (
        P -∗
        WP pred () {{ res,
          ∃ b,
          ⌜res = #b⌝ ∗
          if b then P else Q
        }}
      )
    }}}
      pool_wait_while ctx pred
    {{{
      RET ();
      pool_context t ctx scope ∗
      Q
    }}}.
  Proof.
    iIntros "%Φ ((:context) & HP & Hpred) HΦ".

    wp_apply (base.pool_wait_while_spec with "[$]").
    iSteps.
  Qed.
End pool_G.

#[global] Opaque pool_scope.
#[global] Opaque pool_inv.
#[global] Opaque pool_model.
#[global] Opaque pool_context.
#[global] Opaque pool_obligation.
#[global] Opaque pool_consumer.
#[global] Opaque pool_finished.
