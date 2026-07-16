Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Import zoo.common.gmultiset.
Require Import zoo.iris.bi.big_op.
Require Import zoo.iris.base_logic.lib.ghost_list.
Require Import zoo.iris.base_logic.lib.mono_gmultiset.
Require Import zoo.iris.base_logic.lib.saved_prop.
Require Import zoo.iris.base_logic.lib.spsc_prop.
Require Import zoo.base.
Require Import zoo_std.array.
Require Import zoo_std.domain.
Require Import zoo_std.ivar_4.
Require Export zoo_parabs.base.
Require Export zoo_parabs.pool__code.
Require Import zoo_parabs.pool__types.
Require Import zoo_parabs.ws_hub_std.
Require Import zoo.options.

Implicit Types b : bool.
Implicit Types v ctx hub task notification notify pred ivar waiter : val.
Implicit Types empty : emptiness.
Implicit Types own : ownership.
Implicit Types η : spsc_prop۰name.
Implicit Types ω : gname.

#[local] Definition max_round_noyield :=
  val۰to_nat' pool٠max_round_noyield.
#[local] Lemma pool٠max_round_noyield𑁒unfold :
  pool٠max_round_noyield = #max_round_noyield.
Proof.
  done.
Qed.
Opaque pool٠max_round_noyield.
Opaque max_round_noyield.

#[local] Definition max_round_yield :=
  val۰to_nat' pool٠max_round_yield.
#[local] Lemma pool٠max_round_yield𑁒unfold :
  pool٠max_round_yield = #max_round_yield.
Proof.
  done.
Qed.
Opaque pool٠max_round_yield.
Opaque max_round_yield.

Record job :=
  { job۰val : val
  ; job۰name : gname
  }.
Implicit Types job local global : job.

#[local] Instance job𑁒inhabited : Inhabited job :=
  populate
  {|job۰val := inhabitant
  ; job۰name := inhabitant
  |}.
#[local] Instance job𑁒eq_dec : EqDecision job :=
  ltac:(solve_decision).
#[local] Instance job𑁒countable :
  Countable job.
Proof.
  solve_countable.
Qed.

Implicit Types jobs locals ulocals globals : gmultiset job.
Implicit Types localss : list $ gmultiset job.

Definition pool۰scope :=
  gmultiset job.

#[global] Instance pool۰scope𑁒eq_dec : EqDecision pool۰scope :=
  _.
#[global] Instance pool۰scope𑁒countable :
  Countable pool۰scope.
Proof.
  apply _.
Qed.

Class PoolG Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] pool۰G۰domain۰G :: DomainG Σ
  ; #[local] pool۰G۰ws_hub۰G :: WsHubStdG Σ
  ; #[local] pool۰G۰saved_prop۰G :: SavedPropG Σ
  ; #[local] pool۰G۰jobs۰G :: MonoGmultisetG Σ job
  ; #[local] pool۰G۰locals۰G :: GhostListG Σ (gmultiset job)
  ; #[local] pool۰G۰consumer۰G :: SpscPropG Σ
  }.

Definition pool۰Σ :=
  #[domain۰Σ
  ; ws_hub_std۰Σ
  ; saved_prop۰Σ
  ; mono_gmultiset۰Σ job
  ; ghost_list۰Σ (gmultiset job)
  ; spsc_prop۰Σ
  ].
#[global] Instance subG𑁒pool۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG pool۰Σ Σ →
  PoolG Σ.
Proof.
  solve_inG.
Qed.

Module base.
  Section pool۰G.
    Context `{pool۰G : PoolG Σ}.

    Implicit Types t : location.
    Implicit Types P P_notification P_pred Q Q_pred : iProp Σ.
    Implicit Types Ψ : val → iProp Σ.

    Record pool۰name :=
      { pool۰name۰size : nat
      ; pool۰name۰hub : val
      ; pool۰name۰domains : val
      ; pool۰name۰jobs : gname
      ; pool۰name۰locals : gname
      }.
    Implicit Types γ : pool۰name.
    Implicit Types γ_tokens : list gname.

    #[global] Instance pool۰name𑁒eq_dec : EqDecision pool۰name :=
      ltac:(solve_decision).
    #[global] Instance pool۰name𑁒countable :
      Countable pool۰name.
    Proof.
      solve_countable.
    Qed.

    #[local] Definition pool۰name۰context γ (i : nat) :=
      ( #γ.(pool۰name۰size),
        γ.(pool۰name۰hub),
        #i
      )%V.
    #[local] Instance pool۰name۰context𑁒inj γ :
      Inj (=) (=) (pool۰name۰context γ).
    Proof.
      rewrite /Inj. naive_solver.
    Qed.

    #[local] Definition jobs۰auth' γ_jobs own :=
      mono_gmultiset۰auth γ_jobs own.
    #[local] Definition jobs۰auth γ :=
      jobs۰auth' γ.(pool۰name۰jobs).
    #[local] Definition jobs۰elem γ :=
      mono_gmultiset۰elem γ.(pool۰name۰jobs).

    #[local] Definition jobs۰finished jobs : iProp Σ :=
      [∗ mset] job ∈ jobs,
        ∃ P,
        saved_prop job.(job۰name) P ∗
        □ P.

    #[local] Definition locals۰auth' sz γ_locals ulocals : iProp Σ :=
      ∃ localss,
      ⌜length localss = ˖sz⌝ ∗
      ghost_list۰auth γ_locals localss ∗
      ⌜ulocals = ⋃+ localss⌝.
    #[local] Definition locals۰auth γ :=
      locals۰auth' γ.(pool۰name۰size) γ.(pool۰name۰locals).
    #[local] Instance : CustomIpat "locals۰auth" :=
      " ( %localss{}
        & %Hlocalss{}
        & Hauth{_{}}
        & ->
        )
      ".
    #[local] Definition locals۰at۰running γ_locals i scope : iProp Σ :=
      ∃ locals,
      ghost_list۰at γ_locals i Own (scope ⊎ locals) ∗
      jobs۰finished locals.
    #[local] Instance : CustomIpat "locals۰at۰running" :=
      " ( %locals{}
        & Hat{_{}}
        & Hjobs_finished_locals{}
        )
      ".
    #[local] Definition locals۰at۰finished γ_locals i : iProp Σ :=
      ∃ locals,
      ghost_list۰at γ_locals i Own locals.
    #[local] Instance : CustomIpat "locals۰at۰finished" :=
      " ( %locals{}
        & Hat{_{}}
        )
      ".
    #[local] Definition locals۰at' γ_locals i scope : iProp Σ :=
      match scope with
      | Some scope =>
          locals۰at۰running γ_locals i scope
      | None =>
          locals۰at۰finished γ_locals i
      end.
    #[local] Definition locals۰at γ :=
      locals۰at' γ.(pool۰name۰locals).

    #[local] Definition globals۰model۰running γ globals : iProp Σ :=
      ∃ jobs ulocals,
      ⌜jobs = globals ⊎ ulocals⌝ ∗
      jobs۰auth γ Own jobs ∗
      locals۰auth γ ulocals.
    #[local] Instance : CustomIpat "globals۰model۰running" :=
      " ( %jobs
        & %ulocals
        & ->
        & Hjobs_auth
        & Hlocals_auth
        )
      ".
    #[local] Definition globals۰model۰finished γ : iProp Σ :=
      [∗ list] i ∈ seq 0 ˖(γ.(pool۰name۰size)),
        locals۰at γ i None.
    #[local] Instance : CustomIpat "globals۰model۰finished" :=
      " Hlocals_ats
      ".
    #[local] Definition globals۰model γ globals : iProp Σ :=
        globals۰model۰running γ globals
      ∨ globals۰model۰finished γ.
    #[local] Instance : CustomIpat "globals۰model" :=
      " [ (:globals۰model۰running)
        | (:globals۰model۰finished)
        ]
      ".

    #[local] Definition context₁ γ i (scope : pool۰scope) : iProp Σ :=
      ∃ empty,
      ws_hub_std۰owner γ.(pool۰name۰hub) i Nonblocked empty ∗
      locals۰at γ i (Some scope).
    #[local] Instance : CustomIpat "context₁" :=
      " ( %empty{}
        & Hhub_owner{_{}}
        & Hlocals_at{_{}}
        )
      ".

    #[local] Definition task۰model γ task Ψ : iProp Σ :=
      ∀ i scope,
      ⌜i ≤ γ.(pool۰name۰size)⌝ -∗
      context₁ γ i scope -∗
      WP task (pool۰name۰context γ i) {{ v,
        context₁ γ i scope ∗
        Ψ v
      }}.

    #[local] Definition inv۰inner γ : iProp Σ :=
      ∃ globals 𝑔𝑙𝑜𝑏𝑎𝑙𝑠,
      ⌜𝑔𝑙𝑜𝑏𝑎𝑙𝑠 = gmultiset_map job۰val globals⌝ ∗
      globals۰model γ globals ∗
      ws_hub_std۰model γ.(pool۰name۰hub) 𝑔𝑙𝑜𝑏𝑎𝑙𝑠 ∗
      [∗ mset] global ∈ globals,
        task۰model γ global.(job۰val) (λ _,
          ∃ P,
          saved_prop global.(job۰name) P ∗
          ▷ □ P
        ).
    #[local] Instance : CustomIpat "inv۰inner" :=
      " ( %globals
        & %𝑔𝑙𝑜𝑏𝑎𝑙𝑠
        & >%H𝑔𝑙𝑜𝑏𝑎𝑙𝑠
        & >Hglobals_model
        & >Hhub_model
        & Hglobals
        )
      ".
    #[local] Definition inv₁ γ : iProp Σ :=
      inv (nroot.@"inv") (inv۰inner γ).
    #[local] Definition inv₂ γ : iProp Σ :=
      ws_hub_std۰inv γ.(pool۰name۰hub) (nroot.@"hub") ˖(γ.(pool۰name۰size)) ∗
      inv₁ γ.
    #[local] Instance : CustomIpat "inv₂" :=
      " ( #Hhub_inv{_{}}
        & #Hinv{_{}}
        )
      ".
    Definition pool۰inv γ sz : iProp Σ :=
      ⌜sz = γ.(pool۰name۰size)⌝ ∗
      inv₂ γ.
    #[local] Instance : CustomIpat "inv" :=
      " ( ->
        & {#Hinv_{};(:inv₂)}
        )
      ".

    #[local] Definition context۰finished γ i : iProp Σ :=
      ws_hub_std۰owner γ.(pool۰name۰hub) i Nonblocked Empty ∗
      locals۰at γ i (Some ∅).
    #[local] Instance : CustomIpat "context۰finished" :=
      " ( Hhub_owner{_{}}
        & Hlocals_at{_{}}
        )
      ".
    #[local] Definition context₂ γ i scope : iProp Σ :=
      ⌜i ≤ γ.(pool۰name۰size)⌝ ∗
      inv₂ γ ∗
      context₁ γ i scope.
    #[local] Instance : CustomIpat "context₂" :=
      " ( %Hi{}
        & {#Hinv_{};(:inv₂)}
        & { {lazy} Hctx{}
          ; {lazy} Hctx
          ; (:context₁ ={})
          ; (:context₁)
          }
        )
      ".
    Definition pool۰context γ ctx scope : iProp Σ :=
      ∃ i,
      ⌜ctx = pool۰name۰context γ i⌝ ∗
      context₂ γ i scope.
    #[local] Instance : CustomIpat "context" :=
      " ( %i{}
        & {%Heq{};->}
        & (:context₂)
        )
      ".

    #[local] Definition worker۰post γ i res : iProp Σ :=
      ⌜res = ()%V⌝ ∗
      context۰finished γ i.
    #[local] Instance : CustomIpat "worker۰post" :=
      " ( ->
        & (:context۰finished)
        )
      ".

    Definition pool۰model t γ : iProp Σ :=
      ∃ empty doms,
      ⌜length doms = γ.(pool۰name۰size)⌝ ∗
      t.[size] ↦□ #γ.(pool۰name۰size) ∗
      t.[hub] ↦□ γ.(pool۰name۰hub) ∗
      t.[domains] ↦□ γ.(pool۰name۰domains) ∗
      inv₂ γ ∗
      array۰model γ.(pool۰name۰domains) DfracDiscarded doms ∗
      ( [∗ list] i ↦ dom ∈ doms,
        domain۰model dom (worker۰post γ ˖i)
      ) ∗
      ws_hub_std۰owner γ.(pool۰name۰hub) 0 Blocked empty ∗
      locals۰at γ 0 (Some ∅).
    #[local] Instance : CustomIpat "model" :=
      " ( %empty{}
        & %doms{}
        & %Hdoms{}
        & #Hl{}_size
        & #Hl{}_hub
        & #Hl{}_domains
        & {#Hinv{};(:inv₂)}
        & Hdomains{}
        & Hdoms{}
        & Hhub{}_owner
        & Hlocals_at{_{}}
        )
      ".

    Definition pool۰finished γ : iProp Σ :=
      ∃ jobs,
      jobs۰auth γ Discard jobs ∗
      jobs۰finished jobs.
    #[local] Instance : CustomIpat "finished" :=
      " ( %jobs{}
        & Hjobs_auth{_{}}
        & Hjobs_finished{_jobs{}}
        )
      ".

    Definition pool۰consumer γ P : iProp Σ :=
      pool۰finished γ ={⊤}=∗
      P.

    Definition pool۰obligation γ P : iProp Σ :=
      □ (
        pool۰finished γ -∗
        ▷ □ P
      ).

    #[global] Instance pool۰obligation𑁒proper γ :
      Proper ((≡) ==> (≡)) (pool۰obligation γ).
    Proof.
      solve_proper.
    Qed.
    #[global] Instance pool۰consumer𑁒proper γ :
      Proper ((≡) ==> (≡)) (pool۰consumer γ).
    Proof.
      solve_proper.
    Qed.

    #[local] Instance globals۰model𑁒timeless γ globals :
      Timeless (globals۰model γ globals).
    Proof.
      apply _.
    Qed.

    #[local] Instance jobs۰elem𑁒persistent γ job :
      Persistent (jobs۰elem γ job).
    Proof.
      apply _.
    Qed.
    #[local] Instance jobs۰finished𑁒persistent jobs :
      Persistent (jobs۰finished jobs).
    Proof.
      apply _.
    Qed.
    #[global] Instance pool۰inv𑁒persistent γ sz :
      Persistent (pool۰inv γ sz).
    Proof.
      apply _.
    Qed.
    #[global] Instance pool۰obligation𑁒persistent γ P :
      Persistent (pool۰obligation γ P).
    Proof.
      apply _.
    Qed.
    #[global] Instance pool۰finished𑁒persistent γ :
      Persistent (pool۰finished γ).
    Proof.
      apply _.
    Qed.

    #[local] Lemma jobs𑁒alloc :
      ⊢ |==>
        ∃ γ_jobs,
        jobs۰auth' γ_jobs Own ∅.
    Proof.
      apply mono_gmultiset𑁒alloc.
    Qed.
    #[local] Lemma jobs۰auth𑁒discard γ jobs :
      jobs۰auth γ Own jobs ⊢ |==>
      jobs۰auth γ Discard jobs.
    Proof.
      apply mono_gmultiset۰auth𑁒persist.
    Qed.
    #[local] Lemma jobs۰elem𑁒valid γ own jobs job :
      jobs۰auth γ own jobs -∗
      jobs۰elem γ job -∗
      ⌜job ∈ jobs⌝.
    Proof.
      apply mono_gmultiset۰elem𑁒valid.
    Qed.
    #[local] Lemma jobs𑁒insert {γ jobs} 𝑗𝑜𝑏 P :
      jobs۰auth γ Own jobs ⊢ |==>
        ∃ job,
        ⌜job.(job۰val) = 𝑗𝑜𝑏⌝ ∗
        jobs۰auth γ Own ({[+job+]} ⊎ jobs) ∗
        jobs۰elem γ job ∗
        saved_prop job.(job۰name) P.
    Proof.
      iIntros "Hauth".
      iMod (saved_prop𑁒alloc P) as "(%η & #Hη)".
      pose job :=
      {|job۰val := 𝑗𝑜𝑏
      ; job۰name := η
      |}.
      iMod (mono_gmultiset𑁒insert job with "Hauth") as "Hauth".
      iDestruct (mono_gmultiset۰elem𑁒get job with "Hauth") as "#Helem"; first set_solver.
      iFrameSteps.
    Qed.
    Opaque jobs۰elem.

    #[local] Lemma jobs۰finished𑁒empty :
      ⊢ jobs۰finished ∅.
    Proof.
      iApply (big_sepMS_empty with "[//]").
    Qed.
    #[local] Lemma jobs۰finished𑁒elem_of job jobs :
      job ∈ jobs →
      jobs۰finished jobs ⊢
        ∃ P,
        saved_prop job.(job۰name) P ∗
        □ P.
    Proof.
      apply: big_sepMS_elem_of.
    Qed.
    #[local] Lemma jobs۰finished𑁒insert {jobs} job P :
      jobs۰finished jobs -∗
      saved_prop job.(job۰name) P -∗
      □ P -∗
      jobs۰finished ({[+job+]} ⊎ jobs).
    Proof.
      iIntros "Hfinished #Hjob #HP".
      iApply (big_sepMS𑁒insert₂ with "Hfinished").
      iSteps.
    Qed.
    #[local] Lemma jobs۰finished𑁒union localss :
      ( [∗ list] locals ∈ localss,
        jobs۰finished locals
      ) ⊢
      jobs۰finished (⋃+ localss).
    Proof.
      apply big_sepMS𑁒disj_union_list₂.
    Qed.
    Opaque jobs۰finished.

    #[local] Lemma locals𑁒alloc sz :
      ⊢ |==>
        ∃ γ_locals,
        locals۰auth' sz γ_locals ∅ ∗
        [∗ list] i ∈ seq 0 ˖sz,
          locals۰at' γ_locals i (Some ∅).
    Proof.
      iMod (ghost_list𑁒alloc (replicate ˖sz ∅)) as "(%γ_locals & $ & Hats)".
      iSplitR.
      - iPureIntro. split.
        + simpl_length.
        + rewrite gmultiset𑁒disj_union_list𑁒replicate𑁒empty //.
      - iApply big_sepL𑁒replicate₁ in "Hats".
        iApply (big_sepL_impl with "Hats"). iIntros "!> !> %i_ %i _ Hat".
        iExists ∅. rewrite right_id. iFrame.
        iApply jobs۰finished𑁒empty.
    Qed.
    #[local] Lemma locals۰at𑁒exclusive γ i scope1 scope2 :
      locals۰at γ i scope1 -∗
      locals۰at γ i scope2 -∗
      False.
    Proof.
      all:
        destruct scope1 as [scope1 |];
        [ iIntros "(:locals۰at۰running =1)"
        | iIntros "(:locals۰at۰finished =1)"
        ].
      all:
        destruct scope2 as [scope2 |];
        [ iIntros "(:locals۰at۰running =2)"
        | iIntros "(:locals۰at۰finished =2)"
        ].
      all: iApply (ghost_list۰at𑁒exclusive with "Hat_1 Hat_2").
    Qed.
    #[local] Lemma locals𑁒insert {γ ulocals i scope} local :
      locals۰auth γ ulocals -∗
      locals۰at γ i (Some scope) ==∗
        locals۰auth γ ({[+local+]} ⊎ ulocals) ∗
        locals۰at γ i (Some ({[+local+]} ⊎ scope)).
    Proof.
      iIntros "(:locals۰auth) (:locals۰at۰running)".
      iDestruct (ghost_list𑁒lookup with "Hauth Hat") as %Hlookup.
      iMod (ghost_list𑁒update𑁒at ({[+local+]} ⊎ scope ⊎ locals) with "Hauth Hat") as "($ & $)".
      iFrameSteps; iPureIntro.
      { simpl_length. }
      { rewrite -assoc gmultiset𑁒disj_union_list𑁒insert𑁒disj_union𑁒l //. }
    Qed.
    #[local] Lemma locals۰at𑁒finish γ i local P scope :
      locals۰at γ i (Some ({[+local+]} ⊎ scope)) -∗
      saved_prop local.(job۰name) P -∗
      □ P -∗
      locals۰at γ i (Some scope).
    Proof.
      iIntros "(:locals۰at۰running) Hlocal HP".
      iDestruct (jobs۰finished𑁒insert with "Hjobs_finished_locals Hlocal HP") as "$".
      rewrite (comm (⊎) {[+_+]} scope) assoc //.
    Qed.
    #[local] Lemma locals𑁒close γ ulocals :
      locals۰auth γ ulocals -∗
      ( [∗ list] i ∈ seq 0 ˖(γ.(pool۰name۰size)),
        locals۰at γ i (Some ∅)
      ) -∗
        locals۰auth γ ulocals ∗
        ( [∗ list] i ∈ seq 0 ˖(γ.(pool۰name۰size)),
          locals۰at γ i None
        ) ∗
        jobs۰finished ulocals.
    Proof.
      iIntros "(:locals۰auth) Hats".
      iDestruct (big_sepL𑁒seq𑁒exists with "Hats") as "(%localss_ & %Hlocalss_ & Hats)".
      iDestruct (big_sepL_sep with "Hats") as "(Hats & Hjobs_finisheds)".
      iEval (setoid_rewrite (left_id ∅ (⊎))) in "Hats".
      iDestruct (ghost_list𑁒auth𑁒ats with "Hauth Hats") as %<-; first lia.
      iSplitL "Hauth"; first iFrameSteps.
      iDestruct (jobs۰finished𑁒union with "Hjobs_finisheds") as "$".
      iApply big_sepL𑁒to𑁒seq𑁒0 in "Hats".
      iEval (rewrite Hlocalss) in "Hats".
      iApply (big_sepL_impl with "Hats"). iIntros "!> %i_ %i _ (%locals & _ & $)".
    Qed.
    Opaque locals۰auth'.
    Opaque locals۰at'.

    #[local] Lemma globals۰model𑁒init γ :
      jobs۰auth γ Own ∅ -∗
      locals۰auth γ ∅ -∗
      globals۰model γ ∅.
    Proof.
      iIntros "Hjobs_auth Hlocals_auth".
      iLeft. iExists ∅, ∅. iFrameSteps.
    Qed.
    #[local] Lemma globals۰model𑁒locals۰at γ globals i scope :
      i ≤ γ.(pool۰name۰size) →
      globals۰model γ globals -∗
      locals۰at γ i scope -∗
        globals۰model۰running γ globals ∗
        locals۰at γ i scope.
    Proof.
      iIntros "%Hi (:globals۰model >) Hlocals_at".
      - iFrameSteps.
      - iDestruct (big_sepL𑁒seq𑁒lookup' i with "Hlocals_ats") as "Hlocals_at_"; first lia.
        iDestruct (locals۰at𑁒exclusive with "Hlocals_at Hlocals_at_") as %[].
    Qed.
    #[local] Lemma globals۰model𑁒push {γ globals} 𝑔𝑙𝑜𝑏𝑎𝑙 P i scope :
      i ≤ γ.(pool۰name۰size) →
      globals۰model γ globals -∗
      locals۰at γ i scope ==∗
        ∃ global,
        ⌜global.(job۰val) = 𝑔𝑙𝑜𝑏𝑎𝑙⌝ ∗
        globals۰model γ ({[+global+]} ⊎ globals) ∗
        locals۰at γ i scope ∗
        jobs۰elem γ global ∗
        saved_prop global.(job۰name) P.
    Proof.
      iIntros "%Hi Hglobals_model Hlocals_at".
      iDestruct (globals۰model𑁒locals۰at with "Hglobals_model Hlocals_at") as "((:globals۰model۰running) & $)"; first done.
      iMod (jobs𑁒insert 𝑔𝑙𝑜𝑏𝑎𝑙 P with "Hjobs_auth") as "(%global & % & Hjobs_auth & $ & $)".
      iStep. iLeft. iFrameSteps. iPureIntro.
      set_solver by lia.
    Qed.
    #[local] Lemma globals۰model𑁒pop {γ globals} global globals' i scope :
      i ≤ γ.(pool۰name۰size) →
      globals = {[+global+]} ⊎ globals' →
      globals۰model γ globals -∗
      locals۰at γ i (Some scope) ==∗
        globals۰model γ globals' ∗
        locals۰at γ i (Some ({[+global+]} ⊎ scope)).
    Proof.
      iIntros (Hi ->) "Hglobals_model Hlocals_at".
      iDestruct (globals۰model𑁒locals۰at with "Hglobals_model Hlocals_at") as "((:globals۰model۰running) & Hlocals_at)"; first done.
      iMod (locals𑁒insert global with "Hlocals_auth Hlocals_at") as "(Hlocals_auth & $)".
      iLeft. iFrameSteps. iPureIntro.
      set_solver by lia.
    Qed.
    #[local] Lemma globals۰model𑁒close γ :
      globals۰model γ ∅ -∗
      ( [∗ list] i ∈ seq 0 ˖(γ.(pool۰name۰size)),
        locals۰at γ i (Some ∅)
      ) ==∗
        ∃ jobs,
        globals۰model γ ∅ ∗
        jobs۰auth γ Discard jobs ∗
        jobs۰finished jobs.
    Proof.
      iIntros "Hglobals_model Hlocals_ats".

      iAssert (
        globals۰model۰running γ ∅ ∗
        [∗ list] i ∈ seq 0 ˖(γ.(pool۰name۰size)),
          locals۰at γ i (Some ∅)
      )%I with "[-]" as "((:globals۰model۰running) & Hlocals_ats)".
      { iDestruct (big_sepL_lookup_acc _ _ 0 with "Hlocals_ats") as "(Hlocals_at & Hlocals_ats)"; first done.
        iDestruct (globals۰model𑁒locals۰at with "Hglobals_model Hlocals_at") as "($ & Hlocals_at)"; first lia.
        iApply ("Hlocals_ats" with "Hlocals_at").
      }

      rewrite (left_id ∅ (⊎)).

      iDestruct (locals𑁒close with "Hlocals_auth Hlocals_ats") as "(_ & $ & $)".
      iApply (jobs۰auth𑁒discard with "Hjobs_auth").
    Qed.
    Opaque globals۰model.

    Lemma pool۰inv𑁒agree γ sz1 sz2 :
      pool۰inv γ sz1 -∗
      pool۰inv γ sz2 -∗
      ⌜sz1 = sz2⌝.
    Proof.
      iSteps.
    Qed.

    Lemma pool۰obligation𑁒wand {γ P1} P2 :
      pool۰obligation γ P1 -∗
      □ (P1 -∗ P2) -∗
      pool۰obligation γ P2.
    Proof.
      iIntros "#Hobligation #H !> #Hfinished".
      iDestruct ("Hobligation" with "Hfinished") as "HP1".
      iSteps.
    Qed.
    Lemma pool۰obligation𑁒split γ P1 P2 :
      pool۰obligation γ (P1 ∗ P2) ⊢
        pool۰obligation γ P1 ∗
        pool۰obligation γ P2.
    Proof.
      iIntros "#Hobligation".
      iDestruct (pool۰obligation𑁒wand with "Hobligation []") as "$". 1: iSteps.
      iDestruct (pool۰obligation𑁒wand with "Hobligation []") as "$". 1: iSteps.
    Qed.
    Lemma pool۰obligation𑁒combine γ P1 P2 :
      pool۰obligation γ P1 -∗
      pool۰obligation γ P2 -∗
      pool۰obligation γ (P1 ∗ P2).
    Proof.
      iIntros "#Hobligation_1 #Hobligation_2 !> #Hfinished".
      iDestruct ("Hobligation_1" with "Hfinished") as "HP1".
      iDestruct ("Hobligation_2" with "Hfinished") as "HP2".
      iSteps.
    Qed.
    Lemma pool۰obligation𑁒finished γ P :
      pool۰obligation γ P -∗
      pool۰finished γ -∗
      ▷ □ P.
    Proof.
      iIntros "#Hobligation #Hfinished".
      iApply ("Hobligation" with "Hfinished").
    Qed.

    #[local] Lemma pool٠context𑁒spec {sz : Z} {hub} {i : Z} γ (i_ : nat) :
      sz = γ.(pool۰name۰size) →
      hub = γ.(pool۰name۰hub) →
      i = i_ →
      {{{
        True
      }}}
        pool__code.pool٠context #sz hub #i
      {{{
        RET pool۰name۰context γ i_;
        True
      }}}.
    Proof.
      iSteps.
    Qed.

    #[local] Lemma pool٠context_main𑁒spec t γ :
      {{{
        t.[size] ↦□ #γ.(pool۰name۰size) ∗
        t.[hub] ↦□ γ.(pool۰name۰hub)
      }}}
        pool٠context_main #t
      {{{
        RET pool۰name۰context γ 0;
        True
      }}}.
    Proof.
      iIntros "%Φ (Ht_size & Ht_hub) HΦ".

      wp۰rec. do 2 wp۰load.
      wp۰apply (pool٠context𑁒spec with "[//] HΦ"); done.
    Qed.

    #[local] Lemma pool٠execute𑁒spec γ i scope task Ψ :
      i ≤ γ.(pool۰name۰size) →
      {{{
        context₁ γ i scope ∗
        task۰model γ task Ψ
      }}}
        pool٠execute (pool۰name۰context γ i) task
      {{{
        v
      , RET v;
        context₁ γ i scope ∗
        Ψ v
      }}}.
    Proof.
      iIntros "%Hi %Φ (Hctx & Htask) HΦ".

      wp۰rec.
      wp۰apply+ (wp𑁒wand with "(Htask [//] Hctx) HΦ").
    Qed.

    #[local] Lemma pool٠worker𑁒spec γ i :
      {{{
        context₂ γ i ∅
      }}}
        pool٠worker (pool۰name۰context γ i)
      {{{
        res
      , RET res;
        worker۰post γ i res
      }}}.
    Proof.
      iIntros "%Φ (:context₂ lazy=) HΦ".
      iLöb as "HLöb".
      iDestruct "Hctx" as "(:context₁)".

      wp۰rec. rewrite pool٠max_round_noyield𑁒unfold pool٠max_round_yield𑁒unfold.

      awp۰apply+ (ws_hub_std٠pop_steal𑁒spec with "[$Hhub_inv $Hhub_owner]") without "HΦ"; [done | lia.. |].
      iInv "Hinv" as "(:inv۰inner)".
      iAaccIntro with "Hhub_model"; first iSteps. iIntros ([𝑔𝑙𝑜𝑏𝑎𝑙 |]) "Hhub_model".

      - iDestruct "Hhub_model" as "(%𝑔𝑙𝑜𝑏𝑎𝑙𝑠' & -> & Hhub_model)".
        apply symmetry, gmultiset_map𑁒disj_union𑁒singleton𑁒l𑁒inv in H𝑔𝑙𝑜𝑏𝑎𝑙𝑠 as (global & globals' & -> & -> & ->).
        iDestruct (big_sepMS_disj_union with "Hglobals") as "(Hglobal & Hglobals')".
        iEval (rewrite big_sepMS_singleton) in "Hglobal".
        iMod (globals۰model𑁒pop global with "Hglobals_model Hlocals_at") as "(Hglobals_model & Hlocals_at)"; [done.. |].
        iSplitR "Hglobal Hlocals_at". { iFrameSteps. }
        iIntros "!> {%- Hi} %empty (Hhub_owner & _) HΦ".

        wp۰apply+ (pool٠execute𑁒spec with "[$]") as "{%- Hi} %res((:context₁) & (%P & Hglobal & HP))"; first done.
        iDestruct (locals۰at𑁒finish with "Hlocals_at Hglobal HP") as "Hlocals_at".
        wp۰apply+ ("HLöb" with "[$] HΦ").

      - iSplitR "Hlocals_at". { iFrameSteps. }
        iSteps.
    Qed.

    Lemma pool٠create𑁒spec sz :
      (0 ≤ sz)%Z →
      {{{
        True
      }}}
        pool٠create #sz
      {{{
        t γ
      , RET #t;
        pool۰inv γ ₊sz ∗
        pool۰model t γ ∗
        meta_token t ⊤
      }}}.
    Proof.
      iIntros "%Hsz %Φ _ HΦ".

      wp۰rec.

      wp۰apply+ (ws_hub_std٠create𑁒spec with "[//]") as (hub) "(#Hhub_inv & Hhub_model & Hhub_owners)"; first lia.
      rewrite Z2Nat.inj_add // Nat.add_1_r.
      iDestruct (big_sepL𑁒seq𑁒cons₁ with "Hhub_owners") as "(Hhub_owner & Hhub_owners)".

      wp۰apply+ (ws_hub_std٠block𑁒spec with "[$Hhub_inv $Hhub_owner]") as "Hhub_owner"; first done.

      iMod jobs𑁒alloc as "(%γ_jobs & Hjobs_auth)".

      iMod (locals𑁒alloc ₊sz) as "(%γ_locals & Hlocals_auth & Hlocals_ats)".
      iDestruct (big_sepL𑁒seq𑁒cons₁ with "Hlocals_ats") as "(Hlocals_at & Hlocals_ats)".

      pose γ 𝑑𝑜𝑚𝑠 :=
        {|pool۰name۰size := ₊sz
        ; pool۰name۰hub := hub
        ; pool۰name۰domains := 𝑑𝑜𝑚𝑠
        ; pool۰name۰jobs := γ_jobs
        ; pool۰name۰locals := γ_locals
        |}.

      wp۰apply+ (array٠unsafe_initi𑁒spec𑁒disentangled𑁒strong'
        ( λ 𝑑𝑜𝑚𝑠,
          inv₁ (γ 𝑑𝑜𝑚𝑠)
        )
        ( λ 𝑑𝑜𝑚𝑠 i dom,
          domain۰model dom (worker۰post (γ 𝑑𝑜𝑚𝑠) ˖i)
        )
      with "[Hhub_model Hhub_owners Hjobs_auth Hlocals_auth Hlocals_ats]") as (𝑑𝑜𝑚𝑠 doms) "(%Hdoms & Hdomains & #Hinv & Hdoms)"; first done.
      { iSplitR "Hhub_owners Hlocals_ats".

        - iIntros "!> %𝑑𝑜𝑚𝑠".
          iApply inv_alloc.
          iDestruct (globals۰model𑁒init (γ 𝑑𝑜𝑚𝑠) with "Hjobs_auth Hlocals_auth") as "$".
          iFrame. rewrite big_sepMS_empty //.

        - iDestruct (big_sepL_sep_2 with "Hhub_owners Hlocals_ats") as "H".
          iApply (big_sepL𑁒impl𑁒strong with "H").
          { simpl_length. }
          iIntros "!>" (k i1 i2 (-> & Hi1)%lookup_seq (-> & Hi2)%lookup_seq) "(Hhub_owner & Hlocals_at) %𝑑𝑜𝑚𝑠 #Hinv".

          wp۰apply+ (domain٠spawn𑁒spec with "[Hhub_owner Hlocals_at]"); last iSteps. iIntros "%tid _".
          iApply wp𑁒thread_id_mono.

          wp۰apply+ (pool٠context𑁒spec (γ 𝑑𝑜𝑚𝑠) ˖k with "[//]") as "_"; [naive_solver lia.. |].
          wp۰apply (pool٠worker𑁒spec with "[Hhub_owner Hlocals_at]"); first iFrameSteps.
          iSteps.
      }
      iMod (array۰model𑁒persist with "Hdomains") as "#Hdomains".

      wp۰block t as "Hmeta" "(Ht_size & Ht_hub & Ht_domains & _)".
      iMod (pointsto𑁒persist with "Ht_size") as "#Ht_size".
      iMod (pointsto𑁒persist with "Ht_hub") as "#Ht_hub".
      iMod (pointsto𑁒persist with "Ht_domains") as "#Ht_domains".

      iApply "HΦ".
      iFrameSteps.
    Qed.

    Lemma pool٠run_on𑁒spec Ψ t γ task :
      {{{
        pool۰model t γ ∗
        ( ∀ ctx scope,
          pool۰context γ ctx scope -∗
          WP task ctx {{ v,
            pool۰context γ ctx scope ∗
            Ψ v
          }}
        )
      }}}
        pool٠run_on #t task
      {{{
        v
      , RET v;
        pool۰model t γ ∗
        Ψ v
      }}}.
    Proof.
      iIntros "%Φ ((:model) & Htask) HΦ".

      wp۰rec. wp۰load.
      wp۰apply (ws_hub_std٠unblock𑁒spec with "[$Hhub_inv $Hhub_owner]") as "Hhub_owner"; first done.
      wp۰apply+ (pool٠context_main𑁒spec with "[$]") as "_".

      wp۰apply+ (pool٠execute𑁒spec _ _ _ _ Ψ with "[$Hhub_owner $Hlocals_at Htask]").
      { lia. }
      { iIntros "{%} %i %scope %Hi Hctx".
        wp۰apply (wp𑁒wand with "(Htask [Hctx])") as (v) "((:context =1) & $)"; first iFrameSteps.
        apply (inj _) in Heq1 as <-. iFrame.
      }
      iIntros "{%- Hdoms} %v ((:context₁) & HΨ)".

      wp۰load.
      wp۰apply (ws_hub_std٠block𑁒spec with "[$Hhub_inv $Hhub_owner]") as "Hhub_owner"; first done.
      iSteps.
    Qed.

    Lemma pool٠close𑁒spec t γ :
      {{{
        pool۰model t γ
      }}}
        pool٠close #t
      {{{
        RET ();
        pool۰finished γ
      }}}.
    Proof.
      iIntros "%Φ (:model) HΦ".

      wp۰rec. wp۰load.
      wp۰apply (ws_hub_std٠close𑁒spec with "Hhub_inv") as "_".
      wp۰load.
      wp۰apply (ws_hub_std٠unblock𑁒spec with "[$Hhub_inv $Hhub_owner]") as "Hhub_owner"; first done.
      wp۰apply+ (pool٠context_main𑁒spec with "[$]") as "_".

      wp۰apply+ (pool٠worker𑁒spec with "[$Hhub_owner $Hlocals_at]"); first iSteps.
      iIntros "{%- Hdoms} %res (:worker۰post)".

      wp۰load.

      iApply wp𑁒fupd.
      wp۰apply+ (array٠iter𑁒spec𑁒disentangled' (λ i _, context۰finished γ ˖i)%I with "[$Hdomains Hdoms]") as "(_ & Hdoms)".
      { iApply (big_sepL_impl with "Hdoms"). iIntros "!> %i %dom _ Hdom".
        wp۰apply (domain٠join𑁒spec with "Hdom").
        iSteps.
      }

      iApply (big_sepL𑁒seq𑁒index₂ γ.(pool۰name۰size)) in "Hdoms"; first lia.
      iApply big_sepL𑁒seq𑁒shift𑁒1₂ in "Hdoms".
      iDestruct (big_sepL𑁒seq𑁒cons₂ with "Hdoms [$]") as "Hdoms".
      iDestruct (big_sepL_sep with "Hdoms") as "(Hhub_owners & Hlocals_ats)".

      iApply "HΦ".

      iInv "Hinv" as "(:inv۰inner)".
      iDestruct (ws_hub_std۰model𑁒empty with "Hhub_inv Hhub_model [Hhub_owners]") as %->.
      { iApply (big_sepL_impl with "Hhub_owners").
        iSteps.
      }
      apply symmetry, gmultiset_map𑁒empty𑁒inv in H𝑔𝑙𝑜𝑏𝑎𝑙𝑠 as ->.
      iMod (globals۰model𑁒close _ with "Hglobals_model Hlocals_ats") as "(%jobs & Hglobals_model & #Hjobs_auth & #Hjobs_finished)".
      iSplitL. { iFrameSteps. }
      iSteps.
    Qed.

    Lemma pool٠run𑁒spec (Ψ : location → pool۰name → val → iProp Σ) sz task :
      (0 ≤ sz)%Z →
      {{{
        ∀ t γ ctx scope,
        pool۰inv γ ₊sz -∗
        meta_token t ⊤ -∗
        pool۰context γ ctx scope -∗
        WP task ctx {{ v,
          pool۰context γ ctx scope ∗
          Ψ t γ v
        }}
      }}}
        pool٠run #sz task
      {{{
        t γ v
      , RET v;
        pool۰finished γ ∗
        Ψ t γ v
      }}}.
    Proof.
      iIntros "%Hsz %Φ Htask HΦ".

      wp۰rec.
      wp۰apply+ (pool٠create𑁒spec with "[//]") as (t γ) "(#Hinv & Hmodel & Hmeta)". 1: done.
      wp۰apply+ (pool٠run_on𑁒spec (Ψ t γ) with "[$Hmodel Hmeta Htask]") as (v) "(Hmodel & HΨ)".
      { iIntros "%ctx %scope Hctx".
        iApply ("Htask" with "Hinv Hmeta Hctx").
      }
      wp۰apply+ (pool٠close𑁒spec with "Hmodel") as "#Hfinished".
      wp۰pures.
      iApply ("HΦ" with "[$Hfinished $HΨ]").
    Qed.

    Lemma pool٠size𑁒spec γ sz ctx scope :
      {{{
        pool۰inv γ sz ∗
        pool۰context γ ctx scope
      }}}
        pool٠size ctx
      {{{
        RET #sz;
        pool۰context γ ctx scope
      }}}.
    Proof.
      iSteps.
    Qed.

    Lemma pool٠async𑁒spec P Q γ ctx scope task :
      {{{
        pool۰context γ ctx scope ∗
        ( ∀ ctx scope,
          pool۰context γ ctx scope -∗
          WP task ctx {{ res,
            pool۰context γ ctx scope ∗
            ▷ P ∗
            ▷ □ Q
          }}
        )
      }}}
        pool٠async ctx task
      {{{
        RET ();
        pool۰context γ ctx scope ∗
        pool۰consumer γ P ∗
        pool۰obligation γ Q
      }}}.
    Proof.
      iIntros "%Φ ((:context) & Htask) HΦ".

      iMod (spsc_prop𑁒alloc nroot P) as "(%η & #Hη_inv & Hη_producer & Hη_consumer)".
      set R := (
        Q ∗
        spsc_prop۰resolved η
      )%I.

      wp۰rec credits:"H£".

      awp۰apply+ (ws_hub_std٠push𑁒spec with "[$Hhub_inv $Hhub_owner]") without "Hη_consumer H£ HΦ"; first done.
      iInv "Hinv" as "(:inv۰inner)".
      iAaccIntro with "Hhub_model"; first iFrameSteps. iIntros "Hhub_model".
      iMod (globals۰model𑁒push task R with "Hglobals_model Hlocals_at") as "(%global & %Hglobal & Hglobals_model & Hlocals_at & #Hjobs_elem & #Hglobal)"; first done.
      iSplitR "Hlocals_at".
      { iFrame. iSplitR "Htask Hη_producer".
        - iPureIntro.
          rewrite gmultiset_map_disj_union gmultiset_map_singleton.
          congruence.
        - iApply big_sepMS_singleton.
          rewrite Hglobal. iSteps --silent / as "_ _ HQ HP".
          iMod (spsc_prop𑁒produce with "Hη_inv Hη_producer HP") as "#Hη_resolved". 1: done.
          iFrame "#" => //.
      }
      iIntros "!> Hhub_owner (Hη_consumer & H£ & HΦ)".

      iAssert (pool۰obligation γ R) with "[]" as "#Hobligation".
      { iIntros "!> (:finished)".
        iDestruct (jobs۰elem𑁒valid with "Hjobs_auth Hjobs_elem") as %Helem.
        iDestruct (jobs۰finished𑁒elem_of with "Hjobs_finished") as "(%R_ & Hglobal_ & #HR)". 1: done.
        iDestruct (saved_prop𑁒agree with "Hglobal Hglobal_") as "Heq".
        iModIntro.
        iRewrite "Heq" => //.
      }

      iApply "HΦ".
      iFrame "#∗". iStep. iSplitL.
      { iIntros "#Hfinished".
        iDestruct (pool۰obligation𑁒finished with "Hobligation Hfinished") as "-#HR".
        iDestruct (lc_weaken 2 with "H£") as "H£". 1: done.
        iDestruct "H£" as "(H£_1 & H£_2)".
        iMod (lc_fupd_elim_later with "H£_1 HR") as "(_ & #Hη_resolved)".
        iMod (spsc_prop𑁒consume with "Hη_inv Hη_consumer Hη_resolved") as "HP". 1: done.
        iApply (lc_fupd_elim_later with "H£_2 HP").
      } {
        iApply (pool۰obligation𑁒wand with "Hobligation").
        iSteps.
      }
    Qed.

    #[local] Lemma pool٠wait₀𑁒spec P_notification P_pred Q_pred γ ctx scope notification pred :
      {{{
        pool۰context γ ctx scope ∗
        P_notification ∗
        □ (
          ∀ notify,
          P_notification -∗
          WP notify () {{ itype۰unit }} -∗
          WP notification notify {{ res,
            ⌜res = ()%V⌝ ∗
            P_notification
          }}
        ) ∗
        P_pred ∗
        □ (
          P_pred -∗
          WP pred () {{ res,
            ∃ b,
            ⌜res = #b⌝ ∗
            if b then Q_pred else P_pred
          }}
        )
      }}}
        pool٠wait₀ ctx notification pred
      {{{
        RET ();
        pool۰context γ ctx scope ∗
        Q_pred
      }}}.
    Proof.
      iIntros "%Φ ((:context lazy=) & HP_notification & #Hnotification & HP_pred & #Hpred) HΦ".

      iLöb as "HLöb".

      iDestruct "Hctx" as "(:context₁)".

      wp۰rec. rewrite pool٠max_round_noyield𑁒unfold pool٠max_round_yield𑁒unfold.

      awp۰apply+ (ws_hub_std٠pop_steal_until𑁒spec P_notification P_pred Q_pred with "[$Hhub_inv $Hhub_owner $HP_notification $Hnotification $HP_pred $Hpred]") without "HΦ". 1-3: done.
      iInv "Hinv" as "(:inv۰inner)".
      iAaccIntro with "Hhub_model". 1: iSteps. iIntros ([𝑔𝑙𝑜𝑏𝑎𝑙 |]) "Hhub_model".

      - iDestruct "Hhub_model" as "(%𝑔𝑙𝑜𝑏𝑎𝑙𝑠' & -> & Hhub_model)".
        apply symmetry, gmultiset_map𑁒disj_union𑁒singleton𑁒l𑁒inv in H𝑔𝑙𝑜𝑏𝑎𝑙𝑠 as (global & globals' & -> & -> & ->).
        iDestruct (big_sepMS_disj_union with "Hglobals") as "(Hglobal & Hglobals')".
        iEval (rewrite big_sepMS_singleton) in "Hglobal".
        iMod (globals۰model𑁒pop global with "Hglobals_model Hlocals_at") as "(Hglobals_model & Hlocals_at)"; [done.. |].
        iSplitR "Hglobal Hlocals_at". { iFrameSteps. }
        iIntros "!> {%- Hi} %empty (Hhub_owner & HP_notification & HP_pred) HΦ".

        wp۰apply+ (pool٠execute𑁒spec with "[$]") as "{%- Hi} %res ((:context₁) & (%R & Hglobal & HR))"; first done.
        iDestruct (locals۰at𑁒finish with "Hlocals_at Hglobal HR") as "Hlocals_at".
        wp۰apply+ ("HLöb" with "[$] HP_notification HP_pred HΦ").

      - iSplitR "Hlocals_at". { iFrameSteps. }
        iSteps.
    Qed.

    Lemma pool٠wait𑁒spec P_notification P_pred Q_pred γ ctx scope notification pred :
      {{{
        pool۰context γ ctx scope ∗
        P_notification ∗
        ( ∀ notify,
          P_notification -∗
          WP notify () {{ itype۰unit }} -∗
          WP notification notify {{ res,
            ⌜res = ()%V⌝ ∗
            P_notification
          }}
        ) ∗
        P_pred ∗
        □ (
          P_pred -∗
          WP pred () {{ res,
            ∃ b,
            ⌜res = #b⌝ ∗
            if b then Q_pred else P_pred
          }}
        )
      }}}
        pool٠wait ctx notification pred
      {{{
        RET ();
        pool۰context γ ctx scope ∗
        Q_pred
      }}}.
    Proof.
      iIntros "%Φ (Hctx & HP_notification & Hnotification & HP_pred & #Hpred) HΦ".

      lazymatch iTypeOf "Hnotification" with
      | Some (_, ?P) =>
          pose Q_notification := P
      end.

      wp۰rec.
      wp۰ref notification_registered as "Hnotification_registered".

      wp۰apply+ (pool٠wait₀𑁒spec
        ( ∃ b,
          notification_registered ↦ᵣ #b ∗
          P_notification ∗
          if b then True else Q_notification
        )
        P_pred
        Q_pred
      with "[$Hctx $Hnotification_registered $HP_notification $Hnotification $HP_pred $Hpred]").
      { iIntros "!> %notify (%b & Hnotification & HP_notification & HQ_notification) Hnotify".
        wp۰load.
        destruct b; iSteps.
      }

      iSteps.
    Qed.

    Lemma pool٠wait_ivar𑁒spec `{ivar۰G : !Ivar4G Σ} {context_name} γ ctx scope ivar Ψ Ξ (Γ : _ → context_name → _) :
      {{{
        pool۰context γ ctx scope ∗
        ivar_4۰inv ivar Ψ Ξ Γ
      }}}
        pool٠wait_ivar ctx ivar
      {{{
        RET ();
        £ 2 ∗
        pool۰context γ ctx scope ∗
        ivar_4۰resolved ivar
      }}}.
    Proof.
      iIntros "%Φ (Hctx & #Hivar_inv) HΦ".

      wp۰rec credits:"H£".
      iApply (lc_weaken 2) in "H£"; first done.

      wp۰apply+ (pool٠wait𑁒spec
        True
        True
        (ivar_4۰resolved ivar)
      with "[$Hctx]").
      { repeat iSplit. 1,3: done.

        - iIntros "%notify _ Hnotify".
          wp۰apply+ (ivar_4٠wait𑁒spec True True with "[$Hivar_inv Hnotify]") as ([waiter |]) "".
          all: iSteps.

        - iIntros "!> _".
          wp۰apply+ (ivar_4٠is_set𑁒spec with "Hivar_inv") as "%b".
          destruct b; iSteps.
      }

      iSteps.
    Qed.
  End pool۰G.

  #[global] Opaque pool۰scope.
  #[global] Opaque pool۰inv.
  #[global] Opaque pool۰model.
  #[global] Opaque pool۰context.
  #[global] Opaque pool۰consumer.
  #[global] Opaque pool۰obligation.
  #[global] Opaque pool۰finished.
End base.

Require zoo_parabs.pool__opaque.

Section pool۰G.
  Context `{pool۰G : PoolG Σ}.

  Implicit Types 𝑡 : location.
  Implicit Types t : val.
  Implicit Types γ : base.pool۰name.
  Implicit Types P P_notification P_pred Q Q_pred : iProp Σ.
  Implicit Types Ψ : val → iProp Σ.

  Definition pool۰inv t sz : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.pool۰inv γ sz.
  #[local] Instance : CustomIpat "inv" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hinv{_{}}
      )
    ".

  Definition pool۰context t ctx scope : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.pool۰context γ ctx scope.
  #[local] Instance : CustomIpat "context" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hctx{_{}}
      )
    ".

  Definition pool۰model t : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.pool۰model 𝑡 γ.
  #[local] Instance : CustomIpat "model" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hmodel{_{}}
      )
    ".

  Definition pool۰finished t : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.pool۰finished γ.
  #[local] Instance : CustomIpat "finished" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hfinished{_{}}
      )
    ".

  Definition pool۰consumer t P : iProp Σ :=
    pool۰finished t ={⊤}=∗
    P.

  Definition pool۰obligation t P : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.pool۰obligation γ P.
  #[local] Instance : CustomIpat "obligation" :=
    " ( %𝑡{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hobligation{_{}}
      )
    ".

  #[global] Instance pool۰obligation𑁒proper t :
    Proper ((≡) ==> (≡)) (pool۰obligation t).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance pool۰consumer𑁒proper t :
    Proper ((≡) ==> (≡)) (pool۰consumer t).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance pool۰inv𑁒persistent t sz :
    Persistent (pool۰inv t sz).
  Proof.
    apply _.
  Qed.
  #[global] Instance pool۰obligation𑁒persistent t P :
    Persistent (pool۰obligation t P).
  Proof.
    apply _.
  Qed.
  #[global] Instance pool۰finished𑁒persistent t :
    Persistent (pool۰finished t).
  Proof.
    apply _.
  Qed.

  Lemma pool۰inv𑁒agree t sz1 sz2 :
    pool۰inv t sz1 -∗
    pool۰inv t sz2 -∗
    ⌜sz1 = sz2⌝.
  Proof.
    iIntros "(:inv =1) (:inv =2)". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.pool۰inv𑁒agree with "Hinv_1 Hinv_2").
  Qed.

  Lemma pool۰consumer𑁒intro {t} P :
    (pool۰finished t ={⊤}=∗ P) ⊢
    pool۰consumer t P.
  Proof.
    done.
  Qed.
  Lemma pool۰consumer𑁒wand {t P1} P2 :
    pool۰consumer t P1 -∗
    (P1 -∗ P2) -∗
    pool۰consumer t P2.
  Proof.
    iSteps.
  Qed.
  Lemma pool۰consumer𑁒combine t P1 P2 :
    pool۰consumer t P1 -∗
    pool۰consumer t P2 -∗
    pool۰consumer t (P1 ∗ P2).
  Proof.
    iSteps.
  Qed.
  Lemma pool۰consumer𑁒or t P1 P2 :
    ( pool۰consumer t P1
    ∨ pool۰consumer t P2
    ) ⊢
    pool۰consumer t (P1 ∨ P2).
  Proof.
    iSteps.
  Qed.
  Lemma pool۰consumer𑁒exist {A} {t} (Φ : A → iProp Σ) x :
    pool۰consumer t (Φ x) ⊢
    pool۰consumer t (∃ x, Φ x).
  Proof.
    iSteps.
  Qed.
  Lemma pool۰consumer𑁒forall {A} {t} (Φ : A → iProp Σ) x :
    pool۰consumer t (∀ x, Φ x) ⊢
    pool۰consumer t (Φ x).
  Proof.
    iSteps.
  Qed.
  Lemma pool۰consumer𑁒finished t P :
    pool۰consumer t P -∗
    pool۰finished t ={⊤}=∗
    P.
  Proof.
    iSteps.
  Qed.
  #[global] Instance pool۰consumer𑁒mono t :
    Proper ((⊢) ==> (⊢)) (pool۰consumer t).
  Proof.
    rewrite /pool۰consumer => P1 P2 -> //.
  Qed.
  #[global] Instance pool۰consumer𑁒flip𑁒mono t :
    Proper (flip (⊢) ==> flip (⊢)) (pool۰consumer t).
  Proof.
    rewrite /pool۰consumer => P1 P2 -> //.
  Qed.

  Lemma pool۰obligation𑁒wand {t P1} P2 :
    pool۰obligation t P1 -∗
    □ (P1 -∗ P2) -∗
    pool۰obligation t P2.
  Proof.
    iIntros "(:obligation) H".
    iDestruct (base.pool۰obligation𑁒wand with "Hobligation H") as "$".
    iSteps.
  Qed.
  Lemma pool۰obligation𑁒split t P1 P2 :
    pool۰obligation t (P1 ∗ P2) ⊢
      pool۰obligation t P1 ∗
      pool۰obligation t P2.
  Proof.
    iIntros "(:obligation)".
    iDestruct (base.pool۰obligation𑁒split with "Hobligation") as "($ & $)".
    iSteps.
  Qed.
  Lemma pool۰obligation𑁒combine t P1 P2 :
    pool۰obligation t P1 -∗
    pool۰obligation t P2 -∗
    pool۰obligation t (P1 ∗ P2).
  Proof.
    iIntros "(:obligation =1) (:obligation =2)". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->.
    iDestruct (base.pool۰obligation𑁒combine with "Hobligation_1 Hobligation_2") as "$".
    iSteps.
  Qed.
  Lemma pool۰obligation𑁒finished t P :
    pool۰obligation t P -∗
    pool۰finished t -∗
    ▷ □ P.
  Proof.
    iIntros "(:obligation =1) (:finished =2)". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.pool۰obligation𑁒finished with "Hobligation_1 Hfinished_2").
  Qed.

  Lemma pool٠create𑁒spec sz :
    (0 ≤ sz)%Z →
    {{{
      True
    }}}
      pool٠create #sz
    {{{
      t
    , RET t;
      pool۰inv t ₊sz ∗
      pool۰model t
    }}}.
  Proof.
    iIntros "% %Φ _ HΦ".

    iApply wp𑁒fupd.
    wp۰apply (base.pool٠create𑁒spec with "[//]") as (𝑡 γ) "(Hinv & Hmodel & Hmeta)"; first done.
    iMod (meta𑁒set γ with "Hmeta") as "#Hmeta"; first done.
    iSteps.
  Qed.

  Lemma pool٠run_on𑁒spec Ψ t task :
    {{{
      pool۰model t ∗
      ( ∀ ctx scope,
        pool۰context t ctx scope -∗
        WP task ctx {{ v,
          pool۰context t ctx scope ∗
          Ψ v
        }}
      )
    }}}
      pool٠run_on t task
    {{{
      v
    , RET v;
      pool۰model t ∗
      Ψ v
    }}}.
  Proof.
    iIntros "%Φ ((:model) & Htask) HΦ".

    wp۰apply (base.pool٠run_on𑁒spec Ψ with "[$Hmodel Htask]").
    { iIntros "%ctx %scope Hctx".
      wp۰apply (wp𑁒wand with "(Htask [$Hctx])") as (v) "((:context =1) & $)"; first iSteps.
      simplify.
      iDestruct (meta𑁒agree with "Hmeta Hmeta_1") as %->. iClear "Hmeta".
      iFrame.
    }
    iSteps.
  Qed.

  Lemma pool٠close𑁒spec t :
    {{{
      pool۰model t
    }}}
      pool٠close t
    {{{
      RET ();
      pool۰finished t
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".

    wp۰apply (base.pool٠close𑁒spec with "Hmodel").
    iSteps.
  Qed.

  Lemma pool٠run𑁒spec (Ψ : val → val → iProp Σ) sz task :
    (0 ≤ sz)%Z →
    {{{
      ∀ t ctx scope,
      pool۰inv t ₊sz -∗
      pool۰context t ctx scope -∗
      WP task ctx {{ v,
        pool۰context t ctx scope ∗
        Ψ t v
      }}
    }}}
      pool٠run #sz task
    {{{
      t v
    , RET v;
      pool۰finished t ∗
      Ψ t v
    }}}.
  Proof.
    iIntros "%Hsz %Φ Htask HΦ".

    set (Ψ' 𝑡 γ v := (
      𝑡 ↪ γ ∗
      Ψ #𝑡 v
    )%I).
    wp۰apply (base.pool٠run𑁒spec Ψ' with "[Htask]"). 1: done.
    { iIntros "%𝑡 %γ %ctx %scope #Hinv Hmeta Hctx".
      iMod (meta𑁒set γ with "Hmeta") as "#Hmeta"; first done.
      wp۰apply (wp𑁒wand with "(Htask [] [$Hctx])") as (v) "((:context =1) & HΨ)". 1-2: iSteps.
      simplify.
      iDestruct (meta𑁒agree with "Hmeta Hmeta_1") as %->. iClear "Hmeta".
      iFrameSteps.
    }
    iSteps.
  Qed.

  Lemma pool٠size𑁒spec t sz ctx scope :
    {{{
      pool۰inv t sz ∗
      pool۰context t ctx scope
    }}}
      pool٠size ctx
    {{{
      RET #sz;
      pool۰context t ctx scope
    }}}.
  Proof.
    iIntros "%Φ ((:model =1) & (:context =2)) HΦ". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp۰apply (base.pool٠size𑁒spec with "[$]").
    iSteps.
  Qed.

  Lemma pool٠async𑁒spec P Q t ctx scope task :
    {{{
      pool۰context t ctx scope ∗
      ( ∀ ctx scope,
        pool۰context t ctx scope -∗
        WP task ctx {{ res,
          pool۰context t ctx scope ∗
          ▷ P ∗
          ▷ □ Q
        }}
      )
    }}}
      pool٠async ctx task
    {{{
      RET ();
      pool۰context t ctx scope ∗
      pool۰consumer t P ∗
      pool۰obligation t Q
    }}}.
  Proof.
    iIntros "%Φ ((:context) & Htask) HΦ".

    wp۰apply (base.pool٠async𑁒spec P Q with "[$Hctx Htask]") as "(Hctx & Hconsumer & Hobligation)".
    { iIntros "{%} %ctx %scope Hctx".
      wp۰apply (wp𑁒wand with "(Htask [$Hctx])") as (v) "((:context =1) & $)"; first iSteps.
      simplify.
      iDestruct (meta𑁒agree with "Hmeta Hmeta_1") as %->. iClear "Hmeta".
      iFrame.
    }

    iStep 2. iSplitL "Hconsumer". 2:iSteps.
    iIntros "(:finished =1)". simplify.
    iDestruct (meta𑁒agree with "Hmeta Hmeta_1") as %<-.
    iApply ("Hconsumer" with "Hfinished_1").
  Qed.

  Lemma pool٠wait𑁒spec P_notification P_pred Q_pred t ctx scope notification pred :
    {{{
      pool۰context t ctx scope ∗
      P_notification ∗
      ( ∀ notify,
        P_notification -∗
        WP notify () {{ itype۰unit }} -∗
        WP notification notify {{ res,
          ⌜res = ()%V⌝ ∗
          P_notification
        }}
      ) ∗
      P_pred ∗
      □ (
        P_pred -∗
        WP pred () {{ res,
          ∃ b,
          ⌜res = #b⌝ ∗
          if b then Q_pred else P_pred
        }}
      )
    }}}
      pool٠wait ctx notification pred
    {{{
      RET ();
      pool۰context t ctx scope ∗
      Q_pred
    }}}.
  Proof.
    iIntros "%Φ ((:context) & HP & Hpred) HΦ".

    wp۰apply (base.pool٠wait𑁒spec with "[$]").
    iSteps.
  Qed.

  Lemma pool٠wait_ivar𑁒spec `{ivar۰G : !Ivar4G Σ} {context_name} t ctx scope ivar Ψ Ξ (Γ : _ → context_name → _) :
    {{{
      pool۰context t ctx scope ∗
      ivar_4۰inv ivar Ψ Ξ Γ
    }}}
      pool٠wait_ivar ctx ivar
    {{{
      RET ();
      £ 2 ∗
      pool۰context t ctx scope ∗
      ivar_4۰resolved ivar
    }}}.
  Proof.
    iIntros "%Φ ((:context) & Hivar_inv) HΦ".

    wp۰apply (base.pool٠wait_ivar𑁒spec with "[$]").
    iSteps.
  Qed.
End pool۰G.

#[global] Opaque pool۰scope.
#[global] Opaque pool۰inv.
#[global] Opaque pool۰model.
#[global] Opaque pool۰context.
#[global] Opaque pool۰obligation.
#[global] Opaque pool۰consumer.
#[global] Opaque pool۰finished.

Section pool۰G.
  Context `{pool۰G : PoolG Σ}.

  Implicit Types P Q R : iProp Σ.

  #[global] Instance from_assumption𑁒pool۰consumer t p P Q :
    FromAssumption p P Q →
    KnownRFromAssumption p P (pool۰consumer t Q).
  Proof.
    rewrite /KnownRFromAssumption /FromAssumption => ->.
    rewrite -pool۰consumer𑁒intro.
    iSteps.
  Qed.

  #[global] Instance from_pure𑁒pool۰consumer t a P ϕ :
    FromPure a P ϕ →
    FromPure a (pool۰consumer t P) ϕ.
  Proof.
    rewrite /FromPure => ->.
    rewrite -pool۰consumer𑁒intro.
    iSteps.
  Qed.

  #[global] Instance into_wand𑁒pool۰consumer t p q R P Q :
    IntoWand false false R P Q →
    IntoWand p q (pool۰consumer t R) (pool۰consumer t P) (pool۰consumer t Q).
  Proof.
    rewrite /IntoWand /= => ->.
    rewrite !bi.intuitionistically_if_elim.
    iIntros "HQ HP".
    iApply pool۰consumer𑁒intro. iIntros "#Hfinished".
    iMod (pool۰consumer𑁒finished with "HP Hfinished") as "HP".
    iMod (pool۰consumer𑁒finished with "HQ Hfinished") as "HQ".
    iSteps.
  Qed.
  #[global] Instance into_wand𑁒pool۰consumer𑁒persistent t p q R P Q :
    IntoWand false q R P Q →
    IntoWand p q (pool۰consumer t R) P (pool۰consumer t Q).
  Proof.
    rewrite /IntoWand /= => ->.
    rewrite bi.intuitionistically_if_elim.
    iIntros "HQ HP".
    iApply pool۰consumer𑁒intro. iIntros "#Hfinished".
    iMod (pool۰consumer𑁒finished with "HQ Hfinished") as "HQ".
    iSteps.
  Qed.
  #[global] Instance into_wand𑁒pool۰consumer𑁒args t p q R P Q :
    IntoWand p false R P Q →
    IntoWand' p q R (pool۰consumer t P) (pool۰consumer t Q).
  Proof.
    rewrite /IntoWand' /IntoWand /= => ->.
    rewrite bi.intuitionistically_if_elim.
    iIntros "HQ HP".
    iApply (pool۰consumer𑁒wand with "HP HQ").
  Qed.

  #[global] Instance from_sep𑁒pool۰consumer t P Q1 Q2 :
    FromSep P Q1 Q2 →
    FromSep (pool۰consumer t P) (pool۰consumer t Q1) (pool۰consumer t Q2).
  Proof.
    rewrite /FromSep => <-.
    iIntros "(HQ1 & HQ2)".
    iApply (pool۰consumer𑁒combine with "HQ1 HQ2").
  Qed.

  #[global] Instance from_or𑁒pool۰consumer t P Q1 Q2 :
    FromOr P Q1 Q2 →
    FromOr (pool۰consumer t P) (pool۰consumer t Q1) (pool۰consumer t Q2).
  Proof.
    rewrite /FromOr => <-.
    apply pool۰consumer𑁒or.
  Qed.

  #[global] Instance from_exist𑁒pool۰consumer t {A} P (Φ : A → iProp Σ) :
    FromExist P Φ →
    FromExist (pool۰consumer t P) (λ a, pool۰consumer t (Φ a)).
  Proof.
    rewrite /FromExist => <-.
    iIntros "(%x & H)".
    iApply (pool۰consumer𑁒exist with "H").
  Qed.

  #[global] Instance into_forall𑁒pool۰consumer t {A} P (Φ : A → iProp Σ) :
    IntoForall P Φ →
    IntoForall (pool۰consumer t P) (λ a, pool۰consumer t (Φ a)).
  Proof.
    rewrite /IntoForall => ->.
    iIntros "H %x".
    iApply (pool۰consumer𑁒forall with "H").
  Qed.

  #[global] Instance from_modal𑁒pool۰consumer t P :
    FromModal True modality_id (pool۰consumer t P) (pool۰consumer t P) P.
  Proof.
    rewrite /FromModal -pool۰consumer𑁒intro.
    iSteps.
  Qed.

  #[global] Instance elim_modal𑁒pool۰consumer t p P Q :
    ElimModal True p false (pool۰consumer t P) P (pool۰consumer t Q) (pool۰consumer t Q).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim /=.
    iIntros "_ (HP & HQ)".
    iApply pool۰consumer𑁒intro. iIntros "#Hfinished".
    iMod (pool۰consumer𑁒finished with "HP Hfinished") as "HP".
    iApply (pool۰consumer𑁒finished with "(HQ HP) Hfinished").
  Qed.

  #[global] Instance add_modal𑁒pool۰consumer t P Q :
    AddModal (pool۰consumer t P) P (pool۰consumer t Q).
  Proof.
    rewrite /AddModal.
    iIntros "(HP & HQ)".
    iApply pool۰consumer𑁒intro. iIntros "#Hfinished".
    iMod (pool۰consumer𑁒finished with "HP Hfinished") as "HP".
    iApply (pool۰consumer𑁒finished with "(HQ HP) Hfinished").
  Qed.

  #[global] Instance frame𑁒pool۰consumer t p R P Q :
    Frame p R P Q →
    Frame p R (pool۰consumer t P) (pool۰consumer t Q)
  | 2.
  Proof.
    rewrite /Frame => <-.
    iIntros "(HR & HQ)".
    iApply pool۰consumer𑁒intro. iIntros "#Hfinished".
    iMod (pool۰consumer𑁒finished with "HQ Hfinished") as "HQ".
    iSteps.
  Qed.
End pool۰G.
