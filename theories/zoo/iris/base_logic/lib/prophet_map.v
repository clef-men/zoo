From iris.base_logic.lib Require Import
  ghost_map.

From zoo Require Import
  prelude.
From zoo.iris.base_logic Require Export
  lib.base.
From zoo.iris Require Import
  diaframe.
From zoo Require Import
  options.

Class ProphetMapGpre Σ P V `{Countable P} := {
  #[local] prophet_map_Gpre_inG :: ghost_mapG Σ P (list V) ;
}.

Class ProphetMapG Σ P V `{Countable P} := {
  #[local] prophet_map_inG :: ProphetMapGpre Σ P V ;
  prophet_map_name : gname ;
}.
#[global] Arguments prophet_map_name {_ _ _ _ _} _ : assert.

Definition prophet_map_Σ P V `{Countable P} :=
  ghost_mapΣ P (list V).
#[global] Instance subG_prophet_map_Σ Σ P V `{Countable P} :
  subG (prophet_map_Σ P V) Σ →
  ProphetMapGpre Σ P V.
Proof.
  solve_inG.
Qed.

Section prophecies_resolve.
  Context {P V : Type} `{Countable P}.

  Implicit Type pid : P.
  Implicit Type prophets : gmap P (list V).

  #[local] Fixpoint prophecies_resolve xprophs pid : list V :=
    match xprophs with
    | [] =>
        []
    | xproph :: xprophs =>
        if decide (pid = xproph.1) then
          xproph.2 :: prophecies_resolve xprophs pid
        else
          prophecies_resolve xprophs pid
    end.

  #[local] Definition prophets_resolve prophets xprophs :=
    map_Forall (λ pid prophs, prophs = prophecies_resolve xprophs pid) prophets.

  #[local] Lemma prophets_resolve_insert xprophs pid prophets :
    prophets_resolve prophets xprophs →
    pid ∉ dom prophets →
    prophets_resolve (<[pid := prophecies_resolve xprophs pid]> prophets) xprophs.
  Proof.
    intros Hinlist Hpid pid' prophs Hlookup.
    destruct (decide (pid = pid')) as [-> | Hne].
    - rewrite lookup_insert in Hlookup.
      inversion Hlookup. done.
    - rewrite lookup_insert_ne // in Hlookup.
      apply Hinlist. done.
  Qed.
End prophecies_resolve.

Section prophet_map_G.
  Context `{prophet_map_G : ProphetMapG Σ P V}.

  Definition prophet_map_interp xprophs pids : iProp Σ :=
    ∃ prophets,
    ⌜prophets_resolve prophets xprophs⌝ ∗
    ⌜dom prophets ⊆ pids⌝ ∗
    ghost_map_auth prophet_map_G.(prophet_map_name) 1 prophets.

  Definition prophet_model pid dq prophs : iProp Σ :=
    ghost_map_elem prophet_map_G.(prophet_map_name) pid dq prophs.
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
    iApply ghost_map_elem_valid.
  Qed.
  Lemma prophet_model_combine pid dq1 prophs1 dq2 prophs2 :
    prophet_model pid dq1 prophs1 -∗
    prophet_model pid dq2 prophs2 -∗
      ⌜prophs1 = prophs2⌝ ∗
      prophet_model pid (dq1 ⋅ dq2) prophs1.
  Proof.
    iIntros "Hmodel1 Hmodel2".
    iDestruct (ghost_map_elem_combine with "Hmodel1 Hmodel2") as "(Hmodel & <-)".
    iSteps.
  Qed.
  Lemma prophet_model_valid_2 pid dq1 prophs1 dq2 prophs2 :
    prophet_model pid dq1 prophs1 -∗
    prophet_model pid dq2 prophs2 -∗
      ⌜✓ (dq1 ⋅ dq2)⌝ ∗
      ⌜prophs1 = prophs2⌝.
  Proof.
    iIntros "Hmodel1 Hmodel2".
    iDestruct (prophet_model_combine with "Hmodel1 Hmodel2") as "(<- & Hmodel)".
    iDestruct (prophet_model_valid with "Hmodel") as %?.
    iSteps.
  Qed.
  Lemma prophet_model_agree pid dq1 prophs1 dq2 prophs2 :
    prophet_model pid dq1 prophs1 -∗
    prophet_model pid dq2 prophs2 -∗
    ⌜prophs1 = prophs2⌝.
  Proof.
    iIntros "Hmodel1 Hmodel2".
    iDestruct (prophet_model_combine with "Hmodel1 Hmodel2") as "(<- & _)".
    iSteps.
  Qed.
  Lemma prophet_model_dfrac_ne pid1 dq1 prophs1 pid2 dq2 prophs2 :
    ¬ ✓ (dq1 ⋅ dq2) →
    prophet_model pid1 dq1 prophs1 -∗
    prophet_model pid2 dq2 prophs2 -∗
    ⌜pid1 ≠ pid2⌝.
  Proof.
    iIntros "% Hmodel1 Hmodel2 ->".
    iDestruct (prophet_model_valid_2 with "Hmodel1 Hmodel2") as "(% & _)". done.
  Qed.
  Lemma prophet_model_ne pid1 prophs1 pid2 dq2 prophs2 :
    prophet_model pid1 (DfracOwn 1) prophs1 -∗
    prophet_model pid2 dq2 prophs2 -∗
    ⌜pid1 ≠ pid2⌝.
  Proof.
    iApply prophet_model_dfrac_ne; [done.. | intros []%(exclusive_l _)].
  Qed.
  Lemma prophet_model_exclusive pid prophs1 dq2 prophs2 :
    prophet_model pid (DfracOwn 1) prophs1 -∗
    prophet_model pid dq2 prophs2 -∗
    False.
  Proof.
    iIntros "Hmodel1 Hmodel2".
    iDestruct (prophet_model_ne with "Hmodel1 Hmodel2") as %?. done.
  Qed.
  Lemma prophet_model_persist pid dq prophs :
    prophet_model pid dq prophs ⊢ |==>
    prophet_model pid DfracDiscarded prophs.
  Proof.
    iApply ghost_map_elem_persist.
  Qed.

  Lemma prophet_map_new pid xprophs pids :
    pid ∉ pids →
    prophet_map_interp xprophs pids ⊢ |==>
      prophet_map_interp xprophs ({[pid]} ∪ pids) ∗
      prophet_model pid (DfracOwn 1) (prophecies_resolve xprophs pid).
  Proof.
    iIntros "%Hpid (%prophets & %Hprophets & %Hpids & Hauth)".
    iMod (ghost_map_insert pid (prophecies_resolve xprophs pid) with "Hauth") as "(Hauth & Helem)".
    { apply not_elem_of_dom. set_solver. }
    iFrame. iPureIntro. split.
    - apply prophets_resolve_insert; first done. set_solver.
    - rewrite dom_insert. set_solver.
  Qed.

  Lemma prophet_map_resolve pid proph xprophs pids prophs :
    prophet_map_interp ((pid, proph) :: xprophs) pids -∗
    prophet_model pid (DfracOwn 1) prophs ==∗
      ∃ prophs',
      ⌜prophs = proph :: prophs'⌝ ∗
      prophet_map_interp xprophs pids ∗
      prophet_model pid (DfracOwn 1) prophs'.
  Proof.
    iIntros "(%prophets & %Hprophets & %Hpids & Hauth) Hp".
    iCombine "Hauth Hp" gives %Hlookup.
    assert (prophs = proph :: prophecies_resolve xprophs pid) as ->.
    { rewrite (Hprophets pid prophs Hlookup) /= decide_True //. }
    iMod (ghost_map_update (prophecies_resolve xprophs pid) with "Hauth Hp") as "(Hauth & Helem)".
    iExists (prophecies_resolve xprophs pid). iFrameSteps; iPureIntro.
    - intros pid' prophs' Hlookup'. destruct (decide (pid = pid')) as [<- | Hne].
      + rewrite lookup_insert in Hlookup'.
        inversion Hlookup'. done.
      + rewrite lookup_insert_ne // in Hlookup'.
        rewrite (Hprophets pid' prophs' Hlookup') /= decide_False //.
    - assert (pid ∈ dom prophets) by exact: elem_of_dom_2.
      set_solver.
  Qed.
End prophet_map_G.

Lemma prophet_map_init `{prophet_map_Gpre : ProphetMapGpre Σ P V} xprophs pids :
  ⊢ |==>
    ∃ _ : ProphetMapG Σ P V,
    prophet_map_interp xprophs pids.
Proof.
  iMod (ghost_map_alloc_empty) as (γ) "Hauth".
  iExists (Build_ProphetMapG _ _ _ _ _ _ _), ∅. iSteps.
Qed.

#[global] Opaque prophet_map_interp.
#[global] Opaque prophet_model.
