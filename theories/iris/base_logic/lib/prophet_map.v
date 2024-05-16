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

  Fixpoint prophecies_resolve xprophs pid : list V :=
    match xprophs with
    | [] =>
        []
    | xproph :: xprophs =>
        if decide (pid = xproph.1) then
          xproph.2 :: prophecies_resolve xprophs pid
        else
          prophecies_resolve xprophs pid
    end.

  Definition prophets_resolve prophets xprophs :=
    map_Forall (λ pid prophs, prophs = prophecies_resolve xprophs pid) prophets.

  Lemma resolves_insert xprophs pid prophets :
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
    ⌜prophets_resolve prophets xprophs ∧ dom prophets ⊆ pids⌝ ∗
    ghost_map_auth prophet_map_G.(prophet_map_name) 1 prophets.

  Definition prophet_model pid prophs : iProp Σ :=
    ghost_map_elem prophet_map_G.(prophet_map_name) pid (DfracOwn 1) prophs.

  #[global] Instance prophet_model_timeless pid prophs :
    Timeless (prophet_model pid prophs).
  Proof.
    apply _.
  Qed.

  Lemma prophet_model_exclusive pid prophs1 prophs2 :
    prophet_model pid prophs1 -∗
    prophet_model pid prophs2 -∗
    False.
  Proof.
    iIntros "Hmodel1 Hmodel2".
    iDestruct (ghost_map_elem_ne with "Hmodel1 Hmodel2") as %?.
    iSteps.
  Qed.

  Lemma prophet_map_new pid pids xprophs :
    pid ∉ pids →
    prophet_map_interp xprophs pids ==∗
      prophet_map_interp xprophs ({[pid]} ∪ pids) ∗
      prophet_model pid (prophecies_resolve xprophs pid).
  Proof.
    iIntros "%Hpid Hpids".
    iDestruct "Hpids" as "(%prophets & (%Hprophets & %Hpids) & Hauth)".
    iMod (ghost_map_insert pid (prophecies_resolve xprophs pid) with "Hauth") as "(Hauth & Helem)".
    { apply not_elem_of_dom. set_solver. }
    iModIntro. iFrame. iExists (<[pid := prophecies_resolve xprophs pid]> prophets). iFrame. iPureIntro.
    split.
    - apply resolves_insert; first done. set_solver.
    - rewrite dom_insert. set_solver.
  Qed.

  Lemma prophet_map_resolve pid proph xprophs pids prophs :
    prophet_map_interp ((pid, proph) :: xprophs) pids -∗
    prophet_model pid prophs ==∗
      ∃ prophs',
      ⌜prophs = proph :: prophs'⌝ ∗
      prophet_map_interp xprophs pids ∗
      prophet_model pid prophs'.
  Proof.
    iIntros "Hpids Hp".
    iDestruct "Hpids" as "(%prophets & (%Hprophets & %Hpids) & Hauth)".
    iCombine "Hauth Hp" gives %Hlookup.
    assert (prophs = proph :: prophecies_resolve xprophs pid) as ->.
    { rewrite (Hprophets pid prophs Hlookup) /= decide_True //. }
    iMod (ghost_map_update (prophecies_resolve xprophs pid) with "Hauth Hp") as "(Hauth & Helem)".
    iExists (prophecies_resolve xprophs pid). iFrame. iSplitR; first iSteps.
    iExists _. iFrame. iPureIntro. split.
    - intros pid' prophs' Hlookup'. destruct (decide (pid = pid')) as [<- | Hne].
      + rewrite lookup_insert in Hlookup'.
        inversion Hlookup'. done.
      + rewrite lookup_insert_ne // in Hlookup'.
        rewrite (Hprophets pid' prophs' Hlookup') /= decide_False //.
    - assert (pid ∈ dom prophets) by exact: elem_of_dom_2.
      rewrite dom_insert. set_solver.
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
