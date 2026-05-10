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

Class ProphetMapG Σ P V `{Countable P} :=
  { #[local] prophet_map_G_inG :: ghost_mapG Σ P (list V)
  }.

Definition prophet_map_Σ P V `{Countable P} :=
  #[ghost_mapΣ P (list V)
  ].
#[global] Instance subG_prophet_map_Σ Σ P V `{Countable P} :
  subG (prophet_map_Σ P V) Σ →
  ProphetMapG Σ P V.
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
    destruct_decide (pid = pid') as -> | Hne.
    - rewrite lookup_insert_eq in Hlookup.
      inversion Hlookup. done.
    - rewrite lookup_insert_ne // in Hlookup.
      apply Hinlist. done.
  Qed.
End prophecies_resolve.

Section prophet_map_G.
  Context `{prophet_map_G : ProphetMapG Σ P V}.

  Definition prophet_map_interp γ xprophs pids : iProp Σ :=
    ∃ prophets,
    ⌜prophets_resolve prophets xprophs⌝ ∗
    ⌜dom prophets ⊆ pids⌝ ∗
    ghost_map_auth γ 1 prophets.

  Definition prophet_model γ pid prophs : iProp Σ :=
    ghost_map_elem γ pid (DfracOwn 1) prophs.

  Lemma prophet_map_alloc xprophs pids :
    ⊢ |==>
      ∃ γ,
      prophet_map_interp γ xprophs pids.
  Proof.
    iMod ghost_map_alloc_empty as "(%γ & $)" => //.
  Qed.

  #[global] Instance prophet_model_timeless γ pid prophs :
    Timeless (prophet_model γ pid prophs).
  Proof.
    apply _.
  Qed.

  Lemma prophet_model_exclusive γ pid prophs1 prophs2 :
    prophet_model γ pid prophs1 -∗
    prophet_model γ pid prophs2 -∗
    False.
  Proof.
    iIntros "Hmodel_1 Hmodel_2".
    iDestruct (ghost_map_elem_ne with "Hmodel_1 Hmodel_2") as %[] => //.
  Qed.

  Lemma prophet_map_new {γ xprophs pids} pid :
    pid ∉ pids →
    prophet_map_interp γ xprophs pids ⊢ |==>
      ∃ prophs,
      prophet_map_interp γ xprophs ({[pid]} ∪ pids) ∗
      prophet_model γ pid prophs.
  Proof.
    iIntros "%Hpid (%prophets & %Hprophets & %Hpids & Hauth)".
    iMod (ghost_map_insert pid (prophecies_resolve xprophs pid) with "Hauth") as "(Hauth & Helem)".
    { apply not_elem_of_dom. set_solver. }
    iFrame. iPureIntro. split.
    - apply prophets_resolve_insert; first done. set_solver.
    - rewrite dom_insert. set_solver.
  Qed.

  Lemma prophet_map_resolve γ pid proph xprophs pids prophs :
    prophet_map_interp γ ((pid, proph) :: xprophs) pids -∗
    prophet_model γ pid prophs ==∗
      ∃ prophs',
      ⌜prophs = proph :: prophs'⌝ ∗
      prophet_map_interp γ xprophs pids ∗
      prophet_model γ pid prophs'.
  Proof.
    iIntros "(%prophets & %Hprophets & %Hpids & Hauth) Hp".
    iCombine "Hauth Hp" gives %Hlookup.
    assert (prophs = proph :: prophecies_resolve xprophs pid) as ->.
    { rewrite (Hprophets pid prophs Hlookup) /= decide_True //. }
    iMod (ghost_map_update (prophecies_resolve xprophs pid) with "Hauth Hp") as "(Hauth & Helem)".
    iExists (prophecies_resolve xprophs pid). iFrameSteps; iPureIntro.
    - intros pid' prophs' Hlookup'. destruct_decide (pid = pid') as <- | Hne.
      + rewrite lookup_insert_eq in Hlookup'.
        inversion Hlookup'. done.
      + rewrite lookup_insert_ne // in Hlookup'.
        rewrite (Hprophets pid' prophs' Hlookup') /= decide_False //.
    - assert (pid ∈ dom prophets) by exact: elem_of_dom_2.
      set_solver.
  Qed.
End prophet_map_G.

#[global] Opaque prophet_map_interp.
#[global] Opaque prophet_model.
