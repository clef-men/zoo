From zoo Require Import
  prelude.
From zoo.iris.bi Require Import
  big_op.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
  base
  deque__code.
From zoo_std Require Import
  option
  xdeque.
From zoo Require Import
  options.

Implicit Types fn : val.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition deque_model t vs : iProp Σ :=
    ∃ nodes,
    xdeque_model t nodes ∗
    [∗ list] node; v ∈ nodes; vs, node.[xdeque_data] ↦ v.

  #[global] Instance deque_model_timeless t vs :
    Timeless (deque_model t vs).
  Proof.
    apply _.
  Qed.

  Lemma deque_create_spec :
    {{{
      True
    }}}
      deque_create ()
    {{{ t,
      RET t;
      deque_model t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_apply (xdeque_create_spec with "[//]").
    iSteps.
  Qed.

  Lemma deque_is_empty_spec t vs :
    {{{
      deque_model t vs
    }}}
      deque_is_empty t
    {{{
      RET #(bool_decide (vs = []%list));
      deque_model t vs
    }}}.
  Proof.
    iIntros "%Φ (%nodes & Hmodel & Hnodes) HΦ".
    wp_apply (xdeque_is_empty_spec with "Hmodel").
    iDestruct (big_sepL2_length with "Hnodes") as %Hlength.
    rewrite -!(bool_decide_ext _ _ (length_zero_iff_nil _)) Hlength.
    iSteps.
  Qed.

  Lemma deque_push_front_spec t vs v :
    {{{
      deque_model t vs
    }}}
      deque_push_front t v
    {{{
      RET ();
      deque_model t (v :: vs)
    }}}.
  Proof.
    iIntros "%Φ (%nodes & Hmodel & Hnodes) HΦ".
    wp_rec.
    wp_block node as "(Hnode_prev & Hnode_next & Hnode_data & _)".
    wp_apply (xdeque_push_front_spec with "[$Hmodel $Hnode_prev $Hnode_next]").
    iSteps.
  Qed.

  Lemma deque_push_back_spec t vs v :
    {{{
      deque_model t vs
    }}}
      deque_push_back t v
    {{{
      RET ();
      deque_model t (vs ++ [v])
    }}}.
  Proof.
    iIntros "%Φ (%nodes & Hmodel & Hnodes) HΦ".
    wp_rec.
    wp_block node as "(Hnode_prev & Hnode_next & Hnode_data & _)".
    wp_apply (xdeque_push_back_spec with "[$Hmodel $Hnode_prev $Hnode_next]").
    iSteps. iApply big_sepL2_snoc. iSteps.
  Qed.

  Lemma deque_pop_front_spec t vs :
    {{{
      deque_model t vs
    }}}
      deque_pop_front t
    {{{
      RET head vs : val;
      deque_model t (tail vs)
    }}}.
  Proof.
    iIntros "%Φ (%nodes & Hmodel & Hnodes) HΦ".
    wp_rec.
    wp_apply (xdeque_pop_front_spec with "Hmodel") as "Hmodel".
    destruct nodes as [| node nodes].
    - iDestruct (big_sepL2_nil_inv_l with "Hnodes") as %->.
      iSteps.
    - iDestruct (big_sepL2_cons_inv_l with "Hnodes") as "(%v & %vs' & ->  & Hnode & Hnodes)".
      wp_load.
      iSteps.
  Qed.

  Lemma deque_pop_back_spec t vs :
    {{{
      deque_model t vs
    }}}
      deque_pop_back t
    {{{ o,
      RET o : val;
      match o with
      | None =>
          ⌜vs = []⌝ ∗
          deque_model t []
      | Some v =>
          ∃ vs',
          ⌜vs = vs' ++ [v]⌝ ∗
          deque_model t vs'
      end
    }}}.
  Proof.
    iIntros "%Φ (%nodes & Hmodel & Hnodes) HΦ".
    wp_rec.
    wp_apply (xdeque_pop_back_spec with "Hmodel") as ([node |]) "Hmodel".
    - iDestruct "Hmodel" as "(%nodes' & -> & Hmodel)".
      iDestruct (big_sepL2_snoc_inv_l with "Hnodes") as "(%vs' & %v & -> & Hnodes & Hnode)".
      wp_load. wp_pures.
      iApply ("HΦ" $! (Some _)).
      iSteps.
    - iDestruct "Hmodel" as "(-> & Hmodel)".
      iDestruct (big_sepL2_nil_inv_l with "Hnodes") as %->.
      wp_pures.
      iApply ("HΦ" $! None).
      iSteps.
  Qed.

  Lemma deque_iter_spec Ψ fn t vs :
    {{{
      ▷ Ψ [] ∗
      deque_model t vs ∗
      □ (
        ∀ vs_done v vs_todo,
        ⌜vs = vs_done ++ v :: vs_todo⌝ -∗
        Ψ vs_done -∗
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ (vs_done ++ [v])
        }}
      )
    }}}
      deque_iter fn t
    {{{
      RET ();
      deque_model t vs ∗
      Ψ vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & (%nodes & Hmodel & Hnodes) & #Hfn) HΦ".
    wp_rec.
    pose (Χ (nodes_done : list location) := (
      Ψ (take (length nodes_done) vs) ∗
      [∗ list] node; v ∈ nodes; vs, node.[xdeque_data] ↦ v
    )%I).
    wp_smart_apply (xdeque_iter_spec Χ with "[$HΨ $Hnodes $Hmodel]").
    { iIntros "!> %nodes_done %node %nodes_todo -> (HΨ & Hnodes)".
      iDestruct (big_sepL2_lookup_acc_l _ (length nodes_done) with "Hnodes") as "(%v & %Hvs_lookup & Hnode & Hnodes)".
      { rewrite lookup_app_r // Nat.sub_diag //. }
      wp_load.
      wp_apply (wp_wand with "(Hfn [%] HΨ)").
      { erewrite take_drop_middle => //. }
      rewrite /Χ -take_S_r // length_app Nat.add_1_r. iSteps.
    }
    iIntros "(Hmodel & HΨ & Hnodes)".
    iDestruct (big_sepL2_length with "Hnodes") as %->.
    rewrite firstn_all. iSteps.
  Qed.
End zoo_G.

#[global] Opaque deque_create.
#[global] Opaque deque_is_empty.
#[global] Opaque deque_push_front.
#[global] Opaque deque_push_back.
#[global] Opaque deque_pop_front.
#[global] Opaque deque_pop_back.
#[global] Opaque deque_iter.

#[global] Opaque deque_model.
