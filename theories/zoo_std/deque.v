Require Import zoo.prelude.
Require Import zoo.iris.bi.big_op.
Require Import zoo.base.
Require Import zoo_std.option.
Require Export zoo_std.deque__code.
Require Import zoo_std.deque__types.
Require Import zoo.options.

Implicit Type fn : val.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Definition deque۰model t vs : iProp Σ :=
    ∃ nodes,
    xdeque۰model t nodes ∗
    [∗ list] node; v ∈ nodes; vs, node.[xdeque٠data] ↦ v.

  #[global] Instance deque۰modelｰtimeless t vs :
    Timeless (deque۰model t vs).
  Proof.
    apply _.
  Qed.

  Lemma deque۰modelｰexclusive t vs1 vs2 :
    deque۰model t vs1 -∗
    deque۰model t vs2 -∗
    False.
  Proof.
    iIntros "(%nodes1 & Hmodel1 & _) (%nodes2 & Hmodel2 & _)".
    iApply (xdeque۰modelｰexclusive with "Hmodel1 Hmodel2").
  Qed.

  Lemma deque٠createｰspec :
    {{{
      True
    }}}
      deque٠create ()
    {{{
      t
    , RET t;
      deque۰model t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp۰apply (xdeque٠createｰspec with "[//]").
    iSteps.
  Qed.

  Lemma deque٠is_emptyｰspec t vs :
    {{{
      deque۰model t vs
    }}}
      deque٠is_empty t
    {{{
      RET #(bool_decide (vs = []%list));
      deque۰model t vs
    }}}.
  Proof.
    iIntros "%Φ (%nodes & Hmodel & Hnodes) HΦ".
    wp۰apply (xdeque٠is_emptyｰspec with "Hmodel").
    iDestruct (big_sepL2_length with "Hnodes") as %Hlength.
    rewrite -!(bool_decide_ext _ _ (length_zero_iff_nil _)) Hlength.
    iSteps.
  Qed.

  Lemma deque٠push_frontｰspec t vs v :
    {{{
      deque۰model t vs
    }}}
      deque٠push_front t v
    {{{
      RET ();
      deque۰model t (v :: vs)
    }}}.
  Proof.
    iIntros "%Φ (%nodes & Hmodel & Hnodes) HΦ".
    wp۰rec.
    wp۰block node as "Hnode_prev Hnode_next Hnode_data".
    wp۰apply (xdeque٠push_frontｰspec with "[$Hmodel $Hnode_prev $Hnode_next]").
    iSteps.
  Qed.

  Lemma deque٠push_backｰspec t vs v :
    {{{
      deque۰model t vs
    }}}
      deque٠push_back t v
    {{{
      RET ();
      deque۰model t (vs ++ [v])
    }}}.
  Proof.
    iIntros "%Φ (%nodes & Hmodel & Hnodes) HΦ".
    wp۰rec.
    wp۰block node as "Hnode_prev Hnode_next Hnode_data".
    wp۰apply (xdeque٠push_backｰspec with "[$Hmodel $Hnode_prev $Hnode_next]").
    iSteps. iApply big_sepL2_snoc. iSteps.
  Qed.

  Lemma deque٠pop_frontｰspec t vs :
    {{{
      deque۰model t vs
    }}}
      deque٠pop_front t
    {{{
      RET head vs;
      deque۰model t (tail vs)
    }}}.
  Proof.
    iIntros "%Φ (%nodes & Hmodel & Hnodes) HΦ".
    wp۰rec.
    wp۰apply (xdeque٠pop_frontｰspec with "Hmodel") as "Hmodel".
    destruct nodes as [| node nodes].
    - iDestruct (big_sepL2_nil_inv_l with "Hnodes") as %->.
      iSteps.
    - iDestruct (big_sepL2_cons_inv_l with "Hnodes") as "(%v & %vs' & ->  & Hnode & Hnodes)".
      wp۰load.
      iSteps.
  Qed.

  Lemma deque٠pop_backｰspec t vs :
    {{{
      deque۰model t vs
    }}}
      deque٠pop_back t
    {{{
      o
    , RET o;
      match o with
      | None =>
          ⌜vs = []⌝ ∗
          deque۰model t []
      | Some v =>
          ∃ vs',
          ⌜vs = vs' ++ [v]⌝ ∗
          deque۰model t vs'
      end
    }}}.
  Proof.
    iIntros "%Φ (%nodes & Hmodel & Hnodes) HΦ".
    wp۰rec.
    wp۰apply (xdeque٠pop_backｰspec with "Hmodel") as ([node |]) "Hmodel".
    - iDestruct "Hmodel" as "(%nodes' & -> & Hmodel)".
      iDestruct (big_sepL2ｰsnocｰinvｰl with "Hnodes") as "(%vs' & %v & -> & Hnodes & Hnode)".
      wp۰load. wp۰pures.
      iApply ("HΦ" $! (Some _)).
      iSteps.
    - iDestruct "Hmodel" as "(-> & Hmodel)".
      iDestruct (big_sepL2_nil_inv_l with "Hnodes") as %->.
      wp۰pures.
      iApply ("HΦ" $! None).
      iSteps.
  Qed.

  Lemma deque٠iterｰspec Ψ fn t vs :
    {{{
      ▷ Ψ [] ∗
      deque۰model t vs ∗
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
      deque٠iter fn t
    {{{
      RET ();
      deque۰model t vs ∗
      Ψ vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & (%nodes & Hmodel & Hnodes) & #Hfn) HΦ".
    wp۰rec.
    pose (Χ (nodes_done : list location) := (
      Ψ (take (length nodes_done) vs) ∗
      [∗ list] node; v ∈ nodes; vs, node.[xdeque٠data] ↦ v
    )%I).
    wp۰apply+ (xdeque٠iterｰspec Χ with "[$HΨ $Hnodes $Hmodel]").
    { iIntros "!> %nodes_done %node %nodes_todo -> (HΨ & Hnodes)".
      iDestruct (big_sepL2ｰlookupｰaccｰl (length nodes_done) with "Hnodes") as "(%v & %Hvs_lookup & Hnode & Hnodes)".
      { rewrite lookup_app_r // Nat.sub_diag //. }
      wp۰load.
      wp۰apply (wpｰwand with "(Hfn [%] HΨ)").
      { erewrite take_drop_middle => //. }
      rewrite /Χ -take_S_r // length_app Nat.add_1_r. iSteps.
    }
    iIntros "(Hmodel & HΨ & Hnodes)".
    iDestruct (big_sepL2_length with "Hnodes") as %->.
    rewrite firstn_all. iSteps.
  Qed.
End zoo۰G.

Require zoo_std.deque__opaque.

#[global] Opaque deque۰model.
