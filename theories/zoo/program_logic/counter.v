From iris.base_logic Require Import
  lib.invariants.

From zoo Require Import
  prelude.
From zoo.iris.bi Require Import
  big_op.
From zoo.language Require Import
  notations.
From zoo.program_logic Require Export
  wp.
From zoo.diaframe Require Import
  diaframe.
From zoo Require Import
  options.

Definition zoo_counter_incr : val :=
  fun: <> =>
    FAA (#zoo_counter).[contents] 1.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Lemma zoo_counter_incr_spec ids v :
    {{{
      [∗ list] id ∈ ids,
        ∃ v,
        zoo_counter_at id v
    }}}
      zoo_counter_incr ()
    {{{ id,
      RET #id;
      zoo_counter_at id v ∗
      ⌜Forall (.≠ id) ids⌝
    }}}.
  Proof.
    iIntros "%Φ Hids HΦ".

    iApply wp_state_interp. iIntros "%ns %nt %σ %κs Hinterp !>".
    iDestruct (state_interp_counter_inv with "Hinterp") as "#Hinv".
    iFrame.

    wp_rec.
    wp_pures.

    iInv "Hinv" as "(%cnt & %vs & Hcounter & Hauth & ><-)".
    wp_faa.

    iAssert ⌜Forall (.≠ length vs) ids⌝%I as "%Hids".
    { rewrite Forall_lookup. iIntros "%i %id %Hlookup".
      iDestruct (big_sepL_lookup with "Hids") as "(%w & Hat)"; first done.
      iDestruct (zoo_counter_at_valid with "Hauth Hat") as %Hid%lookup_lt_Some.
      iSteps.
    }

    iMod (zoo_counter_update v with "Hauth") as "Hauth".
    iDestruct (zoo_counter_at_get with "Hauth") as "#Hat".
    { apply list_lookup_middle. done. }
    iSteps. iPureIntro. simpl_length/=. lia.
  Qed.
End zoo_G.
