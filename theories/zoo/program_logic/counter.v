From iris.base_logic Require Import
  lib.invariants.

From zoo Require Import
  prelude.
From zoo.iris.bi Require Import
  big_op.
From zoo.iris.base_logic Require Import
  lib.mono_list.
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
    FAA (#zoo_counter).[contents] #1.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition zoo_counter_at :=
    mono_list_at (mono_list_G := zoo_G_counter_G) zoo_counter_name.

  #[global] Instance zoo_counter_at_timeless id v :
    Timeless (zoo_counter_at id v).
  Proof.
    apply _.
  Qed.
  #[global] Instance zoo_counter_at_persistent id v :
    Persistent (zoo_counter_at id v).
  Proof.
    apply _.
  Qed.

  Lemma zoo_counter_at_agree id v1 v2 :
    zoo_counter_at id v1 -∗
    zoo_counter_at id v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    apply mono_list_at_agree.
  Qed.

  Lemma zoo_counter_incr_spec ids v :
    {{{
      [∗ set] id ∈ ids,
        ∃ v,
        zoo_counter_at id v
    }}}
      zoo_counter_incr ()
    {{{ id,
      RET #id;
      zoo_counter_at id v ∗
      ⌜set_Forall (.≠ id) ids⌝
    }}}.
  Proof.
    iIntros "%Φ Hids HΦ".

    iApply wp_state_interp. iIntros "%nt %σ %κs Hinterp !>".
    iDestruct (state_interp_counter_inv with "Hinterp") as "#Hinv".
    iFrame.

    wp_rec.
    wp_pures.

    iInv "Hinv" as "(%cnt & %vs & Hcounter & Hauth & ><-)".
    wp_faa.
    iAssert ⌜set_Forall (.≠ length vs) ids⌝%I as "%Hids".
    { iApply big_sepS_pure.
      iDestruct (big_sepS_impl_thread with "Hids Hauth []") as "($ & _)". iIntros "!> %id _ (%w & Hat) Hauth".
      iDestruct (mono_list_at_valid with "Hauth Hat") as %Hid%lookup_lt_Some.
      iSteps.
    }
    iMod (mono_list_update_snoc v with "Hauth") as "Hauth".
    iDestruct (mono_list_at_get with "Hauth") as "#Hat".
    { apply list_lookup_middle. done. }
    iSteps. iPureIntro. rewrite length_app /=. lia.
  Qed.
End zoo_G.

#[global] Opaque zoo_counter_at.
