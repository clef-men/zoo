Require Import iris.base_logic.lib.invariants.

Require Import zoo.prelude.
Require Import zoo.iris.bi.big_op.
Require Import zoo.base.
Require Import zoo.options.

Definition zoo_counter٠incr : val :=
  𝗳𝘂𝗻 ⎽ ->
    FAA (#zoo_counter).[contents] 1.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Lemma zoo_counter٠incrｰspec ids v :
    {{{
      [∗ list] id ∈ ids,
        ∃ v,
        zoo_counter۰at id v
    }}}
      zoo_counter٠incr ()
    {{{
      id
    , RET #id;
      zoo_counter۰at id v ∗
      ⌜Forall (.≠ id) ids⌝
    }}}.
  Proof.
    iIntros "%Φ Hids HΦ".

    iApply wpｰstate_interp. iIntros "%ns %nt %σ %κs Hinterp !>".
    iDestruct (state_interpｰzoo_counter۰inv with "Hinterp") as "#Hinv".
    iFrame.

    wp۰rec.
    wp۰pures.

    iInv "Hinv" as "(%cnt & %vs & Hcounter & Hauth & ><-)".
    wp۰faa.

    iAssert ⌜Forall (.≠ length vs) ids⌝%I as "%Hids".
    { rewrite Forall_lookup. iIntros "%i %id %Hlookup".
      iDestruct (big_sepL_lookup with "Hids") as "(%w & Hat)"; first done.
      iDestruct (zoo_counter۰atｰvalid with "Hauth Hat") as %Hid%lookup_lt_Some.
      iSteps.
    }

    iMod (zoo_counterｰupdate v with "Hauth") as "Hauth".
    iDestruct (zoo_counter۰atｰget with "Hauth") as "#Hat".
    { apply list_lookup_middle. done. }
    iSteps. iPureIntro. simp_length/=. lia.
  Qed.
End zoo۰G.
