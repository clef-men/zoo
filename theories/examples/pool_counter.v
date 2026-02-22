From iris.algebra Require Import
  numbers.

From zoo Require Import
  prelude.
From zoo.iris.bi Require Import
  big_op.
From zoo.iris.base_logic Require Import
  lib.cinv.
From zoo.iris.base_logic Require Import
  lib.auth_frac.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  for_.
From zoo_parabs Require Import
  pool.
From examples Require Export
  pool_counter__code.
From zoo Require Import
  options.

Implicit Types n cnt contrib : nat.
Implicit Types r : location.
Implicit Types γ η : gname.

Class PoolCounterG Σ `{zoo_G : !ZooG Σ} := {
  #[local] pool_counter_G_pool_G :: PoolG Σ ;
  #[local] pool_counter_G_cinv_G :: cinvG Σ ;
  #[local] pool_counter_G_tokens_G :: AuthFracG Σ natUR ;
}.

Definition pool_counter_Σ := #[
  pool_Σ ;
  cinvΣ ;
  auth_frac_Σ natUR
].
#[global] Instance subG_pool_counter_Σ Σ `{zoo_G : !ZooG Σ} :
  subG pool_counter_Σ Σ →
  PoolCounterG Σ.
Proof.
  solve_inG.
Qed.

Section pool_counter_G.
  Context `{pool_counter_G : PoolCounterG Σ}.

  #[local] Definition tokens_auth γ cnt :=
    auth_frac_auth γ cnt.
  #[local] Definition tokens_frag γ n contrib :=
    auth_frac_frag γ (1 / Qp_of_nat n) contrib.

  #[local] Definition inv_inner r γ : iProp Σ :=
    ∃ cnt : nat,
    r ↦ᵣ #cnt ∗
    tokens_auth γ cnt.
  #[local] Instance : CustomIpat "inv_inner" :=
    " ( %cnt &
        >Hr &
        >Htokens_auth
      )
    ".
  #[local] Definition inv r γ η :=
    cinv nroot η (inv_inner r γ).

  #[local] Lemma tokens_alloc n :
    ⊢ |==>
      ∃ γ,
      tokens_auth γ 0 ∗
      [∗ list] _ ∈ seq 0 n, tokens_frag γ n 0.
  Proof.
    iMod auth_frac_alloc as "(%γ & $ & Hfrag)". 1: done.
    iDestruct (auth_frac_frag_divide (replicate n 0) with "Hfrag") as "Hfrags".
    { clear. induction n => //. }
    iEval (simpl_length) in "Hfrags".
    iApply (big_sepL_replicate_1 with "Hfrags").
  Qed.
  #[local] Lemma tokens_incr γ cnt n contrib :
    tokens_auth γ cnt -∗
    tokens_frag γ n contrib ==∗
      tokens_auth γ (cnt + 1) ∗
      tokens_frag γ n (contrib + 1).
  Proof.
    iIntros "Hauth Hfrag".
    iMod (auth_frac_update with "Hauth Hfrag") as "($ & $)" => //.
    { apply nat_local_update. lia. }
  Qed.
  #[local] Lemma tokens_agree γ cnt n :
    0 < n →
    tokens_auth γ cnt -∗
    ([∗ list] _ ∈ seq 0 n, tokens_frag γ n 1) -∗
    ⌜cnt = n⌝.
  Proof.
    iIntros "%Hn Hauth Hfrags".
    iDestruct (big_sepL_replicate_2 (λ _, tokens_frag γ n) with "Hfrags") as "Hfrags".
    iDestruct (auth_frac_frag_gather with "Hfrags") as "Hfrag". 1: simpl_length.
    iEval (simpl_length) in "Hfrag".
    iEval (rewrite Qp.mul_div_r) in "Hfrag".
    iDestruct (auth_frac_auth_frag_agree_L with "Hauth Hfrag") as %->.
    iPureIntro.
    clear. induction n => //.
    rewrite replicate_S /=. auto.
  Qed.

  Lemma pool_counter_main_spec (num_dom n : nat) :
    0 < n →
    {{{
      True
    }}}
      pool_counter_main #num_dom #n
    {{{
      RET #n;
      True
    }}}.
  Proof.
    iIntros "%Hn %Φ _ HΦ".

    wp_rec.
    wp_smart_apply (pool_create_spec with "[//]") as (pool) "(_ & Hpool_model)". 1: lia.

    wp_ref r as "Hr".

    iMod (tokens_alloc n) as "(%γ & Htokens_auth & Htokens_frags)".
    iMod (cinv_alloc _ nroot (inv_inner r γ) with "[Hr Htokens_auth]") as (η) "(#Hinv & Hinv_own)". 1: iFrame.
    iDestruct (cinv_own_divide n with "Hinv_own") as "Hinv_owns". 1: lia.
    iDestruct (big_sepL_sep_2 with "Htokens_frags Hinv_owns") as "H".

    wp_smart_apply (pool_run_spec (λ _,
      [∗ list] _ ∈ seq 0 n,
        pool_consumer pool (
          tokens_frag γ n 1 ∗
          cinv_own η (1 / Qp_of_nat n)
        )
    )%I with "[$Hpool_model H]") as (?) "(Hpool_model & H)".
    { iIntros "%ctx %scope Hctx".
      wp_smart_apply (for_spec_nat'
        (λ _ i,
          pool_context pool ctx scope ∗
          [∗ list] _ ∈ seq 0 i,
            pool_consumer pool (
              tokens_frag γ n 1 ∗
              cinv_own η (1 / Qp_of_nat n)
            )
        )%I
        0
      with "[Hctx H]") as "(Hctx & H)". 1: lia.
      { iFrameStep.
        iEval (rewrite Nat.sub_0_r).
        iApply (big_sepL_seq_impl with "H"). iIntros "!> %k %Hk (Htokens_frag & Hinv_own) % -> (Hctx & H)".
        wp_smart_apply (pool_async_spec
          True
          ( tokens_frag γ n 1 ∗
            cinv_own η (1 / Qp_of_nat n)
          )
        with "[- H $Hctx]") as "(Hctx & _ & Hpool_consumer)".
        { iIntros "{% ctx scope} %ctx %scope Hctx".
          wp_pures.
          wp_bind (FAA _ _).
          iInv "Hinv" as "((:inv_inner) & Hinv_own)".
          wp_faa.
          iMod (tokens_incr with "Htokens_auth Htokens_frag") as "($ & Htokens_frag)".
          iFrameSteps.
        }

        iFrameSteps.
        iApply (big_sepL_seq_shift1 (λ _, _) with "H").
      }

      iEval (rewrite Nat.sub_0_r) in "H".
      iFrame.
    }

    wp_smart_apply (pool_kill_spec with "[$Hpool_model]") as "#Hpool_finished".

    iAssert (
      |={⊤}=>
      [∗ list] _ ∈ seq 0 n,
        tokens_frag γ n 1 ∗
        cinv_own η (1 / Qp_of_nat n)
    )%I with "[H]" as ">H".
    { iApply big_sepL_fupd.
      iApply (big_sepL_seq_impl with "H"). iIntros "!> %k %Hk Hpool_consumer".
      iApply (pool_consumer_finished with "Hpool_consumer Hpool_finished").
    }

    iDestruct (big_sepL_sep with "H") as "(Htokens_frags & Hinv_owns)".
    iDestruct (cinv_own_gather with "Hinv_owns") as "Hinv_own". 1: lia.

    iMod (cinv_cancel with "Hinv Hinv_own") as "(:inv_inner)". 1: done.
    iDestruct (tokens_agree with "Htokens_auth Htokens_frags") as %->. 1: done.
    iSteps.
  Qed.
End pool_counter_G.

From examples Require
  pool_counter__opaque.
