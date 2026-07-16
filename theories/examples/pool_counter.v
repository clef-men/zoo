Require Import iris.algebra.numbers.

Require Import zoo.prelude.
Require Import zoo.iris.bi.big_op.
Require Import zoo.iris.base_logic.lib.cinv.
Require Import zoo.iris.base_logic.lib.auth_frac.
Require Import zoo.base.
Require Import zoo_std.for_.
Require Import zoo_parabs.pool.
Require Export examples.pool_counter__code.
Require Import zoo.options.

Implicit Types n cnt contrib : nat.
Implicit Types r : location.
Implicit Types γ η : gname.

Class PoolCounterG Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] pool_counter۰G۰pool۰G :: PoolG Σ
  ; #[local] pool_counter۰G۰cinv۰G :: cinvG Σ
  ; #[local] pool_counter۰G۰tokens۰G :: AuthFracG Σ natUR
  }.

Definition pool_counter۰Σ :=
  #[pool۰Σ
  ; cinvΣ
  ; auth_frac۰Σ natUR
  ].
#[global] Instance subG𑁒pool_counter۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG pool_counter۰Σ Σ →
  PoolCounterG Σ.
Proof.
  solve_inG.
Qed.

Section pool_counter۰G.
  Context `{pool_counter۰G : PoolCounterG Σ}.

  #[local] Definition tokens۰auth γ cnt :=
    auth_frac۰auth γ cnt.
  #[local] Definition tokens۰frag γ n contrib :=
    auth_frac۰frag γ (1 / Qp۰of_nat n) contrib.

  #[local] Definition inv۰inner r γ : iProp Σ :=
    ∃ cnt : nat,
    r ↦ᵣ #cnt ∗
    tokens۰auth γ cnt.
  #[local] Instance : CustomIpat "inv۰inner" :=
    " ( %cnt
      & >Hr
      & >Htokens_auth
      )
    ".
  #[local] Definition inv r γ η :=
    cinv nroot η (inv۰inner r γ).

  #[local] Lemma tokens𑁒alloc n :
    ⊢ |==>
      ∃ γ,
      tokens۰auth γ 0 ∗
      [∗ list] _ ∈ seq 0 n, tokens۰frag γ n 0.
  Proof.
    iMod auth_frac𑁒alloc as "(%γ & $ & Hfrag)". 1: done.
    iDestruct (auth_frac۰frag𑁒divide (replicate n 0) with "Hfrag") as "Hfrags".
    { clear. induction n => //. }
    iEval (simpl_length) in "Hfrags".
    iApply (big_sepL𑁒replicate₁ with "Hfrags").
  Qed.
  #[local] Lemma tokens𑁒incr γ cnt n contrib :
    tokens۰auth γ cnt -∗
    tokens۰frag γ n contrib ==∗
      tokens۰auth γ (cnt + 1) ∗
      tokens۰frag γ n (contrib + 1).
  Proof.
    iIntros "Hauth Hfrag".
    iMod (auth_frac𑁒update with "Hauth Hfrag") as "($ & $)" => //.
    { apply nat_local_update. lia. }
  Qed.
  #[local] Lemma tokens𑁒agree γ cnt n :
    0 < n →
    tokens۰auth γ cnt -∗
    ([∗ list] _ ∈ seq 0 n, tokens۰frag γ n 1) -∗
    ⌜cnt = n⌝.
  Proof.
    iIntros "%Hn Hauth Hfrags".
    iDestruct (big_sepL𑁒replicate₂ (λ _, tokens۰frag γ n) with "Hfrags") as "Hfrags".
    iDestruct (auth_frac۰frag𑁒gather with "Hfrags") as "Hfrag". 1: simpl_length.
    iEval (simpl_length) in "Hfrag".
    iEval (rewrite Qp.mul_div_r) in "Hfrag".
    iDestruct (auth_frac𑁒auth𑁒frag𑁒agree𑁒L with "Hauth Hfrag") as %->.
    iPureIntro.
    clear. induction n => //.
    rewrite replicate_S /=. auto.
  Qed.

  Lemma pool_counter٠main𑁒spec (num_dom n : nat) :
    0 < n →
    {{{
      True
    }}}
      pool_counter٠main #num_dom #n
    {{{
      RET #n;
      True
    }}}.
  Proof.
    iIntros "%Hn %Φ _ HΦ".

    wp۰rec.
    wp۰ref r as "Hr".

    iMod (tokens𑁒alloc n) as "(%γ & Htokens_auth & Htokens_frags)".
    iMod (cinv_alloc _ nroot (inv۰inner r γ) with "[Hr Htokens_auth]") as (η) "(#Hinv & Hinv_own)". 1: iFrame.
    iDestruct (cinv_own𑁒divide n with "Hinv_own") as "Hinv_owns". 1: lia.
    iDestruct (big_sepL_sep_2 with "Htokens_frags Hinv_owns") as "H".

    wp۰apply+ (pool٠run𑁒spec (λ pool _,
      [∗ list] _ ∈ seq 0 n,
        pool۰consumer pool (
          tokens۰frag γ n 1 ∗
          cinv_own η (1 / Qp۰of_nat n)
        )
    )%I with "[H]") as (pool ?) "(#Hpool_finished & H)". 1: lia.
    { iIntros "%pool %ctx %scope _ Hctx".
      wp۰apply+ (for𑁒spec𑁒nat'
        (λ _ i,
          pool۰context pool ctx scope ∗
          [∗ list] _ ∈ seq 0 i,
            pool۰consumer pool (
              tokens۰frag γ n 1 ∗
              cinv_own η (1 / Qp۰of_nat n)
            )
        )%I
        0
      with "[Hctx H]") as "(Hctx & H)". 1: lia.
      { iFrameStep.
        iEval (rewrite Nat.sub_0_r).
        iApply (big_sepL𑁒seq𑁒impl with "H"). iIntros "!> %k %Hk (Htokens_frag & Hinv_own) % -> (Hctx & H)".
        wp۰apply+ (pool٠async𑁒spec
          ( tokens۰frag γ n 1 ∗
            cinv_own η (1 / Qp۰of_nat n)
          )
          True
        with "[- H $Hctx]") as "(Hctx & Hpool_consumer & _)".
        { iIntros "{% ctx scope} %ctx %scope Hctx".
          wp۰pures.
          wp۰bind (FAA _ _).
          iInv "Hinv" as "((:inv۰inner) & Hinv_own)".
          wp۰faa.
          iMod (tokens𑁒incr with "Htokens_auth Htokens_frag") as "($ & Htokens_frag)".
          iFrameSteps.
        }

        iFrameSteps.
        iApply (big_sepL𑁒seq𑁒shift𑁒1 (λ _, _) with "H").
      }

      iEval (rewrite Nat.sub_0_r) in "H".
      iFrame.
    }

    iAssert (
      |={⊤}=>
      [∗ list] _ ∈ seq 0 n,
        tokens۰frag γ n 1 ∗
        cinv_own η (1 / Qp۰of_nat n)
    )%I with "[H]" as ">H".
    { iApply big_sepL_fupd.
      iApply (big_sepL𑁒seq𑁒impl with "H"). iIntros "!> %k %Hk Hpool_consumer".
      iApply (pool۰consumer𑁒finished with "Hpool_consumer Hpool_finished").
    }

    iDestruct (big_sepL_sep with "H") as "(Htokens_frags & Hinv_owns)".
    iDestruct (cinv_own𑁒gather with "Hinv_owns") as "Hinv_own". 1: lia.

    iMod (cinv_cancel with "Hinv Hinv_own") as "(:inv۰inner)". 1: done.
    iDestruct (tokens𑁒agree with "Htokens_auth Htokens_frags") as %->. 1: done.
    iSteps.
  Qed.
End pool_counter۰G.

Require examples.pool_counter__opaque.
