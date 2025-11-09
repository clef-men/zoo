From zoo Require Import
  prelude.
From zoo.iris.bi Require Import
  big_op.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  for_
  option.
From zoo_parabs Require Export
  base
  algo__code.
From zoo_parabs Require Import
  future
  pool.
From zoo Require Import
  options.

Implicit Types v pool ctx task : val.

Class AlgoG Σ `{pool_G : PoolG Σ} := {
  #[local] algo_G_future_G :: FutureG Σ ;
}.

Definition algo_Σ := #[
  future_Σ
].
#[global] Instance subG_algo_Σ Σ `{pool_G : PoolG Σ} :
  subG algo_Σ Σ →
  AlgoG Σ.
Proof.
  solve_inG.
Qed.

Section algo_G.
  Context `{algo_G : AlgoG Σ}.

  #[local] Lemma algo_adjust_chunk_spec pool sz ctx scope (beg end_ : Z) chunk :
    {{{
      pool_inv pool sz ∗
      pool_context pool ctx scope ∗
      itype_option itype_int chunk
    }}}
      algo_adjust_chunk ctx #beg #end_ chunk
    {{{ (chunk : Z),
      RET #chunk;
      pool_context pool ctx scope
    }}}.
  Proof.
    iIntros "%Φ (#Hpool_inv & Hctx & [-> | (% & -> & (%chunk & ->))]) HΦ".

    all: wp_rec.
    all: wp_pures.

    - wp_apply (pool_size_spec with "[$]").
      iSteps.

    - iSteps.
  Qed.

  #[local] Lemma algo_for_0_spec Ψ Χ pool ctx scope beg0 beg end_ end0 (chunk : Z) task :
    (beg0 ≤ beg ≤ end_ ≤ end0)%Z →
    {{{
      pool_context pool ctx scope ∗
      Χ beg ₊(end_ - beg) ∗
      □ (
        ∀ i (n1 n2 : nat),
        ⌜beg0 ≤ i⌝%Z -∗
        ⌜i + n1 + n2 ≤ end0⌝%Z -∗
        Χ i (n1 + n2) -∗
          Χ i n1 ∗
          Χ (i + n1)%Z n2
      ) ∗
      □ (
        ∀ ctx scope i (n : nat),
        pool_context pool ctx scope -∗
        ⌜beg0 ≤ i⌝%Z -∗
        ⌜i + n ≤ end0⌝%Z -∗
        Χ i n -∗
        WP task ctx #i #n {{ res,
          ⌜res = ()%V⌝ ∗
          pool_context pool ctx scope ∗
          [∗ list] j ∈ seqZ i n,
            Ψ j
        }}
      )
    }}}
      algo_for__0 ctx #beg #end_ #chunk task
    {{{
      RET ();
      pool_context pool ctx scope ∗
      [∗ list] i ∈ seqZ beg (end_ - beg),
        Ψ i
    }}}.
  Proof.
    iIntros "%Hrange %Φ (Hctx & HΧ & #HΧ_split & #HΧ_elim) HΦ".

    iLöb as "HLöb" forall (ctx scope beg end_ Φ Hrange).

    wp_rec. wp_pures.
    case_bool_decide; wp_pures.

    - iEval (replace (end_ - beg)%Z with ⁺₊(end_ - beg) by lia) in "HΦ" |- *.
      wp_apply (wp_wand with "(HΧ_elim Hctx [%] [%] HΧ)"); [lia.. |].
      iSteps.

    - pose mid : Z := beg + (end_ - beg) `quot` 2.
      iEval (replace ₊(end_ - beg) with (₊(mid - beg) + ₊(end_ - mid)) by naive_solver lia) in "HΧ".
      iDestruct ("HΧ_split" with "[%] [%] HΧ") as "(HΧ_1 & HΧ_2)"; [naive_solver lia.. |].
      iEval (replace (beg + ₊(mid - beg))%Z with mid by naive_solver lia) in "HΧ_2".

      wp_apply (future_async_spec
        ( λ res,
          ⌜res = ()%V⌝ ∗
          [∗ list] i ∈ seqZ beg (mid - beg),
            Ψ i
        )%I
        ( λ _,
          True
        )%I
      with "[$Hctx HΧ_1]") as (fut1) "(Hctx & #Hfut1_inv & Hfut1_consumer)".
      { clear ctx scope. iIntros "%ctx %scope Hctx".
        wp_smart_apply ("HLöb" with "[%] Hctx HΧ_1"); first naive_solver lia.
        { iSteps. }
      }

      wp_smart_apply ("HLöb" with "[%] Hctx HΧ_2") as "(Hctx & HΨ_2)"; first naive_solver lia.

      iApply wp_fupd.
      wp_smart_apply (future_wait_spec with "[$]") as (res) "(H£ & Hctx & Hfut1_result)".

      iMod (future_inv_result_consumer' with "H£ Hfut1_inv Hfut1_result Hfut1_consumer") as "((-> & HΨ_1) & _)".
      iDestruct (big_sepL_seqZ_app_2 with "HΨ_1 HΨ_2") as "HΨ"; [naive_solver lia.. |].
      iEval (replace (mid - beg + (end_ - mid))%Z with (end_ - beg)%Z by lia) in "HΨ".
      iSteps.
  Qed.
  Lemma algo_for_spec Ψ Χ pool sz ctx scope beg end_ chunk task :
    (beg ≤ end_)%Z →
    {{{
      pool_inv pool sz ∗
      pool_context pool ctx scope ∗
      itype_option itype_int chunk ∗
      Χ beg ₊(end_ - beg) ∗
      □ (
        ∀ i (n1 n2 : nat),
        ⌜beg ≤ i⌝%Z -∗
        ⌜i + n1 + n2 ≤ end_⌝%Z -∗
        Χ i (n1 + n2) -∗
          Χ i n1 ∗
          Χ (i + n1)%Z n2
      ) ∗
      □ (
        ∀ ctx scope i (n : nat),
        pool_context pool ctx scope -∗
        ⌜beg ≤ i⌝%Z -∗
        ⌜i + n ≤ end_⌝%Z -∗
        Χ i n -∗
        WP task ctx #i #n {{ res,
          ⌜res = ()%V⌝ ∗
          pool_context pool ctx scope ∗
          [∗ list] j ∈ seqZ i n,
            Ψ j
        }}
      )
    }}}
      algo_for_ ctx #beg #end_ chunk task
    {{{
      RET ();
      pool_context pool ctx scope ∗
      [∗ list] i ∈ seqZ beg (end_ - beg),
        Ψ i
    }}}.
  Proof.
    iIntros "% %Φ (Hpool_inv & Hctx & Hchunk & HΧ & #HΧ_split & #HΧ_elim) HΦ".

    wp_rec.
    wp_smart_apply (algo_adjust_chunk_spec with "[$]"). clear chunk. iIntros "%chunk Hctx".
    wp_smart_apply (algo_for_0_spec Ψ Χ with "[$]"); first done.
    iSteps.
  Qed.
  Lemma algo_for_spec_nat Ψ Χ pool sz ctx scope beg end_ chunk task :
    (0 ≤ beg ≤ end_)%Z →
    {{{
      pool_inv pool sz ∗
      pool_context pool ctx scope ∗
      itype_option itype_int chunk ∗
      Χ ₊beg ₊(end_ - beg) ∗
      □ (
        ∀ i n1 n2 : nat,
        ⌜beg ≤ i⌝%Z -∗
        ⌜i + n1 + n2 ≤ end_⌝%Z -∗
        Χ i (n1 + n2) -∗
          Χ i n1 ∗
          Χ (i + n1) n2
      ) ∗
      □ (
        ∀ ctx scope (i n : nat),
        pool_context pool ctx scope -∗
        ⌜beg ≤ i⌝%Z -∗
        ⌜i + n ≤ end_⌝%Z -∗
        Χ i n -∗
        WP task ctx #i #n {{ res,
          ⌜res = ()%V⌝ ∗
          pool_context pool ctx scope ∗
          [∗ list] j ∈ seq i n,
            Ψ j
        }}
      )
    }}}
      algo_for_ ctx #beg #end_ chunk task
    {{{
      RET ();
      pool_context pool ctx scope ∗
      [∗ list] i ∈ seq ₊beg ₊(end_ - beg),
        Ψ i
    }}}.
  Proof.
    iIntros "% %Φ (Hpool_inv & Hctx & Hchunk & HΧ & #HΧ_split & #HΧ_elim) HΦ".

    wp_apply (algo_for_spec
      (λ i, Ψ ₊i)
      (λ i n, Χ ₊i n)
    with "[$Hpool_inv $Hctx $Hchunk $HΧ]"); first lia.
    { iSplit.
      - iIntros "!> %i %n1 %n2 % % HΧ".
        iEval (replace ₊(i + n1) with (₊i + n1) by lia).
        iSteps.
      - clear ctx scope. iIntros "!> %ctx %scope %i %n Hctx % % HΧ".
        Z_to_nat i.
        iEval (rewrite Nat2Z.id) in "HΧ".
        wp_apply (wp_wand with "(HΧ_elim Hctx [%] [%] HΧ)"); [done.. |].
        iSteps as "HΨ".
        iApply (big_sepL_seq_to_seqZ with "HΨ").
    }

    iSteps as "HΨ".
    iApply (big_sepL_seqZ_to_seq' with "HΨ"); lia.
  Qed.
  Lemma algo_for_spec' Ψ pool sz ctx scope beg end_ chunk task :
    (beg ≤ end_)%Z →
    {{{
      pool_inv pool sz ∗
      pool_context pool ctx scope ∗
      itype_option itype_int chunk ∗
      □ (
        ∀ ctx scope i (n : nat),
        pool_context pool ctx scope -∗
        ⌜beg ≤ i⌝%Z -∗
        ⌜i + n ≤ end_⌝%Z -∗
        WP task ctx #i #n {{ res,
          ⌜res = ()%V⌝ ∗
          pool_context pool ctx scope ∗
          [∗ list] j ∈ seqZ i n,
            Ψ j
        }}
      )
    }}}
      algo_for_ ctx #beg #end_ chunk task
    {{{
      RET ();
      pool_context pool ctx scope ∗
      [∗ list] i ∈ seqZ beg (end_ - beg),
        Ψ i
    }}}.
  Proof.
    iIntros "% %Φ (Hpool_inv & Hctx & Hchunk & #Htask) HΦ".

    wp_apply (algo_for_spec
      Ψ
      (λ _ _, True)%I
    with "[$Hpool_inv $Hchunk $Hctx] HΦ"); first done.
    { iSteps. }
  Qed.
  Lemma algo_for_spec_nat' Ψ pool sz ctx scope beg end_ chunk task :
    (0 ≤ beg ≤ end_)%Z →
    {{{
      pool_inv pool sz ∗
      pool_context pool ctx scope ∗
      itype_option itype_int chunk ∗
      □ (
        ∀ ctx scope (i n : nat),
        pool_context pool ctx scope -∗
        ⌜beg ≤ i⌝%Z -∗
        ⌜i + n ≤ end_⌝%Z -∗
        WP task ctx #i #n {{ res,
          ⌜res = ()%V⌝ ∗
          pool_context pool ctx scope ∗
          [∗ list] j ∈ seq i n,
            Ψ j
        }}
      )
    }}}
      algo_for_ ctx #beg #end_ chunk task
    {{{
      RET ();
      pool_context pool ctx scope ∗
      [∗ list] i ∈ seq ₊beg ₊(end_ - beg),
        Ψ i
    }}}.
  Proof.
    iIntros "% %Φ (Hpool_inv & Hctx & Hchunk & #Htask) HΦ".

    wp_apply (algo_for_spec'
      (λ i, Ψ ₊i)
    with "[$Hpool_inv $Hchunk $Hctx]"); first lia.
    { clear ctx scope. iIntros "!> %ctx %scope %i %n Hctx % %".
      Z_to_nat i.
      wp_apply (wp_wand with "(Htask Hctx [%] [%])"); [done.. |].
      iSteps as "HΨ".
      iApply (big_sepL_seq_to_seqZ with "HΨ").
    }

    iSteps as "HΨ".
    iApply (big_sepL_seqZ_to_seq' with "HΨ"); lia.
  Qed.

  Lemma algo_for_each_spec' Ψ pool sz ctx scope beg end_ chunk task :
    (beg ≤ end_)%Z →
    {{{
      pool_inv pool sz ∗
      pool_context pool ctx scope ∗
      itype_option itype_int chunk ∗
      [∗ list] i ∈ seqZ beg (end_ - beg),
        ∀ ctx scope,
        pool_context pool ctx scope -∗
        ⌜beg ≤ i < end_⌝%Z -∗
        WP task ctx #i {{ res,
          ⌜res = ()%V⌝ ∗
          pool_context pool ctx scope ∗
          Ψ i
        }}
    }}}
      algo_for_each ctx #beg #end_ chunk task
    {{{
      RET ();
      pool_context pool ctx scope ∗
      [∗ list] i ∈ seqZ beg (end_ - beg),
        Ψ i
    }}}.
  Proof.
    iIntros "% %Φ (Hpool_inv & Hctx & Hchunk & Htask) HΦ".

    wp_rec.
    wp_smart_apply (algo_for_spec
      Ψ
      ( λ i n,
        [∗ list] i ∈ seqZ i n,
          ∀ ctx scope,
          pool_context pool ctx scope -∗
          ⌜beg ≤ i < end_⌝%Z -∗
          WP task ctx #i {{ res,
            ⌜res = ()%V⌝ ∗
            pool_context pool ctx scope ∗
            Ψ i
          }}
      )%I
    with "[$Hpool_inv $Hchunk $Hctx Htask] HΦ"); first done.
    { repeat iSplit.
      - rewrite Z2Nat.id //; first lia.
      - iIntros "!> %i %n1 %n2 % % Htask".
        iEval (rewrite Nat2Z.inj_add) in "Htask".
        iApply (big_sepL_seqZ_app with "Htask"); lia.
      - clear ctx scope. iIntros "!> %ctx %scope %i %n Hctx % % Htask".
        wp_smart_apply (for_spec'
          ( λ j δ,
            pool_context pool ctx scope ∗
            ( [∗ list] k ∈ seqZ j (i + n - j),
              ∀ ctx scope,
              pool_context pool ctx scope -∗
              ⌜beg ≤ k < end_⌝%Z -∗
              WP task ctx #k {{ res,
                ⌜res = ()%V⌝ ∗
                pool_context pool ctx scope ∗
                Ψ k
              }}
            ) ∗
            ( [∗ list] k ∈ seqZ i δ,
              Ψ k
            )
          )%I
        with "[$Hctx Htask]") as "(Hctx & _ & HΨ)"; first lia.
        { repeat iSplitL "Htask".
          - rewrite Z.add_simpl_l //.
          - iSteps.
          - iApply big_sepL_seq_intro. iIntros "!> %δ % % -> (Hctx & Htask & HΨ)".
            iEval (replace (i + n - (i + δ))%Z with (n - δ)%Z by lia) in "Htask".
            iDestruct (big_sepL_seqZ_cons with "Htask") as "(H & Htask)"; first lia.
            wp_smart_apply (wp_wand with "(H Hctx [%])") as (res) "(-> & Hctx & H)"; first lia.
            iDestruct (big_sepL_seqZ_snoc_2 with "HΨ H") as "HΨ"; first lia.
            iEval (replace (i + δ + 1)%Z with (Z.succ (i + δ)%Z) by lia).
            iEval (replace (i + n - Z.succ (i + δ))%Z with (Z.pred (n - δ)) by lia).
            iEval (replace ⁺(S δ) with (Z.succ δ) by lia).
            iFrameSteps.
        }
        rewrite Z.add_simpl_l Nat2Z.id. iSteps.
    }
  Qed.
  Lemma algo_for_each_spec_nat' Ψ pool sz ctx scope beg end_ chunk task :
    (0 ≤ beg ≤ end_)%Z →
    {{{
      pool_inv pool sz ∗
      pool_context pool ctx scope ∗
      itype_option itype_int chunk ∗
      [∗ list] (i : nat) ∈ seq ₊beg ₊(end_ - beg),
        ∀ ctx scope,
        pool_context pool ctx scope -∗
        ⌜beg ≤ i < end_⌝%Z -∗
        WP task ctx #i {{ res,
          ⌜res = ()%V⌝ ∗
          pool_context pool ctx scope ∗
          Ψ i
        }}
    }}}
      algo_for_each ctx #beg #end_ chunk task
    {{{
      RET ();
      pool_context pool ctx scope ∗
      [∗ list] i ∈ seq ₊beg ₊(end_ - beg),
        Ψ i
    }}}.
  Proof.
    iIntros "% %Φ (Hpool_inv & Hctx & Hchunk & Htask) HΦ".

    wp_apply (algo_for_each_spec'
      (λ i, Ψ ₊i)
    with "[$Hpool_inv $Hchunk $Hctx Htask]"); first lia.
    { iDestruct (big_sepL_seq_to_seqZ with "Htask") as "Htask".
      iEval (rewrite !Z2Nat.id; try lia) in "Htask".
      iApply (big_sepL_seqZ_impl with "Htask"). iIntros "!> %k % Htask".
      iEval (rewrite Z2Nat.id; try lia) in "Htask".
      iSteps.
    }

    iSteps as "HΨ".
    iApply (big_sepL_seqZ_to_seq' with "HΨ"); lia.
  Qed.
  Lemma algo_for_each_spec Ψ pool sz ctx scope beg end_ chunk task :
    (beg ≤ end_)%Z →
    {{{
      pool_inv pool sz ∗
      pool_context pool ctx scope ∗
      itype_option itype_int chunk ∗
      □ (
        ∀ ctx scope i,
        pool_context pool ctx scope -∗
        ⌜beg ≤ i < end_⌝%Z -∗
        WP task ctx #i {{ res,
          ⌜res = ()%V⌝ ∗
          pool_context pool ctx scope ∗
          Ψ i
        }}
      )
    }}}
      algo_for_each ctx #beg #end_ chunk task
    {{{
      RET ();
      pool_context pool ctx scope ∗
      [∗ list] i ∈ seqZ beg (end_ - beg),
        Ψ i
    }}}.
  Proof.
    iIntros "% %Φ (Hpool_inv & Hctx & Hchunk & #Htask) HΦ".

    wp_apply (algo_for_each_spec' Ψ with "[$Hpool_inv $Hchunk $Hctx] HΦ"); first done.
    { iApply big_sepL_seqZ_intro.
      iSteps.
    }
  Qed.
  Lemma algo_for_each_spec_nat Ψ pool sz ctx scope beg end_ chunk task :
    (0 ≤ beg ≤ end_)%Z →
    {{{
      pool_inv pool sz ∗
      pool_context pool ctx scope ∗
      itype_option itype_int chunk ∗
      □ (
        ∀ ctx scope (i : nat),
        pool_context pool ctx scope -∗
        ⌜beg ≤ i < end_⌝%Z -∗
        WP task ctx #i {{ res,
          ⌜res = ()%V⌝ ∗
          pool_context pool ctx scope ∗
          Ψ i
        }}
      )
    }}}
      algo_for_each ctx #beg #end_ chunk task
    {{{
      RET ();
      pool_context pool ctx scope ∗
      [∗ list] i ∈ seq ₊beg ₊(end_ - beg),
        Ψ i
    }}}.
  Proof.
    iIntros "% %Φ (Hpool_inv & Hctx & Hchunk & #Htask) HΦ".

    wp_apply (algo_for_each_spec_nat' Ψ with "[$Hpool_inv $Hchunk $Hctx] HΦ"); first done.
    { iApply big_sepL_seq_intro.
      iSteps.
    }
  Qed.
End algo_G.

From zoo_parabs Require
  algo__opaque.
