From zoo Require Import
  prelude.
From zoo.common Require Import
  countable.
From zoo.iris.bi Require Import
  big_op.
From zoo.iris.base_logic Require Import
  lib.ghost_var.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  for_
  mvar
  option.
From zoo_parabs Require Export
  base
  algo__code.
From zoo_parabs Require Import
  future
  pool.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types v pool ctx task pred found : val.
Implicit Types o : option val.

Class AlgoG Σ `{pool_G : PoolG Σ} := {
  #[local] algo_G_future_G :: FutureG Σ ;
  #[local] algo_G_mvar_G :: MvarG Σ ;
  #[local] algo_G_find_G :: GhostVarG Σ unitO ;
}.

Definition algo_Σ := #[
  future_Σ ;
  mvar_Σ ;
  ghost_var_Σ unitO
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

  #[local] Lemma algo_for_0_spec (Ψ : Z → iProp Σ) (Χ : Z → nat → iProp Σ) pool ctx scope beg0 beg end_ end0 (chunk : Z) task :
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
      with "[$Hctx HΧ_1]") as (fut) "(Hctx & #Hfut_inv & Hfut_consumer)".
      { clear ctx scope. iIntros "%ctx %scope Hctx".
        wp_smart_apply ("HLöb" with "[%] Hctx HΧ_1"); first naive_solver lia.
        { iSteps. }
      }

      wp_smart_apply ("HLöb" with "[%] Hctx HΧ_2") as "(Hctx & HΨ_2)"; first naive_solver lia.

      iApply wp_fupd.
      wp_smart_apply (future_wait_spec with "[$]") as (res) "(H£ & Hctx & Hfut_result)".

      iMod (future_inv_result_consumer' with "H£ Hfut_inv Hfut_result Hfut_consumer") as "((-> & HΨ_1) & _)".
      iDestruct (big_sepL_seqZ_app_2 with "HΨ_1 HΨ_2") as "HΨ"; [naive_solver lia.. |].
      iEval (replace (mid - beg + (end_ - mid))%Z with (end_ - beg)%Z by lia) in "HΨ".
      iSteps.
  Qed.
  Lemma algo_for_spec (Ψ : Z → iProp Σ) (Χ : Z → nat → iProp Σ) pool sz ctx scope beg end_ chunk task :
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
  Lemma algo_for_spec_nat (Ψ : nat → iProp Σ) (Χ : Z → nat → iProp Σ) pool sz ctx scope beg end_ chunk task :
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
  Lemma algo_for_spec' (Ψ : Z → iProp Σ) pool sz ctx scope beg end_ chunk task :
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
  Lemma algo_for_spec_nat' (Ψ : nat → iProp Σ) pool sz ctx scope beg end_ chunk task :
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

  Lemma algo_for_each_spec' (Ψ : Z → iProp Σ) pool sz ctx scope beg end_ chunk task :
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
  Lemma algo_for_each_spec_nat' (Ψ : nat → iProp Σ) pool sz ctx scope beg end_ chunk task :
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
    { iDestruct (big_sepL_seq_to_seqZ' with "Htask") as "Htask"; [lia.. |].
      iApply (big_sepL_seqZ_impl with "Htask"). iIntros "!> %k % Htask".
      iEval (rewrite Z2Nat.id; try lia) in "Htask".
      iSteps.
    }

    iSteps as "HΨ".
    iApply (big_sepL_seqZ_to_seq' with "HΨ"); lia.
  Qed.
  Lemma algo_for_each_spec (Ψ : Z → iProp Σ) pool sz ctx scope beg end_ chunk task :
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
  Lemma algo_for_each_spec_nat (Ψ : nat → iProp Σ) pool sz ctx scope beg end_ chunk task :
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

  #[local] Definition find_token γ q :=
    ghost_var γ (DfracOwn q) ().
  #[local] Definition find_inv γ (Ψ : Z → iProp Σ) beg end_ v : iProp Σ :=
    ∃ (i : Z) q,
    ⌜v = #i⌝ ∗
    ⌜beg ≤ i < end_⌝%Z ∗
    find_token γ q ∗
    Ψ i.
  #[local] Instance : CustomIpatFormat "find_inv" :=
    " ( %i &
        %q &
        -> &
        % &
        Htoken{_{}} &
        HΨ
      )
    ".
  #[local] Lemma algo_find_seq_spec pool ctx scope beg0 beg end_ end0 pred Ψ (Χ : Z → iProp Σ) found γ q :
    (beg0 ≤ beg ≤ end_ ≤ end0)%Z →
    {{{
      pool_context pool ctx scope ∗
      mvar_inv found (find_inv γ Ψ beg0 end0) ∗
      find_token γ q ∗
      [∗ list] (i : Z) ∈ seqZ beg (end_ - beg),
        ∀ ctx scope,
        pool_context pool ctx scope -∗
        WP pred ctx #i {{ res,
          ∃ b,
          ⌜res = #b⌝ ∗
          pool_context pool ctx scope ∗
          if b then
            Ψ i
          else
            Χ i
        }}
    }}}
      algo_find_seq ctx #beg #end_ pred found
    {{{
      RET ();
      pool_context pool ctx scope ∗
      ( mvar_resolved found
      ∨ find_token γ q ∗
        [∗ list] i ∈ seqZ beg (end_ - beg),
          Χ i
      )
    }}}.
  Proof.
    iIntros "%Hrange %Φ (Hctx & #Hfound_inv & Htoken & Hpred) HΦ".

    iLöb as "HLöb" forall (beg Φ Hrange).

    wp_rec. wp_pures.
    case_bool_decide; wp_pures.

    - iEval (rewrite seqZ_nil; first lia) in "HΦ".
      iSteps.

    - wp_apply (mvar_is_unset_spec with "[$]") as ([]) "H"; last iSteps.
      iClear "H".

      iDestruct (big_sepL_seqZ_cons_1 with "Hpred") as "(H & Hpred)"; first lia.
      wp_smart_apply (wp_wand with "(H Hctx)") as (res) "(%b & -> & Hctx & H)".
      destruct b; wp_pures.

      + wp_apply (mvar_set_spec with "[$Hfound_inv $Htoken $H]"); first iSteps.
        iSteps.

      + wp_apply ("HLöb" with "[%] [$] [$] [Hpred]") as "(Hctx & [#Hfound_resolved | (Htoken & HΧ)])"; first lia.
        { iEval (replace (beg + 1)%Z with (Z.succ beg) by lia).
          iEval (replace (end_ - Z.succ beg)%Z with (Z.pred (end_ - beg)) by lia).
          iFrame.
        }

        * iSteps.

        * iDestruct (big_sepL_seqZ_cons_2 with "HΧ [H]") as "HΧ"; first lia.
          { iEval (replace (Z.pred (beg + 1)) with beg by lia).
            iFrame.
          }
          iEval (replace (Z.pred (beg + 1)) with beg by lia) in "HΧ".
          iEval (replace (Z.succ (end_ - (beg + 1))) with (end_ - beg)%Z by lia) in "HΧ".
          iSteps.
  Qed.
  #[local] Lemma algo_find_0_spec pool ctx scope beg0 beg end_ end0 (chunk : Z) pred Ψ (Χ : Z → iProp Σ) found γ q :
    (beg0 ≤ beg ≤ end_ ≤ end0)%Z →
    {{{
      pool_context pool ctx scope ∗
      mvar_inv found (find_inv γ Ψ beg0 end0) ∗
      find_token γ q ∗
      [∗ list] (i : Z) ∈ seqZ beg (end_ - beg),
        ∀ ctx scope,
        pool_context pool ctx scope -∗
        WP pred ctx #i {{ res,
          ∃ b,
          ⌜res = #b⌝ ∗
          pool_context pool ctx scope ∗
          if b then
            Ψ i
          else
            Χ i
        }}
    }}}
      algo_find_0 ctx #beg #end_ #chunk pred found
    {{{
      RET ();
      pool_context pool ctx scope ∗
      ( mvar_resolved found
      ∨ find_token γ q ∗
        [∗ list] i ∈ seqZ beg (end_ - beg),
          Χ i
      )
    }}}.
  Proof.
    iIntros "%Hrange %Φ (Hctx & #Hfound_inv & Htoken & Hpred) HΦ".

    iLöb as "HLöb" forall (ctx scope beg end_ q Φ Hrange).

    wp_rec. wp_pures.
    case_bool_decide; wp_pures.

    - iEval (replace (beg + (end_ - beg))%Z with end_ by lia).
      wp_apply (algo_find_seq_spec with "[$Hctx $Hfound_inv $Htoken $Hpred] HΦ"); first done.

    - wp_apply (mvar_is_unset_spec with "[$]") as ([]) "H"; last iSteps.
      iClear "H".

      iDestruct "Htoken" as "(Htoken_1 & Htoken_2)".

      pose mid : Z := beg + (end_ - beg) `quot` 2.
      iEval (replace (end_ - beg)%Z with ((mid - beg) + (end_ - mid))%Z by lia) in "Hpred".
      iDestruct (big_sepL_seqZ_app with "Hpred") as "(Hpred_1 & Hpred_2)"; [naive_solver lia.. |].
      iEval (replace (beg + (mid - beg))%Z with mid by lia) in "Hpred_2".

      wp_smart_apply (future_async_spec
        ( λ res,
          ⌜res = ()%V⌝ ∗
          ( mvar_resolved found
          ∨ find_token γ (q / 2) ∗
            [∗ list] i ∈ seqZ beg (mid - beg),
              Χ i
          )
        )%I
        (λ _, True)%I
        with "[$Hctx Htoken_1 Hpred_1]") as (fut) "(Hctx & #Hfut_inv & Hfut_consumer)".
      { clear ctx scope. iIntros "%ctx %scope Hctx".
        wp_smart_apply ("HLöb" with "[%] [$] [$] Hpred_1"); first naive_solver lia.
        iSteps.
      }

      wp_smart_apply ("HLöb" with "[%] [$] [$] Hpred_2") as "(Hctx & H)"; first naive_solver lia.

      iApply wp_fupd.
      wp_smart_apply (future_wait_spec with "[$]") as (res) "(H£ & Hctx & #Hfut_result)".

      iMod (future_inv_result_consumer' with "H£ Hfut_inv Hfut_result Hfut_consumer") as "((-> & [#Hfound_resolved | (Htoken_1 & HΧ_1)]) & _)"; first iSteps.
      iDestruct "H" as "[#Hfound_resolved | (Htoken_2 & HΧ_2)]"; first iSteps.

      iCombine "Htoken_1 Htoken_2" as "Htoken".

      iDestruct (big_sepL_seqZ_app_2 with "HΧ_1 HΧ_2") as "HΧ"; [naive_solver lia.. |].
      iEval (replace (mid - beg + (end_ - mid))%Z with (end_ - beg)%Z by lia) in "HΧ".

      iSteps.
  Qed.
  Lemma algo_find_spec' (Ψ Χ : Z → iProp Σ) pool sz ctx scope beg end_ chunk pred :
    (beg ≤ end_)%Z →
    {{{
      pool_inv pool sz ∗
      pool_context pool ctx scope ∗
      itype_option itype_int chunk ∗
      [∗ list] (i : Z) ∈ seqZ beg (end_ - beg),
        ∀ ctx scope,
        pool_context pool ctx scope -∗
        WP pred ctx #i {{ res,
          ∃ b,
          ⌜res = #b⌝ ∗
          pool_context pool ctx scope ∗
          if b then
            Ψ i
          else
            Χ i
        }}
    }}}
      algo_find ctx #beg #end_ chunk pred
    {{{ (o : option Z),
      RET ((#@{Z}) <$> o : option val) : val;
      pool_context pool ctx scope ∗
      if o is Some i then
        ⌜beg ≤ i < end_⌝%Z ∗
        Ψ i
      else
        [∗ list] i ∈ seqZ beg (end_ - beg),
          Χ i
    }}}.
  Proof.
    iIntros "% %Φ (#Hpool_inv & Hctx & Hchunk & Hpred) HΦ".

    wp_rec.
    wp_smart_apply (algo_adjust_chunk_spec with "[$]"). clear chunk. iIntros "%chunk Hctx".

    iMod (ghost_var_alloc (ghost_var_G := algo_G_find_G) ()) as "(%γ & Htoken)".
    wp_smart_apply (mvar_create_spec (find_inv γ Ψ beg end_) with "[//]") as (found) "(#Hfound_inv & Hfound_consumer)".

    wp_smart_apply (algo_find_0_spec with "[$]") as "(Hctx & [#Hfound_resolved | (Htoken & HΧ)])"; first done.

    - wp_smart_apply (mvar_try_get_spec_resolved_consumer with "[$]") as (v) "(:find_inv)".

      iSpecialize ("HΦ" $! (Some i)).
      iSteps.

    - wp_smart_apply (mvar_try_get_spec_consumer with "[$]") as ([v |]) "H".

      + iDestruct "H" as "(_ & (:find_inv =1))".
        iDestruct (ghost_var_exclusive with "Htoken Htoken_1") as %[].

      + iSpecialize ("HΦ" $! None).
        iSteps.
  Qed.
  Lemma algo_find_spec_nat' (Ψ Χ : nat → iProp Σ) pool sz ctx scope beg end_ chunk pred :
    (0 ≤ beg ≤ end_)%Z →
    {{{
      pool_inv pool sz ∗
      pool_context pool ctx scope ∗
      itype_option itype_int chunk ∗
      [∗ list] (i : nat) ∈ seq ₊beg ₊(end_ - beg),
        ∀ ctx scope,
        pool_context pool ctx scope -∗
        WP pred ctx #i {{ res,
          ∃ b,
          ⌜res = #b⌝ ∗
          pool_context pool ctx scope ∗
          if b then
            Ψ i
          else
            Χ i
        }}
    }}}
      algo_find ctx #beg #end_ chunk pred
    {{{ (o : option nat),
      RET ((#@{nat}) <$> o : option val) : val;
      pool_context pool ctx scope ∗
      if o is Some i then
        ⌜beg ≤ i < end_⌝%Z ∗
        Ψ i
      else
        [∗ list] i ∈ seq ₊beg ₊(end_ - beg),
          Χ i
    }}}.
  Proof.
    iIntros "% %Φ (#Hpool_inv & Hctx & Hchunk & Hpred) HΦ".

    wp_apply (algo_find_spec'
      (λ i, Ψ ₊i)
      (λ i, Χ ₊i)
    with "[$Hpool_inv $Hctx $Hchunk Hpred]") as (o) "(Hctx & H)"; first lia.
    { iDestruct (big_sepL_seq_to_seqZ' with "Hpred") as "Hpred"; [lia.. |].
      iApply (big_sepL_seqZ_impl with "Hpred"). iIntros "!> %k % Hpred".
      iEval (rewrite Z2Nat.id; try lia) in "Hpred".
      iSteps.
    }

    iSpecialize ("HΦ" $! (fmap (FMap := option_fmap) Z.to_nat o)).
    destruct o as [i |] => /=.
    - iDestruct "H" as "(% & HΨ)".
      iEval (rewrite Z2Nat.id; try lia) in "HΦ".
      iSteps.
    - iSteps.
      iApply (big_sepL_seqZ_to_seq' with "H"); lia.
  Qed.
  Lemma algo_find_spec (Ψ Χ : Z → iProp Σ) pool sz ctx scope beg end_ chunk pred :
    (beg ≤ end_)%Z →
    {{{
      pool_inv pool sz ∗
      pool_context pool ctx scope ∗
      itype_option itype_int chunk ∗
      □ (
        ∀ ctx scope i,
        pool_context pool ctx scope -∗
        ⌜beg ≤ i < end_⌝%Z -∗
        WP pred ctx #i {{ res,
          ∃ b,
          ⌜res = #b⌝ ∗
          pool_context pool ctx scope ∗
          if b then
            Ψ i
          else
            Χ i
        }}
      )
    }}}
      algo_find ctx #beg #end_ chunk pred
    {{{ (o : option Z),
      RET ((#@{Z}) <$> o : option val) : val;
      pool_context pool ctx scope ∗
      if o is Some i then
        ⌜beg ≤ i < end_⌝%Z ∗
        Ψ i
      else
        [∗ list] i ∈ seqZ beg (end_ - beg),
          Χ i
    }}}.
  Proof.
    iIntros "% %Φ (#Hpool_inv & Hctx & Hchunk & #Hpred) HΦ".

    wp_apply (algo_find_spec' with "[$Hpool_inv $Hctx $Hchunk] HΦ"); first done.
    { iApply big_sepL_seqZ_intro.
      iSteps.
    }
  Qed.
  Lemma algo_find_spec_nat (Ψ Χ : nat → iProp Σ) pool sz ctx scope beg end_ chunk pred :
    (0 ≤ beg ≤ end_)%Z →
    {{{
      pool_inv pool sz ∗
      pool_context pool ctx scope ∗
      itype_option itype_int chunk ∗
      □ (
        ∀ ctx scope (i : nat),
        pool_context pool ctx scope -∗
        ⌜beg ≤ i < end_⌝%Z -∗
        WP pred ctx #i {{ res,
          ∃ b,
          ⌜res = #b⌝ ∗
          pool_context pool ctx scope ∗
          if b then
            Ψ i
          else
            Χ i
        }}
      )
    }}}
      algo_find ctx #beg #end_ chunk pred
    {{{ (o : option nat),
      RET ((#@{nat}) <$> o : option val) : val;
      pool_context pool ctx scope ∗
      if o is Some i then
        ⌜beg ≤ i < end_⌝%Z ∗
        Ψ i
      else
        [∗ list] i ∈ seq ₊beg ₊(end_ - beg),
          Χ i
    }}}.
  Proof.
    iIntros "% %Φ (#Hpool_inv & Hctx & Hchunk & #Hpred) HΦ".

    wp_apply (algo_find_spec_nat' with "[$Hpool_inv $Hctx $Hchunk] HΦ"); first done.
    { iApply big_sepL_seq_intro.
      iSteps.
    }
  Qed.
End algo_G.

From zoo_parabs Require
  algo__opaque.
