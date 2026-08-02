Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Import zoo.iris.bi.big_op.
Require Import zoo.iris.base_logic.lib.ghost_var.
Require Import zoo.base.
Require Import zoo_std.for_.
Require Import zoo_std.option.
Require Export zoo_parabs.base.
Require Export zoo_parabs.algo__code.
Require Import zoo_parabs.algo__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type v pool ctx task pred found body op zero acc : val.
Implicit Type o : option val.

Class AlgoG Σ `{pool۰G : PoolG Σ} :=
  { #[local] algo۰G۰future۰G :: FutureG Σ
  ; #[local] algo۰G۰mvar۰G :: MvarG Σ
  ; #[local] algo۰G۰find۰G :: GhostVarG Σ unitO
  }.

Definition algo۰Σ :=
  #[future۰Σ
  ; mvar۰Σ
  ; ghost_var۰Σ unitO
  ].
#[global] Instance subGｰalgo۰Σ Σ `{pool۰G : PoolG Σ} :
  subG algo۰Σ Σ →
  AlgoG Σ.
Proof.
  solve_inG.
Qed.

Section algo۰G.
  Context `{algo۰G : AlgoG Σ}.

  #[local] Lemma algo٠adjust_chunkｰspec pool sz ctx scope (beg end_ : Z) chunk :
    {{{
      pool۰inv pool sz ∗
      pool۰context pool ctx scope ∗
      itype۰option itype۰int chunk
    }}}
      algo٠adjust_chunk ctx #beg #end_ chunk
    {{{
      (chunk : Z)
    , RET #chunk;
      pool۰context pool ctx scope
    }}}.
  Proof.
    iIntros "%Φ (#Hpool_inv & Hctx & [-> | (% & -> & (%chunk & ->))]) HΦ".

    all: wp۰rec.
    all: wp۰pures.

    - wp۰apply (pool٠sizeｰspec with "[$]").
      iSteps.

    - iSteps.
  Qed.

  #[local] Lemma algo٠for_₁ｰspec Ψ Χ pool ctx scope beg0 beg end_ end0 (chunk : Z) task :
    (beg0 ≤ beg ≤ end_ ≤ end0)%Z →
    {{{
      pool۰context pool ctx scope ∗
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
        pool۰context pool ctx scope -∗
        ⌜beg0 ≤ i⌝%Z -∗
        ⌜i + n ≤ end0⌝%Z -∗
        Χ i n -∗
        WP task ctx #i #n {{ res,
          ⌜res = ()%V⌝ ∗
          pool۰context pool ctx scope ∗
          [∗ list] j ∈ seqZ i n,
            Ψ j
        }}
      )
    }}}
      algo٠for_₁ ctx #beg #end_ #chunk task
    {{{
      RET ();
      pool۰context pool ctx scope ∗
      [∗ list] i ∈ seqZ beg (end_ - beg),
        Ψ i
    }}}.
  Proof.
    iIntros "%Hrange %Φ (Hctx & HΧ & #HΧ_split & #HΧ_elim) HΦ".

    iLöb as "HLöb" forall (ctx scope beg end_ Φ Hrange).

    wp۰rec. wp۰pures.
    case_bool_decide; wp۰pures.

    - iEval (replace (end_ - beg)%Z with ⁺₊(end_ - beg) by lia) in "HΦ" |- *.
      wp۰apply (wpｰwand with "(HΧ_elim Hctx [%] [%] HΧ)"); [lia.. |].
      iSteps.

    - pose mid : Z := beg + (end_ - beg) `quot` 2.
      iEval (replace ₊(end_ - beg) with (₊(mid - beg) + ₊(end_ - mid)) by naive_solver lia) in "HΧ".
      iDestruct ("HΧ_split" with "[%] [%] HΧ") as "(HΧ_1 & HΧ_2)"; [naive_solver lia.. |].
      iEval (replace (beg + ₊(mid - beg))%Z with mid by naive_solver lia) in "HΧ_2".

      wp۰apply (future٠asyncｰspec
        ( λ res,
          ⌜res = ()%V⌝ ∗
          [∗ list] i ∈ seqZ beg (mid - beg),
            Ψ i
        )%I
        ( λ _,
          True
        )%I
      with "[$Hctx HΧ_1]") as (fut) "(Hctx & #Hfut_inv & Hfut_consumer)".
      { iIntros "{% ctx scope} %ctx %scope Hctx".
        wp۰apply+ ("HLöb" with "[%] Hctx HΧ_1"); first naive_solver lia.
        { iSteps. }
      }

      wp۰apply+ ("HLöb" with "[%] Hctx HΧ_2") as "(Hctx & HΨ_2)"; first naive_solver lia.

      iApply wpｰfupd.
      wp۰apply+ (future٠waitｰspec with "[$]") as (res) "(H£ & Hctx & Hfut_result)".
      iMod (futureｰinvｰresultｰconsumer' with "H£ Hfut_inv Hfut_result Hfut_consumer") as "((-> & HΨ_1) & _)".

      iDestruct (big_sepLｰseqZｰapp₂ with "HΨ_1 HΨ_2") as "HΨ"; [naive_solver lia.. |].
      iEval (replace (mid - beg + (end_ - mid))%Z with (end_ - beg)%Z by lia) in "HΨ".

      iSteps.
  Qed.
  Lemma algo٠for_ｰspec (Ψ : Z → iProp Σ) (Χ : Z → nat → iProp Σ) pool sz ctx scope beg end_ chunk task :
    (beg ≤ end_)%Z →
    {{{
      pool۰inv pool sz ∗
      pool۰context pool ctx scope ∗
      itype۰option itype۰int chunk ∗
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
        pool۰context pool ctx scope -∗
        ⌜beg ≤ i⌝%Z -∗
        ⌜i + n ≤ end_⌝%Z -∗
        Χ i n -∗
        WP task ctx #i #n {{ res,
          ⌜res = ()%V⌝ ∗
          pool۰context pool ctx scope ∗
          [∗ list] j ∈ seqZ i n,
            Ψ j
        }}
      )
    }}}
      algo٠for_ ctx #beg #end_ chunk task
    {{{
      RET ();
      pool۰context pool ctx scope ∗
      [∗ list] i ∈ seqZ beg (end_ - beg),
        Ψ i
    }}}.
  Proof.
    iIntros "% %Φ (Hpool_inv & Hctx & Hchunk & HΧ & #HΧ_split & #HΧ_elim) HΦ".

    wp۰rec.
    wp۰apply+ (algo٠adjust_chunkｰspec with "[$]") as "{% chunk} %chunk Hctx".
    wp۰apply+ (algo٠for_₁ｰspec Ψ Χ with "[$]"); first done.
    iSteps.
  Qed.
  Lemma algo٠for_ｰspecｰnat (Ψ : nat → iProp Σ) (Χ : Z → nat → iProp Σ) pool sz ctx scope beg end_ chunk task :
    (0 ≤ beg ≤ end_)%Z →
    {{{
      pool۰inv pool sz ∗
      pool۰context pool ctx scope ∗
      itype۰option itype۰int chunk ∗
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
        pool۰context pool ctx scope -∗
        ⌜beg ≤ i⌝%Z -∗
        ⌜i + n ≤ end_⌝%Z -∗
        Χ i n -∗
        WP task ctx #i #n {{ res,
          ⌜res = ()%V⌝ ∗
          pool۰context pool ctx scope ∗
          [∗ list] j ∈ seq i n,
            Ψ j
        }}
      )
    }}}
      algo٠for_ ctx #beg #end_ chunk task
    {{{
      RET ();
      pool۰context pool ctx scope ∗
      [∗ list] i ∈ seq ₊beg ₊(end_ - beg),
        Ψ i
    }}}.
  Proof.
    iIntros "% %Φ (Hpool_inv & Hctx & Hchunk & HΧ & #HΧ_split & #HΧ_elim) HΦ".

    wp۰apply (algo٠for_ｰspec
      (λ i, Ψ ₊i)
      (λ i n, Χ ₊i n)
    with "[$Hpool_inv $Hctx $Hchunk $HΧ]"); first lia.
    { iSplit.
      - iIntros "!> %i %n1 %n2 % % HΧ".
        iEval (replace ₊(i + n1) with (₊i + n1) by lia).
        iSteps.
      - iIntros "!> {% ctx scope} %ctx %scope %i %n Hctx % % HΧ".
        Z_to_nat i.
        iEval (rewrite Nat2Z.id) in "HΧ".
        wp۰apply (wpｰwand with "(HΧ_elim Hctx [%] [%] HΧ)"); [done.. |].
        iSteps as "HΨ".
        iApply (big_sepLｰseqｰtoｰseqZ with "HΨ").
    }

    iSteps as "HΨ".
    iApply (big_sepLｰseqZｰtoｰseq' with "HΨ"); lia.
  Qed.
  Lemma algo٠for_ｰspec' (Ψ : Z → iProp Σ) pool sz ctx scope beg end_ chunk task :
    (beg ≤ end_)%Z →
    {{{
      pool۰inv pool sz ∗
      pool۰context pool ctx scope ∗
      itype۰option itype۰int chunk ∗
      □ (
        ∀ ctx scope i (n : nat),
        pool۰context pool ctx scope -∗
        ⌜beg ≤ i⌝%Z -∗
        ⌜i + n ≤ end_⌝%Z -∗
        WP task ctx #i #n {{ res,
          ⌜res = ()%V⌝ ∗
          pool۰context pool ctx scope ∗
          [∗ list] j ∈ seqZ i n,
            Ψ j
        }}
      )
    }}}
      algo٠for_ ctx #beg #end_ chunk task
    {{{
      RET ();
      pool۰context pool ctx scope ∗
      [∗ list] i ∈ seqZ beg (end_ - beg),
        Ψ i
    }}}.
  Proof.
    iIntros "% %Φ (Hpool_inv & Hctx & Hchunk & #Htask) HΦ".

    wp۰apply (algo٠for_ｰspec
      Ψ
      (λ _ _, True)%I
    with "[$Hpool_inv $Hchunk $Hctx] HΦ"); first done.
    { iSteps. }
  Qed.
  Lemma algo٠for_ｰspecｰnat' (Ψ : nat → iProp Σ) pool sz ctx scope beg end_ chunk task :
    (0 ≤ beg ≤ end_)%Z →
    {{{
      pool۰inv pool sz ∗
      pool۰context pool ctx scope ∗
      itype۰option itype۰int chunk ∗
      □ (
        ∀ ctx scope (i n : nat),
        pool۰context pool ctx scope -∗
        ⌜beg ≤ i⌝%Z -∗
        ⌜i + n ≤ end_⌝%Z -∗
        WP task ctx #i #n {{ res,
          ⌜res = ()%V⌝ ∗
          pool۰context pool ctx scope ∗
          [∗ list] j ∈ seq i n,
            Ψ j
        }}
      )
    }}}
      algo٠for_ ctx #beg #end_ chunk task
    {{{
      RET ();
      pool۰context pool ctx scope ∗
      [∗ list] i ∈ seq ₊beg ₊(end_ - beg),
        Ψ i
    }}}.
  Proof.
    iIntros "% %Φ (Hpool_inv & Hctx & Hchunk & #Htask) HΦ".

    wp۰apply (algo٠for_ｰspec'
      (λ i, Ψ ₊i)
    with "[$Hpool_inv $Hchunk $Hctx]"); first lia.
    { iIntros "{% ctx scope} !> %ctx %scope %i %n Hctx % %".
      Z_to_nat i.
      wp۰apply (wpｰwand with "(Htask Hctx [%] [%])"); [done.. |].
      iSteps as "HΨ".
      iApply (big_sepLｰseqｰtoｰseqZ with "HΨ").
    }

    iSteps as "HΨ".
    iApply (big_sepLｰseqZｰtoｰseq' with "HΨ"); lia.
  Qed.

  Lemma algo٠for_eachｰspec' (Ψ : Z → iProp Σ) pool sz ctx scope beg end_ chunk task :
    (beg ≤ end_)%Z →
    {{{
      pool۰inv pool sz ∗
      pool۰context pool ctx scope ∗
      itype۰option itype۰int chunk ∗
      [∗ list] i ∈ seqZ beg (end_ - beg),
        ∀ ctx scope,
        pool۰context pool ctx scope -∗
        ⌜beg ≤ i < end_⌝%Z -∗
        WP task ctx #i {{ res,
          ⌜res = ()%V⌝ ∗
          pool۰context pool ctx scope ∗
          Ψ i
        }}
    }}}
      algo٠for_each ctx #beg #end_ chunk task
    {{{
      RET ();
      pool۰context pool ctx scope ∗
      [∗ list] i ∈ seqZ beg (end_ - beg),
        Ψ i
    }}}.
  Proof.
    iIntros "% %Φ (Hpool_inv & Hctx & Hchunk & Htask) HΦ".

    wp۰rec.
    wp۰apply+ (algo٠for_ｰspec
      Ψ
      ( λ i n,
        [∗ list] i ∈ seqZ i n,
          ∀ ctx scope,
          pool۰context pool ctx scope -∗
          ⌜beg ≤ i < end_⌝%Z -∗
          WP task ctx #i {{ res,
            ⌜res = ()%V⌝ ∗
            pool۰context pool ctx scope ∗
            Ψ i
          }}
      )%I
    with "[$Hpool_inv $Hchunk $Hctx Htask] HΦ"); first done.
    { repeat iSplit.
      - rewrite Z2Nat.id //; first lia.
      - iIntros "!> %i %n1 %n2 % % Htask".
        iEval (rewrite Nat2Z.inj_add) in "Htask".
        iApply (big_sepLｰseqZｰapp with "Htask"); lia.
      - iIntros "{% ctx scope} !> %ctx %scope %i %n Hctx % % Htask".
        wp۰apply+ (forｰspec'
          ( λ j δ,
            pool۰context pool ctx scope ∗
            ( [∗ list] k ∈ seqZ j (i + n - j),
              ∀ ctx scope,
              pool۰context pool ctx scope -∗
              ⌜beg ≤ k < end_⌝%Z -∗
              WP task ctx #k {{ res,
                ⌜res = ()%V⌝ ∗
                pool۰context pool ctx scope ∗
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
          - iApply big_sepLｰseqｰintro. iIntros "!> %δ % % -> (Hctx & Htask & HΨ)".
            iEval (replace (i + n - (i + δ))%Z with (n - δ)%Z by lia) in "Htask".
            iDestruct (big_sepLｰseqZｰcons with "Htask") as "(H & Htask)"; first lia.
            wp۰apply+ (wpｰwand with "(H Hctx [%])") as (res) "(-> & Hctx & H)"; first lia.
            iDestruct (big_sepLｰseqZｰsnoc₂ with "HΨ H") as "HΨ"; first lia.
            iEval (replace (i + δ + 1)%Z with (Z.succ (i + δ)%Z) by lia).
            iEval (replace (i + n - Z.succ (i + δ))%Z with (Z.pred (n - δ)) by lia).
            iEval (replace ⁺˖δ with (Z.succ δ) by lia).
            iFrameSteps.
        }
        rewrite Z.add_simpl_l Nat2Z.id. iSteps.
    }
  Qed.
  Lemma algo٠for_eachｰspecｰnat' (Ψ : nat → iProp Σ) pool sz ctx scope beg end_ chunk task :
    (0 ≤ beg ≤ end_)%Z →
    {{{
      pool۰inv pool sz ∗
      pool۰context pool ctx scope ∗
      itype۰option itype۰int chunk ∗
      [∗ list] (i : nat) ∈ seq ₊beg ₊(end_ - beg),
        ∀ ctx scope,
        pool۰context pool ctx scope -∗
        ⌜beg ≤ i < end_⌝%Z -∗
        WP task ctx #i {{ res,
          ⌜res = ()%V⌝ ∗
          pool۰context pool ctx scope ∗
          Ψ i
        }}
    }}}
      algo٠for_each ctx #beg #end_ chunk task
    {{{
      RET ();
      pool۰context pool ctx scope ∗
      [∗ list] i ∈ seq ₊beg ₊(end_ - beg),
        Ψ i
    }}}.
  Proof.
    iIntros "% %Φ (Hpool_inv & Hctx & Hchunk & Htask) HΦ".

    wp۰apply (algo٠for_eachｰspec'
      (λ i, Ψ ₊i)
    with "[$Hpool_inv $Hchunk $Hctx Htask]"); first lia.
    { iDestruct (big_sepLｰseqｰtoｰseqZ' with "Htask") as "Htask"; [lia.. |].
      iApply (big_sepLｰseqZｰimpl with "Htask"). iIntros "!> %k % Htask".
      iEval (rewrite Z2Nat.id; try lia) in "Htask".
      iSteps.
    }

    iSteps as "HΨ".
    iApply (big_sepLｰseqZｰtoｰseq' with "HΨ"); lia.
  Qed.
  Lemma algo٠for_eachｰspec (Ψ : Z → iProp Σ) pool sz ctx scope beg end_ chunk task :
    (beg ≤ end_)%Z →
    {{{
      pool۰inv pool sz ∗
      pool۰context pool ctx scope ∗
      itype۰option itype۰int chunk ∗
      □ (
        ∀ ctx scope i,
        pool۰context pool ctx scope -∗
        ⌜beg ≤ i < end_⌝%Z -∗
        WP task ctx #i {{ res,
          ⌜res = ()%V⌝ ∗
          pool۰context pool ctx scope ∗
          Ψ i
        }}
      )
    }}}
      algo٠for_each ctx #beg #end_ chunk task
    {{{
      RET ();
      pool۰context pool ctx scope ∗
      [∗ list] i ∈ seqZ beg (end_ - beg),
        Ψ i
    }}}.
  Proof.
    iIntros "% %Φ (Hpool_inv & Hctx & Hchunk & #Htask) HΦ".

    wp۰apply (algo٠for_eachｰspec' Ψ with "[$Hpool_inv $Hchunk $Hctx] HΦ"); first done.
    { iApply big_sepLｰseqZｰintro.
      iSteps.
    }
  Qed.
  Lemma algo٠for_eachｰspecｰnat (Ψ : nat → iProp Σ) pool sz ctx scope beg end_ chunk task :
    (0 ≤ beg ≤ end_)%Z →
    {{{
      pool۰inv pool sz ∗
      pool۰context pool ctx scope ∗
      itype۰option itype۰int chunk ∗
      □ (
        ∀ ctx scope (i : nat),
        pool۰context pool ctx scope -∗
        ⌜beg ≤ i < end_⌝%Z -∗
        WP task ctx #i {{ res,
          ⌜res = ()%V⌝ ∗
          pool۰context pool ctx scope ∗
          Ψ i
        }}
      )
    }}}
      algo٠for_each ctx #beg #end_ chunk task
    {{{
      RET ();
      pool۰context pool ctx scope ∗
      [∗ list] i ∈ seq ₊beg ₊(end_ - beg),
        Ψ i
    }}}.
  Proof.
    iIntros "% %Φ (Hpool_inv & Hctx & Hchunk & #Htask) HΦ".

    wp۰apply (algo٠for_eachｰspecｰnat' Ψ with "[$Hpool_inv $Hchunk $Hctx] HΦ"); first done.
    { iApply big_sepLｰseqｰintro.
      iSteps.
    }
  Qed.

  #[local] Lemma algo٠fold_seqｰspec {Ψ Χ pool ctx scope beg0} beg1 (n : nat) beg end_ end0 body op acc :
    beg = (beg1 + n)%Z →
    (beg0 ≤ beg1 ≤ beg ≤ end_ ≤ end0)%Z →
    {{{
      pool۰context pool ctx scope ∗
      ( [∗ list] (i : Z) ∈ seqZ beg (end_ - beg),
        ∀ ctx scope,
        pool۰context pool ctx scope -∗
        WP body ctx #i {{ v,
          pool۰context pool ctx scope ∗
          ▷ Ψ i v
        }}
      ) ∗
      □ (
        ∀ i (n : nat) acc v,
        ⌜beg0 ≤ i⌝%Z -∗
        ⌜i + n ≤ end0⌝%Z -∗
        Χ i n acc -∗
        Ψ (i + n)%Z v -∗
        WP op acc v {{ acc,
          ▷ Χ i ˖n acc
        }}
      ) ∗
      Χ beg1 n acc
    }}}
      algo٠fold_seq ctx #beg #end_ body op acc
    {{{
      acc
    , RET acc;
      pool۰context pool ctx scope ∗
      Χ beg1 ₊(n + end_ - beg) acc
    }}}.
  Proof.
    iIntros "%Heq %Hrange %Φ (Hctx & Hbody & #Hop & HΧ) HΦ".

    iLöb as "HLöb" forall (n beg acc Φ Heq Hrange).
    subst beg.

    wp۰rec. wp۰pures.
    case_bool_decide; wp۰pures.

    - subst end_.
      iEval (rewrite Z.add_simpl_r Nat2Z.id) in "HΦ".
      iSteps.

    - iDestruct (big_sepLｰseqZｰcons₁ with "Hbody") as "(H & Hbody)"; first lia.
      wp۰apply (wpｰwand with "(H Hctx)") as (v) "(Hctx & HΨ)".

      wp۰apply+ (wpｰwand with "(Hop [%] [%] HΧ HΨ)") as (acc1) "HΧ"; [lia.. |].

      wp۰apply+ ("HLöb" $! ˖n with "[%] [%] [$] [Hbody] HΧ") as (acc2) "HΧ"; [lia.. | |].
      { iEval (replace (beg1 + n + 1)%Z with (Z.succ (beg1 + n)) by lia).
        iEval (replace (end_ - Z.succ (beg1 + n))%Z with (Z.pred (end_ - (beg1 + n))) by lia).
        iFrame.
      }

      iEval (replace (˖n + end_ - _)%Z with (n + end_ - (beg1 + n))%Z by lia) in "HΧ".
      iSteps.
  Qed.
  #[local] Lemma algo٠fold₁ｰspec Ψ Χ pool ctx scope beg0 beg end_ end0 (chunk : Z) body op zero :
    (beg0 ≤ beg ≤ end_ ≤ end0)%Z →
    {{{
      pool۰context pool ctx scope ∗
      ( [∗ list] (i : Z) ∈ seqZ beg (end_ - beg),
        ∀ ctx scope,
        pool۰context pool ctx scope -∗
        WP body ctx #i {{ v,
          pool۰context pool ctx scope ∗
          ▷ Ψ i v
        }}
      ) ∗
      □ (
        ∀ i,
        ⌜beg0 ≤ i ≤ end0⌝%Z -∗
        Χ i 0 zero
      ) ∗
      □ (
        ∀ i (n : nat) acc v,
        ⌜beg0 ≤ i⌝%Z -∗
        ⌜i + n ≤ end0⌝%Z -∗
        Χ i n acc -∗
        Ψ (i + n)%Z v -∗
        WP op acc v {{ acc,
          ▷ Χ i ˖n acc
        }}
      ) ∗
      □ (
        ∀ i (n1 n2 : nat) acc1 acc2,
        ⌜beg0 ≤ i⌝%Z -∗
        ⌜i + n1 + n2 ≤ end0⌝%Z -∗
        Χ i n1 acc1 -∗
        Χ (i + n1)%Z n2 acc2 -∗
        WP op acc1 acc2 {{ acc,
          ▷ Χ i (n1 + n2) acc
        }}
      )
    }}}
      algo٠fold₁ ctx #beg #end_ #chunk body op zero
    {{{
      acc
    , RET acc;
      pool۰context pool ctx scope ∗
      Χ beg ₊(end_ - beg) acc
    }}}.
  Proof.
    iIntros "%Hrange %Φ (Hctx & Hbody & #Hzero & #Hop_succ & #Hop_app) HΦ".

    iLöb as "HLöb" forall (ctx scope beg end_ Φ Hrange).

    wp۰rec credit: "H£_1". wp۰pures.
    case_bool_decide; wp۰pures.

    - iEval (replace (beg + (end_ - beg))%Z with end_ by lia).
      wp۰apply (algo٠fold_seqｰspec beg 0 with "[$Hctx $Hbody $Hop_succ]"); [lia.. | iSteps |].
      iSteps.

    - pose mid : Z := beg + (end_ - beg) `quot` 2.
      iEval (replace (end_ - beg)%Z with ((mid - beg) + (end_ - mid))%Z by lia) in "Hbody".
      iDestruct (big_sepLｰseqZｰapp with "Hbody") as "(Hbody_1 & Hbody_2)"; [naive_solver lia.. |].
      iEval (replace (beg + (mid - beg))%Z with mid by lia) in "Hbody_2".

      wp۰apply+ (future٠asyncｰspec
        (Χ beg ₊(mid - beg))
        (λ _, True)%I
        with "[$Hctx Hbody_1]") as (fut) "(Hctx & #Hfut_inv & Hfut_consumer)".
      { iIntros "{% ctx scope} %ctx %scope Hctx".
        wp۰apply+ ("HLöb" with "[%] [$] Hbody_1"); first naive_solver lia.
        iSteps.
      }

      wp۰apply+ ("HLöb" with "[%] [$] Hbody_2") as (acc2) "(Hctx & HΧ_2)"; first naive_solver lia.

      wp۰apply+ (future٠waitｰspec with "[$]") as (acc1) "(H£_2 & Hctx & #Hfut_result)".
      iMod (futureｰinvｰresultｰconsumer' with "H£_2 Hfut_inv Hfut_result Hfut_consumer") as "(HΧ_1 & _)".

      iEval (replace mid with (beg + ₊(mid - beg))%Z by naive_solver lia) in "HΧ_2".
      iApply wpｰfupd.
      wp۰apply+ (wpｰwand with "(Hop_app [%] [%] HΧ_1 HΧ_2)") as (acc) "HΧ"; [naive_solver lia.. |].
      iMod (lc_fupd_elim_later with "H£_1 HΧ") as "HΧ".
      iEval (replace _ with ₊(end_ - beg) by naive_solver lia) in "HΧ".

      iSteps.
  Qed.
  Lemma algo٠foldｰspec' (Ψ : Z → val → iProp Σ) (Χ : Z → nat → val → iProp Σ) pool sz ctx scope beg end_ chunk body op zero :
    (beg ≤ end_)%Z →
    {{{
      pool۰inv pool sz ∗
      pool۰context pool ctx scope ∗
      itype۰option itype۰int chunk ∗
      ( [∗ list] (i : Z) ∈ seqZ beg (end_ - beg),
        ∀ ctx scope,
        pool۰context pool ctx scope -∗
        WP body ctx #i {{ v,
          pool۰context pool ctx scope ∗
          ▷ Ψ i v
        }}
      ) ∗
      □ (
        ∀ i,
        ⌜beg ≤ i ≤ end_⌝%Z -∗
        Χ i 0 zero
      ) ∗
      □ (
        ∀ i (n : nat) acc v,
        ⌜beg ≤ i⌝%Z -∗
        ⌜i + n ≤ end_⌝%Z -∗
        Χ i n acc -∗
        Ψ (i + n)%Z v -∗
        WP op acc v {{ acc,
          ▷ Χ i ˖n acc
        }}
      ) ∗
      □ (
        ∀ i (n1 n2 : nat) acc1 acc2,
        ⌜beg ≤ i⌝%Z -∗
        ⌜i + n1 + n2 ≤ end_⌝%Z -∗
        Χ i n1 acc1 -∗
        Χ (i + n1)%Z n2 acc2 -∗
        WP op acc1 acc2 {{ acc,
          ▷ Χ i (n1 + n2) acc
        }}
      )
    }}}
      algo٠fold ctx #beg #end_ chunk body op zero
    {{{
      acc
    , RET acc;
      pool۰context pool ctx scope ∗
      Χ beg ₊(end_ - beg) acc
    }}}.
  Proof.
    iIntros "%Hrange %Φ (#Hpool_inv & Hctx & Hchunk & Hbody & #Hzero & #Hop_succ & #Hop_app) HΦ".

    wp۰rec.
    wp۰apply+ (algo٠adjust_chunkｰspec with "[$]") as "{% chunk} %chunk Hctx".
    wp۰apply+ (algo٠fold₁ｰspec Ψ Χ with "[$]"); first done.
    iSteps.
  Qed.
  Lemma algo٠foldｰspecｰnat' (Ψ : nat → val → iProp Σ) (Χ : nat → nat → val → iProp Σ) pool sz ctx scope beg end_ chunk body op zero :
    (0 ≤ beg ≤ end_)%Z →
    {{{
      pool۰inv pool sz ∗
      pool۰context pool ctx scope ∗
      itype۰option itype۰int chunk ∗
      ( [∗ list] (i : nat) ∈ seq ₊beg ₊(end_ - beg),
        ∀ ctx scope,
        pool۰context pool ctx scope -∗
        WP body ctx #i {{ v,
          pool۰context pool ctx scope ∗
          ▷ Ψ i v
        }}
      ) ∗
      □ (
        ∀ i : nat,
        ⌜beg ≤ i ≤ end_⌝%Z -∗
        Χ i 0 zero
      ) ∗
      □ (
        ∀ (i n : nat) acc v,
        ⌜beg ≤ i⌝%Z -∗
        ⌜i + n ≤ end_⌝%Z -∗
        Χ i n acc -∗
        Ψ (i + n) v -∗
        WP op acc v {{ acc,
          ▷ Χ i ˖n acc
        }}
      ) ∗
      □ (
        ∀ (i n1 n2 : nat) acc1 acc2,
        ⌜beg ≤ i⌝%Z -∗
        ⌜i + n1 + n2 ≤ end_⌝%Z -∗
        Χ i n1 acc1 -∗
        Χ (i + n1) n2 acc2 -∗
        WP op acc1 acc2 {{ acc,
          ▷ Χ i (n1 + n2) acc
        }}
      )
    }}}
      algo٠fold ctx #beg #end_ chunk body op zero
    {{{
      acc
    , RET acc;
      pool۰context pool ctx scope ∗
      Χ ₊beg ₊(end_ - beg) acc
    }}}.
  Proof.
    iIntros "%Hrange %Φ (#Hpool_inv & Hctx & Hchunk & Hbody & #Hzero & #Hop_succ & #Hop_app) HΦ".

    wp۰apply (algo٠foldｰspec'
      (λ i, Ψ ₊i)
      (λ i, Χ ₊i)
    with "[$Hpool_inv $Hctx $Hchunk Hbody] HΦ"); first lia.
    { iSplitL "Hbody"; last repeat iSplit.
      - iDestruct (big_sepLｰseqｰtoｰseqZ' with "Hbody") as "Hbody"; [lia.. |].
        iApply (big_sepLｰseqZｰimpl with "Hbody"). iIntros "!> %k % Hbody".
        iEval (rewrite Z2Nat.id; try lia) in "Hbody".
        iSteps.
      - iSteps.
      - iIntros "!> %i %n %acc %v % % HΧ HΨ".
        wp۰apply ("Hop_succ" with "[%] [%] HΧ [HΨ]"); [lia.. |].
        iEval (replace (₊i + n) with ₊(i + n) by lia).
        iFrame.
      - iIntros "!> %i %n1 %n2 %acc1 %acc2 % % HΧ_1 HΧ_2".
        wp۰apply ("Hop_app" with "[%] [%] HΧ_1 [HΧ_2]"); [lia.. |].
        iEval (replace (₊i + n1) with ₊(i + n1) by lia).
        iFrame.
    }
  Qed.
  Lemma algo٠foldｰspec (Ψ : Z → val → iProp Σ) (Χ : Z → nat → val → iProp Σ) pool sz ctx scope beg end_ chunk body op zero :
    (beg ≤ end_)%Z →
    {{{
      pool۰inv pool sz ∗
      pool۰context pool ctx scope ∗
      itype۰option itype۰int chunk ∗
      □ (
        ∀ ctx scope i,
        pool۰context pool ctx scope -∗
        ⌜beg ≤ i < end_⌝%Z -∗
        WP body ctx #i {{ v,
          pool۰context pool ctx scope ∗
          ▷ Ψ i v
        }}
      ) ∗
      □ (
        ∀ i,
        ⌜beg ≤ i ≤ end_⌝%Z -∗
        Χ i 0 zero
      ) ∗
      □ (
        ∀ i (n : nat) acc v,
        ⌜beg ≤ i⌝%Z -∗
        ⌜i + n ≤ end_⌝%Z -∗
        Χ i n acc -∗
        Ψ (i + n)%Z v -∗
        WP op acc v {{ acc,
          ▷ Χ i ˖n acc
        }}
      ) ∗
      □ (
        ∀ i (n1 n2 : nat) acc1 acc2,
        ⌜beg ≤ i⌝%Z -∗
        ⌜i + n1 + n2 ≤ end_⌝%Z -∗
        Χ i n1 acc1 -∗
        Χ (i + n1)%Z n2 acc2 -∗
        WP op acc1 acc2 {{ acc,
          ▷ Χ i (n1 + n2) acc
        }}
      )
    }}}
      algo٠fold ctx #beg #end_ chunk body op zero
    {{{
      acc
    , RET acc;
      pool۰context pool ctx scope ∗
      Χ beg ₊(end_ - beg) acc
    }}}.
  Proof.
    iIntros "%Hrange %Φ (#Hpool_inv & Hctx & Hchunk & #Hbody & #Hzero & #Hop_succ & #Hop_app) HΦ".

    wp۰apply (algo٠foldｰspec' with "[$Hpool_inv $Hctx $Hchunk $Hzero $Hop_succ $Hop_app] HΦ"); first done.
    { iApply big_sepLｰseqZｰintro.
      iSteps.
    }
  Qed.
  Lemma algo٠foldｰspecｰnat (Ψ : nat → val → iProp Σ) (Χ : nat → nat → val → iProp Σ) pool sz ctx scope beg end_ chunk body op zero :
    (0 ≤ beg ≤ end_)%Z →
    {{{
      pool۰inv pool sz ∗
      pool۰context pool ctx scope ∗
      itype۰option itype۰int chunk ∗
      □ (
        ∀ ctx scope (i : nat),
        pool۰context pool ctx scope -∗
        ⌜beg ≤ i < end_⌝%Z -∗
        WP body ctx #i {{ v,
          pool۰context pool ctx scope ∗
          ▷ Ψ i v
        }}
      ) ∗
      □ (
        ∀ i : nat,
        ⌜beg ≤ i ≤ end_⌝%Z -∗
        Χ i 0 zero
      ) ∗
      □ (
        ∀ (i n : nat) acc v,
        ⌜beg ≤ i⌝%Z -∗
        ⌜i + n ≤ end_⌝%Z -∗
        Χ i n acc -∗
        Ψ (i + n) v -∗
        WP op acc v {{ acc,
          ▷ Χ i ˖n acc
        }}
      ) ∗
      □ (
        ∀ (i n1 n2 : nat) acc1 acc2,
        ⌜beg ≤ i⌝%Z -∗
        ⌜i + n1 + n2 ≤ end_⌝%Z -∗
        Χ i n1 acc1 -∗
        Χ (i + n1) n2 acc2 -∗
        WP op acc1 acc2 {{ acc,
          ▷ Χ i (n1 + n2) acc
        }}
      )
    }}}
      algo٠fold ctx #beg #end_ chunk body op zero
    {{{
      acc
    , RET acc;
      pool۰context pool ctx scope ∗
      Χ ₊beg ₊(end_ - beg) acc
    }}}.
  Proof.
    iIntros "%Hrange %Φ (#Hpool_inv & Hctx & Hchunk & #Hbody & #Hzero & #Hop_succ & #Hop_app) HΦ".

    wp۰apply (algo٠foldｰspecｰnat' with "[$Hpool_inv $Hctx $Hchunk $Hzero $Hop_succ $Hop_app] HΦ"); first done.
    { iApply big_sepLｰseqｰintro.
      iSteps.
    }
  Qed.

  #[local] Definition find۰token γ q :=
    ghost_var γ (DfracOwn q) ().
  #[local] Definition find۰inv γ Ψ beg end_ v : iProp Σ :=
    ∃ (i : Z) q,
    ⌜v = #i⌝ ∗
    ⌜beg ≤ i < end_⌝%Z ∗
    find۰token γ q ∗
    Ψ i.
  #[local] Instance : CustomIpat "find۰inv" :=
    " ( %i
      & %q
      & ->
      & %
      & Htoken{_{}}
      & HΨ
      )
    ".
  #[local] Lemma algo٠find_seqｰspec pool ctx scope beg0 beg end_ end0 pred Ψ Χ found γ q :
    (beg0 ≤ beg ≤ end_ ≤ end0)%Z →
    {{{
      pool۰context pool ctx scope ∗
      mvar۰inv found (find۰inv γ Ψ beg0 end0) ∗
      find۰token γ q ∗
      [∗ list] (i : Z) ∈ seqZ beg (end_ - beg),
        ∀ ctx scope,
        pool۰context pool ctx scope -∗
        WP pred ctx #i {{ res,
          ∃ b,
          ⌜res = #b⌝ ∗
          pool۰context pool ctx scope ∗
          if b then
            Ψ i
          else
            Χ i
        }}
    }}}
      algo٠find_seq ctx #beg #end_ pred found
    {{{
      RET ();
      pool۰context pool ctx scope ∗
      ( mvar۰resolved found
      ∨ find۰token γ q ∗
        [∗ list] i ∈ seqZ beg (end_ - beg),
          Χ i
      )
    }}}.
  Proof.
    iIntros "%Hrange %Φ (Hctx & #Hfound_inv & Htoken & Hpred) HΦ".

    iLöb as "HLöb" forall (beg Φ Hrange).

    wp۰rec. wp۰pures.
    case_bool_decide; wp۰pures.

    - iEval (rewrite seqZ_nil; first lia) in "HΦ".
      iSteps.

    - wp۰apply (mvar٠is_unsetｰspec with "[$]") as ([]) "H"; last iSteps.
      iClear "H".

      iDestruct (big_sepLｰseqZｰcons₁ with "Hpred") as "(H & Hpred)"; first lia.
      wp۰apply+ (wpｰwand with "(H Hctx)") as (res) "(%b & -> & Hctx & H)".
      destruct b; wp۰pures.

      + wp۰apply (mvar٠setｰspec with "[$Hfound_inv $Htoken $H]"); first iSteps.
        iSteps.

      + wp۰apply ("HLöb" with "[%] [$] [$] [Hpred]") as "(Hctx & [#Hfound_resolved | (Htoken & HΧ)])"; first lia.
        { iEval (replace (beg + 1)%Z with (Z.succ beg) by lia).
          iEval (replace (end_ - Z.succ beg)%Z with (Z.pred (end_ - beg)) by lia).
          iFrame.
        }

        * iSteps.

        * iDestruct (big_sepLｰseqZｰcons₂ with "HΧ [H]") as "HΧ"; first lia.
          { iEval (replace (Z.pred (beg + 1)) with beg by lia).
            iFrame.
          }
          iEval (replace (Z.pred (beg + 1)) with beg by lia) in "HΧ".
          iEval (replace (Z.succ (end_ - (beg + 1))) with (end_ - beg)%Z by lia) in "HΧ".
          iSteps.
  Qed.
  #[local] Lemma algo٠find₁ｰspec pool ctx scope beg0 beg end_ end0 (chunk : Z) pred Ψ Χ found γ q :
    (beg0 ≤ beg ≤ end_ ≤ end0)%Z →
    {{{
      pool۰context pool ctx scope ∗
      mvar۰inv found (find۰inv γ Ψ beg0 end0) ∗
      find۰token γ q ∗
      [∗ list] (i : Z) ∈ seqZ beg (end_ - beg),
        ∀ ctx scope,
        pool۰context pool ctx scope -∗
        WP pred ctx #i {{ res,
          ∃ b,
          ⌜res = #b⌝ ∗
          pool۰context pool ctx scope ∗
          if b then
            Ψ i
          else
            Χ i
        }}
    }}}
      algo٠find₁ ctx #beg #end_ #chunk pred found
    {{{
      RET ();
      pool۰context pool ctx scope ∗
      ( mvar۰resolved found
      ∨ find۰token γ q ∗
        [∗ list] i ∈ seqZ beg (end_ - beg),
          Χ i
      )
    }}}.
  Proof.
    iIntros "%Hrange %Φ (Hctx & #Hfound_inv & Htoken & Hpred) HΦ".

    iLöb as "HLöb" forall (ctx scope beg end_ q Φ Hrange).

    wp۰rec. wp۰pures.
    case_bool_decide; wp۰pures.

    - iEval (replace (beg + (end_ - beg))%Z with end_ by lia).
      wp۰apply (algo٠find_seqｰspec with "[$Hctx $Hfound_inv $Htoken $Hpred] HΦ"); first done.

    - wp۰apply (mvar٠is_unsetｰspec with "[$]") as ([]) "H"; last iSteps.
      iClear "H".

      iDestruct "Htoken" as "(Htoken_1 & Htoken_2)".

      pose mid : Z := beg + (end_ - beg) `quot` 2.
      iEval (replace (end_ - beg)%Z with ((mid - beg) + (end_ - mid))%Z by lia) in "Hpred".
      iDestruct (big_sepLｰseqZｰapp with "Hpred") as "(Hpred_1 & Hpred_2)"; [naive_solver lia.. |].
      iEval (replace (beg + (mid - beg))%Z with mid by lia) in "Hpred_2".

      wp۰apply+ (future٠asyncｰspec
        ( λ res,
          ⌜res = ()%V⌝ ∗
          ( mvar۰resolved found
          ∨ find۰token γ (q / 2) ∗
            [∗ list] i ∈ seqZ beg (mid - beg),
              Χ i
          )
        )%I
        (λ _, True)%I
        with "[$Hctx Htoken_1 Hpred_1]") as (fut) "(Hctx & #Hfut_inv & Hfut_consumer)".
      { iIntros "{% ctx scope} %ctx %scope Hctx".
        wp۰apply+ ("HLöb" with "[%] [$] [$] Hpred_1"); first naive_solver lia.
        iSteps.
      }

      wp۰apply+ ("HLöb" with "[%] [$] [$] Hpred_2") as "(Hctx & H)"; first naive_solver lia.

      iApply wpｰfupd.
      wp۰apply+ (future٠waitｰspec with "[$]") as (res) "(H£ & Hctx & #Hfut_result)".
      iMod (futureｰinvｰresultｰconsumer' with "H£ Hfut_inv Hfut_result Hfut_consumer") as "((-> & [#Hfound_resolved | (Htoken_1 & HΧ_1)]) & _)"; first iSteps.

      iDestruct "H" as "[#Hfound_resolved | (Htoken_2 & HΧ_2)]"; first iSteps.

      iCombine "Htoken_1 Htoken_2" as "Htoken".

      iDestruct (big_sepLｰseqZｰapp₂ with "HΧ_1 HΧ_2") as "HΧ"; [naive_solver lia.. |].
      iEval (replace (mid - beg + (end_ - mid))%Z with (end_ - beg)%Z by lia) in "HΧ".

      iSteps.
  Qed.
  Lemma algo٠findｰspec' (Ψ Χ : Z → iProp Σ) pool sz ctx scope beg end_ chunk pred :
    (beg ≤ end_)%Z →
    {{{
      pool۰inv pool sz ∗
      pool۰context pool ctx scope ∗
      itype۰option itype۰int chunk ∗
      [∗ list] (i : Z) ∈ seqZ beg (end_ - beg),
        ∀ ctx scope,
        pool۰context pool ctx scope -∗
        WP pred ctx #i {{ res,
          ∃ b,
          ⌜res = #b⌝ ∗
          pool۰context pool ctx scope ∗
          if b then
            Ψ i
          else
            Χ i
        }}
    }}}
      algo٠find ctx #beg #end_ chunk pred
    {{{
      (o : option Z)
    , RET #*@{Z} o : option val;
      pool۰context pool ctx scope ∗
      if o is Some i then
        ⌜beg ≤ i < end_⌝%Z ∗
        Ψ i
      else
        [∗ list] i ∈ seqZ beg (end_ - beg),
          Χ i
    }}}.
  Proof.
    iIntros "% %Φ (#Hpool_inv & Hctx & Hchunk & Hpred) HΦ".

    wp۰rec.
    wp۰apply+ (algo٠adjust_chunkｰspec with "[$]") as "{% chunk} %chunk Hctx".

    iMod (ghost_varｰalloc (ghost_var۰G := algo۰G۰find۰G) ()) as "(%γ & Htoken)".
    wp۰apply+ (mvar٠createｰspec (find۰inv γ Ψ beg end_) with "[//]") as (found) "(#Hfound_inv & Hfound_consumer)".

    wp۰apply+ (algo٠find₁ｰspec with "[$]") as "(Hctx & [#Hfound_resolved | (Htoken & HΧ)])"; first done.

    - wp۰apply+ (mvar٠try_getｰspecｰresolvedｰconsumer with "[$]") as (v) "(:find۰inv)".

      iSpecialize ("HΦ" $! (Some i)).
      iSteps.

    - wp۰apply+ (mvar٠try_getｰspecｰconsumer with "[$]") as ([v |]) "H".

      + iDestruct "H" as "(_ & (:find۰inv =1))".
        iDestruct (ghost_varｰexclusive with "Htoken Htoken_1") as %[].

      + iSpecialize ("HΦ" $! None).
        iSteps.
  Qed.
  Lemma algo٠findｰspecｰnat' (Ψ Χ : nat → iProp Σ) pool sz ctx scope beg end_ chunk pred :
    (0 ≤ beg ≤ end_)%Z →
    {{{
      pool۰inv pool sz ∗
      pool۰context pool ctx scope ∗
      itype۰option itype۰int chunk ∗
      [∗ list] (i : nat) ∈ seq ₊beg ₊(end_ - beg),
        ∀ ctx scope,
        pool۰context pool ctx scope -∗
        WP pred ctx #i {{ res,
          ∃ b,
          ⌜res = #b⌝ ∗
          pool۰context pool ctx scope ∗
          if b then
            Ψ i
          else
            Χ i
        }}
    }}}
      algo٠find ctx #beg #end_ chunk pred
    {{{
      (o : option nat)
    , RET #*@{nat} o : option val;
      pool۰context pool ctx scope ∗
      if o is Some i then
        ⌜beg ≤ i < end_⌝%Z ∗
        Ψ i
      else
        [∗ list] i ∈ seq ₊beg ₊(end_ - beg),
          Χ i
    }}}.
  Proof.
    iIntros "% %Φ (#Hpool_inv & Hctx & Hchunk & Hpred) HΦ".

    wp۰apply (algo٠findｰspec'
      (λ i, Ψ ₊i)
      (λ i, Χ ₊i)
    with "[$Hpool_inv $Hctx $Hchunk Hpred]") as (o) "(Hctx & H)"; first lia.
    { iDestruct (big_sepLｰseqｰtoｰseqZ' with "Hpred") as "Hpred"; [lia.. |].
      iApply (big_sepLｰseqZｰimpl with "Hpred"). iIntros "!> %k % Hpred".
      iEval (rewrite Z2Nat.id; try lia) in "Hpred".
      iSteps.
    }

    iSpecialize ("HΦ" $! (fmap (FMap := option_fmap) Z.to_nat o)).
    destruct o as [i |] => /=.
    - iDestruct "H" as "(% & HΨ)".
      iEval (rewrite Z2Nat.id; try lia) in "HΦ".
      iSteps.
    - iSteps.
      iApply (big_sepLｰseqZｰtoｰseq' with "H"); lia.
  Qed.
  Lemma algo٠findｰspec (Ψ Χ : Z → iProp Σ) pool sz ctx scope beg end_ chunk pred :
    (beg ≤ end_)%Z →
    {{{
      pool۰inv pool sz ∗
      pool۰context pool ctx scope ∗
      itype۰option itype۰int chunk ∗
      □ (
        ∀ ctx scope i,
        pool۰context pool ctx scope -∗
        ⌜beg ≤ i < end_⌝%Z -∗
        WP pred ctx #i {{ res,
          ∃ b,
          ⌜res = #b⌝ ∗
          pool۰context pool ctx scope ∗
          if b then
            Ψ i
          else
            Χ i
        }}
      )
    }}}
      algo٠find ctx #beg #end_ chunk pred
    {{{
      (o : option Z)
    , RET #*@{Z} o : option val;
      pool۰context pool ctx scope ∗
      if o is Some i then
        ⌜beg ≤ i < end_⌝%Z ∗
        Ψ i
      else
        [∗ list] i ∈ seqZ beg (end_ - beg),
          Χ i
    }}}.
  Proof.
    iIntros "% %Φ (#Hpool_inv & Hctx & Hchunk & #Hpred) HΦ".

    wp۰apply (algo٠findｰspec' with "[$Hpool_inv $Hctx $Hchunk] HΦ"); first done.
    { iApply big_sepLｰseqZｰintro.
      iSteps.
    }
  Qed.
  Lemma algo٠findｰspecｰnat (Ψ Χ : nat → iProp Σ) pool sz ctx scope beg end_ chunk pred :
    (0 ≤ beg ≤ end_)%Z →
    {{{
      pool۰inv pool sz ∗
      pool۰context pool ctx scope ∗
      itype۰option itype۰int chunk ∗
      □ (
        ∀ ctx scope (i : nat),
        pool۰context pool ctx scope -∗
        ⌜beg ≤ i < end_⌝%Z -∗
        WP pred ctx #i {{ res,
          ∃ b,
          ⌜res = #b⌝ ∗
          pool۰context pool ctx scope ∗
          if b then
            Ψ i
          else
            Χ i
        }}
      )
    }}}
      algo٠find ctx #beg #end_ chunk pred
    {{{
      (o : option nat)
    , RET #*@{nat} o : option val;
      pool۰context pool ctx scope ∗
      if o is Some i then
        ⌜beg ≤ i < end_⌝%Z ∗
        Ψ i
      else
        [∗ list] i ∈ seq ₊beg ₊(end_ - beg),
          Χ i
    }}}.
  Proof.
    iIntros "% %Φ (#Hpool_inv & Hctx & Hchunk & #Hpred) HΦ".

    wp۰apply (algo٠findｰspecｰnat' with "[$Hpool_inv $Hctx $Hchunk] HΦ"); first done.
    { iApply big_sepLｰseqｰintro.
      iSteps.
    }
  Qed.
End algo۰G.

Require zoo_parabs.algo__opaque.
