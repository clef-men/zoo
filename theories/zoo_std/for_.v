From zoo Require Import
  prelude.
From zoo.iris.bi Require Import
  big_op.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
  base.
From zoo Require Import
  options.

Implicit Types δ : nat.
Implicit Types body : expr.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  #[local] Lemma for𑁒spec_stronger beg i δ Ψ _end body :
    i = (beg + δ)%Z →
    {{{
      ▷ Ψ i δ ∗
      □ (
        ∀ i δ,
        ⌜i = (beg + δ)%Z⌝ -∗
        ⌜i < _end⌝%Z -∗
        Ψ i δ -∗
        WP body #i {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ (i + 1)%Z (S δ)
        }}
      )
    }}}
      For #i #_end body
    {{{
      RET ();
      Ψ (i `max` _end)%Z (δ + ₊(_end - i))
    }}}.
  Proof.
    iIntros "%Hi %Φ (HΨ & #Hbody) HΦ".
    remember ₊(_end - i) as ϵ eqn:Hϵ.
    iInduction ϵ as [| ϵ] "IH" forall (i δ Hi Hϵ).
    all: wp_for credit:"H£".
    - rewrite decide_True; first lia.
      assert (i `max` _end = i)%Z as -> by lia.
      rewrite Nat.add_0_r. iSteps.
    - rewrite decide_False; first lia.
      wp_apply (wp_wand with "(Hbody [//] [%] HΨ)") as "%res (-> & HΨ)"; first lia.
      iMod (lc_fupd_elim_later with "H£ HΨ") as "HΨ".
      wp_apply+ ("IH" with "[] [] HΨ [HΦ]"); [iSteps.. |].
      assert ((i + 1) `max` _end = i `max` _end)%Z as -> by lia. rewrite -Nat.add_succ_comm //.
  Qed.
  Lemma for𑁒spec_strong Ψ beg _end body :
    {{{
      ▷ Ψ beg 0 ∗
      □ (
        ∀ i δ,
        ⌜i = (beg + δ)%Z⌝ -∗
        ⌜i < _end⌝%Z -∗
        Ψ i δ -∗
        WP body #i {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ (i + 1)%Z (S δ)
        }}
      )
    }}}
      For #beg #_end body
    {{{
      RET ();
      Ψ (beg `max` _end)%Z ₊(_end - beg)
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #Hbody) HΦ".
    wp_apply (for𑁒spec_stronger with "[$HΨ $Hbody]"); first lia.
    iSteps.
  Qed.
  Lemma for𑁒spec Ψ beg _end body :
    (beg ≤ _end)%Z →
    {{{
      ▷ Ψ beg 0 ∗
      □ (
        ∀ i δ,
        ⌜i = (beg + δ)%Z⌝ -∗
        ⌜i < _end⌝%Z -∗
        Ψ i δ -∗
        WP body #i {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ (i + 1)%Z (S δ)
        }}
      )
    }}}
      For #beg #_end body
    {{{
      RET ();
      Ψ _end ₊(_end - beg)
    }}}.
  Proof.
    iIntros "% %Φ H HΦ".
    wp_apply (for𑁒spec_strong Ψ with "H").
    rewrite Z.max_r //.
  Qed.
  Lemma for𑁒spec_strong' Ψ beg _end body :
    {{{
      ▷ Ψ beg 0 ∗
      ( [∗ list] δ ∈ seq 0 ₊(_end - beg),
        ∀ i,
        ⌜i = (beg + δ)%Z⌝ -∗
        Ψ i δ -∗
        WP body #i {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ (i + 1)%Z (S δ)
        }}
      )
    }}}
      For #beg #_end body
    {{{
      RET ();
      Ψ (beg `max` _end)%Z ₊(_end - beg)
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hbody) HΦ".
    match goal with |- context [big_opL bi_sep (λ _, ?Ξ') _] => set Ξ := Ξ' end.
    pose (Ψ' i δ := (
      Ψ i δ ∗
      [∗ list] ϵ ∈ seq δ (₊(_end - beg) - δ), Ξ ϵ
    )%I).
    wp_apply (for𑁒spec_strong Ψ' with "[HΨ Hbody]"); last iSteps.
    rewrite /Ψ' Nat.sub_0_r. iFrame. iIntros "!> %i %δ %Hi1 %Hi2 (HΨ & HΞ)".
    assert (₊(_end - beg) - δ = S $ ₊(_end - beg) - S δ) as -> by lia.
    iSteps.
  Qed.
  Lemma for𑁒spec' Ψ beg _end body :
    (beg ≤ _end)%Z →
    {{{
      ▷ Ψ beg 0 ∗
      ( [∗ list] δ ∈ seq 0 ₊(_end - beg),
        ∀ i,
        ⌜i = (beg + δ)%Z⌝ -∗
        Ψ i δ -∗
        WP body #i {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ (i + 1)%Z (S δ)
        }}
      )
    }}}
      For #beg #_end body
    {{{
      RET ();
      Ψ _end ₊(_end - beg)
    }}}.
  Proof.
    iIntros "% %Φ H HΦ".
    wp_apply (for𑁒spec_strong' Ψ with "H").
    rewrite Z.max_r //.
  Qed.
  Lemma for𑁒spec_disentangled Ψ beg _end body :
    {{{
      □ (
        ∀ i δ,
        ⌜i = (beg + δ)%Z⌝ -∗
        ⌜i < _end⌝%Z -∗
        WP body #i {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i δ
        }}
      )
    }}}
      For #beg #_end body
    {{{
      RET ();
      ( [∗ list] δ ∈ seq 0 ₊(_end - beg),
        Ψ (beg + δ)%Z δ
      )
    }}}.
  Proof.
    iIntros "%Φ #Hbody HΦ".
    pose (Ψ' (i : Z) δ := (
      [∗ list] δ' ∈ seq 0 δ, Ψ (beg + δ')%Z δ'
    )%I).
    wp_apply (for𑁒spec_strong Ψ'); last iSteps. iSplit; first iSteps. iIntros "!> %i %δ %Hi1 %Hi2 HΨ'".
    wp_apply (wp_wand with "(Hbody [//] [//])") as "%res (-> & HΨ)".
    iStep.
    rewrite /Ψ' seq_S big_sepL_snoc Hi1. iSteps.
  Qed.
  Lemma for𑁒spec_disentangled' Ψ beg _end body :
    {{{
      ( [∗ list] δ ∈ seq 0 ₊(_end - beg),
        ∀ i,
        ⌜i = (beg + δ)%Z⌝ -∗
        WP body #i {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i δ
        }}
      )
    }}}
      For #beg #_end body
    {{{
      RET ();
      ( [∗ list] δ ∈ seq 0 ₊(_end - beg),
        Ψ (beg + δ)%Z δ
      )
    }}}.
  Proof.
    iIntros "%Φ Hbody HΦ".
    pose (Ψ' (i : Z) δ := (
      [∗ list] δ' ∈ seq 0 δ, Ψ (beg + δ')%Z δ'
    )%I).
    wp_apply (for𑁒spec_strong' Ψ' with "[Hbody]"); last iSteps. iSplit; first iSteps.
    iApply (big_sepL_seq_impl with "Hbody"). iIntros "!> %δ %Hδ Hbody %i -> HΨ' /=".
    wp_apply (wp_wand with "(Hbody [//])") as "%res (-> & HΨ)".
    iStep.
    rewrite /Ψ' seq_S big_sepL_snoc. iSteps.
  Qed.

  Lemma for𑁒spec_nat_strong Ψ beg _end body :
    {{{
      ▷ Ψ beg 0 ∗
      □ (
        ∀ i δ,
        ⌜i = (beg + δ)%nat⌝ -∗
        ⌜i < _end⌝ -∗
        Ψ i δ -∗
        WP body #i {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ (S i) (S δ)
        }}
      )
    }}}
      For #beg #_end body
    {{{
      RET ();
      Ψ (beg `max` _end) (_end - beg)
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #Hbody) HΦ".
    pose Ψ' i δ :=
      Ψ ₊i δ.
    wp_apply (for𑁒spec_strong Ψ' with "[HΨ]").
    - rewrite /Ψ' !Nat2Z.id. iFrame. iIntros "!> %i %δ -> %Hδ HΨ".
      rewrite -Nat2Z.inj_add Z.add_1_r -Nat2Z.inj_succ !Nat2Z.id. iSteps.
    - rewrite /Ψ' -Nat2Z.inj_max Z2Nat.inj_sub; first lia. rewrite !Nat2Z.id //.
  Qed.
  Lemma for𑁒spec_nat Ψ beg _end body :
    beg ≤ _end →
    {{{
      ▷ Ψ beg 0 ∗
      □ (
        ∀ i δ,
        ⌜i = (beg + δ)%nat⌝ -∗
        ⌜i < _end⌝ -∗
        Ψ i δ -∗
        WP body #i {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ (S i) (S δ)
        }}
      )
    }}}
      For #beg #_end body
    {{{
      RET ();
      Ψ _end (_end - beg)
    }}}.
  Proof.
    iIntros "% %Φ H HΦ".
    wp_apply (for𑁒spec_nat_strong Ψ with "H").
    rewrite Nat.max_r //.
  Qed.
  Lemma for𑁒spec_nat_strong' Ψ beg _end body :
    {{{
      ▷ Ψ beg 0 ∗
      ( [∗ list] δ ∈ seq 0 (_end - beg),
        ∀ i,
        ⌜i = (beg + δ)%nat⌝ -∗
        Ψ i δ -∗
        WP body #i {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ (S i) (S δ)
        }}
      )
    }}}
      For #beg #_end body
    {{{
      RET ();
      Ψ (beg `max` _end) (_end - beg)
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hbody) HΦ".
    pose Ψ' i δ :=
      Ψ ₊i δ.
    wp_apply (for𑁒spec_strong' Ψ' with "[HΨ Hbody]").
    - rewrite /Ψ' !Nat2Z.id Z2Nat.inj_sub; first lia. rewrite !Nat2Z.id. iFrame.
      iApply (big_sepL_seq_impl with "Hbody"). iIntros "!> %δ %Hδ Hbody %i -> HΨ /=".
      rewrite -Nat2Z.inj_add Nat2Z.id Z.add_1_r -Nat2Z.inj_succ Nat2Z.id. iSteps.
    - rewrite /Ψ' -Nat2Z.inj_max Z2Nat.inj_sub; first lia. rewrite !Nat2Z.id //.
  Qed.
  Lemma for𑁒spec_nat' Ψ beg _end body :
    beg ≤ _end →
    {{{
      ▷ Ψ beg 0 ∗
      ( [∗ list] δ ∈ seq 0 (_end - beg),
        ∀ i,
        ⌜i = (beg + δ)%nat⌝ -∗
        Ψ i δ -∗
        WP body #i {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ (S i) (S δ)
        }}
      )
    }}}
      For #beg #_end body
    {{{
      RET ();
      Ψ _end (_end - beg)
    }}}.
  Proof.
    iIntros "% %Φ H HΦ".
    wp_apply (for𑁒spec_nat_strong' Ψ with "H").
    rewrite Nat.max_r //.
  Qed.
  Lemma for𑁒spec_disentangled_nat Ψ beg _end body :
    {{{
      □ (
        ∀ i δ,
        ⌜i = (beg + δ)%nat⌝ -∗
        ⌜i < _end⌝ -∗
        WP body #i {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i δ
        }}
      )
    }}}
      For #beg #_end body
    {{{
      RET ();
      ( [∗ list] δ ∈ seq 0 (_end - beg),
        Ψ (beg + δ) δ
      )
    }}}.
  Proof.
    iIntros "%Φ #Hbody HΦ".
    pose Ψ' i δ :=
      Ψ ₊i δ.
    wp_apply (for𑁒spec_disentangled Ψ').
    - iIntros "!> %i %δ -> %Hδ".
      rewrite -Nat2Z.inj_add /Ψ' Nat2Z.id. iSteps.
    - rewrite /Ψ' Z2Nat.inj_sub; first lia. rewrite !Nat2Z.id.
      setoid_rewrite <- Nat2Z.inj_add. setoid_rewrite Nat2Z.id.
      iSteps.
  Qed.
  Lemma for𑁒spec_disentangled_nat' Ψ beg _end body :
    {{{
      ( [∗ list] δ ∈ seq 0 (_end - beg),
        ∀ i,
        ⌜i = (beg + δ)%nat⌝ -∗
        WP body #i {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i δ
        }}
      )
    }}}
      For #beg #_end body
    {{{
      RET ();
      ( [∗ list] δ ∈ seq 0 (_end - beg),
        Ψ (beg + δ) δ
      )
    }}}.
  Proof.
    iIntros "%Φ Hbody HΦ".
    pose Ψ' i δ :=
      Ψ ₊i δ.
    wp_apply (for𑁒spec_disentangled' Ψ' with "[Hbody]").
    - rewrite Z2Nat.inj_sub; first lia. rewrite !Nat2Z.id.
      iApply (big_sepL_seq_impl with "Hbody"). iIntros "!> %δ %Hδ Hbody %i -> /=".
      rewrite -Nat2Z.inj_add /Ψ' Nat2Z.id. iSteps.
    - rewrite /Ψ' Z2Nat.inj_sub; first lia. rewrite !Nat2Z.id.
      setoid_rewrite <- Nat2Z.inj_add. setoid_rewrite Nat2Z.id.
      iSteps.
  Qed.

  Lemma for𑁒type τ `{!iType (iProp Σ) τ} x beg _end body :
    {{{
      (itype_int_range beg _end --> itype_unit)%T (fun: x => body)
    }}}
      for: x := #beg to #_end begin body end
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ #Hbody HΦ".
    wp_apply (for𑁒spec_disentangled (λ _ _, True%I)); last iSteps. iIntros "!> %i %δ %Hi1 %Hi2".
    wp_apply+ (wp_wand with "(Hbody [])"); iSteps.
  Qed.
End zoo_G.
