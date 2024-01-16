From zebra Require Import
  prelude.
From zebra.language Require Import
  notations
  diaframe.
From zebra.std Require Export
  base.
From zebra Require Import
  options.

Implicit Types δ : nat.
Implicit Types fn : val.

Definition for_upto : val :=
  rec: "for_upto" "beg" "end" "fn" :=
    ifnot: "end" ≤ "beg" then (
      "fn" "beg" ;;
      "for_upto" (#1 + "beg") "end" "fn"
    ).

Notation "'for:' i = beg 'to' _end 'begin' e 'end'" :=
  (for_upto beg _end (λ: i, e))%E
( i at level 1,
  beg, _end, e at level 200,
  format "'[hv' for:  i  =  beg  to  _end  begin  '/  ' '[' e ']'  '/' end ']'"
) : expr_scope.

Section zebra_G.
  Context `{zebra_G : !ZebraG Σ}.

  #[local] Lemma for_upto_spec_stronger beg i δ Ψ _end fn :
    i = (beg + δ)%Z →
    {{{
      ▷ Ψ i δ ∗
      □ (
        ∀ i δ,
        ⌜i = (beg + δ)%Z ∧ (i < _end)%Z⌝ -∗
        Ψ i δ -∗
        WP fn #i {{ res,
          ⌜res = #()⌝ ∗
          ▷ Ψ (1 + i)%Z (S δ)
        }}
      )
    }}}
      for_upto #i #_end fn
    {{{
      RET #();
      Ψ (i `max` _end)%Z (δ + Z.to_nat (_end - i))
    }}}.
  Proof.
    iIntros "%Hi %Φ (HΨ & #Hfn) HΦ".
    remember (Z.to_nat (_end - i)) as ϵ eqn:Hϵ.
    iInduction ϵ as [| ϵ] "IH" forall (i δ Hi Hϵ);
      wp_rec; wp_pure credit:"H£"; wp_pures.
    - assert (i `max` _end = i)%Z as -> by lia. rewrite Nat.add_0_r. iSteps.
    - rewrite bool_decide_eq_false_2; first lia. wp_pures.
      wp_apply (wp_wand with "(Hfn [] HΨ)") as "%res (-> & HΨ)"; first iSteps.
      iMod (lc_fupd_elim_later with "H£ HΨ") as "HΨ".
      wp_smart_apply ("IH" with "[] [] HΨ [HΦ]"); [iSteps.. |].
      assert ((1 + i) `max` _end = i `max` _end)%Z as -> by lia. rewrite -Nat.add_succ_comm //.
  Qed.
  Lemma for_upto_spec_strong Ψ beg _end fn :
    {{{
      ▷ Ψ beg 0 ∗
      □ (
        ∀ i δ,
        ⌜i = (beg + δ)%Z ∧ (i < _end)%Z⌝ -∗
        Ψ i δ -∗
        WP fn #i {{ res,
          ⌜res = #()⌝ ∗
          ▷ Ψ (1 + i)%Z (S δ)
        }}
      )
    }}}
      for_upto #beg #_end fn
    {{{
      RET #();
      Ψ (beg `max` _end)%Z (Z.to_nat (_end - beg))
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #Hfn) HΦ".
    wp_apply (for_upto_spec_stronger beg beg 0 with "[$HΨ $Hfn]"); first lia.
    iSteps.
  Qed.
  Lemma for_upto_spec Ψ beg _end fn :
    (beg ≤ _end)%Z →
    {{{
      ▷ Ψ beg 0 ∗
      □ (
        ∀ i δ,
        ⌜i = (beg + δ)%Z ∧ (i < _end)%Z⌝ -∗
        Ψ i δ -∗
        WP fn #i {{ res,
          ⌜res = #()⌝ ∗
          ▷ Ψ (1 + i)%Z (S δ)
        }}
      )
    }}}
      for_upto #beg #_end fn
    {{{
      RET #();
      Ψ _end (Z.to_nat (_end - beg))
    }}}.
  Proof.
    iIntros "% %Φ H HΦ".
    wp_apply (for_upto_spec_strong Ψ with "H").
    rewrite Z.max_r //.
  Qed.
  Lemma for_upto_spec_strong' Ψ beg _end fn :
    {{{
      ▷ Ψ beg 0 ∗
      ( [∗ list] δ ∈ seq 0 (Z.to_nat (_end - beg)),
        ∀ i,
        ⌜i = (beg + δ)%Z⌝ -∗
        Ψ i δ -∗
        WP fn #i {{ res,
          ⌜res = #()⌝ ∗
          ▷ Ψ (1 + i)%Z (S δ)
        }}
      )
    }}}
      for_upto #beg #_end fn
    {{{
      RET #();
      Ψ (beg `max` _end)%Z (Z.to_nat (_end - beg))
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep (λ _, ?Ξ') _] => set Ξ := Ξ' end.
    pose (Ψ' i δ := (
      Ψ i δ ∗
      [∗ list] ϵ ∈ seq δ (Z.to_nat (_end - beg) - δ), Ξ ϵ
    )%I).
    wp_apply (for_upto_spec_strong Ψ' with "[HΨ Hfn]"); last iSteps.
    rewrite /Ψ' Nat.sub_0_r. iFrame. iIntros "!> %i %δ %Hi (HΨ & HΞ)".
    assert (Z.to_nat (_end - beg) - δ = S $ Z.to_nat (_end - beg) - S δ) as -> by lia.
    iSteps.
  Qed.
  Lemma for_upto_spec' Ψ beg _end fn :
    (beg ≤ _end)%Z →
    {{{
      ▷ Ψ beg 0 ∗
      ( [∗ list] δ ∈ seq 0 (Z.to_nat (_end - beg)),
        ∀ i,
        ⌜i = (beg + δ)%Z⌝ -∗
        Ψ i δ -∗
        WP fn #i {{ res,
          ⌜res = #()⌝ ∗
          ▷ Ψ (1 + i)%Z (S δ)
        }}
      )
    }}}
      for_upto #beg #_end fn
    {{{
      RET #();
      Ψ _end (Z.to_nat (_end - beg))
    }}}.
  Proof.
    iIntros "% %Φ H HΦ".
    wp_apply (for_upto_spec_strong' Ψ with "H").
    rewrite Z.max_r //.
  Qed.
  Lemma for_upto_spec_disentangled Ψ beg _end fn :
    {{{
      □ (
        ∀ i δ,
        ⌜i = (beg + δ)%Z ∧ (i < _end)%Z⌝ -∗
        WP fn #i {{ res,
          ⌜res = #()⌝ ∗
          ▷ Ψ i δ
        }}
      )
    }}}
      for_upto #beg #_end fn
    {{{
      RET #();
      ( [∗ list] δ ∈ seq 0 (Z.to_nat (_end - beg)),
        Ψ (beg + δ)%Z δ
      )
    }}}.
  Proof.
    iIntros "%Φ #Hfn HΦ".
    pose (Ψ' (i : Z) δ := (
      [∗ list] δ' ∈ seq 0 δ, Ψ (beg + δ')%Z δ'
    )%I).
    wp_apply (for_upto_spec_strong Ψ'); last iSteps. iSplit; first iSteps. iIntros "!> %i %δ (%Hi1 & %Hi2) HΨ'".
    wp_apply (wp_wand with "(Hfn [//])") as "%res (-> & HΨ)". iStep.
    rewrite /Ψ' seq_S big_sepL_snoc. iSteps.
  Qed.
  Lemma for_upto_spec_disentangled' Ψ beg _end fn :
    {{{
      ( [∗ list] δ ∈ seq 0 (Z.to_nat (_end - beg)),
        ∀ i,
        ⌜i = (beg + δ)%Z⌝ -∗
        WP fn #i {{ res,
          ⌜res = #()⌝ ∗
          ▷ Ψ i δ
        }}
      )
    }}}
      for_upto #beg #_end fn
    {{{
      RET #();
      ( [∗ list] δ ∈ seq 0 (Z.to_nat (_end - beg)),
        Ψ (beg + δ)%Z δ
      )
    }}}.
  Proof.
    iIntros "%Φ Hfn HΦ".
    pose (Ψ' (i : Z) δ := (
      [∗ list] δ' ∈ seq 0 δ, Ψ (beg + δ')%Z δ'
    )%I).
    wp_apply (for_upto_spec_strong' Ψ' with "[Hfn]"); last iSteps. iSplit; first iSteps.
    iApply (big_sepL_impl with "Hfn"). iIntros "!>" (δ δ_ (-> & Hδ)%lookup_seq) "Hfn %i -> HΨ' /=".
    wp_apply (wp_wand with "(Hfn [//])") as "%res (-> & HΨ)". iStep.
    rewrite /Ψ' seq_S big_sepL_snoc. iSteps.
  Qed.

  Lemma for_upto_spec_nat_strong Ψ beg _end fn :
    {{{
      ▷ Ψ beg 0 ∗
      □ (
        ∀ i δ,
        ⌜i = (beg + δ)%nat ∧ i < _end⌝ -∗
        Ψ i δ -∗
        WP fn #i {{ res,
          ⌜res = #()⌝ ∗
          ▷ Ψ (S i) (S δ)
        }}
      )
    }}}
      for_upto #beg #_end fn
    {{{
      RET #();
      Ψ (beg `max` _end) (_end - beg)
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #Hfn) HΦ".
    pose Ψ' i δ :=
      Ψ (Z.to_nat i) δ.
    wp_apply (for_upto_spec_strong Ψ' with "[HΨ]").
    - rewrite /Ψ' !Nat2Z.id. iFrame. iIntros "!> %i %δ (-> & %Hδ) HΨ".
      rewrite -Nat2Z.inj_add Z.add_1_l -Nat2Z.inj_succ !Nat2Z.id. iSteps.
    - rewrite /Ψ' -Nat2Z.inj_max Z2Nat.inj_sub; first lia. rewrite !Nat2Z.id //.
  Qed.
  Lemma for_upto_spec_nat Ψ beg _end fn :
    beg ≤ _end →
    {{{
      ▷ Ψ beg 0 ∗
      □ (
        ∀ i δ,
        ⌜i = (beg + δ)%nat ∧ i < _end⌝ -∗
        Ψ i δ -∗
        WP fn #i {{ res,
          ⌜res = #()⌝ ∗
          ▷ Ψ (S i) (S δ)
        }}
      )
    }}}
      for_upto #beg #_end fn
    {{{
      RET #();
      Ψ _end (_end - beg)
    }}}.
  Proof.
    iIntros "% %Φ H HΦ".
    wp_apply (for_upto_spec_nat_strong Ψ with "H").
    rewrite Nat.max_r //.
  Qed.
  Lemma for_upto_spec_nat_strong' Ψ beg _end fn :
    {{{
      ▷ Ψ beg 0 ∗
      ( [∗ list] δ ∈ seq 0 (_end - beg),
        ∀ i,
        ⌜i = (beg + δ)%nat⌝ -∗
        Ψ i δ -∗
        WP fn #i {{ res,
          ⌜res = #()⌝ ∗
          ▷ Ψ (S i) (S δ)
        }}
      )
    }}}
      for_upto #beg #_end fn
    {{{
      RET #();
      Ψ (beg `max` _end) (_end - beg)
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hfn) HΦ".
    pose Ψ' i δ :=
      Ψ (Z.to_nat i) δ.
    wp_apply (for_upto_spec_strong' Ψ' with "[HΨ Hfn]").
    - rewrite /Ψ' !Nat2Z.id Z2Nat.inj_sub; first lia. rewrite !Nat2Z.id. iFrame.
      iApply (big_sepL_impl with "Hfn"). iIntros "!>" (δ δ_ (-> & Hδ)%lookup_seq) "Hfn %i -> HΨ /=".
      rewrite -Nat2Z.inj_add Nat2Z.id Z.add_1_l -Nat2Z.inj_succ Nat2Z.id. iSteps.
    - rewrite /Ψ' -Nat2Z.inj_max Z2Nat.inj_sub; first lia. rewrite !Nat2Z.id //.
  Qed.
  Lemma for_upto_spec_nat' Ψ beg _end fn :
    beg ≤ _end →
    {{{
      ▷ Ψ beg 0 ∗
      ( [∗ list] δ ∈ seq 0 (_end - beg),
        ∀ i,
        ⌜i = (beg + δ)%nat⌝ -∗
        Ψ i δ -∗
        WP fn #i {{ res,
          ⌜res = #()⌝ ∗
          ▷ Ψ (S i) (S δ)
        }}
      )
    }}}
      for_upto #beg #_end fn
    {{{
      RET #();
      Ψ _end (_end - beg)
    }}}.
  Proof.
    iIntros "% %Φ H HΦ".
    wp_apply (for_upto_spec_nat_strong' Ψ with "H").
    rewrite Nat.max_r //.
  Qed.
  Lemma for_upto_spec_disentangled_nat Ψ beg _end fn :
    {{{
      □ (
        ∀ i δ,
        ⌜i = (beg + δ)%nat ∧ i < _end⌝ -∗
        WP fn #i {{ res,
          ⌜res = #()⌝ ∗
          ▷ Ψ i δ
        }}
      )
    }}}
      for_upto #beg #_end fn
    {{{
      RET #();
      ( [∗ list] δ ∈ seq 0 (_end - beg),
        Ψ (beg + δ) δ
      )
    }}}.
  Proof.
    iIntros "%Φ #Hfn HΦ".
    pose Ψ' i δ :=
      Ψ (Z.to_nat i) δ.
    wp_apply (for_upto_spec_disentangled Ψ').
    - iIntros "!> %i %δ (-> & %Hδ)".
      rewrite -Nat2Z.inj_add /Ψ' Nat2Z.id. iSteps.
    - rewrite /Ψ' Z2Nat.inj_sub; first lia. rewrite !Nat2Z.id.
      setoid_rewrite <- Nat2Z.inj_add. setoid_rewrite Nat2Z.id.
      iSteps.
  Qed.
  Lemma for_upto_spec_disentangled_nat' Ψ beg _end fn :
    {{{
      ( [∗ list] δ ∈ seq 0 (_end - beg),
        ∀ i,
        ⌜i = (beg + δ)%nat⌝ -∗
        WP fn #i {{ res,
          ⌜res = #()⌝ ∗
          ▷ Ψ i δ
        }}
      )
    }}}
      for_upto #beg #_end fn
    {{{
      RET #();
      ( [∗ list] δ ∈ seq 0 (_end - beg),
        Ψ (beg + δ) δ
      )
    }}}.
  Proof.
    iIntros "%Φ Hfn HΦ".
    pose Ψ' i δ :=
      Ψ (Z.to_nat i) δ.
    wp_apply (for_upto_spec_disentangled' Ψ' with "[Hfn]").
    - rewrite Z2Nat.inj_sub; first lia. rewrite !Nat2Z.id.
      iApply (big_sepL_impl with "Hfn"). iIntros "!>" (δ δ_ (-> & Hδ)%lookup_seq) "Hfn %i -> /=".
      rewrite -Nat2Z.inj_add /Ψ' Nat2Z.id. iSteps.
    - rewrite /Ψ' Z2Nat.inj_sub; first lia. rewrite !Nat2Z.id.
      setoid_rewrite <- Nat2Z.inj_add. setoid_rewrite Nat2Z.id.
      iSteps.
  Qed.

  Lemma for_upto_type τ `{!iType (iProp Σ) τ} beg _end fn :
    {{{
      (int_range_type beg _end --> unit_type)%T fn
    }}}
      for_upto #beg #_end fn
    {{{
      RET #(); True
    }}}.
  Proof.
    iIntros "%Φ #Hfn HΦ".
    wp_apply (for_upto_spec_disentangled (λ _ _, True%I)); iSteps.
  Qed.
End zebra_G.

#[global] Opaque for_upto.
