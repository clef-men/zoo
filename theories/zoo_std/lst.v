From zoo Require Import
  prelude.
From zoo.language Require Import
  notations
  diaframe.
From zoo_std Require Export
  base
  lst__code.
From zoo Require Import
  options.

Implicit Types i j : nat.
Implicit Types v w t fn acc : val.
Implicit Types vs vs_left vs_right ws : list val.

Fixpoint plst_to_val nil vs :=
  match vs with
  | [] =>
      nil
  | v :: vs =>
      (v :: plst_to_val nil vs)%V
  end.
#[global] Arguments plst_to_val _ !_ : assert.

#[global] Instance plst_to_val_physical nil vs :
  ValPhysical nil →
  ValPhysical (plst_to_val nil vs).
Proof.
  destruct vs; done.
Qed.

Lemma plst_to_val_nil nil :
  plst_to_val nil [] = nil.
Proof.
  done.
Qed.
Lemma plst_to_val_cons nil v vs :
  plst_to_val nil (v :: vs) = (v :: plst_to_val nil vs)%V.
Proof.
  done.
Qed.
Lemma plst_to_val_singleton nil v :
  plst_to_val nil [v] = (v :: nil)%V.
Proof.
  apply plst_to_val_cons.
Qed.
Lemma plst_to_val_app vs1 nil vs2 :
  plst_to_val (plst_to_val nil vs2) vs1 = plst_to_val nil (vs1 ++ vs2).
Proof.
  induction vs1; first done.
  simpl. do 3 f_equal. done.
Qed.

Fixpoint lst_to_val vs :=
  match vs with
  | [] =>
      []%V
  | v :: vs =>
      (v :: lst_to_val vs)%V
  end.
#[global] Arguments lst_to_val !_ : assert.

Lemma lst_to_val_plst_to_val vs :
  lst_to_val vs = plst_to_val [] vs.
Proof.
  induction vs as [| v vs IH]; first done.
  rewrite /= IH //.
Qed.

#[global] Instance lst_to_val_inj' :
  Inj (=) val_eq lst_to_val.
Proof.
  intros vs1. induction vs1 as [| v1 vs1 IH]; intros [| v2 vs2]; [naive_solver.. |].
  intros (_ & _ & [= -> ->%val_eq_refl%IH]) => //.
Qed.
#[global] Instance lst_to_val_inj :
  Inj (=) (=) lst_to_val.
Proof.
  intros ?* ->%val_eq_refl%(inj _) => //.
Qed.
#[global] Instance lst_to_val_physical vs :
  ValPhysical (lst_to_val vs).
Proof.
  rewrite lst_to_val_plst_to_val.
  apply plst_to_val_physical. done.
Qed.

Lemma lst_to_val_nil :
  lst_to_val [] = []%V.
Proof.
  rewrite lst_to_val_plst_to_val.
  apply plst_to_val_nil.
Qed.
Lemma lst_to_val_cons v vs :
  lst_to_val (v :: vs) = (v :: lst_to_val vs)%V.
Proof.
  rewrite !lst_to_val_plst_to_val.
  apply plst_to_val_cons.
Qed.
Lemma lst_to_val_singleton v :
  lst_to_val [v] = (v :: [])%V.
Proof.
  rewrite lst_to_val_plst_to_val.
  apply plst_to_val_singleton.
Qed.
Lemma lst_to_val_app vs1 vs2 :
  plst_to_val (lst_to_val vs2) vs1 = lst_to_val (vs1 ++ vs2).
Proof.
  rewrite !lst_to_val_plst_to_val.
  apply plst_to_val_app.
Qed.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition plst_model' t nil vs :=
    t = plst_to_val nil vs.
  Definition plst_model t nil vs : iProp Σ :=
    ⌜plst_model' t nil vs⌝.

  Definition lst_model' t vs :=
    t = lst_to_val vs.
  Definition lst_model t vs : iProp Σ :=
    ⌜lst_model' t vs⌝.

  Lemma lst_model'_plst_model' t vs :
    lst_model' t vs ↔
    plst_model' t [] vs.
  Proof.
    rewrite /lst_model' lst_to_val_plst_to_val //.
  Qed.

  Lemma lst_singleton_spec v :
    {{{
      True
    }}}
      lst_singleton v
    {{{ t,
      RET t;
      lst_model t [v]
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma lst_head_spec {t vs} v vs' :
    vs = v :: vs' →
    {{{
      lst_model t vs
    }}}
      lst_head t
    {{{
      RET v;
      True
    }}}.
  Proof.
    rewrite /lst_model /lst_model'. iSteps.
  Qed.

  Lemma lst_tail_spec {t vs} v vs' :
    vs = v :: vs' →
    {{{
      lst_model t vs
    }}}
      lst_tail t
    {{{ t',
      RET t';
      lst_model t' vs'
    }}}.
  Proof.
    rewrite /lst_model /lst_model'. iSteps.
  Qed.

  Lemma lst_is_empty_spec t vs :
    {{{
      lst_model t vs
    }}}
      lst_is_empty t
    {{{
      RET #(bool_decide (vs = []%list));
      True
    }}}.
  Proof.
    iIntros "%Φ -> HΦ".
    destruct vs; iSteps.
  Qed.

  Lemma lst_get_spec v t (i : Z) vs :
    vs !! Z.to_nat i = Some v →
    {{{
      lst_model t vs
    }}}
      lst_get t #i
    {{{
      RET v;
      True
    }}}.
  Proof.
    remember (Z.to_nat i) as j eqn:Hj.
    iInduction j as [| j] "IH" forall (t i vs Hj).
    all: iIntros "%Hlookup %Φ %Ht HΦ".
    all: pose proof Hlookup as Hi%lookup_lt_Some.
    all: destruct vs as [| v' vs]; simpl in Hi; first lia.
    all: wp_rec; wp_pures.
    - rewrite bool_decide_eq_true_2; first lia. wp_pures.
      wp_apply lst_head_spec; [done | iSteps |].
      apply (inj Some) in Hlookup as ->. iSteps.
    - rewrite bool_decide_eq_false_2; first lia. wp_pures.
      wp_apply lst_tail_spec as "%t' %Ht'"; [done | iSteps |].
      wp_apply ("IH" with "[] [//] [//] HΦ").
      iSteps.
  Qed.

  #[local] Lemma lst_initi_aux_spec vs_left Ψ sz fn i :
    i ≤ Z.to_nat sz →
    i = length vs_left →
    {{{
      ▷ Ψ i vs_left ∗
      □ (
        ∀ i vs,
        ⌜i < Z.to_nat sz ∧ i = length vs⌝ -∗
        Ψ i vs -∗
        WP fn #i {{ v,
          ▷ Ψ (S i) (vs ++ [v])
        }}
      )
    }}}
      lst_initi_aux #sz fn #i
    {{{ t vs_right,
      RET t;
      ⌜(length vs_left + length vs_right)%nat = Z.to_nat sz⌝ ∗
      lst_model t vs_right ∗
      Ψ (Z.to_nat sz) (vs_left ++ vs_right)
    }}}.
  Proof.
    remember (Z.to_nat sz - i) as j eqn:Hj.
    iInduction j as [| j] "IH" forall (vs_left i Hj).
    all: iIntros "%Hi1 %Hi2 %Φ (HΨ & #Hfn) HΦ".
    all: wp_rec; wp_pures.
    - rewrite bool_decide_eq_true_2; first lia. wp_pures.
      iApply ("HΦ" $! _ []).
      rewrite !right_id. assert (Z.to_nat sz = i) as <- by lia. iSteps.
    - rewrite bool_decide_eq_false_2; first lia. wp_pures.
      wp_apply (wp_wand with "(Hfn [] HΨ)") as "%v HΨ"; first iSteps.
      wp_pures.
      rewrite Z.add_1_r -Nat2Z.inj_succ.
      wp_apply ("IH" $! (vs_left ++ [v]) (S i) with "[] [] [] [$HΨ //]"); rewrite ?length_app /=; [iSteps.. |].
      iIntros "%t %vs_right (%Hvs_right & %Ht & HΨ)". rewrite {}Ht.
      wp_pures.
      iApply ("HΦ" $! _ (v :: vs_right)).
      rewrite -assoc. iSteps.
  Qed.
  Lemma lst_initi_spec Ψ sz fn :
    {{{
      ▷ Ψ 0 [] ∗
      □ (
        ∀ i vs,
        ⌜i < Z.to_nat sz ∧ i = length vs⌝ -∗
        Ψ i vs -∗
        WP fn #i {{ v,
          ▷ Ψ (S i) (vs ++ [v])
        }}
      )
    }}}
      lst_initi #sz fn
    {{{ t vs,
      RET t;
      ⌜length vs = Z.to_nat sz⌝ ∗
      lst_model t vs ∗
      Ψ (Z.to_nat sz) vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (lst_initi_aux_spec [] Ψ with "[$HΨ $Hfn] HΦ"); simpl; lia.
  Qed.
  Lemma lst_initi_spec' Ψ sz fn :
    {{{
      ▷ Ψ 0 [] ∗
      ( [∗ list] i ∈ seq 0 (Z.to_nat sz),
        ∀ vs,
        ⌜i = length vs⌝ -∗
        Ψ i vs -∗
        WP fn #i {{ v,
          ▷ Ψ (S i) (vs ++ [v])
        }}
      )
    }}}
      lst_initi #sz fn
    {{{ t vs,
      RET t;
      ⌜length vs = Z.to_nat sz⌝ ∗
      lst_model t vs ∗
      Ψ (Z.to_nat sz) vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep (λ _, ?Ξ') _] => set Ξ := Ξ' end.
    pose (Ψ' i vs := (
      Ψ i vs ∗
      [∗ list] j ∈ seq i (Z.to_nat sz - i), Ξ j
    )%I).
    wp_apply (lst_initi_spec Ψ' with "[$HΨ Hfn]"); last iSteps.
    rewrite Nat.sub_0_r. iFrame. iIntros "!> %i %vs (%Hi1 & %Hi2) (HΨ & HΞ)".
    destruct (Nat.lt_exists_pred 0 (Z.to_nat sz - i)) as (k & Hk & _); first lia. rewrite Hk.
    rewrite -cons_seq. iDestruct "HΞ" as "(Hfn & HΞ)".
    wp_apply (wp_wand with "(Hfn [//] HΨ)"). iSteps.
    rewrite Nat.sub_succ_r Hk //.
  Qed.
  Lemma lst_initi_spec_disentangled Ψ sz fn :
    {{{
      □ (
        ∀ i,
        ⌜i < Z.to_nat sz⌝ -∗
        WP fn #i {{ v,
          ▷ Ψ i v
        }}
      )
    }}}
      lst_initi #sz fn
    {{{ t vs,
      RET t;
      ⌜length vs = Z.to_nat sz⌝ ∗
      lst_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ #Hfn HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp_apply (lst_initi_spec Ψ'); last iSteps.
    rewrite /Ψ'. iSteps.
    rewrite big_sepL_snoc. iSteps.
  Qed.
  Lemma lst_initi_spec_disentangled' Ψ sz fn :
    {{{
      [∗ list] i ∈ seq 0 (Z.to_nat sz),
        WP fn #i {{ v,
          ▷ Ψ i v
        }}
    }}}
      lst_initi #sz fn
    {{{ t vs,
      RET t;
      ⌜length vs = Z.to_nat sz⌝ ∗
      lst_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ Hfn HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp_apply (lst_initi_spec' Ψ' with "[Hfn]"); last iSteps.
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn"). iSteps.
    rewrite big_sepL_snoc. iSteps.
  Qed.

  Lemma lst_init_spec Ψ sz fn :
    {{{
      ▷ Ψ 0 [] ∗
      □ (
        ∀ i vs,
        ⌜i < Z.to_nat sz ∧ i = length vs⌝ -∗
        Ψ i vs -∗
        WP fn () {{ v,
          ▷ Ψ (S i) (vs ++ [v])
        }}
      )
    }}}
      lst_init #sz fn
    {{{ t vs,
      RET t;
      ⌜length vs = Z.to_nat sz⌝ ∗
      lst_model t vs ∗
      Ψ (Z.to_nat sz) vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (lst_initi_spec Ψ with "[$HΨ] HΦ").
    iSteps.
  Qed.
  Lemma lst_init_spec' Ψ sz fn :
    {{{
      ▷ Ψ 0 [] ∗
      ( [∗ list] i ∈ seq 0 (Z.to_nat sz),
        ∀ vs,
        ⌜i = length vs⌝ -∗
        Ψ i vs -∗
        WP fn () {{ v,
          ▷ Ψ (S i) (vs ++ [v])
        }}
      )
    }}}
      lst_init #sz fn
    {{{ t vs,
      RET t;
      ⌜length vs = Z.to_nat sz⌝ ∗
      lst_model t vs ∗
      Ψ (Z.to_nat sz) vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (lst_initi_spec' Ψ with "[$HΨ Hfn] HΦ").
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.
  Lemma lst_init_spec_disentangled Ψ sz fn :
    {{{
      □ (
        ∀ i,
        ⌜i < Z.to_nat sz⌝ -∗
        WP fn () {{ v,
          ▷ Ψ i v
        }}
      )
    }}}
      lst_init #sz fn
    {{{ t vs,
      RET t;
      ⌜length vs = Z.to_nat sz⌝ ∗
      lst_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ #Hfn HΦ".
    wp_rec.
    wp_smart_apply (lst_initi_spec_disentangled Ψ with "[] HΦ").
    iSteps.
  Qed.
  Lemma lst_init_spec_disentangled' Ψ sz fn :
    {{{
      [∗ list] i ∈ seq 0 (Z.to_nat sz),
        WP fn () {{ v,
          ▷ Ψ i v
        }}
    }}}
      lst_init #sz fn
    {{{ t vs,
      RET t;
      ⌜length vs = Z.to_nat sz⌝ ∗
      lst_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ Hfn HΦ".
    wp_rec.
    wp_smart_apply (lst_initi_spec_disentangled' Ψ with "[Hfn] HΦ").
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  #[local] Lemma lst_foldli_aux_spec vs_left Ψ vs fn i acc t vs_right :
    vs = vs_left ++ vs_right →
    i = length vs_left →
    {{{
      ▷ Ψ i vs_left acc ∗
      lst_model t vs_right ∗
      □ (
        ∀ i v acc,
        ⌜vs !! i = Some v⌝ -∗
        Ψ i (take i vs) acc -∗
        WP fn #i acc v {{ acc,
          ▷ Ψ (S i) (take i vs ++ [v]) acc
        }}
      )
    }}}
      lst_foldli_aux fn #i acc t
    {{{ acc,
      RET acc;
      Ψ (length vs) vs acc
    }}}.
  Proof.
    iInduction vs_right as [| v vs_right] "IH" forall (vs_left acc i t).
    all: iIntros (->); rewrite length_app.
    all: iIntros "%Hi %Φ (HΨ & %Ht & #Hfn) HΦ"; invert Ht.
    all: wp_rec; wp_pures.
    - rewrite !right_id. iSteps.
    - wp_apply (wp_wand with "(Hfn [] [HΨ])").
      { rewrite list_lookup_middle //. }
      { rewrite take_app_length //. }
      clear acc. iIntros "%acc HΨ".
      wp_pures.
      rewrite Z.add_1_r -Nat2Z.inj_succ take_app_length.
      wp_apply ("IH" with "[] [] [$HΨ $Hfn //]").
      { rewrite -assoc //. }
      { rewrite length_app //. iSteps. }
      iSteps.
  Qed.
  Lemma lst_foldli_spec Ψ fn acc t vs :
    {{{
      ▷ Ψ 0 [] acc ∗
      lst_model t vs ∗
      □ (
        ∀ i v acc,
        ⌜vs !! i = Some v⌝ -∗
        Ψ i (take i vs) acc -∗
        WP fn #i acc v {{ acc,
          ▷ Ψ (S i) (take i vs ++ [v]) acc
        }}
      )
    }}}
      lst_foldli fn acc t
    {{{ acc,
      RET acc;
      Ψ (length vs) vs acc
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #Ht & #Hfn) HΦ".
    wp_rec.
    rewrite -Nat2Z.inj_0.
    wp_smart_apply (lst_foldli_aux_spec [] Ψ with "[$HΨ $Hfn //]"); [done.. |].
    iSteps.
  Qed.
  Lemma lst_foldli_spec' Ψ fn acc t vs :
    {{{
      ▷ Ψ 0 [] acc ∗
      lst_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ acc,
        Ψ i (take i vs) acc -∗
        WP fn #i acc v {{ acc,
          ▷ Ψ (S i) (take i vs ++ [v]) acc
        }}
      )
    }}}
      lst_foldli fn acc t
    {{{ acc,
      RET acc;
      Ψ (length vs) vs acc
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #Ht & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep ?Ξ' _] => set Ξ := Ξ' end.
    pose (Ψ' i vs_left acc := (
      Ψ i vs_left acc ∗
      [∗ list] j ↦ v ∈ drop i vs, Ξ (i + j) v
    )%I).
    wp_apply (lst_foldli_spec Ψ' with "[$HΨ $Ht $Hfn]"); last iSteps.
    clear acc. iIntros "!> %i %v %acc %Hlookup (HΨ & HΞ)".
    erewrite drop_S => //.
    iDestruct "HΞ" as "(Hfn & HΞ)".
    rewrite Nat.add_0_r. setoid_rewrite Nat.add_succ_r. iSteps.
  Qed.

  Lemma lst_foldl_spec Ψ fn acc t vs :
    {{{
      ▷ Ψ 0 [] acc ∗
      lst_model t vs ∗
      □ (
        ∀ i v acc,
        ⌜vs !! i = Some v⌝ -∗
        Ψ i (take i vs) acc -∗
        WP fn acc v {{ acc,
          ▷ Ψ (S i) (take i vs ++ [v]) acc
        }}
      )
    }}}
      lst_foldl fn acc t
    {{{ acc,
      RET acc;
      Ψ (length vs) vs acc
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #Ht & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (lst_foldli_spec Ψ with "[$HΨ $Ht] HΦ").
    iSteps.
  Qed.
  Lemma lst_foldl_spec' Ψ fn acc t vs :
    {{{
      ▷ Ψ 0 [] acc ∗
      lst_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ acc,
        Ψ i (take i vs) acc -∗
        WP fn acc v {{ acc,
          ▷ Ψ (S i) (take i vs ++ [v]) acc
        }}
      )
    }}}
      lst_foldl fn acc t
    {{{ acc,
      RET acc;
      Ψ (length vs) vs acc
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #Ht & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (lst_foldli_spec' Ψ with "[$HΨ $Ht Hfn] HΦ").
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  #[local] Lemma lst_foldri_aux_spec vs_left Ψ vs fn i t vs_right acc :
    vs = vs_left ++ vs_right →
    i = length vs_left →
    {{{
      lst_model t vs_right ∗
      ▷ Ψ (length vs) acc [] ∗
      □ (
        ∀ i v acc,
        ⌜vs !! i = Some v⌝ -∗
        Ψ (S i) acc (drop (S i) vs) -∗
        WP fn #i v acc {{ acc,
          ▷ Ψ i acc (v :: drop (S i) vs)
        }}
      )
    }}}
      lst_foldri_aux fn #i t acc
    {{{ acc,
      RET acc;
      Ψ i acc vs_right
    }}}.
  Proof.
    iInduction vs_right as [| v vs_right] "IH" forall (vs_left i t acc).
    all: iIntros (->); rewrite length_app.
    all: iIntros "%Hi %Φ (%Ht & HΨ & #Hfn) HΦ"; invert Ht.
    all: wp_rec; wp_pures credit:"H£".
    - rewrite Nat.add_0_r. iSteps.
    - rewrite Z.add_1_r -Nat2Z.inj_succ.
      wp_apply ("IH" with "[] [] [$HΨ $Hfn //]").
      { rewrite (assoc (++) _ [_]) //. }
      { rewrite length_app. iSteps. }
      clear acc. iIntros "%acc HΨ".
      iApply wp_fupd. wp_apply (wp_wand with "(Hfn [] [HΨ])").
      { rewrite list_lookup_middle //. }
      all: rewrite (assoc (++) _ [_]) drop_app_length' //; first (rewrite length_app /=; lia).
      clear acc. iIntros "%acc HΨ".
      iMod (lc_fupd_elim_later with "H£ HΨ") as "HΨ".
      iSteps.
  Qed.
  Lemma lst_foldri_spec Ψ fn t vs acc :
    {{{
      lst_model t vs ∗
      ▷ Ψ (length vs) acc [] ∗
      □ (
        ∀ i v acc,
        ⌜vs !! i = Some v⌝ -∗
        Ψ (S i) acc (drop (S i) vs) -∗
        WP fn #i v acc {{ acc,
          ▷ Ψ i acc (v :: drop (S i) vs)
        }}
      )
    }}}
      lst_foldri fn t acc
    {{{ acc,
      RET acc;
      Ψ 0 acc vs
    }}}.
  Proof.
    iIntros "%Φ (#Ht & HΨ & #Hfn) HΦ".
    wp_rec.
    rewrite -Nat2Z.inj_0.
    wp_smart_apply (lst_foldri_aux_spec [] Ψ with "[$Ht $HΨ $Hfn]"); [done.. |].
    iSteps.
  Qed.
  Lemma lst_foldri_spec' Ψ fn t vs acc :
    {{{
      lst_model t vs ∗
      ▷ Ψ (length vs) acc [] ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ acc,
        Ψ (S i) acc (drop (S i) vs) -∗
        WP fn #i v acc {{ acc,
          ▷ Ψ i acc (v :: drop (S i) vs)
        }}
      )
    }}}
      lst_foldri fn t acc
    {{{ acc,
      RET acc;
      Ψ 0 acc vs
    }}}.
  Proof.
    iIntros "%Φ (#Ht & HΨ & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep ?Ξ' _] => set Ξ := Ξ' end.
    pose (Ψ' i acc vs_right := (
      Ψ i acc vs_right ∗
      [∗ list] j ↦ v ∈ take i vs, Ξ j v
    )%I).
    wp_apply (lst_foldri_spec Ψ' with "[$Ht HΨ Hfn]"); last iSteps.
    iFrame. rewrite firstn_all2; first lia. iFrame.
    clear acc. iIntros "!> %i %v %acc %Hlookup (HΨ & HΞ)".
    pose proof Hlookup as Hi%lookup_lt_Some.
    erewrite take_S_r => //.
    iDestruct "HΞ" as "(HΞ & Hfn & _)".
    rewrite Nat.add_0_r length_take Nat.min_l; first lia. iSteps.
  Qed.

  Lemma lst_foldr_spec Ψ fn t vs acc :
    {{{
      lst_model t vs ∗
      ▷ Ψ (length vs) acc [] ∗
      □ (
        ∀ i v acc,
        ⌜vs !! i = Some v⌝ -∗
        Ψ (S i) acc (drop (S i) vs) -∗
        WP fn v acc {{ acc,
          ▷ Ψ i acc (v :: drop (S i) vs)
        }}
      )
    }}}
      lst_foldr fn t acc
    {{{ acc,
      RET acc;
      Ψ 0 acc vs
    }}}.
  Proof.
    iIntros "%Φ (#Ht & HΨ & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (lst_foldri_spec Ψ with "[$Ht $HΨ] HΦ").
    iSteps.
  Qed.
  Lemma lst_foldr_spec' Ψ fn t vs acc :
    {{{
      lst_model t vs ∗
      ▷ Ψ (length vs) acc [] ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ acc,
        Ψ (S i) acc (drop (S i) vs) -∗
        WP fn v acc {{ acc,
          ▷ Ψ i acc (v :: drop (S i) vs)
        }}
      )
    }}}
      lst_foldr fn t acc
    {{{ acc,
      RET acc;
      Ψ 0 acc vs
    }}}.
  Proof.
    iIntros "%Φ (#Ht & HΨ & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (lst_foldri_spec' Ψ with "[$Ht $HΨ Hfn] HΦ").
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  Lemma lst_size_spec t vs :
    {{{
      lst_model t vs
    }}}
      lst_size t
    {{{
      RET #(length vs);
      True
    }}}.
  Proof.
    iIntros "%Φ #Ht HΦ".
    wp_rec.
    pose Ψ i vs_left acc : iProp Σ := (
      ⌜acc = #(length vs_left)⌝
    )%I.
    wp_smart_apply (lst_foldl_spec Ψ with "[$Ht]"); last iSteps.
    iSteps. rewrite length_app. iSteps.
  Qed.

  Lemma lst_rev_app_spec t1 vs1 t2 vs2 :
    {{{
      lst_model t1 vs1 ∗
      lst_model t2 vs2
    }}}
      lst_rev_app t1 t2
    {{{ t,
      RET t;
      lst_model t (reverse vs1 ++ vs2)
    }}}.
  Proof.
    iIntros "%Φ (Ht1 & Ht2) HΦ".
    wp_rec.
    pose Ψ i vs acc : iProp Σ := (
      lst_model acc (reverse vs ++ vs2)
    )%I.
    wp_smart_apply (lst_foldl_spec Ψ with "[$Ht1 $Ht2]"); last iSteps.
    iSteps as (? ? ? ? [= ->]). rewrite reverse_app //.
  Qed.

  Lemma lst_rev_spec t vs :
    {{{
      lst_model t vs
    }}}
      lst_rev t
    {{{ t',
      RET t';
      lst_model t' (reverse vs)
    }}}.
  Proof.
    iIntros "%Φ Ht HΦ".
    wp_rec.
    wp_apply (lst_rev_app_spec _ _ _ [] with "[$Ht //]").
    rewrite right_id //.
  Qed.

  Lemma lst_app_spec t1 vs1 t2 vs2 :
    {{{
      lst_model t1 vs1 ∗
      lst_model t2 vs2
    }}}
      lst_app t1 t2
    {{{ t,
      RET t;
      lst_model t (vs1 ++ vs2)
    }}}.
  Proof.
    iIntros "%Φ (#Ht1 & #Ht2) HΦ".
    wp_rec.
    pose Ψ i acc vs : iProp Σ := (
      lst_model acc (vs ++ vs2)
    )%I.
    wp_smart_apply (lst_foldr_spec Ψ with "[$Ht1]"); last iSteps.
    iSplit; first iSteps. iSteps as (? ? ? ? [= ->]). iSteps.
  Qed.

  Lemma lst_snoc_spec t vs v :
    {{{
      lst_model t vs
    }}}
      lst_snoc t v
    {{{ t',
      RET t';
      lst_model t' (vs ++ [v])
    }}}.
  Proof.
    iIntros "%Φ #Ht HΦ".
    wp_rec.
    wp_smart_apply (lst_singleton_spec with "[//]") as "%tv #Htv".
    wp_apply (lst_app_spec _ _ tv with "[$Ht $Htv]").
    iSteps.
  Qed.

  Lemma lst_iteri_spec Ψ fn t vs :
    {{{
      ▷ Ψ 0 [] ∗
      lst_model t vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        Ψ i (take i vs) -∗
        WP fn #i v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ (S i) (take i vs ++ [v])
        }}
      )
    }}}
      lst_iteri fn t
    {{{
      RET ();
      Ψ (length vs) vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #Ht & #Hfn) HΦ".
    wp_rec.
    pose Ψ' i vs acc := (
      ⌜acc = ()%V⌝ ∗
      Ψ i vs
    )%I.
    wp_smart_apply (lst_foldli_spec Ψ' with "[$HΨ $Ht]"); iSteps.
  Qed.
  Lemma lst_iteri_spec' Ψ fn t vs :
    {{{
      ▷ Ψ 0 [] ∗
      lst_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i (take i vs) -∗
        WP fn #i v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ (S i) (take i vs ++ [v])
        }}
      )
    }}}
      lst_iteri fn t
    {{{
      RET ();
      Ψ (length vs) vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #Ht & Hfn) HΦ".
    wp_rec.
    pose Ψ' i vs acc := (
      ⌜acc = ()%V⌝ ∗
      Ψ i vs
    )%I.
    wp_smart_apply (lst_foldli_spec' Ψ' with "[$HΨ $Ht Hfn]"); iSteps.
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.
  Lemma lst_iteri_spec_disentangled Ψ fn t vs :
    {{{
      lst_model t vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        WP fn #i v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i v
        }}
      )
    }}}
      lst_iteri fn t
    {{{
      RET ();
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ (#Ht & #Hfn) HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp_apply (lst_iteri_spec Ψ' with "[$Ht]"); last iSteps.
    rewrite /Ψ'. iSteps.
    rewrite big_sepL_snoc length_take Nat.min_l; last iSteps.
    eapply Nat.lt_le_incl, lookup_lt_Some. done.
  Qed.
  Lemma lst_iteri_spec_disentangled' Ψ fn t vs :
    {{{
      lst_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn #i v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i v
        }}
      )
    }}}
      lst_iteri fn t
    {{{
      RET ();
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ (#Ht & Hfn) HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp_apply (lst_iteri_spec' Ψ' with "[$Ht Hfn]"); last iSteps.
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn"). iSteps.
    rewrite big_sepL_snoc length_take Nat.min_l; last iSteps.
    eapply Nat.lt_le_incl, lookup_lt_Some. done.
  Qed.

  Lemma lst_iter_spec Ψ fn t vs :
    {{{
      ▷ Ψ 0 [] ∗
      lst_model t vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        Ψ i (take i vs) -∗
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ (S i) (take i vs ++ [v])
        }}
      )
    }}}
      lst_iter fn t
    {{{
      RET ();
      Ψ (length vs) vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #Ht & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (lst_iteri_spec Ψ with "[$HΨ $Ht] HΦ").
    iSteps.
  Qed.
  Lemma lst_iter_spec' Ψ fn t vs :
    {{{
      ▷ Ψ 0 [] ∗
      lst_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i (take i vs) -∗
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ (S i) (take i vs ++ [v])
        }}
      )
    }}}
      lst_iter fn t
    {{{
      RET ();
      Ψ (length vs) vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #Ht & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (lst_iteri_spec' Ψ with "[$HΨ $Ht Hfn] HΦ").
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.
  Lemma lst_iter_spec_disentangled Ψ fn t vs :
    {{{
      lst_model t vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i v
        }}
      )
    }}}
      lst_iter fn t
    {{{
      RET ();
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ (#Ht & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (lst_iteri_spec_disentangled Ψ with "[$Ht] HΦ").
    iSteps.
  Qed.
  Lemma lst_iter_spec_disentangled' Ψ fn t vs :
    {{{
      lst_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i v
        }}
      )
    }}}
      lst_iter fn t
    {{{
      RET ();
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ (#Ht & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (lst_iteri_spec_disentangled' Ψ with "[$Ht Hfn] HΦ").
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  #[local] Lemma lst_mapi_aux_spec vs_left ws_left Ψ vs fn i t vs_right :
    vs = vs_left ++ vs_right →
    i = length vs_left →
    i = length ws_left →
    {{{
      ▷ Ψ i vs_left ws_left ∗
      lst_model t vs_right ∗
      □ (
        ∀ i v ws,
        ⌜vs !! i = Some v ∧ i = length ws⌝ -∗
        Ψ i (take i vs) ws -∗
        WP fn #i v {{ w,
          ▷ Ψ (S i) (take i vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      lst_mapi_aux fn #i t
    {{{ t' ws_right,
      RET t';
      ⌜length vs = (length ws_left + length ws_right)%nat⌝ ∗
      lst_model t' ws_right ∗
      Ψ (length vs) vs (ws_left ++ ws_right)
    }}}.
  Proof.
    iInduction vs_right as [| v vs_right] "IH" forall (vs_left ws_left i t).
    all: iIntros (->); rewrite length_app.
    all: iIntros "%Hi1 %Hi2 %Φ (HΨ & %Ht & #Hfn) HΦ"; invert Ht.
    all: wp_rec; wp_pures.
    - iApply ("HΦ" $! _ []).
      rewrite !right_id. iSteps.
    - wp_apply (wp_wand with "(Hfn [] [HΨ])") as "%w HΨ".
      { rewrite list_lookup_middle //. }
      { rewrite take_app_length //. }
      wp_pures.
      rewrite Z.add_1_r -Nat2Z.inj_succ take_app_length.
      wp_apply ("IH" with "[] [] [] [$HΨ $Hfn //]") as "%t' %ws_right (%Hvs & %Ht' & HΨ)".
      { rewrite -assoc //. }
      { rewrite length_app. iSteps. }
      { rewrite length_app. iSteps. }
      wp_pures.
      iApply ("HΦ" $! _ (w :: ws_right)).
      rewrite -!assoc. rewrite length_app /= in Hvs. rewrite Ht'. iSteps.
  Qed.
  Lemma lst_mapi_spec Ψ fn t vs :
    {{{
      ▷ Ψ 0 [] [] ∗
      lst_model t vs ∗
      □ (
        ∀ i v ws,
        ⌜vs !! i = Some v ∧ i = length ws⌝ -∗
        Ψ i (take i vs) ws -∗
        WP fn #i v {{ w,
          ▷ Ψ (S i) (take i vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      lst_mapi fn t
    {{{ t' ws,
      RET t';
      ⌜length vs = length ws⌝ ∗
      lst_model t' ws ∗
      Ψ (length vs) vs ws
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #Ht & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (lst_mapi_aux_spec [] [] Ψ with "[$HΨ $Ht $Hfn]"); [done.. |].
    iSteps.
  Qed.
  Lemma lst_mapi_spec' Ψ fn t vs :
    {{{
      ▷ Ψ 0 [] [] ∗
      lst_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ ws,
        ⌜i = length ws⌝ -∗
        Ψ i (take i vs) ws -∗
        WP fn #i v {{ w,
          ▷ Ψ (S i) (take i vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      lst_mapi fn t
    {{{ t' ws,
      RET t';
      ⌜length vs = length ws⌝ ∗
      lst_model t' ws ∗
      Ψ (length vs) vs ws
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #Ht & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep ?Ξ' _] => set Ξ := Ξ' end.
    pose (Ψ' i vs_left ws := (
      Ψ i vs_left ws ∗
      [∗ list] j ↦ v ∈ drop i vs, Ξ (i + j) v
    )%I).
    wp_apply (lst_mapi_spec Ψ' with "[$HΨ $Ht $Hfn]"); last iSteps. iIntros "!> %i %v %ws (%Hlookup & %Hi) (HΨ & HΞ)".

    erewrite drop_S => //.
    iDestruct "HΞ" as "(Hfn & HΞ)".
    rewrite Nat.add_0_r. setoid_rewrite Nat.add_succ_r. iSteps.
  Qed.
  Lemma lst_mapi_spec_disentangled Ψ fn t vs :
    {{{
      lst_model t vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        WP fn #i v {{ w,
          ▷ Ψ i v w
        }}
      )
    }}}
      lst_mapi fn t
    {{{ t' ws,
      RET t';
      ⌜length vs = length ws⌝ ∗
      lst_model t' ws ∗
      ( [∗ list] i ↦ v; w ∈ vs; ws,
        Ψ i v w
      )
    }}}.
  Proof.
    iIntros "%Φ (#Ht & #Hfn) HΦ".
    pose Ψ' i vs_left ws := (
      [∗ list] j ↦ v; w ∈ vs_left; ws, Ψ j v w
    )%I.
    wp_apply (lst_mapi_spec Ψ' with "[$Ht]"); last iSteps.
    rewrite /Ψ'. iSteps.
    rewrite big_sepL2_snoc length_take Nat.min_l; last iSteps.
    eapply Nat.lt_le_incl, lookup_lt_Some. done.
  Qed.
  Lemma lst_mapi_spec_disentangled' Ψ fn t vs :
    {{{
      lst_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn #i v {{ w,
          ▷ Ψ i v w
        }}
      )
    }}}
      lst_mapi fn t
    {{{ t' ws,
      RET t';
      ⌜length vs = length ws⌝ ∗
      lst_model t' ws ∗
      ( [∗ list] i ↦ v; w ∈ vs; ws,
        Ψ i v w
      )
    }}}.
  Proof.
    iIntros "%Φ (#Ht & Hfn) HΦ".
    pose Ψ' i vs_left ws := (
      [∗ list] j ↦ v; w ∈ vs_left; ws, Ψ j v w
    )%I.
    wp_apply (lst_mapi_spec' Ψ' with "[$Ht Hfn]"); last iSteps.
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn"). iSteps.
    rewrite big_sepL2_snoc length_take Nat.min_l; last iSteps.
    eapply Nat.lt_le_incl, lookup_lt_Some. done.
  Qed.

  Lemma lst_map_spec Ψ fn t vs :
    {{{
      ▷ Ψ 0 [] [] ∗
      lst_model t vs ∗
      □ (
        ∀ i v ws,
        ⌜vs !! i = Some v ∧ i = length ws⌝ -∗
        Ψ i (take i vs) ws -∗
        WP fn v {{ w,
          ▷ Ψ (S i) (take i vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      lst_map fn t
    {{{ t' ws,
      RET t';
      ⌜length vs = length ws⌝ ∗
      lst_model t' ws ∗
      Ψ (length vs) vs ws
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #Ht & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (lst_mapi_spec Ψ with "[$HΨ $Ht] HΦ").
    iSteps.
  Qed.
  Lemma lst_map_spec' Ψ fn t vs :
    {{{
      ▷ Ψ 0 [] [] ∗
      lst_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ ws,
        ⌜i = length ws⌝ -∗
        Ψ i (take i vs) ws -∗
        WP fn v {{ w,
          ▷ Ψ (S i) (take i vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      lst_map fn t
    {{{ t' ws,
      RET t';
      ⌜length vs = length ws⌝ ∗
      lst_model t' ws ∗
      Ψ (length vs) vs ws
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #Ht & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (lst_mapi_spec' Ψ with "[$HΨ $Ht Hfn] HΦ").
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.
  Lemma lst_map_spec_disentangled Ψ fn t vs :
    {{{
      lst_model t vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        WP fn v {{ w,
          ▷ Ψ i v w
        }}
      )
    }}}
      lst_map fn t
    {{{ t' ws,
      RET t';
      ⌜length vs = length ws⌝ ∗
      lst_model t' ws ∗
      ( [∗ list] i ↦ v; w ∈ vs; ws,
        Ψ i v w
      )
    }}}.
  Proof.
    iIntros "%Φ (#Ht & #Hfn) HΦ".
    wp_rec.
    wp_smart_apply (lst_mapi_spec_disentangled Ψ with "[$Ht] HΦ").
    iSteps.
  Qed.
  Lemma lst_map_spec_disentangled' Ψ fn t vs :
    {{{
      lst_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn v {{ w,
          ▷ Ψ i v w
        }}
      )
    }}}
      lst_map fn t
    {{{ t' ws,
      RET t';
      ⌜length vs = length ws⌝ ∗
      lst_model t' ws ∗
      ( [∗ list] i ↦ v; w ∈ vs; ws,
        Ψ i v w
      )
    }}}.
  Proof.
    iIntros "%Φ (#Ht & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (lst_mapi_spec_disentangled' Ψ with "[$Ht Hfn] HΦ").
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.
End zoo_G.

#[global] Opaque lst_singleton.
#[global] Opaque lst_head.
#[global] Opaque lst_tail.
#[global] Opaque lst_is_empty.
#[global] Opaque lst_get.
#[global] Opaque lst_initi.
#[global] Opaque lst_init.
#[global] Opaque lst_foldli.
#[global] Opaque lst_foldl.
#[global] Opaque lst_foldri.
#[global] Opaque lst_foldr.
#[global] Opaque lst_size.
#[global] Opaque lst_rev_app.
#[global] Opaque lst_rev.
#[global] Opaque lst_app.
#[global] Opaque lst_snoc.
#[global] Opaque lst_iteri.
#[global] Opaque lst_iter.
#[global] Opaque lst_mapi.
#[global] Opaque lst_map.
