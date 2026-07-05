From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
  base
  list__code.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types i j : nat.
Implicit Types v w t fn acc pred : val.
Implicit Types vs vs_left vs_right ws : list val.

Fixpoint plist_to_val nil vs :=
  match vs with
  | [] =>
      nil
  | v :: vs =>
      (v :: plist_to_val nil vs)%V
  end.
#[global] Arguments plist_to_val _ !_ : assert.

Lemma plist_to_val_nil nil :
  plist_to_val nil [] = nil.
Proof.
  done.
Qed.
Lemma plist_to_val_cons nil v vs :
  plist_to_val nil (v :: vs) = (v :: plist_to_val nil vs)%V.
Proof.
  done.
Qed.
Lemma plist_to_val_singleton nil v :
  plist_to_val nil [v] = (v :: nil)%V.
Proof.
  apply plist_to_val_cons.
Qed.
Lemma plist_to_val_app vs1 nil vs2 :
  plist_to_val (plist_to_val nil vs2) vs1 = plist_to_val nil (vs1 ++ vs2).
Proof.
  induction vs1; first done.
  simpl. do 3 f_equal. done.
Qed.

Fixpoint list_to_val vs :=
  match vs with
  | [] =>
      []%V
  | v :: vs =>
      (v :: list_to_val vs)%V
  end.
#[global] Arguments list_to_val !_ : assert.

Lemma list_to_val_plist_to_val vs :
  list_to_val vs = plist_to_val [] vs.
Proof.
  induction vs as [| v vs IH]; first done.
  rewrite /= IH //.
Qed.

#[global] Instance list_to_val_inj :
  Inj (=) (=) list_to_val.
Proof.
  intros vs1. induction vs1 as []; intros []; naive_solver.
Qed.

Lemma list_to_val_nil :
  list_to_val [] = []%V.
Proof.
  rewrite list_to_val_plist_to_val.
  apply plist_to_val_nil.
Qed.
Lemma list_to_val_cons v vs :
  list_to_val (v :: vs) = (v :: list_to_val vs)%V.
Proof.
  rewrite !list_to_val_plist_to_val.
  apply plist_to_val_cons.
Qed.
Lemma list_to_val_singleton v :
  list_to_val [v] = (v :: [])%V.
Proof.
  rewrite list_to_val_plist_to_val.
  apply plist_to_val_singleton.
Qed.
Lemma list_to_val_app vs1 vs2 :
  plist_to_val (list_to_val vs2) vs1 = list_to_val (vs1 ++ vs2).
Proof.
  rewrite !list_to_val_plist_to_val.
  apply plist_to_val_app.
Qed.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Definition plist_model' t nil vs :=
    t = plist_to_val nil vs.
  Definition plist_model t nil vs : iProp Σ :=
    ⌜plist_model' t nil vs⌝.

  Definition list_model' t vs :=
    t = list_to_val vs.
  Definition list_model t vs : iProp Σ :=
    ⌜list_model' t vs⌝.

  Lemma list_model'_plist_model' t vs :
    list_model' t vs ↔
    plist_model' t [] vs.
  Proof.
    rewrite /list_model' list_to_val_plist_to_val //.
  Qed.

  Lemma list٠singleton𑁒spec v :
    {{{
      True
    }}}
      list٠singleton v
    {{{
      t
    , RET t;
      list_model t [v]
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma list٠head𑁒spec {t vs} v vs' :
    vs = v :: vs' →
    list_model' t vs →
    {{{
      True
    }}}
      list٠head t
    {{{
      RET v;
      True
    }}}.
  Proof.
    rewrite /list_model'. iSteps.
  Qed.

  Lemma list٠tail𑁒spec {t vs} v vs' :
    vs = v :: vs' →
    list_model' t vs →
    {{{
      True
    }}}
      list٠tail t
    {{{
      t'
    , RET t';
      list_model t' vs'
    }}}.
  Proof.
    rewrite /list_model'. iSteps.
  Qed.

  Lemma list٠is_empty𑁒spec t vs :
    list_model' t vs →
    {{{
      True
    }}}
      list٠is_empty t
    {{{
      RET #(bool_decide (vs = []%list));
      True
    }}}.
  Proof.
    iIntros (->) "%Φ HΦ".
    destruct vs; iSteps.
  Qed.

  Lemma list٠get𑁒spec v t (i : Z) vs :
    vs !! ₊i = Some v →
    list_model' t vs →
    {{{
      True
    }}}
      list٠get t #i
    {{{
      RET v;
      True
    }}}.
  Proof.
    remember ₊i as j eqn:Hj.
    iInduction j as [| j] "IH" forall (t i vs Hj).
    all: iIntros "%Hlookup %Ht %Φ _ HΦ".
    all: pose proof Hlookup as Hi%lookup_lt_Some.
    all: destruct vs as [| v' vs]; simpl in Hi; first lia; simplify.
    all: wp_rec; wp_pures.
    - rewrite bool_decide_eq_true_2; first lia. wp_pures.
      wp_apply list٠head𑁒spec; [done.. |].
      iSteps.
    - rewrite bool_decide_eq_false_2; first lia. wp_pures.
      wp_apply list٠tail𑁒spec as "%t' %Ht'"; [done.. |].
      wp_apply ("IH" with "[%] [//] [//] [//] HΦ"); first lia.
  Qed.

  #[local] Lemma list٠initi₀𑁒spec vs_left Ψ sz fn i :
    i ≤ ₊sz →
    i = length vs_left →
    {{{
      ▷ Ψ i vs_left ∗
      □ (
        ∀ i vs,
        ⌜i < ₊sz ∧ i = length vs⌝ -∗
        Ψ i vs -∗
        WP fn #i {{ v,
          ▷ Ψ ˖i (vs ++ [v])
        }}
      )
    }}}
      list٠initi₀ #sz fn #i
    {{{
      t vs_right
    , RET t;
      ⌜(length vs_left + length vs_right)%nat = ₊sz⌝ ∗
      list_model t vs_right ∗
      Ψ ₊sz (vs_left ++ vs_right)
    }}}.
  Proof.
    remember (₊sz - i) as j eqn:Hj.
    iInduction j as [| j] "IH" forall (vs_left i Hj).
    all: iIntros "%Hi1 %Hi2 %Φ (HΨ & #Hfn) HΦ".
    all: wp_rec; wp_pures.
    - rewrite bool_decide_eq_true_2; first lia. wp_pures.
      iApply ("HΦ" $! _ []).
      rewrite !right_id. assert (₊sz = i) as <- by lia. iSteps.
    - rewrite bool_decide_eq_false_2; first lia. wp_pures.
      wp_apply (wp_wand with "(Hfn [] HΨ)") as "%v HΨ"; first iSteps.
      wp_pures.
      rewrite Z.add_1_r -Nat2Z.inj_succ.
      wp_apply ("IH" $! (vs_left ++ [v]) ˖i with "[] [] [] [$HΨ //]"); simpl_length/=; [iSteps.. |].
      iIntros "%t %vs_right (%Hvs_right & %Ht & HΨ)". rewrite {}Ht.
      wp_pures.
      iApply ("HΦ" $! _ (v :: vs_right)).
      rewrite -assoc. iSteps.
  Qed.
  Lemma list٠initi𑁒spec Ψ sz fn :
    {{{
      ▷ Ψ 0 [] ∗
      □ (
        ∀ i vs,
        ⌜i < ₊sz ∧ i = length vs⌝ -∗
        Ψ i vs -∗
        WP fn #i {{ v,
          ▷ Ψ ˖i (vs ++ [v])
        }}
      )
    }}}
      list٠initi #sz fn
    {{{
      t vs
    , RET t;
      ⌜length vs = ₊sz⌝ ∗
      list_model t vs ∗
      Ψ ₊sz vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #Hfn) HΦ".
    wp_rec.
    wp_apply+ (list٠initi₀𑁒spec [] Ψ with "[$HΨ $Hfn] HΦ"); simpl; lia.
  Qed.
  Lemma list٠initi𑁒spec' Ψ sz fn :
    {{{
      ▷ Ψ 0 [] ∗
      ( [∗ list] i ∈ seq 0 ₊sz,
        ∀ vs,
        ⌜i = length vs⌝ -∗
        Ψ i vs -∗
        WP fn #i {{ v,
          ▷ Ψ ˖i (vs ++ [v])
        }}
      )
    }}}
      list٠initi #sz fn
    {{{
      t vs
    , RET t;
      ⌜length vs = ₊sz⌝ ∗
      list_model t vs ∗
      Ψ ₊sz vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep (λ _, ?Ξ') _] => set Ξ := Ξ' end.
    pose (Ψ' i vs := (
      Ψ i vs ∗
      [∗ list] j ∈ seq i (₊sz - i), Ξ j
    )%I).
    wp_apply (list٠initi𑁒spec Ψ' with "[$HΨ Hfn]"); last iSteps.
    rewrite Nat.sub_0_r. iFrame. iIntros "!> %i %vs (%Hi1 & %Hi2) (HΨ & HΞ)".
    destruct (Nat.lt_exists_pred 0 (₊sz - i)) as (k & Hk & _); first lia. rewrite Hk.
    rewrite -cons_seq. iDestruct "HΞ" as "(Hfn & HΞ)".
    wp_apply (wp_wand with "(Hfn [//] HΨ)"). iSteps.
    rewrite Nat.sub_succ_r Hk //.
  Qed.
  Lemma list٠initi𑁒spec_disentangled Ψ sz fn :
    {{{
      □ (
        ∀ i,
        ⌜i < ₊sz⌝ -∗
        WP fn #i {{ v,
          ▷ Ψ i v
        }}
      )
    }}}
      list٠initi #sz fn
    {{{
      t vs
    , RET t;
      ⌜length vs = ₊sz⌝ ∗
      list_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ #Hfn HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp_apply (list٠initi𑁒spec Ψ'); last iSteps.
    rewrite /Ψ'. iSteps.
    rewrite big_sepL_snoc. iSteps.
  Qed.
  Lemma list٠initi𑁒spec_disentangled' Ψ sz fn :
    {{{
      [∗ list] i ∈ seq 0 ₊sz,
        WP fn #i {{ v,
          ▷ Ψ i v
        }}
    }}}
      list٠initi #sz fn
    {{{
      t vs
    , RET t;
      ⌜length vs = ₊sz⌝ ∗
      list_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ Hfn HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp_apply (list٠initi𑁒spec' Ψ' with "[Hfn]"); last iSteps.
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn"). iSteps.
    rewrite big_sepL_snoc. iSteps.
  Qed.

  Lemma list٠init𑁒spec Ψ sz fn :
    {{{
      ▷ Ψ 0 [] ∗
      □ (
        ∀ i vs,
        ⌜i < ₊sz ∧ i = length vs⌝ -∗
        Ψ i vs -∗
        WP fn () {{ v,
          ▷ Ψ ˖i (vs ++ [v])
        }}
      )
    }}}
      list٠init #sz fn
    {{{
      t vs
    , RET t;
      ⌜length vs = ₊sz⌝ ∗
      list_model t vs ∗
      Ψ ₊sz vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #Hfn) HΦ".
    wp_rec.
    wp_apply+ (list٠initi𑁒spec Ψ with "[$HΨ] HΦ").
    iSteps.
  Qed.
  Lemma list٠init𑁒spec' Ψ sz fn :
    {{{
      ▷ Ψ 0 [] ∗
      ( [∗ list] i ∈ seq 0 ₊sz,
        ∀ vs,
        ⌜i = length vs⌝ -∗
        Ψ i vs -∗
        WP fn () {{ v,
          ▷ Ψ ˖i (vs ++ [v])
        }}
      )
    }}}
      list٠init #sz fn
    {{{
      t vs
    , RET t;
      ⌜length vs = ₊sz⌝ ∗
      list_model t vs ∗
      Ψ ₊sz vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hfn) HΦ".
    wp_rec.
    wp_apply+ (list٠initi𑁒spec' Ψ with "[$HΨ Hfn] HΦ").
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.
  Lemma list٠init𑁒spec_disentangled Ψ sz fn :
    {{{
      □ (
        ∀ i,
        ⌜i < ₊sz⌝ -∗
        WP fn () {{ v,
          ▷ Ψ i v
        }}
      )
    }}}
      list٠init #sz fn
    {{{
      t vs
    , RET t;
      ⌜length vs = ₊sz⌝ ∗
      list_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ #Hfn HΦ".
    wp_rec.
    wp_apply+ (list٠initi𑁒spec_disentangled Ψ with "[] HΦ").
    iSteps.
  Qed.
  Lemma list٠init𑁒spec_disentangled' Ψ sz fn :
    {{{
      [∗ list] i ∈ seq 0 ₊sz,
        WP fn () {{ v,
          ▷ Ψ i v
        }}
    }}}
      list٠init #sz fn
    {{{
      t vs
    , RET t;
      ⌜length vs = ₊sz⌝ ∗
      list_model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ Hfn HΦ".
    wp_rec.
    wp_apply+ (list٠initi𑁒spec_disentangled' Ψ with "[Hfn] HΦ").
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  #[local] Lemma list٠foldli₀𑁒spec vs_left Ψ vs fn i acc t vs_right :
    vs = vs_left ++ vs_right →
    i = length vs_left →
    list_model' t vs_right →
    {{{
      ▷ Ψ i vs_left acc ∗
      □ (
        ∀ i v acc,
        ⌜vs !! i = Some v⌝ -∗
        Ψ i (take i vs) acc -∗
        WP fn #i acc v {{ acc,
          ▷ Ψ ˖i (take i vs ++ [v]) acc
        }}
      )
    }}}
      list٠foldli₀ fn #i acc t
    {{{
      acc
    , RET acc;
      Ψ (length vs) vs acc
    }}}.
  Proof.
    iInduction vs_right as [| v vs_right] "IH" forall (vs_left acc i t).
    all: iIntros (->); simpl_length.
    all: iIntros "%Hi %Ht %Φ (HΨ & #Hfn) HΦ"; invert Ht.
    all: wp_rec; wp_pures.
    - rewrite !right_id. iSteps.
    - wp_apply (wp_wand with "(Hfn [] [HΨ])") as "{% acc} %acc HΨ".
      { rewrite list_lookup_middle //. }
      { rewrite take_app_length //. }
      wp_pures.
      rewrite Z.add_1_r -Nat2Z.inj_succ take_app_length.
      wp_apply ("IH" with "[%] [%] [//] [$HΨ $Hfn]").
      { rewrite -assoc //. }
      { simpl_length/=. lia. }
      iSteps.
  Qed.
  Lemma list٠foldli𑁒spec Ψ fn acc t vs :
    list_model' t vs →
    {{{
      ▷ Ψ 0 [] acc ∗
      □ (
        ∀ i v acc,
        ⌜vs !! i = Some v⌝ -∗
        Ψ i (take i vs) acc -∗
        WP fn #i acc v {{ acc,
          ▷ Ψ ˖i (take i vs ++ [v]) acc
        }}
      )
    }}}
      list٠foldli fn acc t
    {{{
      acc
    , RET acc;
      Ψ (length vs) vs acc
    }}}.
  Proof.
    iIntros "%Ht %Φ (HΨ & #Hfn) HΦ".
    wp_rec.
    rewrite -Nat2Z.inj_0.
    wp_apply+ (list٠foldli₀𑁒spec [] Ψ with "[$HΨ $Hfn //] HΦ"); done.
  Qed.
  Lemma list٠foldli𑁒spec' Ψ fn acc t vs :
    list_model' t vs →
    {{{
      ▷ Ψ 0 [] acc ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ acc,
        Ψ i (take i vs) acc -∗
        WP fn #i acc v {{ acc,
          ▷ Ψ ˖i (take i vs ++ [v]) acc
        }}
      )
    }}}
      list٠foldli fn acc t
    {{{
      acc
    , RET acc;
      Ψ (length vs) vs acc
    }}}.
  Proof.
    iIntros "%Ht %Φ (HΨ & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep ?Ξ' _] => set Ξ := Ξ' end.
    pose (Ψ' i vs_left acc := (
      Ψ i vs_left acc ∗
      [∗ list] j ↦ v ∈ drop i vs, Ξ (i + j) v
    )%I).
    wp_apply (list٠foldli𑁒spec Ψ' with "[$HΨ $Hfn]"); [done | | iSteps].
    iIntros "!> {% acc} %i %v %acc %Hlookup (HΨ & HΞ)".
    erewrite drop_S => //.
    iDestruct "HΞ" as "(Hfn & HΞ)".
    rewrite Nat.add_0_r. setoid_rewrite Nat.add_succ_r. iSteps.
  Qed.

  Lemma list٠foldl𑁒spec Ψ fn acc t vs :
    list_model' t vs →
    {{{
      ▷ Ψ 0 [] acc ∗
      □ (
        ∀ i v acc,
        ⌜vs !! i = Some v⌝ -∗
        Ψ i (take i vs) acc -∗
        WP fn acc v {{ acc,
          ▷ Ψ ˖i (take i vs ++ [v]) acc
        }}
      )
    }}}
      list٠foldl fn acc t
    {{{
      acc
    , RET acc;
      Ψ (length vs) vs acc
    }}}.
  Proof.
    iIntros "%Ht %Φ (HΨ & #Hfn) HΦ".
    wp_rec.
    wp_apply+ (list٠foldli𑁒spec Ψ with "[$HΨ] HΦ"); first done.
    iSteps.
  Qed.
  Lemma list٠foldl𑁒spec' Ψ fn acc t vs :
    list_model' t vs →
    {{{
      ▷ Ψ 0 [] acc ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ acc,
        Ψ i (take i vs) acc -∗
        WP fn acc v {{ acc,
          ▷ Ψ ˖i (take i vs ++ [v]) acc
        }}
      )
    }}}
      list٠foldl fn acc t
    {{{
      acc
    , RET acc;
      Ψ (length vs) vs acc
    }}}.
  Proof.
    iIntros "%Ht %Φ (HΨ & Hfn) HΦ".
    wp_rec.
    wp_apply+ (list٠foldli𑁒spec' Ψ with "[$HΨ Hfn] HΦ"); first done.
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  #[local] Lemma list٠foldri₀𑁒spec vs_left Ψ vs fn i t vs_right acc :
    vs = vs_left ++ vs_right →
    i = length vs_left →
    list_model' t vs_right →
    {{{
      ▷ Ψ (length vs) acc [] ∗
      □ (
        ∀ i v acc,
        ⌜vs !! i = Some v⌝ -∗
        Ψ ˖i acc (drop ˖i vs) -∗
        WP fn #i v acc {{ acc,
          ▷ Ψ i acc (v :: drop ˖i vs)
        }}
      )
    }}}
      list٠foldri₀ fn #i t acc
    {{{
      acc
    , RET acc;
      Ψ i acc vs_right
    }}}.
  Proof.
    iInduction vs_right as [| v vs_right] "IH" forall (vs_left i t acc).
    all: iIntros (->); simpl_length.
    all: iIntros "%Hi %Ht %Φ (HΨ & #Hfn) HΦ"; invert Ht.
    all: wp_rec; wp_pures credit:"H£".
    - rewrite Nat.add_0_r. iSteps.
    - rewrite Z.add_1_r -Nat2Z.inj_succ.
      wp_apply ("IH" with "[%] [%] [//] [$HΨ $Hfn]") as "{% acc} %acc HΨ".
      { rewrite (assoc (++) _ [_]) //. }
      { simpl_length/=. lia. }
      iApply wp_fupd. wp_apply (wp_wand with "(Hfn [] [HΨ])") as "{% acc} %acc HΨ".
      { rewrite list_lookup_middle //. }
      all: rewrite (assoc (++) _ [_]) drop_app_length' //; first (simpl_length/=; lia).
      iMod (lc_fupd_elim_later with "H£ HΨ") as "HΨ".
      iSteps.
  Qed.
  Lemma list٠foldri𑁒spec Ψ fn t vs acc :
    list_model' t vs →
    {{{
      ▷ Ψ (length vs) acc [] ∗
      □ (
        ∀ i v acc,
        ⌜vs !! i = Some v⌝ -∗
        Ψ ˖i acc (drop ˖i vs) -∗
        WP fn #i v acc {{ acc,
          ▷ Ψ i acc (v :: drop ˖i vs)
        }}
      )
    }}}
      list٠foldri fn t acc
    {{{
      acc
    , RET acc;
      Ψ 0 acc vs
    }}}.
  Proof.
    iIntros "%Ht %Φ (HΨ & #Hfn) HΦ".
    wp_rec.
    rewrite -Nat2Z.inj_0.
    wp_apply+ (list٠foldri₀𑁒spec [] Ψ with "[$HΨ $Hfn] HΦ"); done.
  Qed.
  Lemma list٠foldri𑁒spec' Ψ fn t vs acc :
    list_model' t vs →
    {{{
      ▷ Ψ (length vs) acc [] ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ acc,
        Ψ ˖i acc (drop ˖i vs) -∗
        WP fn #i v acc {{ acc,
          ▷ Ψ i acc (v :: drop ˖i vs)
        }}
      )
    }}}
      list٠foldri fn t acc
    {{{
      acc
    , RET acc;
      Ψ 0 acc vs
    }}}.
  Proof.
    iIntros "%Ht %Φ (HΨ & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep ?Ξ' _] => set Ξ := Ξ' end.
    pose (Ψ' i acc vs_right := (
      Ψ i acc vs_right ∗
      [∗ list] j ↦ v ∈ take i vs, Ξ j v
    )%I).
    wp_apply (list٠foldri𑁒spec Ψ' with "[HΨ Hfn]"); [done | | iSteps].
    iFrame. rewrite firstn_all2; first lia. iFrame.
    iIntros "!> {% acc} %i %v %acc %Hlookup (HΨ & HΞ)".
    pose proof Hlookup as Hi%lookup_lt_Some.
    erewrite take_S_r => //.
    iDestruct "HΞ" as "(HΞ & Hfn & _)".
    rewrite Nat.add_0_r length_take Nat.min_l; first lia. iSteps.
  Qed.

  Lemma list٠foldr𑁒spec Ψ fn t vs acc :
    list_model' t vs →
    {{{
      ▷ Ψ (length vs) acc [] ∗
      □ (
        ∀ i v acc,
        ⌜vs !! i = Some v⌝ -∗
        Ψ ˖i acc (drop ˖i vs) -∗
        WP fn v acc {{ acc,
          ▷ Ψ i acc (v :: drop ˖i vs)
        }}
      )
    }}}
      list٠foldr fn t acc
    {{{
      acc
    , RET acc;
      Ψ 0 acc vs
    }}}.
  Proof.
    iIntros "%Ht %Φ (HΨ & #Hfn) HΦ".
    wp_rec.
    wp_apply+ (list٠foldri𑁒spec Ψ with "[$HΨ] HΦ"); first done.
    iSteps.
  Qed.
  Lemma list٠foldr𑁒spec' Ψ fn t vs acc :
    list_model' t vs →
    {{{
      ▷ Ψ (length vs) acc [] ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ acc,
        Ψ ˖i acc (drop ˖i vs) -∗
        WP fn v acc {{ acc,
          ▷ Ψ i acc (v :: drop ˖i vs)
        }}
      )
    }}}
      list٠foldr fn t acc
    {{{
      acc
    , RET acc;
      Ψ 0 acc vs
    }}}.
  Proof.
    iIntros "%Ht %Φ (HΨ & Hfn) HΦ".
    wp_rec.
    wp_apply+ (list٠foldri𑁒spec' Ψ with "[$HΨ Hfn] HΦ"); first done.
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  Lemma list٠size𑁒spec t vs :
    list_model' t vs →
    {{{
      True
    }}}
      list٠size t
    {{{
      RET #(length vs);
      True
    }}}.
  Proof.
    iIntros "%Ht %Φ _ HΦ".
    wp_rec.
    pose Ψ i vs_left acc : iProp Σ := (
      ⌜acc = #(length vs_left)⌝
    )%I.
    wp_apply+ (list٠foldl𑁒spec Ψ); [done | | iSteps].
    iSteps. simpl_length. iSteps.
  Qed.

  Lemma list٠rev_app𑁒spec t1 vs1 t2 vs2 :
    list_model' t1 vs1 →
    list_model' t2 vs2 →
    {{{
      True
    }}}
      list٠rev_app t1 t2
    {{{
      t
    , RET t;
      list_model t (reverse vs1 ++ vs2)
    }}}.
  Proof.
    iIntros "%Ht1 %Ht2 %Φ True HΦ".
    wp_rec.
    pose Ψ i vs acc : iProp Σ := (
      list_model acc (reverse vs ++ vs2)
    )%I.
    wp_apply+ (list٠foldl𑁒spec Ψ); [done | | iSteps].
    iSteps as (? ? ? ? [= ->]). rewrite reverse_app //.
  Qed.

  Lemma list٠rev𑁒spec t vs :
    list_model' t vs →
    {{{
      True
    }}}
      list٠rev t
    {{{
      t'
    , RET t';
      list_model t' (reverse vs)
    }}}.
  Proof.
    iIntros "%ht %Φ _ HΦ".
    wp_rec.
    wp_apply (list٠rev_app𑁒spec _ _ _ [] with "[//]"); [done.. |].
    rewrite right_id //.
  Qed.

  Lemma list٠app𑁒spec t1 vs1 t2 vs2 :
    list_model' t1 vs1 →
    list_model' t2 vs2 →
    {{{
      True
    }}}
      list٠app t1 t2
    {{{
      t
    , RET t;
      list_model t (vs1 ++ vs2)
    }}}.
  Proof.
    iIntros "%Ht1 %Ht2 %Φ True HΦ".
    wp_rec.
    pose Ψ i acc vs : iProp Σ := (
      list_model acc (vs ++ vs2)
    )%I.
    wp_apply+ (list٠foldr𑁒spec Ψ); [done | | iSteps].
    iSteps as (? ? ? ? [= ->]). iSteps.
  Qed.

  Lemma list٠snoc𑁒spec t vs v :
    list_model' t vs →
    {{{
      True
    }}}
      list٠snoc t v
    {{{
      t'
    , RET t';
      list_model t' (vs ++ [v])
    }}}.
  Proof.
    iIntros "%Ht %Φ _ HΦ".
    wp_rec.
    wp_apply+ (list٠singleton𑁒spec with "[//]") as "%t' %Ht'".
    wp_apply (list٠app𑁒spec _ _ t' with "[//] HΦ"); done.
  Qed.

  Lemma list٠iteri𑁒spec Ψ fn t vs :
    list_model' t vs →
    {{{
      ▷ Ψ 0 [] ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        Ψ i (take i vs) -∗
        WP fn #i v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ ˖i (take i vs ++ [v])
        }}
      )
    }}}
      list٠iteri fn t
    {{{
      RET ();
      Ψ (length vs) vs
    }}}.
  Proof.
    iIntros "%Ht %Φ (HΨ & #Hfn) HΦ".
    wp_rec.
    pose Ψ' i vs acc := (
      ⌜acc = ()%V⌝ ∗
      Ψ i vs
    )%I.
    wp_apply+ (list٠foldli𑁒spec Ψ' with "[$HΨ]"); [done | iSteps..].
  Qed.
  Lemma list٠iteri𑁒spec' Ψ fn t vs :
    list_model' t vs →
    {{{
      ▷ Ψ 0 [] ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i (take i vs) -∗
        WP fn #i v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ ˖i (take i vs ++ [v])
        }}
      )
    }}}
      list٠iteri fn t
    {{{
      RET ();
      Ψ (length vs) vs
    }}}.
  Proof.
    iIntros "%Ht %Φ (HΨ & Hfn) HΦ".
    wp_rec.
    pose Ψ' i vs acc := (
      ⌜acc = ()%V⌝ ∗
      Ψ i vs
    )%I.
    wp_apply+ (list٠foldli𑁒spec' Ψ' with "[$HΨ Hfn]"); [done | iSteps..].
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.
  Lemma list٠iteri𑁒spec_disentangled Ψ fn t vs :
    list_model' t vs →
    {{{
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        WP fn #i v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i v
        }}
      )
    }}}
      list٠iteri fn t
    {{{
      RET ();
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Ht %Φ #Hfn HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp_apply (list٠iteri𑁒spec Ψ'); [done | | iSteps].
    rewrite /Ψ'. iSteps.
    rewrite big_sepL_snoc length_take Nat.min_l; last iSteps.
    eapply Nat.lt_le_incl, lookup_lt_Some. done.
  Qed.
  Lemma list٠iteri𑁒spec_disentangled' Ψ fn t vs :
    list_model' t vs →
    {{{
      ( [∗ list] i ↦ v ∈ vs,
        WP fn #i v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i v
        }}
      )
    }}}
      list٠iteri fn t
    {{{
      RET ();
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%ht %Φ Hfn HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp_apply (list٠iteri𑁒spec' Ψ' with "[Hfn]"); [done | | iSteps].
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn"). iSteps.
    rewrite big_sepL_snoc length_take Nat.min_l; last iSteps.
    eapply Nat.lt_le_incl, lookup_lt_Some. done.
  Qed.

  Lemma list٠iter𑁒spec Ψ fn t vs :
    list_model' t vs →
    {{{
      ▷ Ψ 0 [] ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        Ψ i (take i vs) -∗
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ ˖i (take i vs ++ [v])
        }}
      )
    }}}
      list٠iter fn t
    {{{
      RET ();
      Ψ (length vs) vs
    }}}.
  Proof.
    iIntros "%Ht %Φ (HΨ & #Hfn) HΦ".
    wp_rec.
    wp_apply+ (list٠iteri𑁒spec Ψ with "[$HΨ] HΦ"); first done.
    iSteps.
  Qed.
  Lemma list٠iter𑁒spec' Ψ fn t vs :
    list_model' t vs →
    {{{
      ▷ Ψ 0 [] ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i (take i vs) -∗
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ ˖i (take i vs ++ [v])
        }}
      )
    }}}
      list٠iter fn t
    {{{
      RET ();
      Ψ (length vs) vs
    }}}.
  Proof.
    iIntros "%Ht %Φ (HΨ & Hfn) HΦ".
    wp_rec.
    wp_apply+ (list٠iteri𑁒spec' Ψ with "[$HΨ Hfn] HΦ"); first done.
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.
  Lemma list٠iter𑁒spec_disentangled Ψ fn t vs :
    list_model' t vs →
    {{{
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i v
        }}
      )
    }}}
      list٠iter fn t
    {{{
      RET ();
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Ht %Φ #Hfn HΦ".
    wp_rec.
    wp_apply+ (list٠iteri𑁒spec_disentangled Ψ with "[] HΦ"); first done.
    iSteps.
  Qed.
  Lemma list٠iter𑁒spec_disentangled' Ψ fn t vs :
    list_model' t vs →
    {{{
      ( [∗ list] i ↦ v ∈ vs,
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i v
        }}
      )
    }}}
      list٠iter fn t
    {{{
      RET ();
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Ht %Φ Hfn HΦ".
    wp_rec.
    wp_apply+ (list٠iteri𑁒spec_disentangled' Ψ with "[Hfn] HΦ"); first done.
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  #[local] Lemma list٠mapi₀𑁒spec vs_left ws_left Ψ vs fn i t vs_right :
    vs = vs_left ++ vs_right →
    i = length vs_left →
    i = length ws_left →
    list_model' t vs_right →
    {{{
      ▷ Ψ i vs_left ws_left ∗
      □ (
        ∀ i v ws,
        ⌜vs !! i = Some v ∧ i = length ws⌝ -∗
        Ψ i (take i vs) ws -∗
        WP fn #i v {{ w,
          ▷ Ψ ˖i (take i vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      list٠mapi₀ fn #i t
    {{{
      t' ws_right
    , RET t';
      ⌜length vs = (length ws_left + length ws_right)%nat⌝ ∗
      list_model t' ws_right ∗
      Ψ (length vs) vs (ws_left ++ ws_right)
    }}}.
  Proof.
    iInduction vs_right as [| v vs_right] "IH" forall (vs_left ws_left i t).
    all: iIntros (->); simpl_length.
    all: iIntros "%Hi1 %Hi2 %Ht %Φ (HΨ & #Hfn) HΦ"; invert Ht.
    all: wp_rec; wp_pures.
    - iApply ("HΦ" $! _ []).
      rewrite !right_id. iSteps.
    - wp_apply (wp_wand with "(Hfn [] [HΨ])") as "%w HΨ".
      { rewrite list_lookup_middle //. }
      { rewrite take_app_length //. }
      wp_pures.
      rewrite Z.add_1_r -Nat2Z.inj_succ take_app_length.
      wp_apply ("IH" with "[%] [%] [%] [//] [$HΨ $Hfn]") as "%t' %ws_right (%Hvs & %Ht' & HΨ)".
      { rewrite -assoc //. }
      { simpl_length/=. lia. }
      { simpl_length/=. lia. }
      wp_pures.
      iApply ("HΦ" $! _ (w :: ws_right)).
      rewrite -!assoc. simpl_length/= in Hvs. rewrite Ht'. iSteps.
  Qed.
  Lemma list٠mapi𑁒spec Ψ fn t vs :
    list_model' t vs →
    {{{
      ▷ Ψ 0 [] [] ∗
      □ (
        ∀ i v ws,
        ⌜vs !! i = Some v ∧ i = length ws⌝ -∗
        Ψ i (take i vs) ws -∗
        WP fn #i v {{ w,
          ▷ Ψ ˖i (take i vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      list٠mapi fn t
    {{{
      t' ws
    , RET t';
      ⌜length vs = length ws⌝ ∗
      list_model t' ws ∗
      Ψ (length vs) vs ws
    }}}.
  Proof.
    iIntros "%Ht %Φ (HΨ & #Hfn) HΦ".
    wp_rec.
    wp_apply+ (list٠mapi₀𑁒spec [] [] Ψ with "[$HΨ $Hfn]"); [done.. |].
    iSteps.
  Qed.
  Lemma list٠mapi𑁒spec' Ψ fn t vs :
    list_model' t vs →
    {{{
      ▷ Ψ 0 [] [] ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ ws,
        ⌜i = length ws⌝ -∗
        Ψ i (take i vs) ws -∗
        WP fn #i v {{ w,
          ▷ Ψ ˖i (take i vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      list٠mapi fn t
    {{{
      t' ws
    , RET t';
      ⌜length vs = length ws⌝ ∗
      list_model t' ws ∗
      Ψ (length vs) vs ws
    }}}.
  Proof.
    iIntros "%Ht %Φ (HΨ & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep ?Ξ' _] => set Ξ := Ξ' end.
    pose (Ψ' i vs_left ws := (
      Ψ i vs_left ws ∗
      [∗ list] j ↦ v ∈ drop i vs, Ξ (i + j) v
    )%I).
    wp_apply (list٠mapi𑁒spec Ψ' with "[$HΨ $Hfn]"); [done | | iSteps]. iIntros "!> %i %v %ws (%Hlookup & %Hi) (HΨ & HΞ)".

    erewrite drop_S => //.
    iDestruct "HΞ" as "(Hfn & HΞ)".
    rewrite Nat.add_0_r. setoid_rewrite Nat.add_succ_r. iSteps.
  Qed.
  Lemma list٠mapi𑁒spec_disentangled Ψ fn t vs :
    list_model' t vs →
    {{{
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        WP fn #i v {{ w,
          ▷ Ψ i v w
        }}
      )
    }}}
      list٠mapi fn t
    {{{
      t' ws
    , RET t';
      ⌜length vs = length ws⌝ ∗
      list_model t' ws ∗
      ( [∗ list] i ↦ v; w ∈ vs; ws,
        Ψ i v w
      )
    }}}.
  Proof.
    iIntros "%Ht %Φ #Hfn HΦ".
    pose Ψ' i vs_left ws := (
      [∗ list] j ↦ v; w ∈ vs_left; ws, Ψ j v w
    )%I.
    wp_apply (list٠mapi𑁒spec Ψ'); [done | | iSteps].
    rewrite /Ψ'. iSteps.
    rewrite big_sepL2_snoc length_take Nat.min_l; last iSteps.
    eapply Nat.lt_le_incl, lookup_lt_Some. done.
  Qed.
  Lemma list٠mapi𑁒spec_disentangled' Ψ fn t vs :
    list_model' t vs →
    {{{
      ( [∗ list] i ↦ v ∈ vs,
        WP fn #i v {{ w,
          ▷ Ψ i v w
        }}
      )
    }}}
      list٠mapi fn t
    {{{
      t' ws
    , RET t';
      ⌜length vs = length ws⌝ ∗
      list_model t' ws ∗
      ( [∗ list] i ↦ v; w ∈ vs; ws,
        Ψ i v w
      )
    }}}.
  Proof.
    iIntros "%Ht %Φ Hfn HΦ".
    pose Ψ' i vs_left ws := (
      [∗ list] j ↦ v; w ∈ vs_left; ws, Ψ j v w
    )%I.
    wp_apply (list٠mapi𑁒spec' Ψ' with "[Hfn]"); [done | | iSteps].
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn"). iSteps.
    rewrite big_sepL2_snoc length_take Nat.min_l; last iSteps.
    eapply Nat.lt_le_incl, lookup_lt_Some. done.
  Qed.

  Lemma list٠map𑁒spec Ψ fn t vs :
    list_model' t vs →
    {{{
      ▷ Ψ 0 [] [] ∗
      □ (
        ∀ i v ws,
        ⌜vs !! i = Some v ∧ i = length ws⌝ -∗
        Ψ i (take i vs) ws -∗
        WP fn v {{ w,
          ▷ Ψ ˖i (take i vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      list٠map fn t
    {{{
      t' ws
    , RET t';
      ⌜length vs = length ws⌝ ∗
      list_model t' ws ∗
      Ψ (length vs) vs ws
    }}}.
  Proof.
    iIntros "%Ht %Φ (HΨ & #Hfn) HΦ".
    wp_rec.
    wp_apply+ (list٠mapi𑁒spec Ψ with "[$HΨ] HΦ"); first done.
    iSteps.
  Qed.
  Lemma list٠map𑁒spec' Ψ fn t vs :
    list_model' t vs →
    {{{
      ▷ Ψ 0 [] [] ∗
      ( [∗ list] i ↦ v ∈ vs,
        ∀ ws,
        ⌜i = length ws⌝ -∗
        Ψ i (take i vs) ws -∗
        WP fn v {{ w,
          ▷ Ψ ˖i (take i vs ++ [v]) (ws ++ [w])
        }}
      )
    }}}
      list٠map fn t
    {{{
      t' ws
    , RET t';
      ⌜length vs = length ws⌝ ∗
      list_model t' ws ∗
      Ψ (length vs) vs ws
    }}}.
  Proof.
    iIntros "%Ht %Φ (HΨ & Hfn) HΦ".
    wp_rec.
    wp_apply+ (list٠mapi𑁒spec' Ψ with "[$HΨ Hfn] HΦ"); first done.
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.
  Lemma list٠map𑁒spec_disentangled Ψ fn t vs :
    list_model' t vs →
    {{{
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        WP fn v {{ w,
          ▷ Ψ i v w
        }}
      )
    }}}
      list٠map fn t
    {{{
      t' ws
    , RET t';
      ⌜length vs = length ws⌝ ∗
      list_model t' ws ∗
      ( [∗ list] i ↦ v; w ∈ vs; ws,
        Ψ i v w
      )
    }}}.
  Proof.
    iIntros "%Ht %Φ #Hfn HΦ".
    wp_rec.
    wp_apply+ (list٠mapi𑁒spec_disentangled Ψ with "[] HΦ"); first done.
    iSteps.
  Qed.
  Lemma list٠map𑁒spec_disentangled' Ψ fn t vs :
    list_model' t vs →
    {{{
      ( [∗ list] i ↦ v ∈ vs,
        WP fn v {{ w,
          ▷ Ψ i v w
        }}
      )
    }}}
      list٠map fn t
    {{{
      t' ws
    , RET t';
      ⌜length vs = length ws⌝ ∗
      list_model t' ws ∗
      ( [∗ list] i ↦ v; w ∈ vs; ws,
        Ψ i v w
      )
    }}}.
  Proof.
    iIntros "%Ht %Φ Hfn HΦ".
    wp_rec.
    wp_apply+ (list٠mapi𑁒spec_disentangled' Ψ with "[Hfn] HΦ"); first done.
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  Lemma list٠forall𑁒spec Ψ pred t vs :
    list_model' t vs →
    {{{
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        WP pred v {{ res,
          ∃ b,
          ⌜res = #b⌝ ∗
          Ψ i v b
        }}
      )
    }}}
      list٠forall pred t
    {{{
      b
    , RET #b;
      if b then
        [∗ list] i ↦ v ∈ vs, Ψ i v true
      else
        ∃ i v,
        ⌜vs !! i = Some v⌝ ∗
        Ψ i v false
    }}}.
  Proof.
    iInduction vs as [| v vs] "IH" forall (Ψ t).
    all: iIntros (->) "%Φ #Hpred HΦ".
    all: wp_rec.
    - iSteps.
    - wp_apply+ (wp_wand with "(Hpred [%])") as (res) "(%b & -> & HΨ0)".
      { rewrite lookup_cons_Some. left. done. }
      destruct b.
      + wp_apply+ ("IH" $! (λ i, Ψ ˖i) with "[//]") as ([]) "HΨ".
        { iIntros "!> %i %w %Hlookup".
          iSpecialize ("Hpred" $! ˖i).
          iSteps.
        }
        * iSteps.
        * iDestruct "HΨ" as "(%i & %w & %Hlookup & HΨ)".
          iSteps. iExists ˖i. iSteps.
      + iSteps. iExists 0. iSteps.
  Qed.

  Lemma list٠exists𑁒spec Ψ pred t vs :
    list_model' t vs →
    {{{
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        WP pred v {{ res,
          ∃ b,
          ⌜res = #b⌝ ∗
          Ψ i v b
        }}
      )
    }}}
      list٠exists pred t
    {{{
      b
    , RET #b;
      if b then
        ∃ i v,
        ⌜vs !! i = Some v⌝ ∗
        Ψ i v true
      else
        [∗ list] i ↦ v ∈ vs, Ψ i v false
    }}}.
  Proof.
    iInduction vs as [| v vs] "IH" forall (Ψ t).
    all: iIntros (->) "%Φ #Hpred HΦ".
    all: wp_rec.
    - iSteps.
    - wp_apply+ (wp_wand with "(Hpred [%])") as (res) "(%b & -> & HΨ0)".
      { rewrite lookup_cons_Some. left. done. }
      destruct b.
      + iSteps. iExists 0. iSteps.
      + wp_apply+ ("IH" $! (λ i, Ψ ˖i) with "[//]") as ([]) "HΨ".
        { iIntros "!> %i %w %Hlookup".
          iSpecialize ("Hpred" $! ˖i).
          iSteps.
        }
        * iDestruct "HΨ" as "(%i & %w & %Hlookup & HΨ)".
          iSteps. iExists ˖i. iSteps.
        * iSteps.
  Qed.
End zoo_G.

From zoo_std Require
  list__opaque.
