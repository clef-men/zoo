Require Import zoo.prelude.
Require Import zoo.base.
Require Export zoo_std.list__code.
Require Import zoo_std.list__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type i j : nat.
Implicit Type v w t fn acc pred : val.
Implicit Type vs vs_left vs_right ws : list val.

Fixpoint plist۰to_val nil vs :=
  match vs with
  | [] =>
      nil
  | v :: vs =>
      (v :: plist۰to_val nil vs)%V
  end.
#[global] Arguments plist۰to_val _ !_ : assert.

Lemma plist۰to_valｰnil nil :
  plist۰to_val nil [] = nil.
Proof.
  done.
Qed.
Lemma plist۰to_valｰcons nil v vs :
  plist۰to_val nil (v :: vs) = (v :: plist۰to_val nil vs)%V.
Proof.
  done.
Qed.
Lemma plist۰to_valｰsingleton nil v :
  plist۰to_val nil [v] = (v :: nil)%V.
Proof.
  apply plist۰to_valｰcons.
Qed.
Lemma plist۰to_valｰapp vs1 nil vs2 :
  plist۰to_val (plist۰to_val nil vs2) vs1 = plist۰to_val nil (vs1 ++ vs2).
Proof.
  induction vs1; first done.
  simpl. do 3 f_equal. done.
Qed.

Fixpoint list۰to_val vs :=
  match vs with
  | [] =>
      []%V
  | v :: vs =>
      (v :: list۰to_val vs)%V
  end.
#[global] Arguments list۰to_val !_ : assert.

Lemma list۰to_valｰplist۰to_val vs :
  list۰to_val vs = plist۰to_val [] vs.
Proof.
  induction vs as [| v vs IH]; first done.
  rewrite /= IH //.
Qed.

#[global] Instance list۰to_valｰinj :
  Inj (=) (=) list۰to_val.
Proof.
  intros vs1. induction vs1 as []; intros []; naive_solver.
Qed.

Lemma list۰to_valｰnil :
  list۰to_val [] = []%V.
Proof.
  rewrite list۰to_valｰplist۰to_val.
  apply plist۰to_valｰnil.
Qed.
Lemma list۰to_valｰcons v vs :
  list۰to_val (v :: vs) = (v :: list۰to_val vs)%V.
Proof.
  rewrite !list۰to_valｰplist۰to_val.
  apply plist۰to_valｰcons.
Qed.
Lemma list۰to_valｰsingleton v :
  list۰to_val [v] = (v :: [])%V.
Proof.
  rewrite list۰to_valｰplist۰to_val.
  apply plist۰to_valｰsingleton.
Qed.
Lemma list۰to_valｰapp vs1 vs2 :
  plist۰to_val (list۰to_val vs2) vs1 = list۰to_val (vs1 ++ vs2).
Proof.
  rewrite !list۰to_valｰplist۰to_val.
  apply plist۰to_valｰapp.
Qed.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Definition plist۰model' t nil vs :=
    t = plist۰to_val nil vs.
  Definition plist۰model t nil vs : iProp Σ :=
    ⌜plist۰model' t nil vs⌝.

  Definition list۰model' t vs :=
    t = list۰to_val vs.
  Definition list۰model t vs : iProp Σ :=
    ⌜list۰model' t vs⌝.

  Lemma list۰model'ｰplist۰model' t vs :
    list۰model' t vs ↔
    plist۰model' t [] vs.
  Proof.
    rewrite /list۰model' list۰to_valｰplist۰to_val //.
  Qed.

  Lemma list٠singletonｰspec v :
    {{{
      True
    }}}
      list٠singleton v
    {{{
      t
    , RET t;
      list۰model t [v]
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma list٠headｰspec {t vs} v vs' :
    vs = v :: vs' →
    list۰model' t vs →
    {{{
      True
    }}}
      list٠head t
    {{{
      RET v;
      True
    }}}.
  Proof.
    rewrite /list۰model'. iSteps.
  Qed.

  Lemma list٠tailｰspec {t vs} v vs' :
    vs = v :: vs' →
    list۰model' t vs →
    {{{
      True
    }}}
      list٠tail t
    {{{
      t'
    , RET t';
      list۰model t' vs'
    }}}.
  Proof.
    rewrite /list۰model'. iSteps.
  Qed.

  Lemma list٠is_emptyｰspec t vs :
    list۰model' t vs →
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

  Lemma list٠getｰspec v t (i : Z) vs :
    vs !! ₊i = Some v →
    list۰model' t vs →
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
    all: destruct vs as [| v' vs]; simpl in Hi; first lia; simp.
    all: wp۰rec; wp۰pures.
    - rewrite bool_decide_eq_true_2; first lia. wp۰pures.
      wp۰apply list٠headｰspec; [done.. |].
      iSteps.
    - rewrite bool_decide_eq_false_2; first lia. wp۰pures.
      wp۰apply list٠tailｰspec as "%t' %Ht'"; [done.. |].
      wp۰apply ("IH" with "[%] [//] [//] [//] HΦ"); first lia.
  Qed.

  #[local] Lemma list٠initi₁ｰspec vs_left Ψ sz fn i :
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
      list٠initi₁ #sz fn #i
    {{{
      t vs_right
    , RET t;
      ⌜(length vs_left + length vs_right)%nat = ₊sz⌝ ∗
      list۰model t vs_right ∗
      Ψ ₊sz (vs_left ++ vs_right)
    }}}.
  Proof.
    remember (₊sz - i) as j eqn:Hj.
    iInduction j as [| j] "IH" forall (vs_left i Hj).
    all: iIntros "%Hi1 %Hi2 %Φ (HΨ & #Hfn) HΦ".
    all: wp۰rec; wp۰pures.
    - rewrite bool_decide_eq_true_2; first lia. wp۰pures.
      iApply ("HΦ" $! _ []).
      rewrite !right_id. assert (₊sz = i) as <- by lia. iSteps.
    - rewrite bool_decide_eq_false_2; first lia. wp۰pures.
      wp۰apply (wpｰwand with "(Hfn [] HΨ)") as "%v HΨ"; first iSteps.
      wp۰pures.
      rewrite Z.add_1_r -Nat2Z.inj_succ.
      wp۰apply ("IH" $! (vs_left ++ [v]) ˖i with "[] [] [] [$HΨ //]"); simp_length/=; [iSteps.. |].
      iIntros "%t %vs_right (%Hvs_right & %Ht & HΨ)". rewrite {}Ht.
      wp۰pures.
      iApply ("HΦ" $! _ (v :: vs_right)).
      rewrite -assoc. iSteps.
  Qed.
  Lemma list٠initiｰspec Ψ sz fn :
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
      list۰model t vs ∗
      Ψ ₊sz vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (list٠initi₁ｰspec [] Ψ with "[$HΨ $Hfn] HΦ"); simpl; lia.
  Qed.
  Lemma list٠initiｰspec' Ψ sz fn :
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
      list۰model t vs ∗
      Ψ ₊sz vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep (λ _, ?Ξ') _] => set Ξ := Ξ' end.
    pose (Ψ' i vs := (
      Ψ i vs ∗
      [∗ list] j ∈ seq i (₊sz - i), Ξ j
    )%I).
    wp۰apply (list٠initiｰspec Ψ' with "[$HΨ Hfn]"); last iSteps.
    rewrite Nat.sub_0_r. iFrame. iIntros "!> %i %vs (%Hi1 & %Hi2) (HΨ & HΞ)".
    destruct (Nat.lt_exists_pred 0 (₊sz - i)) as (k & Hk & _); first lia. rewrite Hk.
    rewrite -cons_seq. iDestruct "HΞ" as "(Hfn & HΞ)".
    wp۰apply (wpｰwand with "(Hfn [//] HΨ)"). iSteps.
    rewrite Nat.sub_succ_r Hk //.
  Qed.
  Lemma list٠initiｰspecｰdisentangled Ψ sz fn :
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
      list۰model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ #Hfn HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp۰apply (list٠initiｰspec Ψ'); last iSteps.
    rewrite /Ψ'. iSteps.
    rewrite big_sepL_snoc. iSteps.
  Qed.
  Lemma list٠initiｰspecｰdisentangled' Ψ sz fn :
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
      list۰model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ Hfn HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp۰apply (list٠initiｰspec' Ψ' with "[Hfn]"); last iSteps.
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn"). iSteps.
    rewrite big_sepL_snoc. iSteps.
  Qed.

  Lemma list٠initｰspec Ψ sz fn :
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
      list۰model t vs ∗
      Ψ ₊sz vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (list٠initiｰspec Ψ with "[$HΨ] HΦ").
    iSteps.
  Qed.
  Lemma list٠initｰspec' Ψ sz fn :
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
      list۰model t vs ∗
      Ψ ₊sz vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (list٠initiｰspec' Ψ with "[$HΨ Hfn] HΦ").
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.
  Lemma list٠initｰspecｰdisentangled Ψ sz fn :
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
      list۰model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ #Hfn HΦ".
    wp۰rec.
    wp۰apply+ (list٠initiｰspecｰdisentangled Ψ with "[] HΦ").
    iSteps.
  Qed.
  Lemma list٠initｰspecｰdisentangled' Ψ sz fn :
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
      list۰model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ Hfn HΦ".
    wp۰rec.
    wp۰apply+ (list٠initiｰspecｰdisentangled' Ψ with "[Hfn] HΦ").
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  #[local] Lemma list٠foldli₁ｰspec vs_left Ψ vs fn i acc t vs_right :
    vs = vs_left ++ vs_right →
    i = length vs_left →
    list۰model' t vs_right →
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
      list٠foldli₁ fn #i acc t
    {{{
      acc
    , RET acc;
      Ψ (length vs) vs acc
    }}}.
  Proof.
    iInduction vs_right as [| v vs_right] "IH" forall (vs_left acc i t).
    all: iIntros (->); simp_length.
    all: iIntros "%Hi %Ht %Φ (HΨ & #Hfn) HΦ"; invert Ht.
    all: wp۰rec; wp۰pures.
    - rewrite !right_id. iSteps.
    - wp۰apply (wpｰwand with "(Hfn [] [HΨ])") as "{% acc} %acc HΨ".
      { rewrite list_lookup_middle //. }
      { rewrite take_app_length //. }
      wp۰pures.
      rewrite Z.add_1_r -Nat2Z.inj_succ take_app_length.
      wp۰apply ("IH" with "[%] [%] [//] [$HΨ $Hfn]").
      { rewrite -assoc //. }
      { simp_length/=. lia. }
      iSteps.
  Qed.
  Lemma list٠foldliｰspec Ψ fn acc t vs :
    list۰model' t vs →
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
    wp۰rec.
    rewrite -Nat2Z.inj_0.
    wp۰apply+ (list٠foldli₁ｰspec [] Ψ with "[$HΨ $Hfn //] HΦ"); done.
  Qed.
  Lemma list٠foldliｰspec' Ψ fn acc t vs :
    list۰model' t vs →
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
    wp۰apply (list٠foldliｰspec Ψ' with "[$HΨ $Hfn]"); [done | | iSteps].
    iIntros "!> {% acc} %i %v %acc %Hlookup (HΨ & HΞ)".
    erewrite drop_S => //.
    iDestruct "HΞ" as "(Hfn & HΞ)".
    rewrite Nat.add_0_r. setoid_rewrite Nat.add_succ_r. iSteps.
  Qed.

  Lemma list٠foldlｰspec Ψ fn acc t vs :
    list۰model' t vs →
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
    wp۰rec.
    wp۰apply+ (list٠foldliｰspec Ψ with "[$HΨ] HΦ"); first done.
    iSteps.
  Qed.
  Lemma list٠foldlｰspec' Ψ fn acc t vs :
    list۰model' t vs →
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
    wp۰rec.
    wp۰apply+ (list٠foldliｰspec' Ψ with "[$HΨ Hfn] HΦ"); first done.
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  #[local] Lemma list٠foldri₁ｰspec vs_left Ψ vs fn i t vs_right acc :
    vs = vs_left ++ vs_right →
    i = length vs_left →
    list۰model' t vs_right →
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
      list٠foldri₁ fn #i t acc
    {{{
      acc
    , RET acc;
      Ψ i acc vs_right
    }}}.
  Proof.
    iInduction vs_right as [| v vs_right] "IH" forall (vs_left i t acc).
    all: iIntros (->); simp_length.
    all: iIntros "%Hi %Ht %Φ (HΨ & #Hfn) HΦ"; invert Ht.
    all: wp۰rec; wp۰pures credit:"H£".
    - rewrite Nat.add_0_r. iSteps.
    - rewrite Z.add_1_r -Nat2Z.inj_succ.
      wp۰apply ("IH" with "[%] [%] [//] [$HΨ $Hfn]") as "{% acc} %acc HΨ".
      { rewrite (assoc (++) _ [_]) //. }
      { simp_length/=. lia. }
      iApply wpｰfupd. wp۰apply (wpｰwand with "(Hfn [] [HΨ])") as "{% acc} %acc HΨ".
      { rewrite list_lookup_middle //. }
      all: rewrite (assoc (++) _ [_]) drop_app_length' //; first (simp_length/=; lia).
      iMod (lc_fupd_elim_later with "H£ HΨ") as "HΨ".
      iSteps.
  Qed.
  Lemma list٠foldriｰspec Ψ fn t vs acc :
    list۰model' t vs →
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
    wp۰rec.
    rewrite -Nat2Z.inj_0.
    wp۰apply+ (list٠foldri₁ｰspec [] Ψ with "[$HΨ $Hfn] HΦ"); done.
  Qed.
  Lemma list٠foldriｰspec' Ψ fn t vs acc :
    list۰model' t vs →
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
    wp۰apply (list٠foldriｰspec Ψ' with "[HΨ Hfn]"); [done | | iSteps].
    iFrame. rewrite firstn_all2; first lia. iFrame.
    iIntros "!> {% acc} %i %v %acc %Hlookup (HΨ & HΞ)".
    pose proof Hlookup as Hi%lookup_lt_Some.
    erewrite take_S_r => //.
    iDestruct "HΞ" as "(HΞ & Hfn & _)".
    rewrite Nat.add_0_r length_take Nat.min_l; first lia. iSteps.
  Qed.

  Lemma list٠foldrｰspec Ψ fn t vs acc :
    list۰model' t vs →
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
    wp۰rec.
    wp۰apply+ (list٠foldriｰspec Ψ with "[$HΨ] HΦ"); first done.
    iSteps.
  Qed.
  Lemma list٠foldrｰspec' Ψ fn t vs acc :
    list۰model' t vs →
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
    wp۰rec.
    wp۰apply+ (list٠foldriｰspec' Ψ with "[$HΨ Hfn] HΦ"); first done.
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  Lemma list٠sizeｰspec t vs :
    list۰model' t vs →
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
    wp۰rec.
    pose Ψ i vs_left acc : iProp Σ := (
      ⌜acc = #(length vs_left)⌝
    )%I.
    wp۰apply+ (list٠foldlｰspec Ψ); [done | | iSteps].
    iSteps. simp_length. iSteps.
  Qed.

  Lemma list٠rev_appｰspec t1 vs1 t2 vs2 :
    list۰model' t1 vs1 →
    list۰model' t2 vs2 →
    {{{
      True
    }}}
      list٠rev_app t1 t2
    {{{
      t
    , RET t;
      list۰model t (reverse vs1 ++ vs2)
    }}}.
  Proof.
    iIntros "%Ht1 %Ht2 %Φ True HΦ".
    wp۰rec.
    pose Ψ i vs acc : iProp Σ := (
      list۰model acc (reverse vs ++ vs2)
    )%I.
    wp۰apply+ (list٠foldlｰspec Ψ); [done | | iSteps].
    iSteps as (? ? ? ? [= ->]). rewrite reverse_app //.
  Qed.

  Lemma list٠revｰspec t vs :
    list۰model' t vs →
    {{{
      True
    }}}
      list٠rev t
    {{{
      t'
    , RET t';
      list۰model t' (reverse vs)
    }}}.
  Proof.
    iIntros "%ht %Φ _ HΦ".
    wp۰rec.
    wp۰apply (list٠rev_appｰspec _ _ _ [] with "[//]"); [done.. |].
    rewrite right_id //.
  Qed.

  Lemma list٠appｰspec t1 vs1 t2 vs2 :
    list۰model' t1 vs1 →
    list۰model' t2 vs2 →
    {{{
      True
    }}}
      list٠app t1 t2
    {{{
      t
    , RET t;
      list۰model t (vs1 ++ vs2)
    }}}.
  Proof.
    iIntros "%Ht1 %Ht2 %Φ True HΦ".
    wp۰rec.
    pose Ψ i acc vs : iProp Σ := (
      list۰model acc (vs ++ vs2)
    )%I.
    wp۰apply+ (list٠foldrｰspec Ψ); [done | | iSteps].
    iSteps as (? ? ? ? [= ->]). iSteps.
  Qed.

  Lemma list٠snocｰspec t vs v :
    list۰model' t vs →
    {{{
      True
    }}}
      list٠snoc t v
    {{{
      t'
    , RET t';
      list۰model t' (vs ++ [v])
    }}}.
  Proof.
    iIntros "%Ht %Φ _ HΦ".
    wp۰rec.
    wp۰apply+ (list٠singletonｰspec with "[//]") as "%t' %Ht'".
    wp۰apply (list٠appｰspec _ _ t' with "[//] HΦ"); done.
  Qed.

  Lemma list٠iteriｰspec Ψ fn t vs :
    list۰model' t vs →
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
    wp۰rec.
    pose Ψ' i vs acc := (
      ⌜acc = ()%V⌝ ∗
      Ψ i vs
    )%I.
    wp۰apply+ (list٠foldliｰspec Ψ' with "[$HΨ]"); [done | iSteps..].
  Qed.
  Lemma list٠iteriｰspec' Ψ fn t vs :
    list۰model' t vs →
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
    wp۰rec.
    pose Ψ' i vs acc := (
      ⌜acc = ()%V⌝ ∗
      Ψ i vs
    )%I.
    wp۰apply+ (list٠foldliｰspec' Ψ' with "[$HΨ Hfn]"); [done | iSteps..].
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.
  Lemma list٠iteriｰspecｰdisentangled Ψ fn t vs :
    list۰model' t vs →
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
    wp۰apply (list٠iteriｰspec Ψ'); [done | | iSteps].
    rewrite /Ψ'. iSteps.
    rewrite big_sepL_snoc length_take Nat.min_l; last iSteps.
    eapply Nat.lt_le_incl, lookup_lt_Some. done.
  Qed.
  Lemma list٠iteriｰspecｰdisentangled' Ψ fn t vs :
    list۰model' t vs →
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
    wp۰apply (list٠iteriｰspec' Ψ' with "[Hfn]"); [done | | iSteps].
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn"). iSteps.
    rewrite big_sepL_snoc length_take Nat.min_l; last iSteps.
    eapply Nat.lt_le_incl, lookup_lt_Some. done.
  Qed.

  Lemma list٠iterｰspec Ψ fn t vs :
    list۰model' t vs →
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
    wp۰rec.
    wp۰apply+ (list٠iteriｰspec Ψ with "[$HΨ] HΦ"); first done.
    iSteps.
  Qed.
  Lemma list٠iterｰspec' Ψ fn t vs :
    list۰model' t vs →
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
    wp۰rec.
    wp۰apply+ (list٠iteriｰspec' Ψ with "[$HΨ Hfn] HΦ"); first done.
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.
  Lemma list٠iterｰspecｰdisentangled Ψ fn t vs :
    list۰model' t vs →
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
    wp۰rec.
    wp۰apply+ (list٠iteriｰspecｰdisentangled Ψ with "[] HΦ"); first done.
    iSteps.
  Qed.
  Lemma list٠iterｰspecｰdisentangled' Ψ fn t vs :
    list۰model' t vs →
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
    wp۰rec.
    wp۰apply+ (list٠iteriｰspecｰdisentangled' Ψ with "[Hfn] HΦ"); first done.
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  #[local] Lemma list٠mapi₁ｰspec vs_left ws_left Ψ vs fn i t vs_right :
    vs = vs_left ++ vs_right →
    i = length vs_left →
    i = length ws_left →
    list۰model' t vs_right →
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
      list٠mapi₁ fn #i t
    {{{
      t' ws_right
    , RET t';
      ⌜length vs = (length ws_left + length ws_right)%nat⌝ ∗
      list۰model t' ws_right ∗
      Ψ (length vs) vs (ws_left ++ ws_right)
    }}}.
  Proof.
    iInduction vs_right as [| v vs_right] "IH" forall (vs_left ws_left i t).
    all: iIntros (->); simp_length.
    all: iIntros "%Hi1 %Hi2 %Ht %Φ (HΨ & #Hfn) HΦ"; invert Ht.
    all: wp۰rec; wp۰pures.
    - iApply ("HΦ" $! _ []).
      rewrite !right_id. iSteps.
    - wp۰apply (wpｰwand with "(Hfn [] [HΨ])") as "%w HΨ".
      { rewrite list_lookup_middle //. }
      { rewrite take_app_length //. }
      wp۰pures.
      rewrite Z.add_1_r -Nat2Z.inj_succ take_app_length.
      wp۰apply ("IH" with "[%] [%] [%] [//] [$HΨ $Hfn]") as "%t' %ws_right (%Hvs & %Ht' & HΨ)".
      { rewrite -assoc //. }
      { simp_length/=. lia. }
      { simp_length/=. lia. }
      wp۰pures.
      iApply ("HΦ" $! _ (w :: ws_right)).
      rewrite -!assoc. simp_length/= in Hvs. rewrite Ht'. iSteps.
  Qed.
  Lemma list٠mapiｰspec Ψ fn t vs :
    list۰model' t vs →
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
      list۰model t' ws ∗
      Ψ (length vs) vs ws
    }}}.
  Proof.
    iIntros "%Ht %Φ (HΨ & #Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (list٠mapi₁ｰspec [] [] Ψ with "[$HΨ $Hfn]"); [done.. |].
    iSteps.
  Qed.
  Lemma list٠mapiｰspec' Ψ fn t vs :
    list۰model' t vs →
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
      list۰model t' ws ∗
      Ψ (length vs) vs ws
    }}}.
  Proof.
    iIntros "%Ht %Φ (HΨ & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep ?Ξ' _] => set Ξ := Ξ' end.
    pose (Ψ' i vs_left ws := (
      Ψ i vs_left ws ∗
      [∗ list] j ↦ v ∈ drop i vs, Ξ (i + j) v
    )%I).
    wp۰apply (list٠mapiｰspec Ψ' with "[$HΨ $Hfn]"); [done | | iSteps]. iIntros "!> %i %v %ws (%Hlookup & %Hi) (HΨ & HΞ)".

    erewrite drop_S => //.
    iDestruct "HΞ" as "(Hfn & HΞ)".
    rewrite Nat.add_0_r. setoid_rewrite Nat.add_succ_r. iSteps.
  Qed.
  Lemma list٠mapiｰspecｰdisentangled Ψ fn t vs :
    list۰model' t vs →
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
      list۰model t' ws ∗
      ( [∗ list] i ↦ v; w ∈ vs; ws,
        Ψ i v w
      )
    }}}.
  Proof.
    iIntros "%Ht %Φ #Hfn HΦ".
    pose Ψ' i vs_left ws := (
      [∗ list] j ↦ v; w ∈ vs_left; ws, Ψ j v w
    )%I.
    wp۰apply (list٠mapiｰspec Ψ'); [done | | iSteps].
    rewrite /Ψ'. iSteps.
    rewrite big_sepL2_snoc length_take Nat.min_l; last iSteps.
    eapply Nat.lt_le_incl, lookup_lt_Some. done.
  Qed.
  Lemma list٠mapiｰspecｰdisentangled' Ψ fn t vs :
    list۰model' t vs →
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
      list۰model t' ws ∗
      ( [∗ list] i ↦ v; w ∈ vs; ws,
        Ψ i v w
      )
    }}}.
  Proof.
    iIntros "%Ht %Φ Hfn HΦ".
    pose Ψ' i vs_left ws := (
      [∗ list] j ↦ v; w ∈ vs_left; ws, Ψ j v w
    )%I.
    wp۰apply (list٠mapiｰspec' Ψ' with "[Hfn]"); [done | | iSteps].
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn"). iSteps.
    rewrite big_sepL2_snoc length_take Nat.min_l; last iSteps.
    eapply Nat.lt_le_incl, lookup_lt_Some. done.
  Qed.

  Lemma list٠mapｰspec Ψ fn t vs :
    list۰model' t vs →
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
      list۰model t' ws ∗
      Ψ (length vs) vs ws
    }}}.
  Proof.
    iIntros "%Ht %Φ (HΨ & #Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (list٠mapiｰspec Ψ with "[$HΨ] HΦ"); first done.
    iSteps.
  Qed.
  Lemma list٠mapｰspec' Ψ fn t vs :
    list۰model' t vs →
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
      list۰model t' ws ∗
      Ψ (length vs) vs ws
    }}}.
  Proof.
    iIntros "%Ht %Φ (HΨ & Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (list٠mapiｰspec' Ψ with "[$HΨ Hfn] HΦ"); first done.
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.
  Lemma list٠mapｰspecｰdisentangled Ψ fn t vs :
    list۰model' t vs →
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
      list۰model t' ws ∗
      ( [∗ list] i ↦ v; w ∈ vs; ws,
        Ψ i v w
      )
    }}}.
  Proof.
    iIntros "%Ht %Φ #Hfn HΦ".
    wp۰rec.
    wp۰apply+ (list٠mapiｰspecｰdisentangled Ψ with "[] HΦ"); first done.
    iSteps.
  Qed.
  Lemma list٠mapｰspecｰdisentangled' Ψ fn t vs :
    list۰model' t vs →
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
      list۰model t' ws ∗
      ( [∗ list] i ↦ v; w ∈ vs; ws,
        Ψ i v w
      )
    }}}.
  Proof.
    iIntros "%Ht %Φ Hfn HΦ".
    wp۰rec.
    wp۰apply+ (list٠mapiｰspecｰdisentangled' Ψ with "[Hfn] HΦ"); first done.
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  Lemma list٠forallｰspec Ψ pred t vs :
    list۰model' t vs →
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
    all: wp۰rec.
    - iSteps.
    - wp۰apply+ (wpｰwand with "(Hpred [%])") as (res) "(%b & -> & HΨ0)".
      { rewrite lookup_cons_Some. left. done. }
      destruct b.
      + wp۰apply+ ("IH" $! (λ i, Ψ ˖i) with "[//]") as ([]) "HΨ".
        { iIntros "!> %i %w %Hlookup".
          iSpecialize ("Hpred" $! ˖i).
          iSteps.
        }
        * iSteps.
        * iDestruct "HΨ" as "(%i & %w & %Hlookup & HΨ)".
          iSteps. iExists ˖i. iSteps.
      + iSteps. iExists 0. iSteps.
  Qed.

  Lemma list٠existsｰspec Ψ pred t vs :
    list۰model' t vs →
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
    all: wp۰rec.
    - iSteps.
    - wp۰apply+ (wpｰwand with "(Hpred [%])") as (res) "(%b & -> & HΨ0)".
      { rewrite lookup_cons_Some. left. done. }
      destruct b.
      + iSteps. iExists 0. iSteps.
      + wp۰apply+ ("IH" $! (λ i, Ψ ˖i) with "[//]") as ([]) "HΨ".
        { iIntros "!> %i %w %Hlookup".
          iSpecialize ("Hpred" $! ˖i).
          iSteps.
        }
        * iDestruct "HΨ" as "(%i & %w & %Hlookup & HΨ)".
          iSteps. iExists ˖i. iSteps.
        * iSteps.
  Qed.
End zoo۰G.

Require zoo_std.list__opaque.
