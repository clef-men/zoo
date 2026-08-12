Require Import zoo.prelude.
Require Import zoo.base.
Require Export zoo_std.dynarray_1__code.
Require Import zoo_std.dynarray_1__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type i : nat.
Implicit Type l : location.
Implicit Type v t fn : val.
Implicit Type vs : list val.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  #[local] Definition model' t vs extra : iProp Σ :=
    ∃ l data,
    ⌜t = #l⌝ ∗
    l.[size] ↦ #(length vs) ∗
    l.[data] ↦ data ∗
    array۰model data (DfracOwn 1) (vs ++ replicate extra ()%V).
  #[local] Instance : CustomIpat "model'" :=
    " ( %l{}
      & %data{}
      & ->
      & Hl{}_size
      & Hl{}_data
      & Hmodel
      )
    ".
  Definition dynarray_1۰model t vs : iProp Σ :=
    ∃ extra,
    model' t vs extra.
  #[local] Instance : CustomIpat "model" :=
    " ( %extra
      & {{lazy}Hmodel;(:model')}
      )
    ".

  #[global] Instance dynarray_1۰modelｰtimeless t vs :
    Timeless (dynarray_1۰model t vs).
  Proof.
    apply _.
  Qed.

  Lemma dynarray_1٠createｰspec' :
    {{{
      True
    }}}
      dynarray_1٠create ()
    {{{
      l
    , RET #l;
      dynarray_1۰model #l [] ∗
      meta_token l (↑nroot.@"user")
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp۰rec.
    wp۰apply (array٠createｰspec with "[//]") as "%data Hmodel".
    wp۰block l as "Hl_meta" "(Hl_size & Hl_data & _)".
    iDestruct (meta_tokenｰdifference (↑nroot.@"user") with "Hl_meta") as "(Hl_meta & _)"; first done.
    iSteps. iExists 0. iSteps.
  Qed.
  Lemma dynarray_1٠createｰspec :
    {{{
      True
    }}}
      dynarray_1٠create ()
    {{{
      t
    , RET t;
      dynarray_1۰model t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp۰apply (dynarray_1٠createｰspec' with "[//]").
    iSteps.
  Qed.

  Lemma dynarray_1٠makeｰspec sz v :
    (0 ≤ sz)%Z →
    {{{
      True
    }}}
      dynarray_1٠make #sz v
    {{{
      t
    , RET t;
      dynarray_1۰model t (replicate ₊sz v)
    }}}.
  Proof.
    iIntros "% %Φ _ HΦ".
    Z_to_nat sz. rewrite Nat2Z.id.
    wp۰rec.
    wp۰apply+ (array٠unsafe_makeｰspec with "[//]") as "%data Hmodel"; first done.
    iSteps.
    - simp_length.
    - iExists 0. rewrite right_id Nat2Z.id. iSteps.
  Qed.

  Lemma dynarray_1٠initiｰspec Ψ sz fn :
    (0 ≤ sz)%Z →
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
      dynarray_1٠initi #sz fn
    {{{
      t vs
    , RET t;
      ⌜length vs = ₊sz⌝ ∗
      dynarray_1۰model t vs ∗
      Ψ ₊sz vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & #Hfn) HΦ".

    wp۰rec.
    wp۰apply+ (array٠unsafe_initiｰspec (λ _, Ψ) with "[$HΨ]") as "%data %vs (%Hvs & Hmodel & HΨ)"; [done | iSteps |].
    wp۰block l as "(Hl_size & Hl_data & _)".
    iSteps. iExists 0. rewrite right_id. iSteps.
  Qed.
  Lemma dynarray_1٠initiｰspec' Ψ sz fn :
    (0 ≤ sz)%Z →
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
      dynarray_1٠initi #sz fn
    {{{
      t vs
    , RET t;
      ⌜length vs = ₊sz⌝ ∗
      dynarray_1۰model t vs ∗
      Ψ ₊sz vs
    }}}.
  Proof.
    iIntros "%Hsz %Φ (HΨ & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep (λ _, ?Ξ') _] => set Ξ := Ξ' end.
    pose (Ψ' i vs := (
      Ψ i vs ∗
      [∗ list] j ∈ seq i (₊sz - i), Ξ j
    )%I).
    wp۰apply (dynarray_1٠initiｰspec Ψ' with "[$HΨ Hfn]"); first done.
    { rewrite Nat.sub_0_r. iFrame. iIntros "!> %i %vs (%Hi1 & %Hi2) (HΨ & HΞ)".
      destruct (Nat.lt_exists_pred 0 (₊sz - i)) as (k & Hk & _); first lia. rewrite Hk.
      rewrite -cons_seq. iDestruct "HΞ" as "(Hfn & HΞ)".
      wp۰apply (wpｰwand with "(Hfn [//] HΨ)").
      iSteps. rewrite Nat.sub_succ_r Hk //.
    }
    iSteps.
  Qed.
  Lemma dynarray_1٠initiｰspecｰdisentangled Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      □ (
        ∀ i,
        ⌜i < ₊sz⌝ -∗
        WP fn #i {{ v,
          ▷ Ψ i v
        }}
      )
    }}}
      dynarray_1٠initi #sz fn
    {{{
      t vs
    , RET t;
      ⌜length vs = ₊sz⌝ ∗
      dynarray_1۰model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Hsz %Φ #Hfn HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp۰apply (dynarray_1٠initiｰspec Ψ' with "[] HΦ"); first done.
    rewrite /Ψ'. iSteps.
    rewrite big_sepL_snoc. iSteps.
  Qed.
  Lemma dynarray_1٠initiｰspecｰdisentangled' Ψ sz fn :
    (0 ≤ sz)%Z →
    {{{
      ( [∗ list] i ∈ seq 0 ₊sz,
        WP fn #i {{ v,
          ▷ Ψ i v
        }}
      )
    }}}
      dynarray_1٠initi #sz fn
    {{{
      t vs
    , RET t;
      ⌜length vs = ₊sz⌝ ∗
      dynarray_1۰model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Hsz %Φ Hfn HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp۰apply (dynarray_1٠initiｰspec' Ψ' with "[Hfn] HΦ"); first done.
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn").
    iSteps. rewrite big_sepL_snoc. iSteps.
  Qed.

  Lemma dynarray_1٠sizeｰspec t vs :
    {{{
      dynarray_1۰model t vs
    }}}
      dynarray_1٠size t
    {{{
      RET #(length vs);
      dynarray_1۰model t vs
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma dynarray_1٠capacityｰspec t vs :
    {{{
      dynarray_1۰model t vs
    }}}
      dynarray_1٠capacity t
    {{{
      cap
    , RET #cap;
      ⌜length vs ≤ cap⌝ ∗
      dynarray_1۰model t vs
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".
    wp۰rec. wp۰load.
    wp۰apply (array٠sizeｰspec with "Hmodel") as "Hmodel".
    simp_length. iSteps.
  Qed.

  Lemma dynarray_1٠is_emptyｰspec t vs :
    {{{
      dynarray_1۰model t vs
    }}}
      dynarray_1٠is_empty t
    {{{
      RET #(bool_decide (vs = []%list));
      dynarray_1۰model t vs
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp۰rec.
    wp۰apply+ (dynarray_1٠sizeｰspec with "Hmodel") as "Hmodel".
    wp۰pures.
    destruct vs; iApply ("HΦ" with "Hmodel").
  Qed.

  Lemma dynarray_1٠getｰspec t vs (i : Z) v :
    (0 ≤ i)%Z →
    vs !! ₊i = Some v →
    {{{
      dynarray_1۰model t vs
    }}}
      dynarray_1٠get t #i
    {{{
      RET v;
      dynarray_1۰model t vs
    }}}.
  Proof.
    iIntros "%Hi %Hlookup %Φ (:model) HΦ".
    wp۰rec. wp۰load.
    wp۰apply (array٠unsafe_getｰspec with "Hmodel"); [lia | | done |].
    { rewrite lookup_app_l //. eapply lookup_lt_Some. done. }
    iSteps.
  Qed.

  Lemma dynarray_1٠setｰspec t vs (i : Z) v :
    (0 ≤ i < length vs)%Z →
    {{{
      dynarray_1۰model t vs
    }}}
      dynarray_1٠set t #i v
    {{{
      RET ();
      dynarray_1۰model t (<[₊i := v]> vs)
    }}}.
  Proof.
    iIntros "%Hi %Φ (:model) HΦ".
    wp۰rec. wp۰load.
    wp۰apply (array٠unsafe_setｰspec with "Hmodel") as "Hmodel".
    { simp_length. lia. }
    iApply "HΦ".
    iExists extra. iStep.
    rewrite length_insert insert_app_l; first lia. iSteps.
  Qed.

  #[local] Lemma dynarray_1٠next_capacityｰspec n :
    (0 ≤ n)%Z →
    {{{
      True
    }}}
      dynarray_1٠next_capacity #n
    {{{
      m
    , RET #m;
      ⌜n ≤ m⌝%Z
    }}}.
  Proof.
    iSteps.
  Qed.
  #[local] Lemma dynarray_1٠reserveｰspec' t vs n :
    (0 ≤ n)%Z →
    {{{
      dynarray_1۰model t vs
    }}}
      dynarray_1٠reserve t #n
    {{{
      extra
    , RET ();
      ⌜₊n ≤ length vs + extra⌝ ∗
      model' t vs extra
    }}}.
  Proof.
    iIntros "%Hn %Φ (:model) HΦ".
    wp۰rec. wp۰load.
    wp۰apply+ (array٠sizeｰspec with "Hmodel") as "Hmodel".
    wp۰pures.
    case_bool_decide as Htest.
    all: wp۰pures.
    all: simp_length in Htest.
    - wp۰apply (dynarray_1٠next_capacityｰspec with "[//]") as "%n' %Hn'"; first lia.
      wp۰apply int٠maxｰspec.
      wp۰apply+ (array٠unsafe_allocｰspec with "[//]") as "%data' Hmodel'"; first lia.
      wp۰load.
      wp۰apply+ (array٠unsafe_copy_sliceｰspec with "[$Hmodel $Hmodel']") as "(Hmodel & Hmodel')"; try lia.
      { simp_length. lia. }
      { simp_length. lia. }
      wp۰store.
      iApply ("HΦ" $! (₊(n `max` n') - length vs)).
      rewrite Nat2Z.id with_sliceｰ0 drop_replicate take_app_length.
      iSteps.
    - iApply ("HΦ" $! extra).
      iSteps.
  Qed.
  Lemma dynarray_1٠reserveｰspec t vs n :
    (0 ≤ n)%Z →
    {{{
      dynarray_1۰model t vs
    }}}
      dynarray_1٠reserve t #n
    {{{
      RET ();
      dynarray_1۰model t vs
    }}}.
  Proof.
    iIntros "%Hn %Φ Hmodel HΦ".
    wp۰apply (dynarray_1٠reserveｰspec' with "Hmodel"); first done.
    iSteps.
  Qed.

  #[local] Lemma dynarray_1٠reserve_extraｰspec' t vs n :
    (0 ≤ n)%Z →
    {{{
      dynarray_1۰model t vs
    }}}
      dynarray_1٠reserve_extra t #n
    {{{
      extra
    , RET ();
      ⌜₊n ≤ extra⌝ ∗
      model' t vs extra
    }}}.
  Proof.
    iIntros "%Hn %Φ (:model) HΦ".
    wp۰rec. wp۰load.
    wp۰apply+ (dynarray_1٠reserveｰspec' with "[Hl_size Hl_data Hmodel]") as "%extra' (%Hextra' & Hmodel)"; [lia | iFrameSteps |].
    iApply ("HΦ" $! extra').
    iFrameSteps.
  Qed.
  Lemma dynarray_1٠reserve_extraｰspec t vs n :
    (0 ≤ n)%Z →
    {{{
      dynarray_1۰model t vs
    }}}
      dynarray_1٠reserve_extra t #n
    {{{
      RET ();
      dynarray_1۰model t vs
    }}}.
  Proof.
    iIntros "%Hn %Φ Hmodel HΦ".
    wp۰apply (dynarray_1٠reserve_extraｰspec' with "Hmodel"); first done.
    iSteps.
  Qed.

  Lemma dynarray_1٠growｰspec t vs sz v :
    (0 ≤ sz)%Z →
    {{{
      dynarray_1۰model t vs
    }}}
      dynarray_1٠grow t #sz v
    {{{
      RET ();
      dynarray_1۰model t (vs ++ replicate (₊sz - length vs) v)
    }}}.
  Proof.
    iIntros "% %Φ (:model) HΦ".
    wp۰rec. wp۰load. wp۰pures.
    case_bool_decide.
    - wp۰apply+ (dynarray_1٠reserveｰspec' with "[$Hl_size $Hl_data $Hmodel //]") as "%extra' (%Hextra' & (:model' ='))"; first lia.
      wp۰load.
      wp۰apply+ (array٠unsafe_fill_sliceｰspec with "Hmodel") as "Hmodel".
      { lia. }
      { simp_length. lia. }
      iSteps.
      { iPureIntro.
        simp_length.
        rewrite -Nat.le_add_sub; first lia.
        rewrite Z2Nat.id //.
      } {
        rewrite Z2Nat.inj_sub; first lia.
        rewrite Nat2Z.id with_sliceｰappｰlength drop_replicate assoc.
        iSteps.
      }
    - assert (₊sz - length vs = 0) as -> by lia. rewrite right_id.
      iSteps.
  Qed.

  Lemma dynarray_1٠pushｰspec t vs v :
    {{{
      dynarray_1۰model t vs
    }}}
      dynarray_1٠push t v
    {{{
      RET ();
      dynarray_1۰model t (vs ++ [v])
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp۰rec.
    wp۰apply+ (dynarray_1٠reserve_extraｰspec' with "Hmodel") as "%extra (%Hextra & (:model'))"; first lia.
    wp۰load. wp۰store. wp۰load.
    wp۰apply (array٠unsafe_setｰspec with "Hmodel").
    { simp_length. lia. }
    rewrite Nat2Z.id insert_app_r_alt // Nat.sub_diag insert_replicate_lt // /= (assoc (++) vs [v] (replicate _ _)).
    iSteps. simp_length. iSteps.
  Qed.

  Lemma dynarray_1٠popｰspec {t vs} vs' v :
    vs = vs' ++ [v] →
    {{{
      dynarray_1۰model t vs
    }}}
      dynarray_1٠pop t
    {{{
      RET v;
      dynarray_1۰model t vs'
    }}}.
  Proof.
    iIntros (->) "%Φ (:model) HΦ".
    wp۰rec. wp۰load. wp۰store. wp۰load.
    simp_length. rewrite Nat.add_1_r Z.sub_1_r -Nat2Z.inj_pred /=; first lia.
    wp۰apply+ (array٠unsafe_getｰspec with "Hmodel") as "Hmodel"; [lia | | done |].
    { rewrite lookup_app_l; first (simp_length/=; lia).
      rewrite lookup_app_r; first lia.
      rewrite Nat2Z.id Nat.sub_diag //.
    }
    wp۰apply+ (array٠unsafe_setｰspec with "Hmodel").
    { simp_length/=. lia. }
    iSteps. iExists ˖extra.
    rewrite -assoc insert_app_r_alt; first lia. rewrite Nat2Z.id Nat.sub_diag //.
  Qed.

  Lemma dynarray_1٠fit_capacityｰspec t vs :
    {{{
      dynarray_1۰model t vs
    }}}
      dynarray_1٠fit_capacity t
    {{{
      RET ();
      dynarray_1۰model t vs
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".
    wp۰rec. do 2 wp۰load.
    wp۰apply+ (array٠sizeｰspec with "Hmodel") as "Hmodel".
    wp۰pures.
    case_bool_decide; wp۰pures; first iSteps.
    wp۰apply (array٠unsafe_shrinkｰspec with "Hmodel") as "%data' (_ & Hmodel)".
    { simp_length. lia. }
    wp۰store.
    iSteps. iExists 0. rewrite Nat2Z.id take_app_length right_id //.
  Qed.

  Lemma dynarray_1٠resetｰspec t vs :
    {{{
      dynarray_1۰model t vs
    }}}
      dynarray_1٠reset t
    {{{
      RET ();
      dynarray_1۰model t []
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".
    wp۰rec. wp۰store.
    wp۰apply+ (array٠createｰspec with "[//]") as "%data' Hmodel'".
    wp۰store.
    iSteps. iExists 0. iSteps.
  Qed.

  Lemma dynarray_1٠iteriｰspec Ψ fn t vs :
    {{{
      ▷ Ψ 0 [] ∗
      dynarray_1۰model t vs ∗
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
      dynarray_1٠iteri fn t
    {{{
      RET ();
      dynarray_1۰model t vs ∗
      Ψ (length vs) vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & (:model) & #Hfn) HΦ".
    wp۰rec. do 2 wp۰load.
    wp۰apply (array٠unsafe_iteri_sliceｰspec Ψ with "[$HΨ $Hmodel]").
    { lia. }
    { lia. }
    { simp_length. lia. }
    { iIntros "!> %i %v %Hi %Hlookup HΨ".
      rewrite sliceｰ0 take_app_le; first lia.
      wp۰apply (wpｰwand with "(Hfn [%] HΨ)").
      { rewrite lookup_app_l // in Hlookup. lia. }
      iSteps.
    }
    rewrite sliceｰ0 Nat2Z.id take_app_length. iSteps.
  Qed.
  Lemma dynarray_1٠iteriｰspec' Ψ fn t vs :
    {{{
      ▷ Ψ 0 [] ∗
      dynarray_1۰model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i (take i vs) -∗
        WP fn #i v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ ˖i (take i vs ++ [v])
        }}
      )
    }}}
      dynarray_1٠iteri fn t
    {{{
      RET ();
      dynarray_1۰model t vs ∗
      Ψ (length vs) vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep ?Ξ' _] => set Ξ := Ξ' end.
    pose (Ψ' i vs_left := (
      Ψ i vs_left ∗
      [∗ list] j ↦ v ∈ drop i vs, Ξ (i + j) v
    )%I).
    wp۰apply (dynarray_1٠iteriｰspec Ψ' with "[$HΨ $Hmodel $Hfn]").
    { iIntros "!> %i %v %Hlookup (HΨ & HΞ)".
      erewrite drop_S => //.
      iDestruct "HΞ" as "(Hfn & HΞ)".
      rewrite Nat.add_0_r. setoid_rewrite Nat.add_succ_r. iSteps.
    }
    iSteps.
  Qed.
  Lemma dynarray_1٠iteriｰspecｰdisentangled Ψ fn t vs :
    {{{
      dynarray_1۰model t vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        WP fn #i v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i v
        }}
      )
    }}}
      dynarray_1٠iteri fn t
    {{{
      RET ();
      dynarray_1۰model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & #Hfn) HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp۰apply (dynarray_1٠iteriｰspec Ψ' with "[$Hmodel]").
    { rewrite /Ψ'. iSteps.
      rewrite big_sepL_snoc length_take Nat.min_l; last iSteps.
      eapply Nat.lt_le_incl, lookup_lt_Some. done.
    }
    iSteps.
  Qed.
  Lemma dynarray_1٠iteriｰspecｰdisentangled' Ψ fn t vs :
    {{{
      dynarray_1۰model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn #i v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i v
        }}
      )
    }}}
      dynarray_1٠iteri fn t
    {{{
      RET ();
      dynarray_1۰model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & Hfn) HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp۰apply (dynarray_1٠iteriｰspec' Ψ' with "[$Hmodel Hfn]").
    { rewrite /Ψ'. iSteps.
      iApply (big_sepL_impl with "Hfn"). iSteps.
      rewrite big_sepL_snoc length_take Nat.min_l; last iSteps.
      eapply Nat.lt_le_incl, lookup_lt_Some. done.
    }
    iSteps.
  Qed.

  Lemma dynarray_1٠iterｰspec Ψ fn t vs :
    {{{
      ▷ Ψ 0 [] ∗
      dynarray_1۰model t vs ∗
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
      dynarray_1٠iter fn t
    {{{
      RET ();
      dynarray_1۰model t vs ∗
      Ψ (length vs) vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & #Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (dynarray_1٠iteriｰspec Ψ with "[$HΨ $Hmodel] HΦ").
    iSteps.
  Qed.
  Lemma dynarray_1٠iterｰspec' Ψ fn t vs :
    {{{
      ▷ Ψ 0 [] ∗
      dynarray_1۰model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i (take i vs) -∗
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ ˖i (take i vs ++ [v])
        }}
      )
    }}}
      dynarray_1٠iter fn t
    {{{
      RET ();
      dynarray_1۰model t vs ∗
      Ψ (length vs) vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (dynarray_1٠iteriｰspec' Ψ with "[$HΨ $Hmodel Hfn] HΦ").
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.
  Lemma dynarray_1٠iterｰspecｰdisentangled Ψ fn t vs :
    {{{
      dynarray_1۰model t vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i v
        }}
      )
    }}}
      dynarray_1٠iter fn t
    {{{
      RET ();
      dynarray_1۰model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & #Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (dynarray_1٠iteriｰspecｰdisentangled Ψ with "[$Hmodel] HΦ").
    iSteps.
  Qed.
  Lemma dynarray_1٠iterｰspecｰdisentangled' Ψ fn t vs :
    {{{
      dynarray_1۰model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i v
        }}
      )
    }}}
      dynarray_1٠iter fn t
    {{{
      RET ();
      dynarray_1۰model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (dynarray_1٠iteriｰspecｰdisentangled' Ψ with "[$Hmodel Hfn] HΦ").
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.
End zoo۰G.

Require zoo_std.dynarray_1__opaque.

#[global] Opaque dynarray_1۰model.
