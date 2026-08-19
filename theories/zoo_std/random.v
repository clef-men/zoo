Require Import zoo.prelude.
Require Import zoo.base.
Require Export zoo_std.random__code.
Require Import zoo_std.random__types.
Require Import zoo.options.

Axiom random٠initｰspec : ∀ `{zoo۰G : !ZooG Σ} Φ,
  Φ ()%V ⊢
  WP random٠init () {{ Φ }}.

Axiom random٠bitsｰspec : ∀ `{zoo۰G : !ZooG Σ} Φ,
  ( ∀ n : Z,
    Φ #n
  ) ⊢
  WP random٠bits () {{ Φ }}.

Axiom random٠intｰspec : ∀ `{zoo۰G : !ZooG Σ} ub Φ,
  (0 < ub)%Z →
  ( ∀ n,
    ⌜0 ≤ n < ub⌝%Z -∗
    Φ #n
  ) ⊢
  WP random٠int #ub {{ Φ }}.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Lemma random٠intｰspecｰnat (ub : nat) Φ :
    0 < ub →
    ( ∀ n,
      ⌜n < ub⌝ -∗
      Φ #n
    ) ⊢
    WP random٠int #ub {{ Φ }}.
  Proof.
    iIntros "%Hub HΦ".
    wp۰apply random٠intｰspec as (n) "%Hn"; first lia.
    Z_to_nat n. iSteps.
  Qed.

  Lemma random٠int_in_rangeｰspec lb ub Φ :
    (lb < ub)%Z →
    ( ∀ n,
      ⌜lb ≤ n < ub⌝%Z -∗
      Φ #n
    ) ⊢
    WP random٠int_in_range #lb #ub {{ Φ }}.
  Proof.
    iIntros "%Hlt HΦ".
    wp۰rec.
    wp۰apply+ random٠intｰspec as "%n %Hn"; first lia.
    iSteps.
  Qed.
  Lemma random٠int_in_rangeｰspecｰnat lb ub Φ :
    lb < ub →
    ( ∀ n,
      ⌜lb ≤ n < ub⌝ -∗
      Φ #n
    ) ⊢
    WP random٠int_in_range #lb #ub {{ Φ }}.
  Proof.
    iIntros "%Hlt HΦ".
    wp۰rec.
    wp۰apply+ random٠intｰspec as "%n %Hn"; first lia.
    wp۰pures.
    Z_to_nat n. rewrite -Nat2Z.inj_add. iSteps.
  Qed.
End zoo۰G.

Section random۰state.
  Implicit Type t : val.

  Parameter random۰state۰model : ∀ `{zoo۰G : !ZooG Σ}, val → iProp Σ.

  Axiom random٠state٠createｰspec : ∀ `{zoo۰G : !ZooG Σ},
    {{{
      True
    }}}
      random٠state٠create ()
    {{{
      t
    , RET t;
      random۰state۰model t
    }}}.

  Axiom random٠state٠bitsｰspec : ∀ `{zoo۰G : !ZooG Σ} t,
    {{{
      random۰state۰model t
    }}}
      random٠state٠bits t
    {{{
      (n : Z)
    , RET #n;
      random۰state۰model t
    }}}.

  Axiom random٠state٠intｰspec : ∀ `{zoo۰G : !ZooG Σ} t ub,
    (0 < ub)%Z →
    {{{
      random۰state۰model t
    }}}
      random٠state٠int t #ub
    {{{
      n
    , RET #n;
      ⌜0 ≤ n < ub⌝%Z ∗
      random۰state۰model t
    }}}.

  Section zoo۰G.
    Context `{zoo۰G : !ZooG Σ}.

    Lemma random٠state٠intｰspecｰnat t (ub : nat) :
      0 < ub →
      {{{
        random۰state۰model t
      }}}
        random٠state٠int t #ub
      {{{
        n
      , RET #n;
        ⌜n < ub⌝ ∗
        random۰state۰model t
      }}}.
    Proof.
      iIntros "%Hub %Φ Ht HΦ".
      wp۰apply (random٠state٠intｰspec with "Ht") as (n) "(%Hn & Ht)"; first lia.
      Z_to_nat n. iSteps.
    Qed.

    Lemma random٠state٠int_in_rangeｰspec t lb ub :
      (lb < ub)%Z →
      {{{
        random۰state۰model t
      }}}
        random٠state٠int_in_range t #lb #ub
      {{{
        n
      , RET #n;
        ⌜lb ≤ n < ub⌝%Z ∗
        random۰state۰model t
      }}}.
    Proof.
      iIntros "%Hlt %Φ Ht HΦ".
      wp۰rec.
      wp۰apply+ (random٠state٠intｰspec with "Ht") as "%n (%Hn & Ht)"; first lia.
      iSteps.
    Qed.
    Lemma random٠state٠int_in_rangeｰspecｰnat t lb ub :
      lb < ub →
      {{{
        random۰state۰model t
      }}}
        random٠state٠int_in_range t #lb #ub
      {{{
        n
      , RET #n;
        ⌜lb ≤ n < ub⌝ ∗
        random۰state۰model t
      }}}.
    Proof.
      iIntros "%Hlt %Φ Ht HΦ".
      wp۰rec.
      wp۰apply+ (random٠state٠intｰspec with "Ht") as "%n (%Hn & Ht)"; first lia.
      wp۰pures.
      Z_to_nat n. rewrite -Nat2Z.inj_add. iSteps.
    Qed.
  End zoo۰G.
End random۰state.

Section random۰round.
  Implicit Type i n cnt : nat.
  Implicit Type prevs nexts : list nat.
  Implicit Type l : location.
  Implicit Type t rand arr : val.

  Section zoo۰G.
    Context `{zoo۰G : !ZooG Σ}.

    Definition random۰round۰model t sz prevs : iProp Σ :=
      ∃ l rand arr nexts,
      ⌜t = #l⌝ ∗
      ⌜nexts ++ reverse prevs ≡ₚ seq 0 sz⌝ ∗
      l.[round٠random] ↦ rand ∗
      l.[round٠array] ↦ arr ∗
      l.[round٠index] ↦ #(length nexts) ∗
      random۰state۰model rand ∗
      array۰model arr (DfracOwn 1) (#*@{nat} $ nexts ++ reverse prevs).
    #[local] Instance : CustomIpat "model" :=
      " ( %l
        & %rand
        & %arr
        & %nexts
        & ->
        & %Hpermutation
        & Hl_random
        & Hl_array
        & Hl_index
        & Hrand
        & Harr
        )
      ".

    Lemma random٠round٠createｰspec sz :
      (0 ≤ sz)%Z →
      {{{
        True
      }}}
        random٠round٠create #sz
      {{{
        t
      , RET t;
        random۰round۰model t ₊sz []
      }}}.
    Proof.
      iIntros "%Hsz %Φ _ HΦ".

      wp۰rec.

      pose (Ψ := λ arr i vs, (
        ⌜vs = #*@{nat} $ seq 0 i⌝
      )%I : iProp Σ).
      wp۰apply+ (array٠unsafe_initiｰspec Ψ) as (arr vs) "(_ & Harr & ->)"; first done.
      { iStep 2. iIntros "%arr %i %vs _ _ ->".
        wp۰pures.
        iPureIntro. rewrite seq_S fmap_snoc //.
      }

      wp۰apply (random٠state٠createｰspec with "[//]") as (rand) "Hrand".
      wp۰block l as "Hl_random Hl_array Hl_index".

      iApply "HΦ".
      iFrameSteps. iExists (seq 0 ₊sz).
      rewrite app_nil_r length_seq. iSteps.
    Qed.

    Lemma random٠round٠resetｰspec t sz prevs :
      {{{
        random۰round۰model t sz prevs
      }}}
        random٠round٠reset t
      {{{
        RET ();
        random۰round۰model t sz []
      }}}.
    Proof.
      iIntros "%Φ (:model) HΦ".

      wp۰rec. wp۰load.
      wp۰apply (array٠sizeｰspec with "Harr") as "Harr".

      iSteps. iExists (nexts ++ reverse prevs).
      rewrite app_nil_r. iSteps. simp_length.
    Qed.

    Lemma random٠round٠nextｰspec t sz prevs :
      length prevs ≠ sz →
      {{{
        random۰round۰model t sz prevs
      }}}
        random٠round٠next t
      {{{
        n
      , RET #n;
        ⌜n < sz⌝ ∗
        ⌜n ∉ prevs⌝ ∗
        random۰round۰model t sz (prevs ++ [n])
      }}}.
    Proof.
      iIntros "%Hprevs %Φ (:model) HΦ".
      pose proof Hpermutation as Hlength%Permutation_length.
      simp_length in Hlength.

      wp۰rec. do 3 wp۰load.
      wp۰apply+ (random٠state٠intｰspec with "Hrand") as (j) "(%Hj & Hrand)"; first lia.

      Z_to_nat j.
      set i := length nexts - 1.

      destruct (lookup_lt_is_Some_2 nexts j) as (prev & Hnexts_lookup_j); first lia.
      wp۰apply+ (array٠unsafe_getｰspec with "Harr") as "Harr".
      { lia. }
      { rewrite list_lookup_fmap. erewrite lookup_app_l_Some => //. }
      { lia. }

      destruct (lookup_lt_is_Some_2 nexts i) as (next & Hnexts_lookup_i); first lia.
      wp۰apply+ (array٠unsafe_getｰspec with "Harr") as "Harr".
      { lia. }
      { rewrite list_lookup_fmap. erewrite lookup_app_l_Some => //. }
      { lia. }

      wp۰apply+ (array٠unsafe_setｰspec with "Harr") as "Harr".
      { simp_length. lia. }
      wp۰apply+ (array٠unsafe_setｰspec with "Harr") as "Harr".
      { simp_length. lia. }
      wp۰store. wp۰pures.

      iApply "HΦ".
      iSplitR.
      { iPureIntro.
        assert (prev ∈ seq 0 sz) as ?%elem_of_seq; last naive_solver.
        rewrite -Hpermutation elem_of_app list_elem_of_lookup.
        naive_solver.
      }
      iSplitR.
      { iPureIntro.
        pose proof (NoDup_seq 0 sz) as Hnodup.
        rewrite -Hpermutation NoDup_app in Hnodup.
        setoid_rewrite elem_of_reverse in Hnodup.
        setoid_rewrite list_elem_of_lookup at 1 in Hnodup.
        naive_solver.
      }
      rewrite Nat2Z.id -!list_fmap_insert.
      assert (₊(length nexts - 1) = i) as -> by lia.
      assert (<[j := next]> (take i nexts) ++ [prev] = <[i := prev]> (<[j := next]> nexts)) as Heq.
      { destruct_decide (j = i) as -> | H.
        - rewrite list_insert_ge. { simp_length. lia. }
          rewrite list_insert_insert_eq insert_take_drop; first lia.
          rewrite skipn_all2 //; first lia.
        - rewrite list_insert_insert_ne // (insert_take_drop nexts); first lia.
          rewrite skipn_all2; first lia.
          rewrite -insert_app_l // length_take; first lia.
      }
      iSteps. iExists (<[j := next]> (take i nexts)). iSteps.
      + iPureIntro.
        rewrite -Hpermutation reverse_snoc (assoc _ _ [_]) Heq Permutationｰswap' //.
      + simp_length. iSteps.
      + rewrite reverse_snoc (assoc _ _ [_]) Heq insert_app_l; first lia.
        rewrite insert_app_l // length_insert; first lia.
    Qed.
  End zoo۰G.

  #[global] Opaque random۰round۰model.

  Section zoo۰G.
    Context `{zoo۰G : !ZooG Σ}.

    Definition random۰round۰model' t sz cnt : iProp Σ :=
      ∃ prevs,
      ⌜(cnt + length prevs)%nat = sz⌝ ∗
      random۰round۰model t sz prevs.
    #[local] Instance : CustomIpat "model'" :=
      " ( %prevs
        & %H
        & Ht
        )
      ".

    Lemma random٠round٠createｰspec' sz :
      (0 ≤ sz)%Z →
      {{{
        True
      }}}
        random٠round٠create #sz
      {{{
        t
      , RET t;
        random۰round۰model' t ₊sz ₊sz
      }}}.
    Proof.
      iIntros "%Hsz %Φ _ HΦ".

      wp۰apply (random٠round٠createｰspec with "[//]") as (t) "Ht"; first done.
      iStepFrameSteps.
    Qed.

    Lemma random٠round٠resetｰspec' t sz cnt :
      {{{
        random۰round۰model' t sz cnt
      }}}
        random٠round٠reset t
      {{{
        RET ();
        random۰round۰model' t sz sz
      }}}.
    Proof.
      iIntros "%Φ (:model') HΦ".

      wp۰apply (random٠round٠resetｰspec with "Ht") as "Ht".
      iStepFrameSteps.
    Qed.

    Lemma random٠round٠nextｰspec' t sz cnt :
      0 < cnt →
      {{{
        random۰round۰model' t sz cnt
      }}}
        random٠round٠next t
      {{{
        n
      , RET #n;
        ⌜n < sz⌝ ∗
        random۰round۰model' t sz (cnt - 1)
      }}}.
    Proof.
      iIntros "%Hcnt %Φ (:model') HΦ".

      wp۰apply (random٠round٠nextｰspec with "Ht") as (i) "(%Hi & Ht)"; first lia.
      iSteps. iExists (prevs ++ [i]). simp_length. iSteps.
    Qed.
  End zoo۰G.

  #[global] Opaque random۰round۰model'.
End random۰round.

Require zoo_std.random__opaque.
