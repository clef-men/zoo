Require Import zoo.prelude.
Require Import zoo.base.
Require Export zoo_std.bqueue__code.
Require Import zoo_std.bqueue__types.
Require Import zoo_std.option.
Require Import zoo_std.array.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type l : location.
Implicit Type front back : nat.
Implicit Type v t : val.
Implicit Type o : option val.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Definition bqueue۰model t (cap : nat) vs : iProp Σ :=
    ∃ l data front back extra,
    ⌜t = #l⌝ ∗
    l.[capacity] ↦□ #cap ∗
    l.[data] ↦□ data ∗
    l.[front] ↦ #front ∗
    l.[back] ↦ #back ∗
    array۰cslice data cap front (DfracOwn 1) vs ∗
    array۰cslice data cap back (DfracOwn 1) (replicate extra ()%V) ∗
    ⌜back = (front + length vs)%nat⌝ ∗
    ⌜cap = (length vs + extra)%nat⌝.
  #[local] Instance : CustomIpat "model" :=
    " ( %l
      & %data
      & %front
      & %back
      & %extra
      & ->
      & Hl_capacity
      & Hl_data
      & Hl_front
      & Hl_back
      & Hvs
      & Hextra
      & %
      & %
      )
    ".

  #[global] Instance bqueue۰model𑁒timeless t cap vs :
    Timeless (bqueue۰model t cap vs).
  Proof.
    apply _.
  Qed.

  Lemma bqueue۰model𑁒valid t cap vs :
    bqueue۰model t cap vs ⊢
    ⌜length vs ≤ cap⌝.
  Proof.
    iSteps.
  Qed.
  Lemma bqueue۰model𑁒exclusive t cap1 vs1 cap2 vs2 :
    bqueue۰model t cap1 vs1 -∗
    bqueue۰model t cap2 vs2 -∗
    False.
  Proof.
    iSteps.
  Qed.

  Lemma bqueue٠create𑁒spec cap :
    (0 ≤ cap)%Z →
    {{{
      True
    }}}
      bqueue٠create #cap
    {{{
      t
    , RET t;
      bqueue۰model t ₊cap []
    }}}.
  Proof.
    iIntros "% %Φ _ HΦ".

    wp۰rec.
    wp۰apply (array٠unsafe_make𑁒spec with "[//]") as (data) "Hextra"; first done.
    iApply array۰model𑁒to𑁒cslice in "Hextra". simpl_length.
    iDestruct (array۰cslice𑁒to𑁒inv with "Hextra") as "#Hdata_inv".
    iDestruct (array۰cslice𑁒nil with "Hdata_inv") as "Hvs".
    wp۰block l as "(Hl_capacity & Hl_data & Hl_front & Hl_back & _)".
    iFrameSteps. rewrite Z2Nat.id //. iSteps.
  Qed.

  Lemma bqueue٠size𑁒spec t cap vs :
    {{{
      bqueue۰model t cap vs
    }}}
      bqueue٠size t
    {{{
      RET #(length vs);
      bqueue۰model t cap vs
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".

    wp۰rec. do 2 wp۰load. wp۰pures.
    assert (back - front = length vs)%Z as -> by lia.
    iSteps.
  Qed.

  Lemma bqueue٠is_empty𑁒spec t cap vs :
    {{{
      bqueue۰model t cap vs
    }}}
      bqueue٠is_empty t
    {{{
      RET #(bool_decide (vs = []%list));
      bqueue۰model t cap vs
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".

    wp۰rec.
    wp۰apply (bqueue٠size𑁒spec with "Hmodel") as "Hmodel".
    wp۰pures.
    rewrite (bool_decide_ext (⁺(length vs) = 0) (vs = [])).
    { rewrite -length_zero_iff_nil. lia. }
    iApply ("HΦ" with "Hmodel").
  Qed.

  Lemma bqueue٠unsafe_get𑁒spec {t cap vs i} v :
    (0 ≤ i)%Z →
    vs !! ₊i = Some v →
    {{{
      bqueue۰model t cap vs
    }}}
      bqueue٠unsafe_get t #i
    {{{
      RET v;
      bqueue۰model t cap vs
    }}}.
  Proof.
    iIntros "%Hi %Hlookup %Φ (:model) HΦ".

    wp۰rec. do 2 wp۰load.
    wp۰apply (array٠unsafe_cget𑁒spec with "Hvs"); [lia | done | lia |].
    iSteps.
  Qed.

  Lemma bqueue٠unsafe_set𑁒spec t cap vs i v :
    (0 ≤ i < length vs)%Z →
    {{{
      bqueue۰model t cap vs
    }}}
      bqueue٠unsafe_set t #i v
    {{{
      RET ();
      bqueue۰model t cap (<[₊i := v]> vs)
    }}}.
  Proof.
    iIntros "%Hi %Φ (:model) HΦ".

    wp۰rec. do 2 wp۰load.
    wp۰apply (array٠unsafe_cset𑁒spec with "Hvs"); first lia.
    replace (₊(front + i) - front) with ₊i by lia.
    iSteps; simpl_length.
  Qed.

  Lemma bqueue٠push𑁒spec t cap vs v :
    {{{
      bqueue۰model t cap vs
    }}}
      bqueue٠push t v
    {{{
      b
    , RET #b;
      ⌜if b then True else length vs = cap⌝ ∗
      bqueue۰model t cap (if b then vs ++ [v] else vs)
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".

    wp۰rec. do 3 wp۰load. wp۰pures.
    case_bool_decide; first iSteps.
    wp۰load.
    destruct (Nat.lt_exists_pred 0 extra) as (extra' & -> & _); first lia.
    iDestruct (array۰cslice𑁒cons with "Hextra") as "(Hcell & Hextra)". rewrite -/replicate.
    wp۰apply (array٠unsafe_cset𑁒spec𑁒cell with "Hcell") as "Hcell"; first done.
    iDestruct (array۰cslice𑁒app₁ with "Hvs Hcell") as "Hvs"; first done.
    wp۰store. wp۰pures.
    replace (back + 1)%Z with ⁺˖back by lia.
    iSteps; iPureIntro; simpl_length/=; lia.
  Qed.

  Lemma bqueue٠pop_front𑁒spec t cap vs :
    {{{
      bqueue۰model t cap vs
    }}}
      bqueue٠pop_front t
    {{{
      RET head vs;
      bqueue۰model t cap (tail vs)
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".

    wp۰rec. do 2 wp۰load. wp۰pures.
    case_bool_decide.

    - destruct vs; last naive_solver lia.
      iSteps.

    - destruct vs as [| v vs]; first naive_solver. simpl in *.
      wp۰load.
      iDestruct (array۰cslice𑁒cons with "Hvs") as "(Hcell & Hvs)".
      wp۰apply+ (array٠unsafe_cget𑁒spec𑁒cell with "Hcell") as "Hcell"; first done.
      wp۰apply+ (array٠unsafe_cset𑁒spec𑁒cell with "Hcell") as "Hcell"; first done.
      wp۰store. wp۰pures.
      iApply array۰cslice𑁒shift𑁒right in "Hcell".
      iDestruct (array۰cslice𑁒app₁ with "Hextra Hcell") as "Hextra".
      { simpl_length. lia. }
      iApply "HΦ".
      rewrite -replicate_S_end.
      replace (front + 1)%Z with ⁺˖front by lia.
      iFrameSteps.
  Qed.

  Lemma bqueue٠pop_back𑁒spec t cap vs :
    {{{
      bqueue۰model t cap vs
    }}}
      bqueue٠pop_back t
    {{{
      o
    , RET o;
      match o with
      | None =>
          ⌜vs = []⌝ ∗
          bqueue۰model t cap []
      | Some v =>
          ∃ vs',
          ⌜vs = vs' ++ [v]⌝ ∗
          bqueue۰model t cap vs'
      end
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".

    wp۰rec. do 2 wp۰load. wp۰pures.
    case_bool_decide.

    - destruct vs; last naive_solver lia.
      iSpecialize ("HΦ" $! None).
      iSteps.

    - destruct vs as [| v vs _] using rev_ind; first naive_solver. simpl_length/= in *.
      wp۰load.
      iDestruct (array۰cslice𑁒app with "Hvs") as "(Hvs & Hcell)".
      wp۰apply+ (array٠unsafe_cget𑁒spec𑁒cell with "Hcell") as "Hcell"; first lia.
      wp۰apply+ (array٠unsafe_cset𑁒spec𑁒cell with "Hcell") as "Hcell"; first lia.
      wp۰store. wp۰pures.
      iDestruct (array۰cslice𑁒cons₂' with "Hcell Hextra") as "Hextra"; first lia.
      iApply ("HΦ" $! (Some v)).
      rewrite -replicate_S.
      iExists vs. iFrameSteps.
  Qed.
End zoo۰G.

Require zoo_std.bqueue__opaque.

#[global] Opaque bqueue۰model.
