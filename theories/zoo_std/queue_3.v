Require Import zoo.prelude.
Require Import zoo.base.
Require Import zoo_std.option.
Require Export zoo_std.queue_3__code.
Require Import zoo_std.queue_3__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type l : location.
Implicit Type front back : nat.
Implicit Type v t : val.
Implicit Type o : option val.

#[local] Definition min_capacity :=
  val۰to_nat' queue_3٠min_capacity.
#[local] Lemma queue_3٠min_capacityｰunfold :
  queue_3٠min_capacity = #min_capacity.
Proof.
  done.
Qed.
Opaque queue_3٠min_capacity.
Opaque min_capacity.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  #[local] Definition model' t vs extra : iProp Σ :=
    ∃ l data cap front back,
    ⌜t = #l⌝ ∗
    l.[data] ↦ data ∗
    l.[front] ↦ #front ∗
    l.[back] ↦ #back ∗
    array۰cslice data cap front (DfracOwn 1) vs ∗
    array۰cslice data cap back (DfracOwn 1) (replicate extra ()%V) ∗
    ⌜back = (front + length vs)%nat⌝ ∗
    ⌜cap = (length vs + extra)%nat⌝ ∗
    ⌜cap ≠ 0⌝.
  #[local] Instance : CustomIpat "model'" :=
    " ( %l
      & %data
      & %cap
      & %front
      & %back
      & ->
      & Hl_data
      & Hl_front
      & Hl_back
      & Hvs
      & Hextra
      & %Hback
      & %Hcap
      & %
      )
    ".
  Definition queue_3۰model t vs : iProp Σ :=
    ∃ extra,
    model' t vs extra.
  #[local] Instance : CustomIpat "model" :=
    " ( %extra
      & {{lazy}Hmodel;(:model')}
      )
    ".

  #[global] Instance queue_3۰modelｰtimeless t vs :
    Timeless (queue_3۰model t vs).
  Proof.
    apply _.
  Qed.

  Lemma queue_3۰modelｰexclusive t vs1 vs2 :
    queue_3۰model t vs1 -∗
    queue_3۰model t vs2 -∗
    False.
  Proof.
    iSteps.
  Qed.

  Lemma queue_3٠createｰspec :
    {{{
      True
    }}}
      queue_3٠create ()
    {{{
      t
    , RET t;
      queue_3۰model t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp۰rec. rewrite queue_3٠min_capacityｰunfold.
    wp۰apply (array٠unsafe_makeｰspec with "[//]") as (data) "Hextra"; first done.
    iApply array۰modelｰtoｰcslice in "Hextra". simp_length.
    iDestruct (array۰csliceｰtoｰinv with "Hextra") as "#Hdata_inv".
    iDestruct (array۰csliceｰnil with "Hdata_inv") as "Hvs".
    wp۰block l as "(Hl_data & Hl_front & Hl_back & _)".
    iSteps.
  Qed.

  Lemma queue_3٠sizeｰspec t vs :
    {{{
      queue_3۰model t vs
    }}}
      queue_3٠size t
    {{{
      RET #(length vs);
      queue_3۰model t vs
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".

    wp۰rec. do 2 wp۰load. wp۰pures.
    assert (back - front = length vs)%Z as -> by lia.
    iSteps.
  Qed.

  Lemma queue_3٠is_emptyｰspec t vs :
    {{{
      queue_3۰model t vs
    }}}
      queue_3٠is_empty t
    {{{
      RET #(bool_decide (vs = []%list));
      queue_3۰model t vs
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".

    wp۰rec.
    wp۰apply (queue_3٠sizeｰspec with "Hmodel") as "Hmodel".
    wp۰pures.
    rewrite (bool_decide_ext (⁺(length vs) = 0) (vs = [])).
    { rewrite -length_zero_iff_nil. lia. }
    iApply ("HΦ" with "Hmodel").
  Qed.

  Lemma queue_3٠unsafe_getｰspec {t vs i} v :
    (0 ≤ i)%Z →
    vs !! ₊i = Some v →
    {{{
      queue_3۰model t vs
    }}}
      queue_3٠unsafe_get t #i
    {{{
      RET v;
      queue_3۰model t vs
    }}}.
  Proof.
    iIntros "%Hi %Hlookup %Φ (:model) HΦ".

    wp۰rec. do 2 wp۰load.
    wp۰apply (array٠unsafe_cgetｰspec with "Hvs"); [lia | done | lia |].
    iSteps.
  Qed.

  Lemma queue_3٠unsafe_setｰspec t vs i v :
    (0 ≤ i < length vs)%Z →
    {{{
      queue_3۰model t vs
    }}}
      queue_3٠unsafe_set t #i v
    {{{
      RET ();
      queue_3۰model t (<[₊i := v]> vs)
    }}}.
  Proof.
    iIntros "%Hi %Φ (:model) HΦ".

    wp۰rec. do 2 wp۰load.
    wp۰apply (array٠unsafe_csetｰspec with "Hvs"); first lia.
    replace (₊(front + i) - front) with ₊i by lia.
    iSteps; simp_length.
  Qed.

  #[local] Lemma queue_3٠next_capacityｰspec n :
    (0 ≤ n)%Z →
    {{{
      True
    }}}
      queue_3٠next_capacity #n
    {{{
      m
    , RET #m;
      ⌜n ≤ m⌝%Z
    }}}.
  Proof.
    iSteps.
  Qed.
  #[local] Lemma queue_3٠growｰspec t vs extra :
    {{{
      model' t vs extra
    }}}
      queue_3٠grow t
    {{{
      extra
    , RET ();
      ⌜0 < extra⌝ ∗
      model' t vs extra
    }}}.
  Proof.
    iIntros "%Φ (:model') HΦ".

    wp۰rec. do 3 wp۰load.
    wp۰apply+ (array٠sizeｰspecｰcslice with "Hvs") as "Hvs".
    wp۰pures.
    case_bool_decide.

    - iClear "Hextra".
      wp۰apply+ (queue_3٠next_capacityｰspec with "[//]") as (cap') "%Hcap'"; first lia.
      wp۰apply+ int٠maxｰspec.
      wp۰apply+ (array٠unsafe_cgrowｰspec with "Hvs") as (data') "(_ & Hvs)"; [lia.. |].
      wp۰store.
      iDestruct (array۰csliceｰapp with "Hvs") as "(Hvs & Hextra)".
      rewrite -Hback. iSteps.
      iExists ₊(((⁺cap + 1) `max` cap') - cap). iSteps.
      rewrite Z2Nat.inj_sub; first lia. rewrite Nat2Z.id. iSteps.

    - iSteps. iExists extra. iSteps.
  Qed.

  Lemma queue_3٠pushｰspec t vs v :
    {{{
      queue_3۰model t vs
    }}}
      queue_3٠push t v
    {{{
      RET ();
      queue_3۰model t (vs ++ [v])
    }}}.
  Proof.
    iIntros "%Φ (:model lazy=) HΦ".

    wp۰rec.
    wp۰apply+ (queue_3٠growｰspec with "Hmodel") as (extra') "(%Hextra' & (:model'))".
    do 2 wp۰load.
    destruct (Nat.lt_exists_pred 0 extra') as (extra'' & -> & _); first lia.
    iDestruct (array۰csliceｰcons with "Hextra") as "(Hcell & Hextra)". rewrite -/replicate.
    wp۰apply (array٠unsafe_csetｰspecｰcell with "Hcell") as "Hcell"; first done.
    iDestruct (array۰csliceｰapp₁ with "Hvs Hcell") as "Hvs"; first done.
    wp۰store.
    replace (back + 1)%Z with ⁺˖back by lia.
    iSteps; iPureIntro; simp_length/=; lia.
  Qed.

  #[local] Lemma queue_3٠shrinkｰspec t vs :
    {{{
      queue_3۰model t vs
    }}}
      queue_3٠shrink t
    {{{
      RET ();
      queue_3۰model t vs
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".

    wp۰rec. rewrite queue_3٠min_capacityｰunfold. do 3 wp۰load.
    wp۰apply+ (array٠sizeｰspecｰcslice with "Hvs") as "Hvs".
    wp۰pures.
    case_bool_decide; last iSteps.
    iDestruct (array۰csliceｰapp₁ with "Hvs Hextra") as "Hvs"; first done.
    wp۰pures. rewrite -Z.div2_spec.
    wp۰apply (array٠unsafe_cshrink_sliceｰspec with "Hvs") as (data') "(_ & Hvs)"; [simp_length; lia.. |].
    wp۰store.
    rewrite Nat2Z.id Nat.sub_diag sliceｰ0 take_app_ge; first lia.
    rewrite take_replicate.
    iDestruct (array۰csliceｰapp with "Hvs") as "(Hvs & Hextra)".
    iStepFrameSteps.
  Qed.

  Lemma queue_3٠pop_frontｰspec t vs :
    {{{
      queue_3۰model t vs
    }}}
      queue_3٠pop_front t
    {{{
      RET head vs;
      queue_3۰model t (tail vs)
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".

    wp۰rec. do 2 wp۰load. wp۰pures.
    case_bool_decide.

    - destruct vs; last naive_solver lia.
      iSteps.

    - destruct vs as [| v vs]; first naive_solver. simpl in *.
      wp۰load.
      iDestruct (array۰csliceｰcons with "Hvs") as "(Hcell & Hvs)".
      wp۰apply+ (array٠unsafe_cgetｰspecｰcell with "Hcell") as "Hcell"; first done.
      wp۰apply+ (array٠unsafe_csetｰspecｰcell with "Hcell") as "Hcell"; first done.
      wp۰store.
      iApply array۰csliceｰshiftｰright in "Hcell".
      iDestruct (array۰csliceｰapp₁ with "Hextra Hcell") as "Hextra".
      { simp_length. lia. }
      rewrite -replicate_S_end.
      wp۰apply+ (queue_3٠shrinkｰspec _ vs with "[-HΦ]") as "Hmodel".
      { iExists ˖extra. iFrameSteps. }
      wp۰pures.
      iApply ("HΦ" with "Hmodel").
  Qed.

  Lemma queue_3٠pop_backｰspec t vs :
    {{{
      queue_3۰model t vs
    }}}
      queue_3٠pop_back t
    {{{
      o
    , RET o;
      match o with
      | None =>
          ⌜vs = []⌝ ∗
          queue_3۰model t []
      | Some v =>
          ∃ vs',
          ⌜vs = vs' ++ [v]⌝ ∗
          queue_3۰model t vs'
      end
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".

    wp۰rec. do 2 wp۰load. wp۰pures.
    case_bool_decide.

    - destruct vs; last naive_solver lia.
      iSpecialize ("HΦ" $! None).
      iSteps.

    - destruct vs as [| v vs _] using rev_ind; first naive_solver. simp_length/= in *.
      wp۰load.
      iDestruct (array۰csliceｰapp with "Hvs") as "(Hvs & Hcell)".
      wp۰apply+ (array٠unsafe_cgetｰspecｰcell with "Hcell") as "Hcell"; first lia.
      wp۰apply+ (array٠unsafe_csetｰspecｰcell with "Hcell") as "Hcell"; first lia.
      wp۰store.
      iDestruct (array۰csliceｰcons₂' with "Hcell Hextra") as "Hextra"; first lia.
      rewrite -replicate_S.
      wp۰apply+ (queue_3٠shrinkｰspec _ vs with "[-HΦ]") as "Hmodel".
      { iExists ˖extra. iFrameSteps. }
      wp۰pures.
      iApply ("HΦ" $! (Some v)).
      iFrameSteps.
  Qed.
End zoo۰G.

Require zoo_std.queue_3__opaque.

#[global] Opaque queue_3۰model.
