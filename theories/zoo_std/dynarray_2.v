Require Import zoo.prelude.
Require Import zoo.common.list.
Require Import zoo.iris.bi.big_op.
Require Import zoo.base.
Require Export zoo_std.dynarray_2__code.
Require Import zoo_std.array.
Require Import zoo_std.assume.
Require Import zoo_std.diverge.
Require Import zoo_std.dynarray_2__types.
Require Import zoo_std.int.
Require Import zoo.options.

Implicit Types b : bool.
Implicit Types i : nat.
Implicit Types l elem  : location.
Implicit Types elems : list location.
Implicit Types v t data slot fn : val.
Implicit Types vs slots : list val.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  #[local] Definition element۰model elem v : iProp Σ :=
    elem ↦ₕ Header 1 §Element ∗
    elem.[value] ↦ v.
  #[local] Instance : CustomIpat "element۰model" :=
    " ( Helem_header
      & Helem_value
      )
    ".
  Definition dynarray_2۰model t vs : iProp Σ :=
    ∃ l data elems extra,
    ⌜t = #l⌝ ∗
    l.[size] ↦ #(length vs) ∗
    l.[data] ↦ data ∗
    array۰model data (DfracOwn 1) ((#*@{location} elems) ++ replicate extra §Empty%V) ∗
    [∗ list] elem; v ∈ elems; vs, element۰model elem v.
  #[local] Instance : CustomIpat "model" :=
    " ( %l
      & %data
      & %elems
      & %extra
      & ->
      & Hl_size
      & Hl_data
      & Hmodel
      & Helems
      )
    ".

  #[global] Instance dynarray_2۰model𑁒timeless t vs :
    Timeless (dynarray_2۰model t vs).
  Proof.
    apply _.
  Qed.

  #[local] Lemma dynarray_2٠element𑁒spec v :
    {{{
      True
    }}}
      dynarray_2٠element v
    {{{
      elem
    , RET #elem;
      element۰model elem v
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma dynarray_2٠create𑁒spec' :
    {{{
      True
    }}}
      dynarray_2٠create ()
    {{{
      l
    , RET #l;
      dynarray_2۰model #l [] ∗
      meta_token l (↑nroot.@"user")
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp۰rec.
    wp۰apply (array٠create𑁒spec with "[//]") as "%data Hmodel".
    wp۰block l as "Hl_meta" "(Hl_size & Hl_data & _)".
    iDestruct (meta_token𑁒difference (↑nroot.@"user") with "Hl_meta") as "(Hl_meta & _)"; first done.
    iSteps. iExists [], 0. iSteps.
  Qed.
  Lemma dynarray_2٠create𑁒spec :
    {{{
      True
    }}}
      dynarray_2٠create ()
    {{{
      t
    , RET t;
      dynarray_2۰model t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp۰apply (dynarray_2٠create𑁒spec' with "[//]").
    iSteps.
  Qed.

  Lemma dynarray_2٠make𑁒spec sz v :
    {{{
      True
    }}}
      dynarray_2٠make #sz v
    {{{
      t
    , RET t;
      ⌜0 ≤ sz⌝%Z ∗
      dynarray_2۰model t (replicate ₊sz v)
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp۰rec.
    pose (Ψ data i slots := (
      ∃ elems,
      ⌜slots = #*@{location} elems⌝ ∗
      [∗ list] elem ∈ elems, element۰model elem v
    )%I).
    wp۰apply+ (array٠init𑁒spec Ψ) as "%data %slots (%Hsz & %Helems & Hmodel & (%elems & -> & Helems))".
    { iSplit.
      - iSteps. iExists []. iSteps.
      - iIntros "!> %data %i %slots %Hi1 %Hi2 (%elems & -> & Helems)".
        wp۰apply+ (dynarray_2٠element𑁒spec with "[//]") as (elem) "Helem".
        iExists (elems ++ [elem]).
        rewrite -fmap_snoc big_sepL_snoc. iSteps.
    }

    iSteps.
    - simpl_length. iSteps.
    - iExists elems, 0. rewrite right_id. iSteps.
      iApply (big_sepL2𑁒replicate𑁒r₂ (λ _, element۰model) with "Helems").
      { simpl_length in Helems. }
  Qed.

  Lemma dynarray_2٠initi𑁒spec Ψ sz fn :
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
      dynarray_2٠initi #sz fn
    {{{
      t vs
    , RET t;
      ⌜sz = length vs⌝ ∗
      dynarray_2۰model t vs ∗
      Ψ ₊sz vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & #Hfn) HΦ".
    wp۰rec.
    pose (Ψ' data i slots := (
      ∃ elems vs,
      ⌜slots = #*@{location} elems⌝ ∗
      Ψ i vs ∗
      [∗ list] elem; v ∈ elems; vs, element۰model elem v
    )%I).
    wp۰apply+ (array٠initi𑁒spec Ψ' with "[HΨ]") as "%data %elems (%Hsz & %Helems & Hmodel & (%slots & %vs & -> & HΨ & Helems))".
    { iSplit.
      - iSteps. iExists []. iSteps.
      - iIntros "!> %t %i %slots %Hi1 %Hi2 (%elems & %vs & -> & HΨ & Helems)".
        simpl_length in Hi2.
        iDestruct (big_sepL2_length with "Helems") as %Helems.
        wp۰apply+ (wp𑁒wand with "(Hfn [%] HΨ)") as "%v HΨ"; first lia.
        wp۰apply (dynarray_2٠element𑁒spec with "[//]") as (elem) "Helem".
        iExists (elems ++ [elem]), (vs ++ [v]).
        rewrite -fmap_snoc big_sepL2_snoc. iSteps.
    }

    wp۰block l as "(Hl_size & Hl_data & _)".

    iApply "HΦ".
    iDestruct (big_sepL2_length with "Helems") as %Helems'.
    simpl_length in Helems.
    iFrameStep. iExists 0. rewrite right_id. iSteps.
  Qed.
  Lemma dynarray_2٠initi𑁒spec' Ψ sz fn :
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
      dynarray_2٠initi #sz fn
    {{{
      t vs
    , RET t;
      ⌜sz = length vs⌝ ∗
      dynarray_2۰model t vs ∗
      Ψ ₊sz vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep (λ _, ?Ξ') _] => set Ξ := Ξ' end.
    pose (Ψ' i vs := (
      Ψ i vs ∗
      [∗ list] j ∈ seq i (₊sz - i), Ξ j
    )%I).
    wp۰apply (dynarray_2٠initi𑁒spec Ψ' with "[$HΨ Hfn]"); last iSteps.
    rewrite Nat.sub_0_r. iFrame. iIntros "!> %i %vs (%Hi1 & %Hi2) (HΨ & HΞ)".
    destruct (Nat.lt_exists_pred 0 (₊sz - i)) as (k & Hk & _); first lia. rewrite Hk.
    rewrite -cons_seq. iDestruct "HΞ" as "(Hfn & HΞ)".
    wp۰apply (wp𑁒wand with "(Hfn [//] HΨ)"). iSteps.
    rewrite Nat.sub_succ_r Hk //.
  Qed.
  Lemma dynarray_2٠initi𑁒spec𑁒disentangled Ψ sz fn :
    {{{
      □ (
        ∀ i,
        ⌜i < ₊sz⌝ -∗
        WP fn #i {{ v,
          ▷ Ψ i v
        }}
      )
    }}}
      dynarray_2٠initi #sz fn
    {{{
      t vs
    , RET t;
      ⌜sz = length vs⌝ ∗
      dynarray_2۰model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ #Hfn HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp۰apply (dynarray_2٠initi𑁒spec Ψ'); last iSteps.
    rewrite /Ψ'. iSteps.
    rewrite big_sepL_snoc. iSteps.
  Qed.
  Lemma dynarray_2٠initi𑁒spec𑁒disentangled' Ψ sz fn :
    {{{
      ( [∗ list] i ∈ seq 0 ₊sz,
        WP fn #i {{ v,
          ▷ Ψ i v
        }}
      )
    }}}
      dynarray_2٠initi #sz fn
    {{{
      t vs
    , RET t;
      ⌜sz = length vs⌝ ∗
      dynarray_2۰model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ Hfn HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp۰apply (dynarray_2٠initi𑁒spec' Ψ' with "[Hfn]"); last iSteps.
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn"). iSteps.
    rewrite big_sepL_snoc. iSteps.
  Qed.

  Lemma dynarray_2٠size𑁒spec t vs :
    {{{
      dynarray_2۰model t vs
    }}}
      dynarray_2٠size t
    {{{
      RET #(length vs);
      dynarray_2۰model t vs
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma dynarray_2٠capacity𑁒spec t vs :
    {{{
      dynarray_2۰model t vs
    }}}
      dynarray_2٠capacity t
    {{{
      cap
    , RET #cap;
      ⌜length vs ≤ cap⌝ ∗
      dynarray_2۰model t vs
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".
    wp۰rec. rewrite /dynarray_2٠data. wp۰load.
    wp۰apply (array٠size𑁒spec with "Hmodel") as "Hmodel".
    simpl_length.
    iDestruct (big_sepL2_length with "Helems") as %->.
    iSteps.
  Qed.

  Lemma dynarray_2٠is_empty𑁒spec t vs :
    {{{
      dynarray_2۰model t vs
    }}}
      dynarray_2٠is_empty t
    {{{
      RET #(bool_decide (vs = []%list));
      dynarray_2۰model t vs
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp۰rec.
    wp۰apply+ (dynarray_2٠size𑁒spec with "Hmodel") as "Hmodel".
    wp۰pures.
    destruct vs; iApply ("HΦ" with "Hmodel").
  Qed.

  Lemma dynarray_2٠get𑁒spec t vs (i : Z) v :
    (0 ≤ i)%Z →
    vs !! ₊i = Some v →
    {{{
      dynarray_2۰model t vs
    }}}
      dynarray_2٠get t #i
    {{{
      RET v;
      ⌜0 ≤ i < length vs⌝%Z ∗
      dynarray_2۰model t vs
    }}}.
  Proof.
    iIntros "%Hi %Hvs_lookup %Φ (:model) HΦ".
    Z_to_nat i. rewrite Nat2Z.id in Hvs_lookup.
    clear Hi. pose proof Hvs_lookup as Hi%lookup_lt_Some.
    iDestruct (big_sepL2_length with "Helems") as "%Helems".
    iDestruct (big_sepL2𑁒lookup𑁒acc𑁒r with "Helems") as "(%elem & %Helems_lookup & (:element۰model) & Helems)"; first done.
    wp۰rec. rewrite /dynarray_2٠data. wp۰load.
    wp۰apply+ (array٠get𑁒spec with "[$Hmodel]") as "(% & Hmodel)".
    { rewrite Nat2Z.id lookup_app_l.
      { simpl_length. lia. }
      rewrite list_lookup_fmap_Some. naive_solver.
    }
    iSteps.
  Qed.

  Lemma dynarray_2٠set𑁒spec t vs (i : Z) v :
    (0 ≤ i < length vs)%Z →
    {{{
      dynarray_2۰model t vs
    }}}
      dynarray_2٠set t #i v
    {{{
      RET ();
      ⌜0 ≤ i < length vs⌝%Z ∗
      dynarray_2۰model t (<[₊i := v]> vs)
    }}}.
  Proof.
    iIntros "%Hi %Φ (:model) HΦ".
    Z_to_nat i. rewrite Nat2Z.id.
    iDestruct (big_sepL2_length with "Helems") as "%Helems".
    opose proof* (lookup_lookup_total vs i) as Hvs_lookup.
    { apply lookup_lt_is_Some_2. lia. }
    iDestruct (big_sepL2𑁒insert𑁒acc𑁒r with "Helems") as "(%elem & %Helems_lookup & (:element۰model) & Helems)"; first done.
    wp۰rec. rewrite /dynarray_2٠data. wp۰load.
    wp۰apply+ (array٠get𑁒spec with "[$Hmodel]") as "Hmodel".
    { rewrite Nat2Z.id lookup_app_l.
      { simpl_length. lia. }
      rewrite list_lookup_fmap_Some. naive_solver.
    }
    wp۰match. wp۰store.
    iDestruct ("Helems" with "[Helem_header Helem_value]") as "Helems"; first iSteps.
    rewrite (list_insert_id elems) //.
    iSteps. simpl_length.
  Qed.

  #[local] Lemma dynarray_2٠next_capacity𑁒spec n :
    (0 ≤ n)%Z →
    {{{
      True
    }}}
      dynarray_2٠next_capacity #n
    {{{
      m
    , RET #m;
      ⌜n ≤ m⌝%Z
    }}}.
  Proof.
    iSteps.
  Qed.
  Lemma dynarray_2٠reserve𑁒spec t vs (n : Z) :
    {{{
      dynarray_2۰model t vs
    }}}
      dynarray_2٠reserve t #n
    {{{
      RET ();
      ⌜0 ≤ n⌝%Z ∗
      dynarray_2۰model t vs
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".
    wp۰rec. rewrite /dynarray_2٠data.
    wp۰apply+ assume𑁒spec' as "%Hn".
    wp۰load.
    wp۰apply+ (array٠size𑁒spec with "Hmodel") as "Hmodel".
    wp۰pures.
    case_bool_decide; wp۰pures; last iSteps.
    wp۰apply+ (dynarray_2٠next_capacity𑁒spec with "[//]") as "%n' %Hn'"; first lia.
    wp۰apply int٠max𑁒spec.
    wp۰apply+ (array٠unsafe_grow𑁒spec with "Hmodel") as (data') "(Hmodel & Hmodel')"; first lia.
    rewrite /dynarray_2٠set_data. wp۰store.
    rewrite -assoc -replicate_add. iSteps.
  Qed.

  Lemma dynarray_2٠reserve_extra𑁒spec t vs (n : Z) :
    {{{
      dynarray_2۰model t vs
    }}}
      dynarray_2٠reserve_extra t #n
    {{{
      RET ();
      ⌜0 ≤ n⌝%Z ∗
      dynarray_2۰model t vs
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp۰rec.
    wp۰apply+ assume𑁒spec' as "%Hn".
    wp۰apply+ (dynarray_2٠size𑁒spec with "Hmodel") as "Hmodel".
    wp۰apply+ (dynarray_2٠reserve𑁒spec with "Hmodel").
    iSteps.
  Qed.

  #[local] Lemma dynarray_2٠try_grow𑁒spec t vs sz v :
    {{{
      dynarray_2۰model t vs
    }}}
      dynarray_2٠try_grow t #sz v
    {{{
      b
    , RET #b;
      if b then
        dynarray_2۰model t (vs ++ replicate (₊sz - length vs) v)
      else
        dynarray_2۰model t vs
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".
    iDestruct (big_sepL2_length with "Helems") as "%Helems".

    wp۰rec. rewrite /dynarray_2٠size /dynarray_2٠data /dynarray_2٠set_size. wp۰load. wp۰pures.
    case_bool_decide; wp۰pures.

    - replace (₊sz - length vs) with 0 by lia.
      rewrite /= right_id. iSteps.

    - wp۰load.
      wp۰apply+ (array٠size𑁒spec with "Hmodel") as "Hmodel".
      wp۰pures. iEval simpl_length.
      case_bool_decide; wp۰pures; first iSteps.
      wp۰store.

      wp۰apply+ (array٠unsafe_apply_slice𑁒spec𑁒disentangled (λ _ 𝑒𝑙𝑒𝑚,
        ∃ elem,
        ⌜𝑒𝑙𝑒𝑚 = #elem⌝ ∗
        element۰model elem v
      )%I with "[$Hmodel]") as (𝑒𝑙𝑒𝑚𝑠) "(%H𝑒𝑙𝑒𝑚𝑠 & Hmodel & Helems')"; simpl_length; [lia.. | iSteps |].

      iDestruct (big_sepL𑁒exists with "Helems'") as "(%elems' & _ & Helems')".
      iDestruct (big_sepL2_sep with "Helems'") as "(Heq & Helems')".
      iDestruct (big_sepL2𑁒Forall2 with "Heq") as %->%list𑁒fmap𑁒alt𑁒Forall2𑁒l. iClear "Heq".
      iDestruct (big_sepL2_const_sepL_r with "Helems'") as "(_ & Helems')".
      iDestruct (big_sepL2𑁒replicate𑁒r₂ (const element۰model) _ _ (₊sz - length vs) with "Helems'") as "Helems'".
      { simpl_length in H𝑒𝑙𝑒𝑚𝑠. lia. }
      iDestruct (big_sepL2_app with "Helems Helems'") as "Helems".
      rewrite Nat2Z.id with_slice𑁒app𑁒length'; first simpl_length.
      rewrite assoc -fmap_app drop_replicate.
      iSteps. simpl_length. iSteps.
  Qed.
  #[local] Lemma dynarray_2٠grow₀𑁒spec t vs sz v :
    {{{
      dynarray_2۰model t vs
    }}}
      dynarray_2٠grow₀ t #sz v
    {{{
      RET ();
      dynarray_2۰model t (vs ++ replicate (₊sz - length vs) v)
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".

    iLöb as "HLöb".

    wp۰rec.
    wp۰apply+ (dynarray_2٠reserve𑁒spec with "Hmodel") as "(_ & Hmodel)".
    wp۰apply+ (dynarray_2٠try_grow𑁒spec with "Hmodel") as ([]) "Hmodel".

    - wp۰pures.
      iApply ("HΦ" with "Hmodel").

    - wp۰apply+ ("HLöb" with "Hmodel HΦ").
  Qed.
  Lemma dynarray_2٠grow𑁒spec t vs sz v :
    {{{
      dynarray_2۰model t vs
    }}}
      dynarray_2٠grow t #sz v
    {{{
      RET ();
      dynarray_2۰model t (vs ++ replicate (₊sz - length vs) v)
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".

    wp۰rec.
    wp۰apply+ (dynarray_2٠try_grow𑁒spec with "Hmodel") as ([]) "Hmodel".

    - wp۰pures.
      iApply ("HΦ" with "Hmodel").

    - wp۰apply+ (dynarray_2٠grow₀𑁒spec with "Hmodel HΦ").
  Qed.

  #[local] Lemma dynarray_2٠try_push𑁒spec t vs elem v :
    {{{
      dynarray_2۰model t vs ∗
      element۰model elem v
    }}}
      dynarray_2٠try_push t #elem
    {{{
      b
    , RET #b;
      if b then
        dynarray_2۰model t (vs ++ [v])
      else
        dynarray_2۰model t vs ∗
        element۰model elem v
    }}}.
  Proof.
    iIntros "%Φ ((:model) & Helem) HΦ".
    iDestruct (big_sepL2_length with "Helems") as "%Helems".
    wp۰rec. rewrite /dynarray_2٠size /dynarray_2٠data /dynarray_2٠set_size. do 2 wp۰load.
    wp۰apply+ (array٠size𑁒spec with "Hmodel") as "Hmodel".
    wp۰pures.
    case_bool_decide as Htest; wp۰pures.
    { iApply "HΦ". iFrameSteps. }
    wp۰store.
    wp۰apply+ (array٠unsafe_set𑁒spec with "Hmodel") as "Hmodel"; first lia.
    wp۰pures.
    iApply "HΦ".
    iExists l, data, (elems ++ [elem]), (extra - 1). iStep.
    rewrite length_app Z.add_1_r -Nat2Z.inj_succ Nat.add_comm /=. iFrame.
    rewrite insert_app_r_alt.
    { simpl_length. lia. }
    destruct extra.
    - simpl_length in Htest. lia.
    - rewrite Nat2Z.id length_fmap Helems Nat.sub_diag.
      rewrite fmap_snoc -assoc /= Nat.sub_0_r.
      iSteps.
  Qed.
  #[local] Lemma dynarray_2٠push₀𑁒spec t vs elem v :
    {{{
      dynarray_2۰model t vs ∗
      element۰model elem v
    }}}
      dynarray_2٠push₀ t #elem
    {{{
      RET ();
      dynarray_2۰model t (vs ++ [v])
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & Helem) HΦ".
    iLöb as "HLöb".
    wp۰rec.
    wp۰apply+ (dynarray_2٠reserve_extra𑁒spec with "Hmodel") as "(_ & Hmodel)".
    wp۰apply+ (dynarray_2٠try_push𑁒spec with "[$Hmodel $Helem]") as ([]) ""; first iSteps. iIntros "(Hmodel & Helem)".
    wp۰apply+ ("HLöb" with "Hmodel Helem HΦ").
  Qed.
  Lemma dynarray_2٠push𑁒spec t vs v :
    {{{
      dynarray_2۰model t vs
    }}}
      dynarray_2٠push t v
    {{{
      RET ();
      dynarray_2۰model t (vs ++ [v])
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".
    wp۰rec.
    wp۰apply+ (dynarray_2٠element𑁒spec with "[//]") as (elem) "Helem".
    wp۰apply+ (dynarray_2٠try_push𑁒spec with "[$Hmodel $Helem]") as ([]) ""; first iSteps. iIntros "(Hmodel & Helem)".
    wp۰apply+ (dynarray_2٠push₀𑁒spec with "[$Hmodel $Helem]").
    iSteps.
  Qed.

  Lemma dynarray_2٠pop𑁒spec {t vs} vs' v :
    vs = vs' ++ [v] →
    {{{
      dynarray_2۰model t vs
    }}}
      dynarray_2٠pop t
    {{{
      RET v;
      dynarray_2۰model t vs'
    }}}.
  Proof.
    iIntros (->) "%Φ (:model) HΦ".
    wp۰rec. rewrite /dynarray_2٠size /dynarray_2٠data /dynarray_2٠set_size. do 2 wp۰load.
    wp۰apply+ (array٠size𑁒spec with "Hmodel") as "Hmodel".
    do 2 (wp۰apply+ assume𑁒spec' as "_").
    wp۰pures.
    rewrite length_app Nat.add_1_r Z.sub_1_r -Nat2Z.inj_pred /=; first lia.
    iDestruct (big_sepL2_length with "Helems") as %Helems. simpl_length/= in Helems.
    destruct elems as [| elem elems _] using rev_ind; first (simpl in Helems; lia).
    rewrite length_app Nat.add_cancel_r in Helems. iEval (rewrite -Helems).
    iDestruct (big_sepL2_snoc with "Helems") as "(Helems & (:element۰model))".
    wp۰apply (array٠unsafe_get𑁒spec with "Hmodel") as "Hmodel"; [lia | | done |].
    { rewrite Nat2Z.id lookup_app_l.
      { simpl_length/=. lia. }
      rewrite list_lookup_fmap lookup_app_r // Nat.sub_diag //.
    }
    wp۰match.
    wp۰apply (array٠unsafe_set𑁒spec with "Hmodel") as "Hmodel".
    { simpl_length/=. lia. }

    rewrite fmap_snoc -assoc Nat2Z.id insert_app_r_alt.
    all: simpl_length.
    rewrite Nat.sub_diag /=.
    wp۰store. wp۰load.
    iApply "HΦ".
    iExists l, data, elems, ˖extra. iSteps.
  Qed.

  Lemma dynarray_2٠fit_capacity𑁒spec t vs :
    {{{
      dynarray_2۰model t vs
    }}}
      dynarray_2٠fit_capacity t
    {{{
      RET ();
      dynarray_2۰model t vs
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".
    wp۰rec. rewrite /dynarray_2٠size /dynarray_2٠data /dynarray_2٠set_data. do 2 wp۰load.
    wp۰apply+ (array٠size𑁒spec with "Hmodel") as "Hmodel".
    iDestruct (big_sepL2_length with "Helems") as %Helems.
    wp۰pures.
    case_bool_decide; wp۰pures; first iSteps.
    wp۰apply (array٠shrink𑁒spec with "Hmodel") as "%data' (_ & _ & Hmodel')".
    wp۰store.
    iApply "HΦ".
    iExists l, data', elems, 0.
    rewrite take_app_length'.
    { simpl_length. lia. }
    rewrite right_id. iSteps.
  Qed.

  Lemma dynarray_2٠reset𑁒spec t vs :
    {{{
      dynarray_2۰model t vs
    }}}
      dynarray_2٠reset t
    {{{
      RET ();
      dynarray_2۰model t []
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".
    wp۰rec. rewrite /dynarray_2٠set_size /dynarray_2٠set_data. wp۰store.
    wp۰apply+ (array٠create𑁒spec with "[//]") as "%data' Hmodel'".
    wp۰store.
    iSteps. iExists [], 0. iSteps.
  Qed.

  Lemma dynarray_2٠iteri𑁒spec Ψ fn t vs :
    {{{
      ▷ Ψ 0 [] ∗
      dynarray_2۰model t vs ∗
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
      dynarray_2٠iteri fn t
    {{{
      RET ();
      dynarray_2۰model t vs ∗
      Ψ (length vs) vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & #Hfn) HΦ".
    wp۰rec. rewrite /dynarray_2٠data.
    wp۰apply+ (dynarray_2٠size𑁒spec with "Hmodel") as "(:model)".
    wp۰load.
    wp۰apply+ (array٠size𑁒spec with "Hmodel") as "Hmodel".
    wp۰apply+ assume𑁒spec' as "%".
    pose Ψ' i slots := (
      Ψ i (take i vs) ∗
      [∗ list] elem; v ∈ elems; vs, element۰model elem v
    )%I.
    wp۰apply+ (array٠unsafe_iteri_slice𑁒spec Ψ' with "[$HΨ $Helems $Hmodel]"); [lia.. | |].
    { iIntros "!> %i %slots%Hi %Hlookup (HΨ & Helems)".
      iDestruct (big_sepL2_length with "Helems") as "%Helems".
      rewrite lookup_app_l in Hlookup.
      { simpl_length. lia. }
      apply list_lookup_fmap_Some in Hlookup as (elem & -> & Hlookup).
      iDestruct (big_sepL2𑁒lookup𑁒acc𑁒l with "Helems") as "(%v & % & (:element۰model) & Helems)"; first done.
      wp۰match. wp۰load.
      rewrite slice𑁒0 take_app_le.
      { simpl_length. lia. }
      wp۰apply (wp𑁒wand with "(Hfn [//] HΨ)").
      rewrite -take_S_r //. iSteps.
    }
    iSteps. rewrite Nat2Z.id firstn_all //.
  Qed.
  Lemma dynarray_2٠iteri𑁒spec' Ψ fn t vs :
    {{{
      ▷ Ψ 0 [] ∗
      dynarray_2۰model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i (take i vs) -∗
        WP fn #i v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ ˖i (take i vs ++ [v])
        }}
      )
    }}}
      dynarray_2٠iteri fn t
    {{{
      RET ();
      dynarray_2۰model t vs ∗
      Ψ (length vs) vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & Hfn) HΦ".
    match goal with |- context [big_opL bi_sep ?Ξ' _] => set Ξ := Ξ' end.
    pose (Ψ' i vs_left := (
      Ψ i vs_left ∗
      [∗ list] j ↦ v ∈ drop i vs, Ξ (i + j) v
    )%I).
    wp۰apply (dynarray_2٠iteri𑁒spec Ψ' with "[$HΨ $Hmodel $Hfn]"); last iSteps.
    iIntros "!> %i %v %Hlookup (HΨ & HΞ)".
    erewrite drop_S => //.
    iDestruct "HΞ" as "(Hfn & HΞ)".
    rewrite Nat.add_0_r. setoid_rewrite Nat.add_succ_r. iSteps.
  Qed.
  Lemma dynarray_2٠iteri𑁒spec𑁒disentangled Ψ fn t vs :
    {{{
      dynarray_2۰model t vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        WP fn #i v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i v
        }}
      )
    }}}
      dynarray_2٠iteri fn t
    {{{
      RET ();
      dynarray_2۰model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & #Hfn) HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp۰apply (dynarray_2٠iteri𑁒spec Ψ' with "[$Hmodel]"); last iSteps.
    rewrite /Ψ'. iSteps.
    rewrite big_sepL_snoc length_take Nat.min_l; last iSteps.
    eapply Nat.lt_le_incl, lookup_lt_Some. done.
  Qed.
  Lemma dynarray_2٠iteri𑁒spec𑁒disentangled' Ψ fn t vs :
    {{{
      dynarray_2۰model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn #i v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i v
        }}
      )
    }}}
      dynarray_2٠iteri fn t
    {{{
      RET ();
      dynarray_2۰model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & Hfn) HΦ".
    pose (Ψ' i vs := (
      [∗ list] j ↦ v ∈ vs, Ψ j v
    )%I).
    wp۰apply (dynarray_2٠iteri𑁒spec' Ψ' with "[$Hmodel Hfn]"); last iSteps.
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn"). iSteps.
    rewrite big_sepL_snoc length_take Nat.min_l; last iSteps.
    eapply Nat.lt_le_incl, lookup_lt_Some. done.
  Qed.

  Lemma dynarray_2٠iter𑁒spec Ψ fn t vs :
    {{{
      ▷ Ψ 0 [] ∗
      dynarray_2۰model t vs ∗
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
      dynarray_2٠iter fn t
    {{{
      RET ();
      dynarray_2۰model t vs ∗
      Ψ (length vs) vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & #Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (dynarray_2٠iteri𑁒spec Ψ with "[$HΨ $Hmodel] HΦ").
    iSteps.
  Qed.
  Lemma dynarray_2٠iter𑁒spec' Ψ fn t vs :
    {{{
      ▷ Ψ 0 [] ∗
      dynarray_2۰model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i (take i vs) -∗
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ ˖i (take i vs ++ [v])
        }}
      )
    }}}
      dynarray_2٠iter fn t
    {{{
      RET ();
      dynarray_2۰model t vs ∗
      Ψ (length vs) vs
    }}}.
  Proof.
    iIntros "%Φ (HΨ & Hmodel & Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (dynarray_2٠iteri𑁒spec' Ψ with "[$HΨ $Hmodel Hfn] HΦ").
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.
  Lemma dynarray_2٠iter𑁒spec𑁒disentangled Ψ fn t vs :
    {{{
      dynarray_2۰model t vs ∗
      □ (
        ∀ i v,
        ⌜vs !! i = Some v⌝ -∗
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i v
        }}
      )
    }}}
      dynarray_2٠iter fn t
    {{{
      RET ();
      dynarray_2۰model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & #Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (dynarray_2٠iteri𑁒spec𑁒disentangled Ψ with "[$Hmodel] HΦ").
    iSteps.
  Qed.
  Lemma dynarray_2٠iter𑁒spec𑁒disentangled' Ψ fn t vs :
    {{{
      dynarray_2۰model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        WP fn v {{ res,
          ⌜res = ()%V⌝ ∗
          ▷ Ψ i v
        }}
      )
    }}}
      dynarray_2٠iter fn t
    {{{
      RET ();
      dynarray_2۰model t vs ∗
      ( [∗ list] i ↦ v ∈ vs,
        Ψ i v
      )
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (dynarray_2٠iteri𑁒spec𑁒disentangled' Ψ with "[$Hmodel Hfn] HΦ").
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  Context τ `{!iType (iPropI Σ) τ}.

  #[local] Definition itype۰element elem : iProp Σ :=
    elem ↦ₕ Header 1 §Element ∗
    inv nroot (
      ∃ v,
      elem.[value] ↦ v ∗
      τ v
    ).

  Lemma element_get𑁒type elem :
    {{{
      itype۰element elem
    }}}
      (#elem).{value}
    {{{
      v
    , RET v;
      τ v
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma element_set𑁒type elem v :
    {{{
      itype۰element elem ∗
      τ v
    }}}
      #elem <-{value} v
    {{{
      RET ();
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  #[local] Definition itype۰slot slot : iProp Σ :=
      ⌜slot = §Empty%V⌝
    ∨ ∃ elem,
      ⌜slot = #elem⌝ ∗
      itype۰element elem.
  #[local] Instance itype۰slot𑁒itype :
    iType _ itype۰slot.
  Proof.
    split. apply _.
  Qed.

  #[local] Lemma wp𑁒match𑁒slot slot e1 x e2 Φ :
    itype۰slot slot -∗
    ( WP e1 {{ Φ }} ∧
      ∀ elem, itype۰element elem -∗ WP subst' x #elem e2 {{ Φ }}
    ) -∗
    WP match: slot with Empty => e1 | Element <> as: x => e2 end {{ Φ }}.
  Proof.
    iIntros "[-> | (%elem & -> & Helem_header & #Hinv)] H".
    1: rewrite bi.and_elim_l.
    2: rewrite bi.and_elim_r.
    all: iSteps.
  Qed.

  Definition itype۰dynarray_2 t : iProp Σ :=
    ∃ l,
    ⌜t = #l⌝ ∗
    inv nroot (
      ∃ (sz : nat) cap data,
      l.[size] ↦ #sz ∗
      l.[data] ↦ data ∗ itype۰array itype۰slot cap data
    ).
  #[global] Instance itype۰dynarray_2𑁒itype :
    iType _ itype۰dynarray_2.
  Proof.
    split. apply _.
  Qed.

  #[local] Lemma dynarray_2٠element𑁒type v :
    {{{
      τ v
    }}}
      dynarray_2٠element v
    {{{
      slot
    , RET slot;
      itype۰slot slot
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma dynarray_2٠create𑁒type :
    {{{
      True
    }}}
      dynarray_2٠create ()
    {{{
      t
    , RET t;
      itype۰dynarray_2 t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp۰rec.
    wp۰apply (array٠create𑁒type itype۰slot with "[//]") as "%data Hdata_type".
    iSteps.
  Qed.

  Lemma dynarray_2٠make𑁒type (sz : Z) v :
    {{{
      τ v
    }}}
      dynarray_2٠make #sz v
    {{{
      t
    , RET t;
      ⌜0 ≤ sz⌝%Z ∗
      itype۰dynarray_2 t
    }}}.
  Proof.
    iIntros "%Φ #Hv HΦ".
    wp۰rec.
    wp۰apply+ (array٠init𑁒type itype۰slot) as "%data (%Hsz & Hdata_type)"; first iSteps.
    iSteps.
  Qed.

  Lemma dynarray_2٠initi𑁒type sz fn :
    {{{
      (itype۰nat_upto ₊sz --> τ)%T fn
    }}}
      dynarray_2٠initi #sz fn
    {{{
      t
    , RET t;
      itype۰dynarray_2 t
    }}}.
  Proof.
    iIntros "%Φ #Hfn HΦ".
    wp۰rec.
    wp۰apply+ array٠initi𑁒type; last iSteps. iIntros "!> % (% & -> & %Hi)".
    wp۰apply+ (wp𑁒wand with "(Hfn [])") as (v) "#Hv"; first iSteps.
    wp۰apply (dynarray_2٠element𑁒type with "[//]").
    iSteps.
  Qed.

  Lemma dynarray_2٠size𑁒type t :
    {{{
      itype۰dynarray_2 t
    }}}
      dynarray_2٠size t
    {{{
      (sz : nat)
    , RET #sz;
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma dynarray_2٠capacity𑁒type t :
    {{{
      itype۰dynarray_2 t
    }}}
      dynarray_2٠size t
    {{{
      (cap : nat)
    , RET #cap;
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  #[local] Lemma dynarray_2٠data𑁒type t :
    {{{
      itype۰dynarray_2 t
    }}}
      dynarray_2٠data t
    {{{
      cap data
    , RET data;
      itype۰array itype۰slot cap data
    }}}.
  Proof.
    iSteps.
  Qed.

  #[local] Lemma dynarray_2٠set_size𑁒type t sz :
    (0 ≤ sz)%Z →
    {{{
      itype۰dynarray_2 t
    }}}
      dynarray_2٠set_size t #sz
    {{{
      RET ();
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  #[local] Lemma dynarray_2٠set_data𑁒type t cap data :
    {{{
      itype۰dynarray_2 t ∗
      itype۰array itype۰slot cap data
    }}}
      dynarray_2٠set_data t data
    {{{
      RET ();
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma dynarray_2٠is_empty𑁒type t :
    {{{
      itype۰dynarray_2 t
    }}}
      dynarray_2٠is_empty t
    {{{
      b
    , RET #b;
      True
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma dynarray_2٠get𑁒type t (i : Z) :
    {{{
      itype۰dynarray_2 t
    }}}
      dynarray_2٠get t #i
    {{{
      v
    , RET v;
      ⌜0 ≤ i⌝%Z ∗
      τ v
    }}}.
  Proof.
    iIntros "%Φ #Htype HΦ".
    wp۰rec.
    wp۰apply+ (dynarray_2٠data𑁒type with "Htype") as "%cap %data #Hdata_type".
    wp۰apply (array٠get𑁒type with "Hdata_type") as "%slot (%Hi & #Hslot)".
    wp۰apply (wp𑁒match𑁒slot with "Hslot").
    iSteps.
  Qed.

  Lemma dynarray_2٠set𑁒type t (i : Z) v :
    {{{
      itype۰dynarray_2 t ∗
      τ v
    }}}
      dynarray_2٠set t #i v
    {{{
      RET ();
      ⌜0 ≤ i⌝%Z
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hv) HΦ".
    wp۰rec.
    wp۰apply+ (dynarray_2٠data𑁒type with "Htype") as "%cap %data #Hdata_type".
    wp۰apply (array٠get𑁒type with "Hdata_type") as "%slot (%Hi & #Hslot)".
    wp۰apply (wp𑁒match𑁒slot with "Hslot").
    iSteps.
  Qed.

  Lemma dynarray_2٠reserve𑁒type t n :
    {{{
      itype۰dynarray_2 t
    }}}
      dynarray_2٠reserve t #n
    {{{
      RET ();
      ⌜0 ≤ n⌝%Z
    }}}.
  Proof.
    iIntros "%Φ #Htype HΦ".
    wp۰rec.
    wp۰apply+ assume𑁒spec' as "%Hn".
    wp۰apply+ (dynarray_2٠data𑁒type with "Htype") as "%cap %data #Hdata_type".
    wp۰apply+ (array٠size𑁒type with "Hdata_type") as "_".
    wp۰pures.
    case_bool_decide; wp۰pures; last iSteps.
    wp۰apply+ (dynarray_2٠next_capacity𑁒spec with "[//]") as "%n' %Hn'"; first lia.
    wp۰apply int٠max𑁒spec.
    wp۰apply+ (array٠unsafe_grow𑁒type itype۰slot with "[$Hdata_type]") as (data') "#Hdata_type'"; [lia | iSteps |].
    wp۰apply+ (dynarray_2٠set_data𑁒type with "[$Htype $Hdata_type']") as "_".
    iSteps.
  Qed.
  Lemma dynarray_2٠reserve_extra𑁒type t n :
    {{{
      itype۰dynarray_2 t
    }}}
      dynarray_2٠reserve_extra t #n
    {{{
      RET ();
      ⌜0 ≤ n⌝%Z
    }}}.
  Proof.
    iIntros "%Φ #Htype HΦ".
    wp۰rec.
    wp۰apply+ assume𑁒spec' as "%Hn".
    wp۰apply+ (dynarray_2٠size𑁒type with "Htype") as "%sz _".
    wp۰apply+ (dynarray_2٠reserve𑁒type with "Htype").
    iSteps.
  Qed.

  #[local] Lemma dynarray_2٠try_grow𑁒type t (sz' : Z) v :
    {{{
      itype۰dynarray_2 t ∗
      τ v
    }}}
      dynarray_2٠try_grow t #sz' v
    {{{
      b
    , RET #b;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hv) HΦ".

    wp۰rec.
    wp۰apply+ (dynarray_2٠size𑁒type with "Htype") as (sz) "_".
    wp۰pures.
    case_bool_decide; first iSteps.
    wp۰apply+ (dynarray_2٠data𑁒type with "Htype") as (cap data) "#Hdata_type".
    wp۰apply+ (array٠size𑁒type with "Hdata_type") as "_".
    wp۰pures.
    case_bool_decide; first iSteps.
    wp۰apply+ (dynarray_2٠set_size𑁒type with "Htype") as "_"; first lia.
    wp۰apply+ (array٠unsafe_apply_slice𑁒type with "[$Hdata_type]"); [lia.. | iSteps |].
    iSteps.
  Qed.
  #[local] Lemma dynarray_2٠grow₀𑁒type t (sz' : Z) v :
    {{{
      itype۰dynarray_2 t ∗
      τ v
    }}}
      dynarray_2٠grow₀ t #sz' v
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hv) HΦ".

    iLöb as "HLöb".

    wp۰rec.
    wp۰apply+ (dynarray_2٠reserve𑁒type with "Htype") as "_".
    wp۰apply+ (dynarray_2٠try_grow𑁒type with "[$Htype $Hv]") as ([]) "_"; first iSteps.
    wp۰apply+ ("HLöb" with "HΦ").
  Qed.
  #[local] Lemma dynarray_2٠grow𑁒type t (sz' : Z) v :
    {{{
      itype۰dynarray_2 t ∗
      τ v
    }}}
      dynarray_2٠grow t #sz' v
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hv) HΦ".

    wp۰rec.
    wp۰apply+ (dynarray_2٠try_grow𑁒type with "[$Htype $Hv]") as ([]) "_"; first iSteps.
    wp۰apply+ (dynarray_2٠grow₀𑁒type with "[$Htype $Hv] HΦ").
  Qed.

  #[local] Lemma dynarray_2٠try_push𑁒type t slot :
    {{{
      itype۰dynarray_2 t ∗
      itype۰slot slot
    }}}
      dynarray_2٠try_push t slot
    {{{
      b
    , RET #b;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hslot) HΦ".
    wp۰rec.
    wp۰apply+ (dynarray_2٠size𑁒type with "Htype") as "%sz _".
    wp۰apply+ (dynarray_2٠data𑁒type with "Htype") as "%cap %data #Hdata_type".
    wp۰apply+ (array٠size𑁒type with "Hdata_type") as "_".
    wp۰pures.
    case_bool_decide; wp۰pures; first iSteps.
    wp۰apply (dynarray_2٠set_size𑁒type with "Htype") as "_"; first lia.
    wp۰apply+ (array٠unsafe_set𑁒type with "[$Hdata_type $Hslot]") as "_"; first lia.
    iSteps.
  Qed.
  #[local] Lemma dynarray_2٠push₀𑁒type t slot :
    {{{
      itype۰dynarray_2 t ∗
      itype۰slot slot
    }}}
      dynarray_2٠push₀ t slot
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hslot) HΦ".
    iLöb as "HLöb".
    wp۰rec.
    wp۰apply+ (dynarray_2٠reserve_extra𑁒type with "Htype") as "_".
    wp۰apply+ (dynarray_2٠try_push𑁒type with "[$Htype $Hslot]") as ([]) "_"; first iSteps.
    wp۰apply+ ("HLöb" with "HΦ").
  Qed.
  Lemma dynarray_2٠push𑁒type t v :
    {{{
      itype۰dynarray_2 t ∗
      τ v
    }}}
      dynarray_2٠push t v
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hv) HΦ".
    wp۰rec.
    wp۰apply+ (dynarray_2٠element𑁒type with "[//]") as (slot) "#Hslot".
    wp۰apply+ (dynarray_2٠try_push𑁒type with "[$Htype $Hslot]") as ([]) "_"; first iSteps.
    wp۰apply+ (dynarray_2٠push₀𑁒type with "[$Htype $Hslot]").
    iSteps.
  Qed.

  Lemma dynarray_2٠pop𑁒type t :
    {{{
      itype۰dynarray_2 t
    }}}
      dynarray_2٠pop t
    {{{
      v
    , RET v;
      τ v
    }}}.
  Proof.
    iIntros "%Φ #Htype HΦ".
    wp۰rec.
    wp۰apply (dynarray_2٠size𑁒type with "Htype") as "%sz _".
    wp۰apply+ (dynarray_2٠data𑁒type with "Htype") as "%cap %data #Hdata_type".
    wp۰apply+ (array٠size𑁒type with "Hdata_type") as "_".
    wp۰apply+ assume𑁒spec' as "%Hcap".
    wp۰apply+ assume𑁒spec' as "%Hsz".
    wp۰apply+ (array٠unsafe_get𑁒type with "Hdata_type") as "%slot #Hslot"; first lia.
    wp۰apply (wp𑁒match𑁒slot with "Hslot").
    iSplit; first iSteps. iIntros "%elem #Helem /=".
    wp۰apply+ (array٠unsafe_set𑁒type with "[$Hdata_type]") as "_"; [lia | iSteps |].
    wp۰apply+ (dynarray_2٠set_size𑁒type with "Htype") as "_"; first lia.
    wp۰apply+ (element_get𑁒type with "Helem").
    iSteps.
  Qed.

  Lemma dynarray_2٠fit_capacity𑁒type t v :
    {{{
      itype۰dynarray_2 t
    }}}
      dynarray_2٠fit_capacity t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ #Htype HΦ".
    wp۰rec.
    wp۰apply (dynarray_2٠size𑁒type with "Htype") as "%sz _".
    wp۰apply+ (dynarray_2٠data𑁒type with "Htype") as "%cap %data #Hdata_type".
    wp۰apply+ (array٠size𑁒type with "Hdata_type") as "_".
    wp۰pures.
    case_decide; wp۰pures; first iSteps.
    wp۰apply (array٠shrink𑁒type with "Hdata_type") as "%t' (_ & #Hdata_type')".
    wp۰apply (dynarray_2٠set_data𑁒type with "[$Htype $Hdata_type']").
    iSteps.
  Qed.

  Lemma dynarray_2٠reset𑁒type t v :
    {{{
      itype۰dynarray_2 t
    }}}
      dynarray_2٠reset t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ #Htype HΦ".
    wp۰rec.
    wp۰apply (dynarray_2٠set_size𑁒type with "Htype") as "_"; first done.
    wp۰apply+ (array٠create𑁒type with "[//]") as "%data' #Hdata_type'".
    wp۰apply (dynarray_2٠set_data𑁒type with "[$Htype $Hdata_type']").
    iSteps.
  Qed.

  Lemma dynarray_2٠iteri𑁒type fn t :
    {{{
      itype۰dynarray_2 t ∗
      (itype۰nat --> τ --> itype۰unit)%T fn
    }}}
      dynarray_2٠iteri fn t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (dynarray_2٠size𑁒type with "Htype") as "%sz _".
    wp۰apply+ (dynarray_2٠data𑁒type with "Htype") as "%cap %data #Hdata_type".
    wp۰apply+ (array٠size𑁒type with "Hdata_type") as "_".
    wp۰apply+ assume𑁒spec' as "%".
    wp۰apply+ (array٠unsafe_iteri_slice𑁒type with "[$Hdata_type]"); [lia.. | iSteps |].
    iSteps.
  Qed.

  Lemma dynarray_2٠iter𑁒type fn t :
    {{{
      itype۰dynarray_2 t ∗
      (τ --> itype۰unit)%T fn
    }}}
      dynarray_2٠iter fn t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hfn) HΦ".
    wp۰rec.
    wp۰apply+ (dynarray_2٠iteri𑁒type with "[$Htype] HΦ").
    iSteps.
  Qed.
End zoo۰G.

Require zoo_std.dynarray_2__opaque.

#[global] Opaque dynarray_2۰model.
#[global] Opaque itype۰dynarray_2.
