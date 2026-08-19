Require Import zoo.prelude.
Require Import zoo.common.list.
Require Import zoo.iris.bi.big_op.
Require Import zoo.base.
Require Export zoo_std.dynarray_2__code.
Require Import zoo_std.dynarray_2__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type i : nat.
Implicit Type l elem  : location.
Implicit Type elems : list location.
Implicit Type v t data slot fn : val.
Implicit Type vs slots : list val.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  #[local] Definition element۰model elem v : iProp Σ :=
    elem ↦ₕ Header Tag1 §Element ∗
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

  #[global] Instance dynarray_2۰modelｰtimeless t vs :
    Timeless (dynarray_2۰model t vs).
  Proof.
    apply _.
  Qed.

  #[local] Lemma dynarray_2٠elementｰspec v :
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

  Lemma dynarray_2٠createｰspec' :
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
    wp۰apply (array٠createｰspec with "[//]") as "%data Hmodel".
    wp۰block l as "Hl_meta" "Hl_size Hl_data".
    iDestruct (meta_tokenｰdifference (↑nroot.@"user") with "Hl_meta") as "(Hl_meta & _)"; first done.
    iSteps. iExists [], 0. iSteps.
  Qed.
  Lemma dynarray_2٠createｰspec :
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
    wp۰apply (dynarray_2٠createｰspec' with "[//]").
    iSteps.
  Qed.

  Lemma dynarray_2٠makeｰspec sz v :
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
    wp۰apply+ (array٠initｰspec Ψ) as "%data %slots (%Hsz & %Helems & Hmodel & (%elems & -> & Helems))".
    { iSplit.
      - iSteps. iExists []. iSteps.
      - iIntros "!> %data %i %slots %Hi1 %Hi2 (%elems & -> & Helems)".
        wp۰apply+ (dynarray_2٠elementｰspec with "[//]") as (elem) "Helem".
        iExists (elems ++ [elem]).
        rewrite -fmap_snoc big_sepL_snoc. iSteps.
    }

    iSteps.
    - simp_length. iSteps.
    - iExists elems, 0. rewrite right_id. iSteps.
      iApply (big_sepL2ｰreplicateｰr₂ (λ _, element۰model) with "Helems").
      { simp_length in Helems. }
  Qed.

  Lemma dynarray_2٠initiｰspec Ψ sz fn :
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
    wp۰apply+ (array٠initiｰspec Ψ' with "[HΨ]") as "%data %elems (%Hsz & %Helems & Hmodel & (%slots & %vs & -> & HΨ & Helems))".
    { iSplit.
      - iSteps. iExists []. iSteps.
      - iIntros "!> %t %i %slots %Hi1 %Hi2 (%elems & %vs & -> & HΨ & Helems)".
        simp_length in Hi2.
        iDestruct (big_sepL2_length with "Helems") as %Helems.
        wp۰apply+ (wpｰwand with "(Hfn [%] HΨ)") as "%v HΨ"; first lia.
        wp۰apply (dynarray_2٠elementｰspec with "[//]") as (elem) "Helem".
        iExists (elems ++ [elem]), (vs ++ [v]).
        rewrite -fmap_snoc big_sepL2_snoc. iSteps.
    }

    wp۰block l as "Hl_size Hl_data".

    iApply "HΦ".
    iDestruct (big_sepL2_length with "Helems") as %Helems'.
    simp_length in Helems.
    iFrameStep. iExists 0. rewrite right_id. iSteps.
  Qed.
  Lemma dynarray_2٠initiｰspec' Ψ sz fn :
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
    wp۰apply (dynarray_2٠initiｰspec Ψ' with "[$HΨ Hfn]"); last iSteps.
    rewrite Nat.sub_0_r. iFrame. iIntros "!> %i %vs (%Hi1 & %Hi2) (HΨ & HΞ)".
    destruct (Nat.lt_exists_pred 0 (₊sz - i)) as (k & Hk & _); first lia. rewrite Hk.
    rewrite -cons_seq. iDestruct "HΞ" as "(Hfn & HΞ)".
    wp۰apply (wpｰwand with "(Hfn [//] HΨ)"). iSteps.
    rewrite Nat.sub_succ_r Hk //.
  Qed.
  Lemma dynarray_2٠initiｰspecｰdisentangled Ψ sz fn :
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
    wp۰apply (dynarray_2٠initiｰspec Ψ'); last iSteps.
    rewrite /Ψ'. iSteps.
    rewrite big_sepL_snoc. iSteps.
  Qed.
  Lemma dynarray_2٠initiｰspecｰdisentangled' Ψ sz fn :
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
    wp۰apply (dynarray_2٠initiｰspec' Ψ' with "[Hfn]"); last iSteps.
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn"). iSteps.
    rewrite big_sepL_snoc. iSteps.
  Qed.

  Lemma dynarray_2٠sizeｰspec t vs :
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

  Lemma dynarray_2٠capacityｰspec t vs :
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
    wp۰apply (array٠sizeｰspec with "Hmodel") as "Hmodel".
    simp_length.
    iDestruct (big_sepL2_length with "Helems") as %->.
    iSteps.
  Qed.

  Lemma dynarray_2٠is_emptyｰspec t vs :
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
    wp۰apply+ (dynarray_2٠sizeｰspec with "Hmodel") as "Hmodel".
    wp۰pures.
    destruct vs; iApply ("HΦ" with "Hmodel").
  Qed.

  Lemma dynarray_2٠getｰspec t vs (i : Z) v :
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
    iDestruct (big_sepL2ｰlookupｰaccｰr with "Helems") as "(%elem & %Helems_lookup & (:element۰model) & Helems)"; first done.
    wp۰rec. rewrite /dynarray_2٠data. wp۰load.
    wp۰apply+ (array٠getｰspec with "[$Hmodel]") as "(% & Hmodel)".
    { rewrite Nat2Z.id lookup_app_l.
      { simp_length. lia. }
      rewrite list_lookup_fmap_Some. naive_solver.
    }
    iSteps.
  Qed.

  Lemma dynarray_2٠setｰspec t vs (i : Z) v :
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
    iDestruct (big_sepL2ｰinsertｰaccｰr with "Helems") as "(%elem & %Helems_lookup & (:element۰model) & Helems)"; first done.
    wp۰rec. rewrite /dynarray_2٠data. wp۰load.
    wp۰apply+ (array٠getｰspec with "[$Hmodel]") as "Hmodel".
    { rewrite Nat2Z.id lookup_app_l.
      { simp_length. lia. }
      rewrite list_lookup_fmap_Some. naive_solver.
    }
    wp۰match. wp۰store.
    iDestruct ("Helems" with "[Helem_header Helem_value]") as "Helems"; first iSteps.
    rewrite (list_insert_id elems) //.
    iSteps. simp_length.
  Qed.

  #[local] Lemma dynarray_2٠next_capacityｰspec n :
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
  Lemma dynarray_2٠reserveｰspec t vs (n : Z) :
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
    wp۰apply+ assumeｰspec' as "%Hn".
    wp۰load.
    wp۰apply+ (array٠sizeｰspec with "Hmodel") as "Hmodel".
    wp۰pures.
    case_bool_decide; wp۰pures; last iSteps.
    wp۰apply+ (dynarray_2٠next_capacityｰspec with "[//]") as "%n' %Hn'"; first lia.
    wp۰apply int٠maxｰspec.
    wp۰apply+ (array٠unsafe_growｰspec with "Hmodel") as (data') "(Hmodel & Hmodel')"; first lia.
    rewrite /dynarray_2٠set_data. wp۰store.
    rewrite -assoc -replicate_add. iSteps.
  Qed.

  Lemma dynarray_2٠reserve_extraｰspec t vs (n : Z) :
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
    wp۰apply+ assumeｰspec' as "%Hn".
    wp۰apply+ (dynarray_2٠sizeｰspec with "Hmodel") as "Hmodel".
    wp۰apply+ (dynarray_2٠reserveｰspec with "Hmodel").
    iSteps.
  Qed.

  #[local] Lemma dynarray_2٠try_growｰspec t vs sz v :
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
      wp۰apply+ (array٠sizeｰspec with "Hmodel") as "Hmodel".
      wp۰pures. iEval simp_length.
      case_bool_decide; wp۰pures; first iSteps.
      wp۰store.

      wp۰apply+ (array٠unsafe_apply_sliceｰspecｰdisentangled (λ _ 𝑒𝑙𝑒𝑚,
        ∃ elem,
        ⌜𝑒𝑙𝑒𝑚 = #elem⌝ ∗
        element۰model elem v
      )%I with "[$Hmodel]") as (𝑒𝑙𝑒𝑚𝑠) "(%H𝑒𝑙𝑒𝑚𝑠 & Hmodel & Helems')"; simp_length; [lia.. | iSteps |].

      iDestruct (big_sepLｰexists with "Helems'") as "(%elems' & _ & Helems')".
      iDestruct (big_sepL2_sep with "Helems'") as "(Heq & Helems')".
      iDestruct (big_sepL2ｰForall2 with "Heq") as %->%listｰfmapｰaltｰForall2ｰl. iClear "Heq".
      iDestruct (big_sepL2_const_sepL_r with "Helems'") as "(_ & Helems')".
      iDestruct (big_sepL2ｰreplicateｰr₂ (const element۰model) _ _ (₊sz - length vs) with "Helems'") as "Helems'".
      { simp_length in H𝑒𝑙𝑒𝑚𝑠. lia. }
      iDestruct (big_sepL2_app with "Helems Helems'") as "Helems".
      rewrite Nat2Z.id with_sliceｰappｰlength'; first simp_length.
      rewrite assoc -fmap_app drop_replicate.
      iSteps. simp_length. iSteps.
  Qed.
  #[local] Lemma dynarray_2٠grow₁ｰspec t vs sz v :
    {{{
      dynarray_2۰model t vs
    }}}
      dynarray_2٠grow₁ t #sz v
    {{{
      RET ();
      dynarray_2۰model t (vs ++ replicate (₊sz - length vs) v)
    }}}.
  Proof.
    iIntros "%Φ Hmodel HΦ".

    iLöb as "HLöb".

    wp۰rec.
    wp۰apply+ (dynarray_2٠reserveｰspec with "Hmodel") as "(_ & Hmodel)".
    wp۰apply+ (dynarray_2٠try_growｰspec with "Hmodel") as ([]) "Hmodel".

    - wp۰pures.
      iApply ("HΦ" with "Hmodel").

    - wp۰apply+ ("HLöb" with "Hmodel HΦ").
  Qed.
  Lemma dynarray_2٠growｰspec t vs sz v :
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
    wp۰apply+ (dynarray_2٠try_growｰspec with "Hmodel") as ([]) "Hmodel".

    - wp۰pures.
      iApply ("HΦ" with "Hmodel").

    - wp۰apply+ (dynarray_2٠grow₁ｰspec with "Hmodel HΦ").
  Qed.

  #[local] Lemma dynarray_2٠try_pushｰspec t vs elem v :
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
    wp۰apply+ (array٠sizeｰspec with "Hmodel") as "Hmodel".
    wp۰pures.
    case_bool_decide as Htest; wp۰pures.
    { iApply "HΦ". iFrameSteps. }
    wp۰store.
    wp۰apply+ (array٠unsafe_setｰspec with "Hmodel") as "Hmodel"; first lia.
    wp۰pures.
    iApply "HΦ".
    iExists l, data, (elems ++ [elem]), (extra - 1). iStep.
    rewrite length_app Z.add_1_r -Nat2Z.inj_succ Nat.add_comm /=. iFrame.
    rewrite insert_app_r_alt.
    { simp_length. lia. }
    destruct extra.
    - simp_length in Htest. lia.
    - rewrite Nat2Z.id length_fmap Helems Nat.sub_diag.
      rewrite fmap_snoc -assoc /= Nat.sub_0_r.
      iSteps.
  Qed.
  #[local] Lemma dynarray_2٠push₁ｰspec t vs elem v :
    {{{
      dynarray_2۰model t vs ∗
      element۰model elem v
    }}}
      dynarray_2٠push₁ t #elem
    {{{
      RET ();
      dynarray_2۰model t (vs ++ [v])
    }}}.
  Proof.
    iIntros "%Φ (Hmodel & Helem) HΦ".
    iLöb as "HLöb".
    wp۰rec.
    wp۰apply+ (dynarray_2٠reserve_extraｰspec with "Hmodel") as "(_ & Hmodel)".
    wp۰apply+ (dynarray_2٠try_pushｰspec with "[$Hmodel $Helem]") as ([]) ""; first iSteps. iIntros "(Hmodel & Helem)".
    wp۰apply+ ("HLöb" with "Hmodel Helem HΦ").
  Qed.
  Lemma dynarray_2٠pushｰspec t vs v :
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
    wp۰apply+ (dynarray_2٠elementｰspec with "[//]") as (elem) "Helem".
    wp۰apply+ (dynarray_2٠try_pushｰspec with "[$Hmodel $Helem]") as ([]) ""; first iSteps. iIntros "(Hmodel & Helem)".
    wp۰apply+ (dynarray_2٠push₁ｰspec with "[$Hmodel $Helem]").
    iSteps.
  Qed.

  Lemma dynarray_2٠popｰspec {t vs} vs' v :
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
    wp۰apply+ (array٠sizeｰspec with "Hmodel") as "Hmodel".
    do 2 (wp۰apply+ assumeｰspec' as "_").
    wp۰pures.
    rewrite length_app Nat.add_1_r Z.sub_1_r -Nat2Z.inj_pred /=; first lia.
    iDestruct (big_sepL2_length with "Helems") as %Helems. simp_length/= in Helems.
    destruct elems as [| elem elems _] using rev_ind; first (simpl in Helems; lia).
    rewrite length_app Nat.add_cancel_r in Helems. iEval (rewrite -Helems).
    iDestruct (big_sepL2_snoc with "Helems") as "(Helems & (:element۰model))".
    wp۰apply (array٠unsafe_getｰspec with "Hmodel") as "Hmodel"; [lia | | done |].
    { rewrite Nat2Z.id lookup_app_l.
      { simp_length/=. lia. }
      rewrite list_lookup_fmap lookup_app_r // Nat.sub_diag //.
    }
    wp۰match.
    wp۰apply (array٠unsafe_setｰspec with "Hmodel") as "Hmodel".
    { simp_length/=. lia. }

    rewrite fmap_snoc -assoc Nat2Z.id insert_app_r_alt.
    all: simp_length.
    rewrite Nat.sub_diag /=.
    wp۰store. wp۰load.
    iApply "HΦ".
    iExists l, data, elems, ˖extra. iSteps.
  Qed.

  Lemma dynarray_2٠fit_capacityｰspec t vs :
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
    wp۰apply+ (array٠sizeｰspec with "Hmodel") as "Hmodel".
    iDestruct (big_sepL2_length with "Helems") as %Helems.
    wp۰pures.
    case_bool_decide; wp۰pures; first iSteps.
    wp۰apply (array٠shrinkｰspec with "Hmodel") as "%data' (_ & _ & Hmodel')".
    wp۰store.
    iApply "HΦ".
    iExists l, data', elems, 0.
    rewrite take_app_length'.
    { simp_length. lia. }
    rewrite right_id. iSteps.
  Qed.

  Lemma dynarray_2٠resetｰspec t vs :
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
    wp۰apply+ (array٠createｰspec with "[//]") as "%data' Hmodel'".
    wp۰store.
    iSteps. iExists [], 0. iSteps.
  Qed.

  Lemma dynarray_2٠iteriｰspec Ψ fn t vs :
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
    wp۰apply+ (dynarray_2٠sizeｰspec with "Hmodel") as "(:model)".
    wp۰load.
    wp۰apply+ (array٠sizeｰspec with "Hmodel") as "Hmodel".
    wp۰apply+ assumeｰspec' as "%".
    pose Ψ' i slots := (
      Ψ i (take i vs) ∗
      [∗ list] elem; v ∈ elems; vs, element۰model elem v
    )%I.
    wp۰apply+ (array٠unsafe_iteri_sliceｰspec Ψ' with "[$HΨ $Helems $Hmodel]"); [lia.. | |].
    { iIntros "!> %i %slots%Hi %Hlookup (HΨ & Helems)".
      iDestruct (big_sepL2_length with "Helems") as "%Helems".
      rewrite lookup_app_l in Hlookup.
      { simp_length. lia. }
      apply list_lookup_fmap_Some in Hlookup as (elem & -> & Hlookup).
      iDestruct (big_sepL2ｰlookupｰaccｰl with "Helems") as "(%v & % & (:element۰model) & Helems)"; first done.
      wp۰match. wp۰load.
      rewrite sliceｰ0 take_app_le.
      { simp_length. lia. }
      wp۰apply (wpｰwand with "(Hfn [//] HΨ)").
      rewrite -take_S_r //. iSteps.
    }
    iSteps. rewrite Nat2Z.id firstn_all //.
  Qed.
  Lemma dynarray_2٠iteriｰspec' Ψ fn t vs :
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
    wp۰apply (dynarray_2٠iteriｰspec Ψ' with "[$HΨ $Hmodel $Hfn]"); last iSteps.
    iIntros "!> %i %v %Hlookup (HΨ & HΞ)".
    erewrite drop_S => //.
    iDestruct "HΞ" as "(Hfn & HΞ)".
    rewrite Nat.add_0_r. setoid_rewrite Nat.add_succ_r. iSteps.
  Qed.
  Lemma dynarray_2٠iteriｰspecｰdisentangled Ψ fn t vs :
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
    wp۰apply (dynarray_2٠iteriｰspec Ψ' with "[$Hmodel]"); last iSteps.
    rewrite /Ψ'. iSteps.
    rewrite big_sepL_snoc length_take Nat.min_l; last iSteps.
    eapply Nat.lt_le_incl, lookup_lt_Some. done.
  Qed.
  Lemma dynarray_2٠iteriｰspecｰdisentangled' Ψ fn t vs :
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
    wp۰apply (dynarray_2٠iteriｰspec' Ψ' with "[$Hmodel Hfn]"); last iSteps.
    rewrite /Ψ'. iSteps.
    iApply (big_sepL_impl with "Hfn"). iSteps.
    rewrite big_sepL_snoc length_take Nat.min_l; last iSteps.
    eapply Nat.lt_le_incl, lookup_lt_Some. done.
  Qed.

  Lemma dynarray_2٠iterｰspec Ψ fn t vs :
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
    wp۰apply+ (dynarray_2٠iteriｰspec Ψ with "[$HΨ $Hmodel] HΦ").
    iSteps.
  Qed.
  Lemma dynarray_2٠iterｰspec' Ψ fn t vs :
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
    wp۰apply+ (dynarray_2٠iteriｰspec' Ψ with "[$HΨ $Hmodel Hfn] HΦ").
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.
  Lemma dynarray_2٠iterｰspecｰdisentangled Ψ fn t vs :
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
    wp۰apply+ (dynarray_2٠iteriｰspecｰdisentangled Ψ with "[$Hmodel] HΦ").
    iSteps.
  Qed.
  Lemma dynarray_2٠iterｰspecｰdisentangled' Ψ fn t vs :
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
    wp۰apply+ (dynarray_2٠iteriｰspecｰdisentangled' Ψ with "[$Hmodel Hfn] HΦ").
    iApply (big_sepL_impl with "Hfn").
    iSteps.
  Qed.

  Context τ `{!iType (iPropI Σ) τ}.

  #[local] Definition itype۰element elem : iProp Σ :=
    elem ↦ₕ Header Tag1 §Element ∗
    inv nroot (
      ∃ v,
      elem.[value] ↦ v ∗
      τ v
    ).

  Lemma element_getｰtype elem :
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

  Lemma element_setｰtype elem v :
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
  #[local] Instance itype۰slotｰitype :
    iType _ itype۰slot.
  Proof.
    split. apply _.
  Qed.

  #[local] Lemma wpｰmatchｰslot slot e1 x e2 Φ :
    itype۰slot slot -∗
    ( WP e1 {{ Φ }} ∧
      ∀ elem, itype۰element elem -∗ WP subst' x #elem e2 {{ Φ }}
    ) -∗
    WP 𝗺𝗮𝘁𝗰𝗵 slot 𝘄𝗶𝘁𝗵 Empty -> e1 | Element ⎽ 𝗮𝘀: x -> e2 𝗲𝗻𝗱 {{ Φ }}.
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
  #[global] Instance itype۰dynarray_2ｰitype :
    iType _ itype۰dynarray_2.
  Proof.
    split. apply _.
  Qed.

  #[local] Lemma dynarray_2٠elementｰtype v :
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

  Lemma dynarray_2٠createｰtype :
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
    wp۰apply (array٠createｰtype itype۰slot with "[//]") as "%data Hdata_type".
    iSteps.
  Qed.

  Lemma dynarray_2٠makeｰtype (sz : Z) v :
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
    wp۰apply+ (array٠initｰtype itype۰slot) as "%data (%Hsz & Hdata_type)"; first iSteps.
    iSteps.
  Qed.

  Lemma dynarray_2٠initiｰtype sz fn :
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
    wp۰apply+ array٠initiｰtype; last iSteps. iIntros "!> % (% & -> & %Hi)".
    wp۰apply+ (wpｰwand with "(Hfn [])") as (v) "#Hv"; first iSteps.
    wp۰apply (dynarray_2٠elementｰtype with "[//]").
    iSteps.
  Qed.

  Lemma dynarray_2٠sizeｰtype t :
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

  Lemma dynarray_2٠capacityｰtype t :
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

  #[local] Lemma dynarray_2٠dataｰtype t :
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

  #[local] Lemma dynarray_2٠set_sizeｰtype t sz :
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

  #[local] Lemma dynarray_2٠set_dataｰtype t cap data :
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

  Lemma dynarray_2٠is_emptyｰtype t :
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

  Lemma dynarray_2٠getｰtype t (i : Z) :
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
    wp۰apply+ (dynarray_2٠dataｰtype with "Htype") as "%cap %data #Hdata_type".
    wp۰apply (array٠getｰtype with "Hdata_type") as "%slot (%Hi & #Hslot)".
    wp۰apply (wpｰmatchｰslot with "Hslot").
    iSteps.
  Qed.

  Lemma dynarray_2٠setｰtype t (i : Z) v :
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
    wp۰apply+ (dynarray_2٠dataｰtype with "Htype") as "%cap %data #Hdata_type".
    wp۰apply (array٠getｰtype with "Hdata_type") as "%slot (%Hi & #Hslot)".
    wp۰apply (wpｰmatchｰslot with "Hslot").
    iSteps.
  Qed.

  Lemma dynarray_2٠reserveｰtype t n :
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
    wp۰apply+ assumeｰspec' as "%Hn".
    wp۰apply+ (dynarray_2٠dataｰtype with "Htype") as "%cap %data #Hdata_type".
    wp۰apply+ (array٠sizeｰtype with "Hdata_type") as "_".
    wp۰pures.
    case_bool_decide; wp۰pures; last iSteps.
    wp۰apply+ (dynarray_2٠next_capacityｰspec with "[//]") as "%n' %Hn'"; first lia.
    wp۰apply int٠maxｰspec.
    wp۰apply+ (array٠unsafe_growｰtype itype۰slot with "[$Hdata_type]") as (data') "#Hdata_type'"; [lia | iSteps |].
    wp۰apply+ (dynarray_2٠set_dataｰtype with "[$Htype $Hdata_type']") as "_".
    iSteps.
  Qed.
  Lemma dynarray_2٠reserve_extraｰtype t n :
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
    wp۰apply+ assumeｰspec' as "%Hn".
    wp۰apply+ (dynarray_2٠sizeｰtype with "Htype") as "%sz _".
    wp۰apply+ (dynarray_2٠reserveｰtype with "Htype").
    iSteps.
  Qed.

  #[local] Lemma dynarray_2٠try_growｰtype t (sz' : Z) v :
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
    wp۰apply+ (dynarray_2٠sizeｰtype with "Htype") as (sz) "_".
    wp۰pures.
    case_bool_decide; first iSteps.
    wp۰apply+ (dynarray_2٠dataｰtype with "Htype") as (cap data) "#Hdata_type".
    wp۰apply+ (array٠sizeｰtype with "Hdata_type") as "_".
    wp۰pures.
    case_bool_decide; first iSteps.
    wp۰apply+ (dynarray_2٠set_sizeｰtype with "Htype") as "_"; first lia.
    wp۰apply+ (array٠unsafe_apply_sliceｰtype with "[$Hdata_type]"); [lia.. | iSteps |].
    iSteps.
  Qed.
  #[local] Lemma dynarray_2٠grow₁ｰtype t (sz' : Z) v :
    {{{
      itype۰dynarray_2 t ∗
      τ v
    }}}
      dynarray_2٠grow₁ t #sz' v
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hv) HΦ".

    iLöb as "HLöb".

    wp۰rec.
    wp۰apply+ (dynarray_2٠reserveｰtype with "Htype") as "_".
    wp۰apply+ (dynarray_2٠try_growｰtype with "[$Htype $Hv]") as ([]) "_"; first iSteps.
    wp۰apply+ ("HLöb" with "HΦ").
  Qed.
  #[local] Lemma dynarray_2٠growｰtype t (sz' : Z) v :
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
    wp۰apply+ (dynarray_2٠try_growｰtype with "[$Htype $Hv]") as ([]) "_"; first iSteps.
    wp۰apply+ (dynarray_2٠grow₁ｰtype with "[$Htype $Hv] HΦ").
  Qed.

  #[local] Lemma dynarray_2٠try_pushｰtype t slot :
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
    wp۰apply+ (dynarray_2٠sizeｰtype with "Htype") as "%sz _".
    wp۰apply+ (dynarray_2٠dataｰtype with "Htype") as "%cap %data #Hdata_type".
    wp۰apply+ (array٠sizeｰtype with "Hdata_type") as "_".
    wp۰pures.
    case_bool_decide; wp۰pures; first iSteps.
    wp۰apply (dynarray_2٠set_sizeｰtype with "Htype") as "_"; first lia.
    wp۰apply+ (array٠unsafe_setｰtype with "[$Hdata_type $Hslot]") as "_"; first lia.
    iSteps.
  Qed.
  #[local] Lemma dynarray_2٠push₁ｰtype t slot :
    {{{
      itype۰dynarray_2 t ∗
      itype۰slot slot
    }}}
      dynarray_2٠push₁ t slot
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ (#Htype & #Hslot) HΦ".
    iLöb as "HLöb".
    wp۰rec.
    wp۰apply+ (dynarray_2٠reserve_extraｰtype with "Htype") as "_".
    wp۰apply+ (dynarray_2٠try_pushｰtype with "[$Htype $Hslot]") as ([]) "_"; first iSteps.
    wp۰apply+ ("HLöb" with "HΦ").
  Qed.
  Lemma dynarray_2٠pushｰtype t v :
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
    wp۰apply+ (dynarray_2٠elementｰtype with "[//]") as (slot) "#Hslot".
    wp۰apply+ (dynarray_2٠try_pushｰtype with "[$Htype $Hslot]") as ([]) "_"; first iSteps.
    wp۰apply+ (dynarray_2٠push₁ｰtype with "[$Htype $Hslot]").
    iSteps.
  Qed.

  Lemma dynarray_2٠popｰtype t :
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
    wp۰apply (dynarray_2٠sizeｰtype with "Htype") as "%sz _".
    wp۰apply+ (dynarray_2٠dataｰtype with "Htype") as "%cap %data #Hdata_type".
    wp۰apply+ (array٠sizeｰtype with "Hdata_type") as "_".
    wp۰apply+ assumeｰspec' as "%Hcap".
    wp۰apply+ assumeｰspec' as "%Hsz".
    wp۰apply+ (array٠unsafe_getｰtype with "Hdata_type") as "%slot #Hslot"; first lia.
    wp۰apply (wpｰmatchｰslot with "Hslot").
    iSplit; first iSteps. iIntros "%elem #Helem /=".
    wp۰apply+ (array٠unsafe_setｰtype with "[$Hdata_type]") as "_"; [lia | iSteps |].
    wp۰apply+ (dynarray_2٠set_sizeｰtype with "Htype") as "_"; first lia.
    wp۰apply+ (element_getｰtype with "Helem").
    iSteps.
  Qed.

  Lemma dynarray_2٠fit_capacityｰtype t v :
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
    wp۰apply (dynarray_2٠sizeｰtype with "Htype") as "%sz _".
    wp۰apply+ (dynarray_2٠dataｰtype with "Htype") as "%cap %data #Hdata_type".
    wp۰apply+ (array٠sizeｰtype with "Hdata_type") as "_".
    wp۰pures.
    case_decide; wp۰pures; first iSteps.
    wp۰apply (array٠shrinkｰtype with "Hdata_type") as "%t' (_ & #Hdata_type')".
    wp۰apply (dynarray_2٠set_dataｰtype with "[$Htype $Hdata_type']").
    iSteps.
  Qed.

  Lemma dynarray_2٠resetｰtype t v :
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
    wp۰apply (dynarray_2٠set_sizeｰtype with "Htype") as "_"; first done.
    wp۰apply+ (array٠createｰtype with "[//]") as "%data' #Hdata_type'".
    wp۰apply (dynarray_2٠set_dataｰtype with "[$Htype $Hdata_type']").
    iSteps.
  Qed.

  Lemma dynarray_2٠iteriｰtype fn t :
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
    wp۰apply+ (dynarray_2٠sizeｰtype with "Htype") as "%sz _".
    wp۰apply+ (dynarray_2٠dataｰtype with "Htype") as "%cap %data #Hdata_type".
    wp۰apply+ (array٠sizeｰtype with "Hdata_type") as "_".
    wp۰apply+ assumeｰspec' as "%".
    wp۰apply+ (array٠unsafe_iteri_sliceｰtype with "[$Hdata_type]"); [lia.. | iSteps |].
    iSteps.
  Qed.

  Lemma dynarray_2٠iterｰtype fn t :
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
    wp۰apply+ (dynarray_2٠iteriｰtype with "[$Htype] HΦ").
    iSteps.
  Qed.
End zoo۰G.

Require zoo_std.dynarray_2__opaque.

#[global] Opaque dynarray_2۰model.
#[global] Opaque itype۰dynarray_2.
