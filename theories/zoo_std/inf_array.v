From Coq.Logic Require Import
  FunctionalExtensionality.

From zoo Require Import
  prelude.
From zoo.common Require Import
  countable.
From zoo.iris.base_logic Require Import
  lib.twins.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
  base
  inf_array__code.
From zoo_std Require Import
  int
  array
  mutex
  inf_array__types.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types l : location.
Implicit Types pid : prophet_id.
Implicit Types v v_resolve t fn : val.
Implicit Types us : list val.
Implicit Types vs : nat → val.

Class InfArrayG Σ `{zoo_G : !ZooG Σ} := {
  #[local] inf_array_G_mutex_G :: MutexG Σ ;
  #[local] inf_array_G_model_G :: TwinsG Σ (nat -d> val_O) ;
}.

Definition inf_array_Σ := #[
  mutex_Σ ;
  twins_Σ (nat -d> val_O)
].
#[global] Instance subG_inf_array_Σ Σ `{zoo_G : !ZooG Σ} :
  subG inf_array_Σ Σ →
  InfArrayG Σ .
Proof.
  solve_inG.
Qed.

Section inf_array_G.
  Context `{inf_array_G : InfArrayG Σ}.

  Record metadata := {
    metadata_default : val ;
    metadata_model : gname ;
  }.
  Implicit Types γ : metadata.

  #[local] Instance metadata_eq_dec : EqDecision metadata :=
    ltac:(solve_decision).
  #[local] Instance metadata_countable :
    Countable metadata.
  Proof.
    solve_countable.
  Qed.

  #[local] Definition model₁' γ_model vs :=
    twins_twin1 γ_model (DfracOwn 1) vs.
  #[local] Definition model₁ γ vs :=
    model₁' γ.(metadata_model) vs.
  #[local] Definition model₂' γ_model vs :=
    twins_twin2 γ_model vs.
  #[local] Definition model₂ γ vs :=
    model₂' γ.(metadata_model) vs.

  #[local] Definition inv_2 l γ us : iProp Σ :=
    ∃ data vs,
    l.[data] ↦ data ∗
    array_model data (DfracOwn 1) us ∗
    model₂ γ vs ∗
    ⌜vs = λ i, if decide (i < length us) then us !!! i else γ.(metadata_default)⌝.
  #[local] Instance : CustomIpatFormat "inv_2" :=
    "(
      %data &
      %vs &
      Hl_data &
      Hdata &
      Hmodel₂ &
      %Hvs
    )".
  #[local] Definition inv_1 l γ : iProp Σ :=
    ∃ us,
    inv_2 l γ us.
  #[local] Instance : CustomIpatFormat "inv_1" :=
    "(
      %us{} &
      {{lazy}Hinv=(:inv_2)}
    )".
  Definition inf_array_inv t : iProp Σ :=
    ∃ l γ mtx,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    l.[default] ↦□ γ.(metadata_default) ∗
    l.[mutex] ↦□ mtx ∗
    mutex_inv mtx (inv_1 l γ).
  #[local] Instance : CustomIpatFormat "inv" :=
    "(
      %l &
      %γ &
      %mtx &
      -> &
      #Hmeta &
      #Hl_mtx &
      #Hl_default &
      #Hmtx_inv
    )".

  Definition inf_array_model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    model₁ γ vs.
  #[local] Instance : CustomIpatFormat "model" :=
    "(
      %l_ &
      %γ_ &
      %Heq &
      #Hmeta_ &
      Hmodel₁
    )".
  Definition inf_array_model' t vsₗ vsᵣ :=
    inf_array_model t (
      λ i,
        if decide (i < length vsₗ) then vsₗ !!! i else vsᵣ (i - length vsₗ)
    ).

  #[global] Instance inf_array_inv_persistent t :
    Persistent (inf_array_inv t).
  Proof.
    apply _.
  Qed.

  #[global] Instance inf_array_model_ne t n :
    Proper (pointwise_relation nat (=) ==> (≡{n}≡)) (inf_array_model t).
  Proof.
    intros vs1 vs2 ->%functional_extensionality. done.
  Qed.
  #[global] Instance inf_array_model_proper t :
    Proper (pointwise_relation nat (=) ==> (≡)) (inf_array_model t).
  Proof.
    intros vs1 vs2 Hvs. rewrite equiv_dist. solve_proper.
  Qed.
  #[global] Instance inf_array_model_timeless t vs :
    Timeless (inf_array_model t vs).
  Proof.
    apply _.
  Qed.

  #[global] Instance inf_array_model'_ne t n :
    Proper ((=) ==> pointwise_relation nat (=) ==> (≡{n}≡)) (inf_array_model' t).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance inf_array_model'_proper t :
    Proper ((=) ==> pointwise_relation nat (=) ==> (≡)) (inf_array_model' t).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance inf_array_model'_timeless t vsₗ vsᵣ :
    Timeless (inf_array_model' t vsₗ vsᵣ).
  Proof.
    apply _.
  Qed.

  #[local] Lemma model_alloc default :
    ⊢ |==>
      ∃ γ_model,
      model₁' γ_model (λ _, default) ∗
      model₂' γ_model (λ _, default).
  Proof.
    apply twins_alloc'.
  Qed.
  #[local] Lemma model_agree γ vs1 vs2 :
    model₁ γ vs1 -∗
    model₂ γ vs2 -∗
    ⌜vs1 = vs2⌝.
  Proof.
    iIntros "Hmodel₁ Hmodel₂".
    iDestruct (twins_agree_discrete with "Hmodel₁ Hmodel₂") as %->%functional_extensionality.
    iSteps.
  Qed.
  #[local] Lemma model_update {γ vs1 vs2} vs :
    model₁ γ vs1 -∗
    model₂ γ vs2 ==∗
      model₁ γ vs ∗
      model₂ γ vs.
  Proof.
    apply twins_update'.
  Qed.

  Lemma inf_array_model_to_model' {t vs} vsₗ :
    (∀ i v, vsₗ !! i = Some v → vs i = v) →
    inf_array_model t vs ⊢
    inf_array_model' t vsₗ (λ i, vs (length vsₗ + i)).
  Proof.
    intros Hvs.
    rewrite /inf_array_model' inf_array_model_proper; last done.
    intros i. case_decide.
    - apply Hvs, list_lookup_lookup_total_lt. done.
    - rewrite -Nat.le_add_sub //; first lia.
  Qed.
  Lemma inf_array_model_to_model'_replicate {t vs} n v :
    (∀ i, i < n → vs i = v) →
    inf_array_model t vs ⊢
    inf_array_model' t (replicate n v) (λ i, vs (n + i)).
  Proof.
    intros Hvs.
    rewrite -{2}(length_replicate n v).
    apply inf_array_model_to_model'. intros i v_ (-> & Hi)%lookup_replicate.
    auto.
  Qed.
  Lemma inf_array_model_to_model'_constant {t v} n :
    inf_array_model t (λ _, v) ⊢
    inf_array_model' t (replicate n v) (λ _, v).
  Proof.
    apply: inf_array_model_to_model'_replicate. done.
  Qed.

  Lemma inf_array_model'_shift t vsₗ v vsᵣ :
    inf_array_model' t (vsₗ ++ [v]) vsᵣ ⊣⊢
    inf_array_model' t vsₗ (λ i, match i with 0 => v | S i => vsᵣ i end).
  Proof.
    rewrite /inf_array_model' inf_array_model_proper; last done.
    intros j. simpl_length/=.
    destruct (Nat.lt_total j (length vsₗ)) as [| [-> |]].
    - rewrite !decide_True; try lia.
      rewrite lookup_total_app_l //.
    - rewrite decide_True; first lia.
      rewrite decide_False; first lia.
      rewrite lookup_total_app_r //.
      rewrite Nat.sub_diag //.
    - rewrite !decide_False; try lia.
      case_match; [lia | f_equal; lia].
  Qed.
  Lemma inf_array_model'_shift_r t vsₗ v vsᵣ :
    inf_array_model' t (vsₗ ++ [v]) vsᵣ ⊢
    inf_array_model' t vsₗ (λ i, match i with 0 => v | S i => vsᵣ i end).
  Proof.
    rewrite inf_array_model'_shift. iSteps.
  Qed.
  Lemma inf_array_model'_shift_l t vsₗ vsᵣ v vsᵣ' :
    (∀ i, vsᵣ i = match i with 0 => v | S i => vsᵣ' i end) →
    inf_array_model' t vsₗ vsᵣ ⊢
    inf_array_model' t (vsₗ ++ [v]) vsᵣ'.
  Proof.
    intros.
    rewrite inf_array_model'_shift inf_array_model'_proper; last done; done.
  Qed.

  Lemma inf_array_create_spec default :
    {{{
      True
    }}}
      inf_array_create default
    {{{ t,
      RET t;
      inf_array_inv t ∗
      inf_array_model t (λ _, default)
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_rec.
    wp_apply (array_create_spec with "[//]") as "%data Hdata".
    wp_smart_apply (mutex_create_spec_init with "[//]") as (mtx) "Hmtx_init".
    wp_block l as "Hmeta" "(Hl_data & Hl_default & Hl_mtx & _)".
    iMod (pointsto_persist with "Hl_default") as "#Hl_default".

    iMod (model_alloc default) as "(%γ_model & Hmodel₁ & Hmodel₂)".

    pose γ := {|
      metadata_default := default ;
      metadata_model := γ_model ;
    |}.
    iMod (meta_set γ with "Hmeta") as "#Hmeta"; first done.

    iMod (mutex_init_to_inv (inv_1 l γ) with "Hmtx_init [Hl_data Hdata Hmodel₂]") as "#Hmtx_inv".
    { rewrite /inv_1. iSteps. }
    iSteps.
  Qed.

  #[local] Lemma inf_array_next_capacity_spec n :
    (0 ≤ n)%Z →
    {{{
      True
    }}}
      inf_array_next_capacity #n
    {{{ m,
      RET #m;
      ⌜n ≤ m⌝%Z
    }}}.
  Proof.
    iSteps; wp_apply int_max_spec; iSteps.
  Qed.
  #[local] Lemma inf_array_reserve_spec l γ us n :
    (0 ≤ n)%Z →
    {{{
      l.[default] ↦□ γ.(metadata_default) ∗
      inv_2 l γ us
    }}}
      inf_array_reserve #l #n
    {{{ us,
      RET ();
      inv_2 l γ us ∗
      ⌜₊n ≤ length us⌝
    }}}.
  Proof.
    iIntros "%Hn %Φ (#Hl_default & (:inv_2)) HΦ".

    wp_rec. wp_load.
    wp_smart_apply (array_size_spec with "Hdata") as "Hdata".
    wp_pures. case_bool_decide; last iSteps.
    wp_smart_apply (inf_array_next_capacity_spec with "[//]") as (?) "%"; first lia.
    wp_apply int_max_spec.
    wp_load.
    wp_smart_apply (array_unsafe_grow_spec with "Hdata") as (data') "(Hdata & Hdata')"; first lia.
    wp_store.

    iSteps; iPureIntro; simpl_length; last lia.
    apply functional_extensionality => i. rewrite Hvs.
    case_decide; last case_decide.
    - rewrite decide_True; first lia.
      rewrite lookup_total_app_l //.
    - rewrite lookup_total_app_r; first lia.
      rewrite lookup_total_replicate_2 //; first lia.
    - done.
  Qed.

  Lemma inf_array_get_spec t i :
    (0 ≤ i)%Z →
    <<<
      inf_array_inv t
    | ∀∀ vs,
      inf_array_model t vs
    >>>
      inf_array_get t #i
    <<<
      inf_array_model t vs
    | RET vs ₊i;
      True
    >>>.
  Proof.
    iIntros "% %Φ (:inv) HΦ".

    wp_rec. wp_load.
    wp_apply (mutex_protect_spec Φ with "[$Hmtx_inv HΦ]"); last iSteps. iIntros "$ (:inv_1)".
    wp_load.
    wp_smart_apply (array_size_spec with "Hdata") as "Hdata".
    wp_pures. case_decide.

    - rewrite bool_decide_eq_true_2; first lia.
      iApply wp_fupd.
      wp_smart_apply (array_unsafe_get_spec with "Hdata"); [done | | done |].
      { rewrite list_lookup_lookup_total_lt //. lia. }

      iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod ("HΦ" with "[$Hmodel₁]") as "HΦ"; first iSteps.

      rewrite /inv_1. iSteps.
      rewrite Hvs decide_True; first lia. iSteps.

    - rewrite bool_decide_eq_false_2; first lia. wp_load.

      iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod ("HΦ" with "[$Hmodel₁]") as "HΦ"; first iSteps.

      rewrite /inv_1. iSteps.
      rewrite Hvs decide_False; first lia. iSteps.
  Qed.
  Lemma inf_array_get_spec' t i :
    (0 ≤ i)%Z →
    <<<
      inf_array_inv t
    | ∀∀ vsₗ vsᵣ,
      inf_array_model' t vsₗ vsᵣ
    >>>
      inf_array_get t #i
    <<<
      inf_array_model' t vsₗ vsᵣ
    | RET
        if decide (₊i < length vsₗ) then vsₗ !!! ₊i else vsᵣ (₊i - length vsₗ);
      True
    >>>.
  Proof.
    iIntros "% %Φ Hinv HΦ".
    awp_apply (inf_array_get_spec with "Hinv"); first done.
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vsₗ %vsᵣ Hmodel".
    iAaccIntro with "Hmodel"; iSteps.
  Qed.

  Lemma inf_array_update_spec Ψ1 Ψ2 t i fn :
    (0 ≤ i)%Z →
    <<<
      inf_array_inv t ∗
      (∀ v, Ψ1 v -∗ WP fn v {{ Ψ2 v }})
    | ∀∀ vs,
      inf_array_model t vs ∗
      □ Ψ1 (vs ₊i)
    >>>
      inf_array_update t #i fn
    <<<
      ∃∃ v,
      inf_array_model t (<[₊i := v]> vs) ∗
      Ψ2 (vs ₊i) v
    | RET vs ₊i;
      True
    >>>.
  Proof.
    iIntros "% %Φ ((:inv) & Hfn) HΦ".

    wp_rec. wp_load.
    wp_apply (mutex_protect_spec Φ with "[$Hmtx_inv Hfn HΦ]"); last iSteps. iIntros "$ (:inv_1 =1 lazy=)".
    wp_smart_apply (inf_array_reserve_spec with "[$]") as "%us2 ((:inv_2) & %)"; first lia.
    wp_load.

    destruct (lookup_lt_is_Some_2 us2 ₊i) as (v & Hlookup); first lia.
    iApply fupd_wp.
    iMod "HΦ" as "(%vs_ & ((:model) & #Hv) & HΦ & _)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
    assert (vs ₊i = v) as Hv.
    { rewrite Hvs decide_True; first lia.
      apply list_lookup_total_correct. done.
    }
    rewrite Hv.
    iMod ("HΦ" with "[$Hmodel₁]") as "HΦ"; first iSteps.
    iModIntro.

    wp_apply (array_unsafe_get_spec with "Hdata") as "Hdata"; [lia | done.. |].
    wp_smart_apply (wp_wand with "(Hfn Hv)") as (w) "Hw".
    wp_load.
    wp_smart_apply (array_unsafe_set_spec with "Hdata") as "Hdata"; first lia.
    wp_pures.

    iMod "HΦ" as "(%vs_ & ((:model) & _) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
    iMod (model_update (<[₊i := w]> vs) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iMod ("HΦ" with "[$Hmodel₁ Hw]") as "HΦ"; first naive_solver.

    iFrame. rewrite Hv. iSplitR "HΦ"; last iSteps. iPureIntro.
    rewrite length_insert Hvs.
    apply functional_extensionality => j.
    destruct (decide (j = ₊i)) as [-> |].
    - rewrite fn_lookup_insert decide_True; first lia.
      rewrite list_lookup_total_insert //. lia.
    - rewrite fn_lookup_insert_ne //. case_decide; last done.
      rewrite list_lookup_total_insert_ne //.
  Qed.

  Lemma inf_array_xchg_spec t i v :
    (0 ≤ i)%Z →
    <<<
      inf_array_inv t
    | ∀∀ vs,
      inf_array_model t vs
    >>>
      inf_array_xchg t #i v
    <<<
      inf_array_model t (<[₊i := v]> vs)
    | RET vs ₊i;
      True
    >>>.
  Proof.
    iIntros "% %Φ Hinv HΦ".

    wp_rec.
    awp_smart_apply (inf_array_update_spec (λ _, True)%I (λ _ w, ⌜w = v⌝)%I with "[$Hinv]"); [done | iSteps |].
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs Hmodel".
    rewrite /atomic_acc /=. iFrameSteps.
  Qed.

  Lemma inf_array_xchg_resolve_spec t i v pid v_resolve Φ :
    (0 ≤ i)%Z →
    inf_array_inv t -∗
    ( |={⊤,∅}=>
      ∃ vs,
      inf_array_model t vs ∗
      ( ∀ e,
        ⌜PureExec True 1 e ()⌝ -∗
        ⌜to_val e = None⌝ -∗
        inf_array_model t (<[₊i := v]> vs) -∗
        WP Resolve e #pid v_resolve @ ∅ {{ _,
          |={∅,⊤}=>
          Φ (vs ₊i)
        }}
      )
    ) -∗
    WP inf_array_xchg_resolve t #i v #pid v_resolve {{ Φ }}.
  Proof.
    iIntros "% (:inv) HΦ".

    wp_rec. wp_load.
    wp_apply (mutex_protect_spec Φ with "[$Hmtx_inv HΦ]"); last iSteps. iIntros "$ (:inv_1 =1 lazy=)".
    wp_smart_apply (inf_array_reserve_spec with "[$]") as "%us2 ((:inv_2) & %)"; first lia.
    wp_load.

    destruct (lookup_lt_is_Some_2 us2 ₊i) as (w & Hlookup); first lia.
    assert (vs ₊i = w) as Hw.
    { rewrite Hvs decide_True; first lia.
      apply list_lookup_total_correct. done.
    }

    wp_apply (array_unsafe_get_spec with "Hdata") as "Hdata"; [lia | done.. |].
    wp_load.
    wp_smart_apply (array_unsafe_set_spec with "Hdata") as "Hdata"; first lia.
    wp_pures.

    set vs' := <[₊i := v]> vs.
    wp_bind (Resolve _ _ _).
    wp_apply (wp_wand (λ _,
      model₂ γ vs' ∗
      Φ w
    )%I with "[Hmodel₂ HΦ]") as (?) "(Hmodel₂ & HΦ)".
    { iMod "HΦ" as "(%vs_ & (:model) & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod (model_update vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & $)".
      rewrite Hw.
      wp_apply (wp_wand with "(HΦ [%] [%] [Hmodel₁])") as (?) "$".
      { done. }
      { iSteps. }
    }

    wp_pures.
    iFrame. iPureIntro.
    rewrite /vs' length_insert Hvs.
    apply functional_extensionality => j.
    destruct (decide (j = ₊i)) as [-> |].
    - rewrite fn_lookup_insert decide_True; first lia.
      rewrite list_lookup_total_insert //. lia.
    - rewrite fn_lookup_insert_ne //. case_decide; last done.
      rewrite list_lookup_total_insert_ne //.
  Qed.

  Lemma inf_array_set_spec t i v :
    (0 ≤ i)%Z →
    <<<
      inf_array_inv t
    | ∀∀ vs,
      inf_array_model t vs
    >>>
      inf_array_set t #i v
    <<<
      inf_array_model t (<[₊i := v]> vs)
    | RET ();
      True
    >>>.
  Proof.
    iIntros "% %Φ Hinv HΦ".

    wp_rec.
    wp_smart_apply (inf_array_xchg_spec with "Hinv"); first done.
    iApply (atomic_update_wand with "HΦ").
    iSteps.
  Qed.
  Lemma inf_array_set_spec' t i v :
    (0 ≤ i)%Z →
    <<<
      inf_array_inv t
    | ∀∀ vsₗ vsᵣ,
      inf_array_model' t vsₗ vsᵣ
    >>>
      inf_array_set t #i v
    <<<
      if decide (₊i < length vsₗ) then
        inf_array_model' t (<[₊i := v]> vsₗ) vsᵣ
      else
        inf_array_model' t vsₗ (<[₊i - length vsₗ := v]> vsᵣ)
    | RET ();
      True
    >>>.
  Proof.
    iIntros "% %Φ Hinv HΦ".
    awp_apply (inf_array_set_spec with "Hinv"); first done.
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vsₗ %vsᵣ Hmodel".
    iAaccIntro with "Hmodel"; first iSteps. iIntros "Hmodel !>".
    iSplitL "Hmodel"; last iSteps.
    Z_to_nat i. rewrite Nat2Z.id. case_decide.
    all: iApply (inf_array_model_proper with "Hmodel"); intros j.
    - simpl_length. case_decide.
      + destruct (decide (j = i)) as [-> |].
        * rewrite list_lookup_total_insert // fn_lookup_insert //.
        * rewrite list_lookup_total_insert_ne // fn_lookup_insert_ne // decide_True //.
      + rewrite fn_lookup_insert_ne; first lia.
        rewrite decide_False //.
    - case_decide.
      + rewrite fn_lookup_insert_ne; first lia.
        rewrite decide_True //.
      + destruct (decide (j = i)) as [-> |].
        * rewrite !fn_lookup_insert //.
        * rewrite !fn_lookup_insert_ne; try lia.
          rewrite decide_False //.
  Qed.

  Lemma inf_array_cas_spec t i v1 v2 :
    (0 ≤ i)%Z →
    <<<
      inf_array_inv t
    | ∀∀ vs,
      inf_array_model t vs
    >>>
      inf_array_cas t #i v1 v2
    <<<
      ∃∃ b,
      ⌜(if b then (≈) else (≉)) (vs ₊i) v1⌝ ∗
      inf_array_model t (if b then <[₊i := v2]> vs else vs)
    | RET #b;
      True
    >>>.
  Proof.
    iIntros "% %Φ (:inv) HΦ".

    wp_rec. wp_load.
    wp_apply (mutex_protect_spec Φ with "[$Hmtx_inv HΦ]"); last iSteps. iIntros "$ (:inv_1 =1 lazy=)".
    wp_smart_apply (inf_array_reserve_spec with "[$]") as "%us2 ((:inv_2) & %)"; first lia.
    wp_load.

    destruct (lookup_lt_is_Some_2 us2 ₊i) as (v & Hlookup); first lia.
    assert (vs ₊i = v) as Hv.
    { rewrite Hvs decide_True; first lia.
      apply list_lookup_total_correct. done.
    }

    wp_apply (array_unsafe_get_spec with "Hdata") as "Hdata"; [lia | done.. |].
    wp_apply wp_equal_nobranch as (b) "%".
    wp_pures.

    wp_bind (if: _ then _ else _)%E.
    wp_apply (wp_wand (λ res,
      l.[data] ↦ data ∗
      array_model data (DfracOwn 1) (if b then <[₊i := v2]> us2 else us2)
    )%I with "[Hl_data Hdata]") as (res) "(Hl_data & Hdata)".
    { destruct b; last iSteps.
      wp_load.
      wp_apply (array_unsafe_set_spec with "Hdata") as "Hdata"; first lia.
      iSteps.
    }

    wp_pures.

    iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
    set vs' := if b then <[₊i := v2]> vs else vs.
    iMod (model_update vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iMod ("HΦ" $! b with "[Hmodel₁] [//]") as "$".
    { rewrite Hv. iSteps. }

    iFrame. iPureIntro.
    destruct b; last done.
    rewrite /vs' length_insert Hvs.
    apply functional_extensionality => j.
    destruct (decide (j = ₊i)) as [-> |].
    - rewrite fn_lookup_insert decide_True; first lia.
      rewrite list_lookup_total_insert //. lia.
    - rewrite fn_lookup_insert_ne //. case_decide; last done.
      rewrite list_lookup_total_insert_ne //.
  Qed.

  Lemma inf_array_cas_resolve_spec t i v1 v2 pid v_resolve Φ :
    (0 ≤ i)%Z →
    inf_array_inv t -∗
    ( |={⊤,∅}=>
      ∃ vs,
      inf_array_model t vs ∗
      ( ∀ e b,
        ⌜PureExec True 1 e ()⌝ -∗
        ⌜to_val e = None⌝ -∗
        ⌜(if b then (≈) else (≉)) (vs ₊i) v1⌝ -∗
        inf_array_model t (if b then <[₊i := v2]> vs else vs) -∗
        WP Resolve e #pid v_resolve @ ∅ {{ _,
          |={∅,⊤}=>
          Φ #b
        }}
      )
    ) -∗
    WP inf_array_cas_resolve t #i v1 v2 #pid v_resolve {{ Φ }}.
  Proof.
    iIntros "% (:inv) HΦ".

    wp_rec. wp_load.
    wp_apply (mutex_protect_spec Φ with "[$Hmtx_inv HΦ]"); last iSteps. iIntros "$ (:inv_1 =1 lazy=)".
    wp_smart_apply (inf_array_reserve_spec with "[$]") as "%us2 ((:inv_2) & %)"; first lia.
    wp_load.

    destruct (lookup_lt_is_Some_2 us2 ₊i) as (v & Hlookup); first lia.
    assert (vs ₊i = v) as Hv.
    { rewrite Hvs decide_True; first lia.
      apply list_lookup_total_correct. done.
    }

    wp_apply (array_unsafe_get_spec with "Hdata") as "Hdata"; [lia | done.. |].
    wp_apply wp_equal_nobranch as (b) "%".
    wp_pures.

    wp_bind (if: _ then _ else _)%E.
    wp_apply (wp_wand (λ res,
      l.[data] ↦ data ∗
      array_model data (DfracOwn 1) (if b then <[₊i := v2]> us2 else us2)
    )%I with "[Hl_data Hdata]") as (res) "(Hl_data & Hdata)".
    { destruct b; last iSteps.
      wp_load.
      wp_apply (array_unsafe_set_spec with "Hdata") as "Hdata"; first lia.
      iSteps.
    }

    wp_pures.

    set vs' := if b then <[₊i := v2]> vs else vs.
    wp_bind (Resolve _ _ _).
    wp_apply (wp_wand (λ _,
      model₂ γ vs' ∗
      Φ #b
    )%I with "[Hmodel₂ HΦ]") as (?) "(Hmodel₂ & HΦ)".
    { iMod "HΦ" as "(%vs_ & (:model) & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod (model_update vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & $)".
      wp_apply (wp_wand with "(HΦ [%] [%] [%] [Hmodel₁])") as (?) "$".
      { done. }
      { rewrite Hv //. }
      { iSteps. }
    }

    wp_pures.
    iFrame. iPureIntro.
    destruct b; last done.
    rewrite /vs' length_insert Hvs.
    apply functional_extensionality => j.
    destruct (decide (j = ₊i)) as [-> |].
    - rewrite fn_lookup_insert decide_True; first lia.
      rewrite list_lookup_total_insert //. lia.
    - rewrite fn_lookup_insert_ne //. case_decide; last done.
      rewrite list_lookup_total_insert_ne //.
  Qed.

  Lemma inf_array_faa_spec t i (incr : Z) :
    (0 ≤ i)%Z →
    <<<
      inf_array_inv t
    | ∀∀ vs (n : Z),
      ⌜vs ₊i = #n⌝ ∗
      inf_array_model t vs
    >>>
      inf_array_faa t #i #incr
    <<<
      inf_array_model t (<[₊i := #(n + incr)]> vs)
    | RET vs ₊i;
      True
    >>>.
  Proof.
    iIntros "% %Φ Hinv HΦ".

    wp_rec.
    awp_smart_apply (inf_array_update_spec (λ v, ∃ n : Z, ⌜v = #n⌝)%I (λ v w, ∃ n : Z, ⌜v = #n ∧ w = #(n + incr)⌝)%I with "[$Hinv]"); [done | iSteps |].
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs %n (%Hn & Hmodel)".
    rewrite /atomic_acc /=. iFrame. iSteps as (l γ n_ Hn_) / --silent.
    rewrite Hn_ in Hn. injection Hn as ->. iSteps.
  Qed.
End inf_array_G.

#[global] Opaque inf_array_create.
#[global] Opaque inf_array_get.
#[global] Opaque inf_array_update.
#[global] Opaque inf_array_set.
#[global] Opaque inf_array_xchg.
#[global] Opaque inf_array_cas.
#[global] Opaque inf_array_cas_resolve.
#[global] Opaque inf_array_faa.

#[global] Opaque inf_array_inv.
#[global] Opaque inf_array_model.
#[global] Opaque inf_array_model'.
