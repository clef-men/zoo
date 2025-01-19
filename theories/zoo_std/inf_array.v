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

Implicit Types l : location.
Implicit Types v t : val.
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

  Record inf_array_meta := {
    inf_array_meta_default : val ;
    inf_array_meta_model : gname ;
  }.
  Implicit Types γ : inf_array_meta.

  #[local] Instance inf_array_meta_eq_dec : EqDecision inf_array_meta :=
    ltac:(solve_decision).
  #[local] Instance inf_array_meta_countable :
    Countable inf_array_meta.
  Proof.
    solve_countable.
  Qed.

  #[local] Definition inf_array_model₁' γ_model vs :=
    twins_twin1 γ_model (DfracOwn 1) vs.
  #[local] Definition inf_array_model₁ γ vs :=
    inf_array_model₁' γ.(inf_array_meta_model) vs.
  #[local] Definition inf_array_model₂' γ_model vs :=
    twins_twin2 γ_model vs.
  #[local] Definition inf_array_model₂ γ vs :=
    inf_array_model₂' γ.(inf_array_meta_model) vs.

  #[local] Definition inf_array_inv'' l γ us : iProp Σ :=
    ∃ data vs,
    l.[data] ↦ data ∗
    array_model data (DfracOwn 1) us ∗
    inf_array_model₂ γ vs ∗
    ⌜vs = λ i, if decide (i < length us) then us !!! i else γ.(inf_array_meta_default)⌝.
  #[local] Definition inf_array_inv' l γ : iProp Σ :=
    ∃ us,
    inf_array_inv'' l γ us.
  Definition inf_array_inv t : iProp Σ :=
    ∃ l γ mtx,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    l.[default] ↦□ γ.(inf_array_meta_default) ∗
    l.[mutex] ↦□ mtx ∗
    mutex_inv mtx (inf_array_inv' l γ).

  Definition inf_array_model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    inf_array_model₁ γ vs.
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

  #[local] Lemma inf_array_model_alloc default :
    ⊢ |==>
      ∃ γ_model,
      inf_array_model₁' γ_model (λ _, default) ∗
      inf_array_model₂' γ_model (λ _, default).
  Proof.
    apply twins_alloc'.
  Qed.
  #[local] Lemma inf_array_model_agree γ vs1 vs2 :
    inf_array_model₁ γ vs1 -∗
    inf_array_model₂ γ vs2 -∗
    ⌜vs1 = vs2⌝.
  Proof.
    iIntros "Hmodel₁ Hmodel₂".
    iDestruct (twins_agree_discrete with "Hmodel₁ Hmodel₂") as %->%functional_extensionality.
    iSteps.
  Qed.
  #[local] Lemma inf_array_model_update {γ vs1 vs2} vs :
    inf_array_model₁ γ vs1 -∗
    inf_array_model₂ γ vs2 ==∗
      inf_array_model₁ γ vs ∗
      inf_array_model₂ γ vs.
  Proof.
    apply twins_update'.
  Qed.

  Lemma inf_array_model'_shift t vsₗ v vsᵣ :
    inf_array_model' t (vsₗ ++ [v]) vsᵣ ⊣⊢
    inf_array_model' t vsₗ (λ i, match i with 0 => v | S i => vsᵣ i end).
  Proof.
    rewrite /inf_array_model' inf_array_model_proper; last done.
    intros j. rewrite length_app /=.
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
    intros. rewrite inf_array_model'_shift inf_array_model'_proper; last done; done.
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

    iMod (inf_array_model_alloc default) as "(%γ_model & Hmodel₁ & Hmodel₂)".

    pose γ := {|
      inf_array_meta_default := default ;
      inf_array_meta_model := γ_model ;
    |}.
    iMod (meta_set _ _ γ with "Hmeta") as "#Hmeta"; first done.

    iMod (mutex_init_to_inv (inf_array_inv' l γ) with "Hmtx_init [Hl_data Hdata Hmodel₂]") as "#Hmtx_inv".
    { rewrite /inf_array_inv'. iSteps. }
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
    iSteps; iModIntro; wp_apply int_max_spec; iSteps.
  Qed.
  #[local] Lemma inf_array_reserve_spec l γ us n :
    (0 ≤ n)%Z →
    {{{
      l.[default] ↦□ γ.(inf_array_meta_default) ∗
      inf_array_inv'' l γ us
    }}}
      inf_array_reserve #l #n
    {{{ us,
      RET ();
      inf_array_inv'' l γ us ∗
      ⌜₊n ≤ length us⌝
    }}}.
  Proof.
    iIntros "%Hn %Φ (#Hl_default & (%data & %vs & Hl_data & Hdata & Hmodel₂ & %Hvs)) HΦ".

    wp_rec. wp_load.
    wp_smart_apply (array_size_spec with "Hdata") as "Hdata".
    wp_pures. case_bool_decide; last iSteps.
    wp_smart_apply (inf_array_next_capacity_spec with "[//]") as (?) "%"; first lia.
    wp_apply int_max_spec.
    wp_load.
    wp_smart_apply (array_unsafe_grow_spec with "Hdata") as (data') "(Hdata & Hdata')"; first lia.
    wp_store.

    iSteps; iPureIntro; rewrite length_app length_replicate; last lia.
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
    iIntros "% !> %Φ (%l & %γ & %mtx & -> & #Hmeta & #Hl_mtx & #Hl_default & #Hmtx_inv) HΦ".
    Z_to_nat i. rewrite Nat2Z.id.

    wp_rec. wp_load.
    wp_apply (mutex_protect_spec Φ with "[$Hmtx_inv HΦ]"); last iSteps. iIntros "Hmtx_locked (%us & %data & %vs & Hl_data & Hdata & Hmodel₂ & %Hvs)".
    wp_load.
    wp_smart_apply (array_size_spec with "Hdata") as "Hdata".
    wp_pures. case_decide.

    - rewrite bool_decide_eq_true_2; first lia.
      iApply wp_fupd.
      wp_smart_apply (array_unsafe_get_spec with "Hdata"); [done | | done |].
      { rewrite Nat2Z.id list_lookup_lookup_total_lt //. lia. }

      iMod "HΦ" as "(%_vs & (%_l & %_γ & %Heq & #_Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (inf_array_model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.

      rewrite /inf_array_inv'. iSteps.
      rewrite Hvs decide_True; first lia. iSteps.

    - rewrite bool_decide_eq_false_2; first lia. wp_load.

      iMod "HΦ" as "(%_vs & (%_l & %_γ & %Heq & #_Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (inf_array_model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.

      rewrite /inf_array_inv'. iSteps.
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
    iIntros "% !> %Φ Hinv HΦ".
    awp_apply (inf_array_get_spec with "Hinv"); first done.
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vsₗ %vsᵣ Hmodel".
    iAaccIntro with "Hmodel"; iSteps.
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
    iIntros "% !> %Φ (%l & %γ & %mtx & -> & #Hmeta & #Hl_mtx & #Hl_default & #Hmtx_inv) HΦ".
    Z_to_nat i. rewrite Nat2Z.id.

    wp_rec. wp_load.
    wp_apply (mutex_protect_spec Φ with "[$Hmtx_inv HΦ]"); last iSteps. iIntros "Hmtx_locked (%us & Hinv)".
    wp_smart_apply (inf_array_reserve_spec with "[$]") as "{%} %us ((%data & %vs & Hl_data & Hdata & Hmodel₂ & %Hvs) & %)"; first lia.
    wp_load.
    iApply wp_fupd.
    wp_smart_apply (array_unsafe_set_spec with "Hdata") as "Hdata"; first lia.

    iMod "HΦ" as "(%_vs & (%_l & %_γ & %Heq & #_Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iDestruct (inf_array_model_agree with "Hmodel₁ Hmodel₂") as %->.
    set us' := <[i := v]> us.
    set vs' := <[i := v]> vs.
    iMod (inf_array_model_update vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.

    iFrame. iSplitR "HΦ"; last iSteps. iPureIntro.
    rewrite Nat2Z.id /us' /vs' length_insert Hvs.
    apply functional_extensionality => j.
    destruct (decide (j = i)) as [-> |].
    - rewrite fn_lookup_insert decide_True; first lia.
      rewrite list_lookup_total_insert //. lia.
    - rewrite fn_lookup_insert_ne //. case_decide; last done.
      rewrite list_lookup_total_insert_ne //.
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
      if decide (₊i < length vsₗ)
      then inf_array_model' t (<[₊i := v]> vsₗ) vsᵣ
      else inf_array_model' t vsₗ (<[₊i - length vsₗ := v]> vsᵣ)
    | RET ();
      True
    >>>.
  Proof.
    iIntros "% !> %Φ Hinv HΦ".
    awp_apply (inf_array_set_spec with "Hinv"); first done.
    iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vsₗ %vsᵣ Hmodel".
    iAaccIntro with "Hmodel"; first iSteps. iIntros "Hmodel !>".
    iSplitL "Hmodel"; last iSteps.
    Z_to_nat i. rewrite Nat2Z.id. case_decide.
    all: iApply (inf_array_model_proper with "Hmodel"); intros j.
    - rewrite length_insert. case_decide.
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
End inf_array_G.

#[global] Opaque inf_array_create.
#[global] Opaque inf_array_get.
#[global] Opaque inf_array_set.

#[global] Opaque inf_array_inv.
#[global] Opaque inf_array_model.
#[global] Opaque inf_array_model'.
