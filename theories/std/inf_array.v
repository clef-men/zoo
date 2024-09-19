From Coq.Logic Require Import
  FunctionalExtensionality.

From zoo Require Import
  prelude.
From zoo.iris.base_logic Require Import
  lib.twins.
From zoo.language Require Import
  notations
  diaframe.
From zoo.std Require Export
  base
  inf_array__code.
From zoo.std Require Import
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
    pose encode γ := (
      γ.(inf_array_meta_default),
      γ.(inf_array_meta_model)
    ).
    pose decode := λ '(default, γ_model), {|
      inf_array_meta_default := default ;
      inf_array_meta_model := γ_model ;
    |}.
    refine (inj_countable' encode decode _). intros []. done.
  Qed.

  #[local] Definition inf_array_model₁' γ_model vs :=
    twins_twin1 γ_model (DfracOwn 1) vs.
  #[local] Definition inf_array_model₁ γ vs :=
    inf_array_model₁' γ.(inf_array_meta_model) vs.
  #[local] Definition inf_array_model₂' γ_model vs :=
    twins_twin2 γ_model vs.
  #[local] Definition inf_array_model₂ γ vs :=
    inf_array_model₂' γ.(inf_array_meta_model) vs.

  #[local] Definition inf_array_inv_inner l γ : iProp Σ :=
    ∃ data us vs,
    l.[data] ↦ data ∗
    array_model data (DfracOwn 1) us ∗
    inf_array_model₂ γ vs ∗
    ⌜vs = λ i, if decide (i < length us) then us !!! i else γ.(inf_array_meta_default)⌝.
  Definition inf_array_inv t : iProp Σ :=
    ∃ l γ mtx,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    l.[default] ↦□ γ.(inf_array_meta_default) ∗
    l.[mutex] ↦□ mtx ∗
    mutex_inv mtx (inf_array_inv_inner l γ).

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
    intros j. rewrite app_length /=.
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

    wp_apply (array_create_spec with "[//]") as "%data Hmodel_data".
    wp_smart_apply (mutex_create_spec_init with "[//]") as (mtx) "Hmtx_init".

    wp_block l as "Hmeta" "(Hdata & Hdefault & Hmtx & _)".
    iMod (pointsto_persist with "Hdefault") as "#Hdefault".

    iMod (inf_array_model_alloc default) as "(%γ_model & Hmodel₁ & Hmodel₂)".

    pose γ := {|
      inf_array_meta_default := default ;
      inf_array_meta_model := γ_model ;
    |}.
    iMod (meta_set _ _ γ with "Hmeta") as "#Hmeta"; first done.

    iMod (mutex_init_to_inv (inf_array_inv_inner l γ) with "Hmtx_init [Hdata Hmodel_data Hmodel₂]") as "#Hmtx_inv"; first iSteps.
    iSteps.
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
    | RET vs (Z.to_nat i);
      True
    >>>.
  Proof.
    iIntros "% !> %Φ (%l & %γ & %mtx & -> & #Hmeta & #Hmtx & #Hdefault & #Hinv_mtx) HΦ".
    Z_to_nat i. rewrite Nat2Z.id.

    wp_rec. wp_load.

    wp_apply (mutex_protect_spec Φ with "[$Hinv_mtx HΦ]"); last iSteps. iIntros "Hlocked_mtx (%data & %us & %vs & Hdata & Hmodel_data & Hmodel₂ & %Hvs)".

    wp_load.

    wp_smart_apply (array_size_spec with "Hmodel_data") as "Hmodel_data".

    wp_pures. case_decide.

    - rewrite bool_decide_eq_true_2; first lia.

      iApply wp_fupd.
      wp_smart_apply (array_unsafe_get_spec with "Hmodel_data"); [done | | done |].
      { rewrite Nat2Z.id list_lookup_lookup_total_lt //. lia. }

      iMod "HΦ" as "(%_vs & (%_l & %_γ & %Heq & #_Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (inf_array_model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.

      iSteps. rewrite decide_True; first lia. iSteps.

    - rewrite bool_decide_eq_false_2; first lia. wp_load.

      iMod "HΦ" as "(%_vs & (%_l & %_γ & %Heq & #_Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (inf_array_model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.

      iSteps. rewrite decide_False; first lia. iSteps.
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
        let i := Z.to_nat i in
        if decide (i < length vsₗ) then vsₗ !!! i else vsᵣ (i - length vsₗ);
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
      inf_array_model t (<[Z.to_nat i := v]> vs)
    | RET ();
      True
    >>>.
  Proof.
    iIntros "% !> %Φ (%l & %γ & %mtx & -> & #Hmeta & #Hmtx & #Hdefault & #Hinv_mtx) HΦ".
    Z_to_nat i. rewrite Nat2Z.id.

    wp_rec. wp_load.

    wp_apply (mutex_protect_spec Φ with "[$Hinv_mtx HΦ]"); last iSteps. iIntros "Hlocked_mtx (%data & %us & %vs & Hdata & Hmodel_data & Hmodel₂ & %Hvs)".

    wp_load.

    wp_smart_apply (array_size_spec with "Hmodel_data") as "Hmodel_data".

    wp_pures. case_decide.

    - rewrite bool_decide_eq_true_2; first lia.

      iApply wp_fupd.
      wp_smart_apply (array_unsafe_set_spec with "Hmodel_data"); first done.

      iMod "HΦ" as "(%_vs & (%_l & %_γ & %Heq & #_Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (inf_array_model_agree with "Hmodel₁ Hmodel₂") as %->.
      set us' := <[i := v]> us.
      set vs' := <[i := v]> vs.
      iMod (inf_array_model_update vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.

      iIntros "Hmodel_data !>". iFrame. iSplitR "HΦ"; last iSteps.
      iExists data, us', vs'. rewrite Nat2Z.id. iFrame. iPureIntro.
      rewrite /us' /vs' insert_length Hvs.
      apply functional_extensionality => j. destruct (decide (j = i)) as [-> |].
      + rewrite fn_lookup_insert decide_True; first lia.
        rewrite list_lookup_total_insert //. lia.
      + rewrite fn_lookup_insert_ne //. case_decide; last done.
        rewrite list_lookup_total_insert_ne //.

    - rewrite bool_decide_eq_false_2; first lia. wp_load.

      wp_smart_apply (array_unsafe_grow_spec with "Hmodel_data") as "%data' Hmodel_data'"; first lia.
      rewrite Z.add_1_r -Nat2Z.inj_succ Nat2Z.id.

      wp_store.

      iApply wp_fupd.
      wp_smart_apply (array_unsafe_set_spec with "Hmodel_data'").
      { rewrite app_length replicate_length. lia. }
      rewrite Nat2Z.id insert_app_r_alt; first lia.
      rewrite insert_replicate_lt; first lia.
      rewrite -Nat.sub_succ_l; first lia.
      rewrite Nat.sub_diag /=.
      iIntros "Hmodel_data'".

      iMod "HΦ" as "(%_vs & (%_l & %_γ & %Heq & #_Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (inf_array_model_agree with "Hmodel₁ Hmodel₂") as %->.
      set us' := us ++ replicate (i - length us) γ.(inf_array_meta_default) ++ [v].
      set vs' := <[i := v]> vs.
      iMod (inf_array_model_update vs' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.

      iModIntro. iFrame. iSplitR "HΦ"; last iSteps.
      iExists data', us', vs'. iFrame. iPureIntro.
      rewrite /us' /vs' !app_length replicate_length Hvs /=.
      apply functional_extensionality => j. destruct (Nat.lt_total j i) as [| [-> |]].
      + rewrite fn_lookup_insert_ne; first lia.
        rewrite (@decide_True _ (j < _ + _)); first lia.
        case_decide.
        * rewrite lookup_total_app_l //.
        * rewrite lookup_total_app_r; first lia.
          rewrite lookup_total_app_l; first (rewrite replicate_length //; lia).
          rewrite lookup_total_replicate_2 //. lia.
      + rewrite fn_lookup_insert decide_True; first lia.
        rewrite lookup_total_app_r; first lia.
        rewrite lookup_total_app_r; first (rewrite replicate_length; lia).
        rewrite replicate_length Nat.sub_diag //.
      + rewrite fn_lookup_insert_ne; first lia.
        rewrite !decide_False //; lia.
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
      let i := Z.to_nat i in
      if decide (i < length vsₗ)
      then inf_array_model' t (<[i := v]> vsₗ) vsᵣ
      else inf_array_model' t vsₗ (<[i - length vsₗ := v]> vsᵣ)
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
    - rewrite insert_length. case_decide.
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
