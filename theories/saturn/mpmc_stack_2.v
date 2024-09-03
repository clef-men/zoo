From zoo Require Import
  prelude.
From zoo.iris.base_logic Require Import
  lib.twins.
From zoo.language Require Import
  notations
  diaframe.
From zoo.std Require Import
  option
  optional
  clst.
From zoo.saturn Require Export
  base.
From zoo Require Import
  options.

Implicit Types l : location.
Implicit Types v t : val.
Implicit Types ws : list val.
Implicit Types vs : option (list val).

Definition mpmc_stack_create : val :=
  fun: <> =>
    ref §ClstOpen.

Definition mpmc_stack_push : val :=
  rec: "mpmc_stack_push" "t" "v" =>
    match: !"t" with
    | ClstClosed =>
        #true
    |_ as "old" =>
        let: "new" := ‘ClstCons( "v", "old" ) in
        if: CAS "t".[contents] "old" "new" then (
          #false
        ) else (
          Yield ;;
          "mpmc_stack_push" "t" "v"
        )
    end.

Definition mpmc_stack_pop : val :=
  rec: "mpmc_stack_pop" "t" =>
    match: !"t" with
    | ClstClosed =>
        §Anything
    | ClstOpen =>
        §Nothing
    | ClstCons "v" "new" as "old" =>
        if: CAS "t".[contents] "old" "new" then (
          ‘Something( "v" )
        ) else (
          Yield ;;
          "mpmc_stack_pop" "t"
        )
    end.

Definition mpmc_stack_is_closed : val :=
  fun: "t" =>
    !"t" = §ClstClosed.

Definition mpmc_stack_close : val :=
  fun: "t" =>
    Xchg "t".[contents] §ClstClosed.

Class MpmcStackG Σ `{zoo_G : !ZooG Σ} := {
  #[local] mpmc_stack_G_model_G :: TwinsG Σ (leibnizO (option $ list val)) ;
}.

Definition mpmc_stack_Σ := #[
  twins_Σ (leibnizO (option $ list val))
].
#[global] Instance subG_mpmc_stack_Σ Σ `{zoo_G : !ZooG Σ} :
  subG mpmc_stack_Σ Σ →
  MpmcStackG Σ.
Proof.
  solve_inG.
Qed.

Section zoo_G.
  Context `{mpmc_stack_G : MpmcStackG Σ}.

  #[local] Definition mpmc_stack_model₁ γ vs :=
    twins_twin1 γ (if vs is None then DfracDiscarded else DfracOwn 1) vs.
  #[local] Definition mpmc_stack_model₂ γ vs :=
    twins_twin2 γ vs.

  #[local] Definition mpmc_stack_inv_inner l γ : iProp Σ :=
    ∃ vs,
    l ↦ᵣ from_option (clist_to_val ∘ list_to_clist_open) §ClstClosed vs ∗
    mpmc_stack_model₂ γ vs.
  Definition mpmc_stack_inv t ι : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    inv ι (mpmc_stack_inv_inner l γ).

  Definition mpmc_stack_model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    mpmc_stack_model₁ γ vs.

  Definition mpmc_stack_closed t :=
    mpmc_stack_model t None.

  #[global] Instance mpmc_stack_model_timeless t vs :
    Timeless (mpmc_stack_model t vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpmc_stack_inv_persistent t ι :
    Persistent (mpmc_stack_inv t ι).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpmc_stack_model_persistent t vs :
    Persistent (mpmc_stack_model t None).
  Proof.
    apply _.
  Qed.

  #[local] Lemma mpmc_stack_model_alloc :
    ⊢ |==>
      ∃ γ,
      mpmc_stack_model₁ γ (Some []) ∗
      mpmc_stack_model₂ γ (Some []).
  Proof.
    apply twins_alloc'.
  Qed.
  #[local] Lemma mpmc_stack_model_agree γ vs1 vs2 :
    mpmc_stack_model₁ γ vs1 -∗
    mpmc_stack_model₂ γ vs2 -∗
    ⌜vs1 = vs2⌝.
  Proof.
    apply: twins_agree_L.
  Qed.
  #[local] Lemma mpmc_stack_model_update {γ ws1 ws2} ws :
    mpmc_stack_model₁ γ (Some ws1) -∗
    mpmc_stack_model₂ γ (Some ws2) ==∗
      mpmc_stack_model₁ γ (Some ws) ∗
      mpmc_stack_model₂ γ (Some ws).
  Proof.
    apply twins_update'.
  Qed.
  #[local] Lemma mpmc_stack_model_close γ ws1 ws2 :
    mpmc_stack_model₁ γ (Some ws1) -∗
    mpmc_stack_model₂ γ (Some ws2) ==∗
      mpmc_stack_model₁ γ None ∗
      mpmc_stack_model₂ γ None.
  Proof.
    iIntros "Hmodel₁ Hmodel₂".
    iMod (twins_update' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iMod (twins_twin1_persist with "Hmodel₁") as "Hmodel₁".
    iSteps.
  Qed.

  Lemma mpmc_stack_create_spec ι :
    {{{
      True
    }}}
      mpmc_stack_create ()
    {{{ t,
      RET t;
      mpmc_stack_inv t ι ∗
      mpmc_stack_model t (Some [])
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_rec.
    wp_ref l as "Hmeta" "Hl".

    iMod mpmc_stack_model_alloc as "(%γ & Hmodel₁ & Hmodel₂)".

    iMod (meta_set with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ". iSplitR "Hmodel₁"; last iSteps.
    iStep 2. iApply inv_alloc. iExists (Some []). iSteps.
  Qed.

  Lemma mpmc_stack_push_spec t ι v :
    <<<
      mpmc_stack_inv t ι
    | ∀∀ vs,
      mpmc_stack_model t vs
    >>>
      mpmc_stack_push t v @ ↑ι
    <<<
      mpmc_stack_model t (cons v <$> vs)
      | RET #(bool_decide (vs = None)); £ 1
    >>>.
  Proof.
    iIntros "!> %Φ (%l & %γ & -> & #Hmeta & #Hinv) HΦ".

    iLöb as "HLöb".

    wp_rec credit:"H£". wp_pures.

    wp_bind (!_)%E.
    iInv "Hinv" as "(%vs & Hl & Hmodel₂)".
    wp_load.
    destruct vs as [ws |].

    - iSplitR "H£ HΦ". { iExists (Some _). iSteps. }
      iModIntro.

      wp_smart_apply wp_match_clist_open.
      wp_pures.

      wp_bind (CAS _ _ _).
      iInv "Hinv" as "(%vs' & Hl & Hmodel₂)".
      destruct vs' as [ws' |].

      + simpl.
        wp_cas as _ | ->%(inj _)%(inj _).

        * iSplitR "HΦ". { iExists (Some _). iSteps. }
          iSteps.

        * iMod "HΦ" as "(%vs & (%_l & %_γ & %Heq & _Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
          iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
          iDestruct (mpmc_stack_model_agree with "Hmodel₁ Hmodel₂") as %->.
          pose ws' := v :: ws.
          iMod (mpmc_stack_model_update ws' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
          iMod ("HΦ" with "[Hmodel₁] H£") as "HΦ"; first iSteps.
          iSplitR "HΦ". { iExists (Some ws'). iSteps. }
          iSteps.

      + wp_cas as _ | []%(inj clist_to_val ClistClosed)%list_to_clist_open_not_closed'.
        iSplitR "HΦ". { iExists None. iSteps. }
        iSteps.

    - iMod "HΦ" as "(%vs & (%_l & %_γ & %Heq & _Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (mpmc_stack_model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod ("HΦ" with "[Hmodel₁] H£") as "HΦ"; first iSteps.
      iSplitR "HΦ". { iExists None. iSteps. }
      iSteps.
  Qed.
  Lemma mpmc_stack_push_spec_closed t ι v :
    {{{
      mpmc_stack_inv t ι ∗
      mpmc_stack_closed t
    }}}
      mpmc_stack_push t v
    {{{
      RET #true;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hclosed) HΦ".

    iApply wp_fupd.
    awp_apply (mpmc_stack_push_spec with "Hinv").
    iAaccIntro with "Hclosed"; first iSteps. iIntros "_ !> H£".
    iDestruct (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
    iSteps.
  Qed.

  Lemma mpmc_stack_pop_spec t ι :
    <<<
      mpmc_stack_inv t ι
    | ∀∀ vs,
      mpmc_stack_model t vs
    >>>
      mpmc_stack_pop t @ ↑ι
    <<<
      mpmc_stack_model t (tail <$> vs)
    | RET default Anything (option_to_optional ∘ head <$> vs); £ 1
    >>>.
  Proof.
    iIntros "!> %Φ (%l & %γ & -> & #Hmeta & #Hinv) HΦ".

    iLöb as "HLöb".

    wp_rec credit:"H£".

    wp_bind (!_)%E.
    iInv "Hinv" as "(%vs & Hl & Hmodel₂)".
    wp_load.
    destruct vs as [[| v ws] |].

    - iMod "HΦ" as "(%_vs & (%_l & %_γ & %Heq & _Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (mpmc_stack_model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
      iSplitR "H£ HΦ". { iExists (Some []). iSteps. }
      iSteps.

    - iSplitR "H£ HΦ". { iExists (Some (v :: ws)). iSteps. }
      iModIntro.

      wp_pures.

      wp_bind (CAS _ _ _).
      iInv "Hinv" as "(%vs' & Hl & Hmodel₂)".
      destruct vs' as [ws' |].

      + wp_cas as _ | ->%(inj clist_to_val _ (ClistCons _ _))%(inj list_to_clist_open _ (_ :: _)).

        * iSplitR "HΦ". { iExists (Some ws'). iSteps. }
          iSteps.

        * iMod "HΦ" as "(%_vs & (%_l & %_γ & %Heq & _Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
          iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
          iDestruct (mpmc_stack_model_agree with "Hmodel₁ Hmodel₂") as %->.
          iMod (mpmc_stack_model_update ws with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
          iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
          iSplitR "H£ HΦ". { iExists (Some ws). iSteps. }
          iSteps.

      + wp_cas as _ | [=].
        iSplitR "HΦ". { iExists None. iSteps. }
        iSteps.

    - iMod "HΦ" as "(%_vs & (%_l & %_γ & %Heq & _Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (mpmc_stack_model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
      iSplitR "H£ HΦ". { iExists None. iSteps. }
      iSteps.
  Qed.
  Lemma mpmc_stack_pop_spec_closed t ι v :
    {{{
      mpmc_stack_inv t ι ∗
      mpmc_stack_closed t
    }}}
      mpmc_stack_pop t
    {{{
      RET §Anything;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hclosed) HΦ".

    iApply wp_fupd.
    awp_apply (mpmc_stack_pop_spec with "Hinv").
    iAaccIntro with "Hclosed"; first iSteps. iIntros "_ !> H£".
    iDestruct (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
    iSteps.
  Qed.

  Lemma mpmc_stack_is_closed_spec t ι :
    <<<
      mpmc_stack_inv t ι
    | ∀∀ vs,
      mpmc_stack_model t vs
    >>>
      mpmc_stack_is_closed t @ ↑ι
    <<<
      mpmc_stack_model t vs
    | RET #(bool_decide (vs = None)); £ 1
    >>>.
  Proof.
    iIntros "!> %Φ (%l & %γ & -> & #Hmeta & #Hinv) HΦ".

    wp_rec credit:"H£".

    wp_bind (!_)%E.
    iInv "Hinv" as "(%vs' & Hl & Hmodel₂)".
    wp_load.
    iMod "HΦ" as "(%vs & (%_l & %_γ & %Heq & _Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iDestruct (mpmc_stack_model_agree with "Hmodel₁ Hmodel₂") as %<-.
    destruct vs as [ws |].

    - iMod ("HΦ" with "[Hmodel₁] H£") as "HΦ"; first iSteps.
      iSplitR "HΦ". { iExists (Some _). iSteps. }
      iModIntro.

      wp_equal as _ | []%(inj clist_to_val _ ClistClosed)%list_to_clist_open_not_closed.
      iSteps.

    - iMod ("HΦ" with "[Hmodel₁] H£") as "HΦ"; first iSteps.
      iSplitR "HΦ". { iExists None. iSteps. }
      iSteps.
  Qed.
  Lemma mpmc_stack_is_closed_spec_closed t ι :
    {{{
      mpmc_stack_inv t ι ∗
      mpmc_stack_closed t
    }}}
      mpmc_stack_is_closed t
    {{{
      RET #true;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hclosed) HΦ".

    iApply wp_fupd.
    awp_apply (mpmc_stack_is_closed_spec with "Hinv").
    iAaccIntro with "Hclosed"; first iSteps. iIntros "_ !> H£".
    iDestruct (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
    iSteps.
  Qed.

  Lemma mpmc_stack_close_spec t ι :
    <<<
      mpmc_stack_inv t ι
    | ∀∀ vs,
      mpmc_stack_model t vs
    >>>
      mpmc_stack_close t @ ↑ι
    <<<
      mpmc_stack_model t None
    | RET from_option list_to_clist_open ClistClosed vs; £ 1
    >>>.
  Proof.
    iIntros "!> %Φ (%l & %γ & -> & #Hmeta & #Hinv) HΦ".

    wp_rec credit:"H£". wp_pures.

    iInv "Hinv" as "(%vs' & Hl & Hmodel₂)".
    wp_xchg.
    iMod "HΦ" as "(%vs & (%_l & %_γ & %Heq & _Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iDestruct (mpmc_stack_model_agree with "Hmodel₁ Hmodel₂") as %<-.
    destruct vs as [ws |].

    - iMod (mpmc_stack_model_close with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "[Hmodel₁] H£") as "HΦ"; first iSteps.
      iSplitR "HΦ". { iExists None. iSteps. }
      iSteps.

    - iMod ("HΦ" with "[Hmodel₁] H£") as "HΦ"; first iSteps.
      iSplitR "HΦ". { iExists None. iSteps. }
      iSteps.
  Qed.
  Lemma mpmc_stack_closed_spec_closed t ι v :
    {{{
      mpmc_stack_inv t ι ∗
      mpmc_stack_closed t
    }}}
      mpmc_stack_close t
    {{{
      RET §ClstClosed;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hclosed) HΦ".

    iApply wp_fupd.
    awp_apply (mpmc_stack_close_spec with "Hinv").
    iAaccIntro with "Hclosed"; first iSteps. iIntros "_ !> H£".
    iDestruct (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
    iSteps.
  Qed.
End zoo_G.

#[global] Opaque mpmc_stack_create.
#[global] Opaque mpmc_stack_push.
#[global] Opaque mpmc_stack_pop.

#[global] Opaque mpmc_stack_inv.
#[global] Opaque mpmc_stack_model.
