From zoo Require Import
  prelude.
From zoo.common Require Import
  countable.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  optional.
From zoo_saturn Require Export
  base
  mpmc_fqueue_2__code.
From zoo_saturn Require Import
  mpmc_fqueue_2__types.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types v : val.
Implicit Types vs : list val.

Class MpmcFqueue2G Σ `{zoo_G : !ZooG Σ} := {
}.

Definition mpmc_fqueue_2_Σ := #[
].
#[global] Instance subG_mpmc_fqueue_2_Σ Σ `{zoo_G : !ZooG Σ} :
  subG mpmc_fqueue_2_Σ Σ →
  MpmcFqueue2G Σ.
Proof.
  (* solve_inG. *)
Qed.

Module base.
  Section mpmc_fqueue_2_G.
    Context `{mpmc_fqueue_2_G : MpmcFqueue2G Σ}.

    Implicit Types t : location.

    Record mpmc_fqueue_2_name := {
    }.
    Implicit Type γ : mpmc_fqueue_2_name.

    #[global] Instance mpmc_fqueue_2_name_eq_dec : EqDecision mpmc_fqueue_2_name :=
      ltac:(solve_decision).
    #[global] Instance mpmc_fqueue_2_name_countable :
      Countable mpmc_fqueue_2_name.
    Proof.
      solve_countable.
    Qed.

    Definition mpmc_fqueue_2_inv t γ (ι : namespace) : iProp Σ.
    Admitted.

    Definition mpmc_fqueue_2_model γ vs : iProp Σ.
    Admitted.

    Definition mpmc_fqueue_2_full γ : iProp Σ.
    Admitted.

    Definition mpmc_fqueue_2_nonfull γ : iProp Σ.
    Admitted.

    Definition mpmc_fqueue_2_finished γ : iProp Σ.
    Admitted.

    #[global] Instance mpmc_fqueue_2_model_timeless γ vs :
      Timeless (mpmc_fqueue_2_model γ vs).
    Proof.
    Admitted.

    #[global] Instance mpmc_fqueue_2_inv_persistent t γ ι :
      Persistent (mpmc_fqueue_2_inv t γ ι).
    Proof.
    Admitted.
    #[global] Instance mpmc_fqueue_2_full_persistent γ :
      Persistent (mpmc_fqueue_2_full γ).
    Proof.
    Admitted.
    #[global] Instance mpmc_fqueue_2_finished_persistent γ :
      Persistent (mpmc_fqueue_2_finished γ).
    Proof.
    Admitted.

    Lemma mpmc_fqueue_2_model_exclusive γ vs1 vs2 :
      mpmc_fqueue_2_model γ vs1 -∗
      mpmc_fqueue_2_model γ vs2 -∗
      False.
    Proof.
    Admitted.

    Lemma mpmc_fqueue_2_full_nonfull γ :
      mpmc_fqueue_2_full γ -∗
      mpmc_fqueue_2_nonfull γ -∗
      False.
    Proof.
    Admitted.

    Lemma mpmc_fqueue_2_model_finished t γ ι vs E :
      ↑ι ⊆ E →
      mpmc_fqueue_2_inv t γ ι -∗
      mpmc_fqueue_2_model γ vs -∗
      mpmc_fqueue_2_finished γ ={E}=∗
        ⌜vs = []⌝ ∗
        mpmc_fqueue_2_model γ vs.
    Proof.
    Admitted.

    Lemma mpmc_fqueue_2_create_spec ι cap :
      (0 ≤ cap)%Z →
      {{{
        True
      }}}
        mpmc_fqueue_2_create #cap
      {{{ t γ,
        RET #t;
        meta_token t ⊤ ∗
        mpmc_fqueue_2_inv t γ ι ∗
        mpmc_fqueue_2_model γ []
      }}}.
    Proof.
    Admitted.

    Lemma mpmc_fqueue_2_make_spec ι cap v :
      (0 ≤ cap)%Z →
      {{{
        True
      }}}
        mpmc_fqueue_2_make #cap v
      {{{ t γ,
        RET #t;
        meta_token t ⊤ ∗
        mpmc_fqueue_2_inv t γ ι ∗
        mpmc_fqueue_2_model γ [v]
      }}}.
    Proof.
    Admitted.

    Lemma mpmc_fqueue_2_is_empty_spec t γ ι :
      <<<
        mpmc_fqueue_2_inv t γ ι
      | ∀∀ vs,
        mpmc_fqueue_2_model γ vs
      >>>
        mpmc_fqueue_2_is_empty #t @ ↑ι
      <<<
        mpmc_fqueue_2_model γ vs
      | b,
        RET #b;
        ⌜if b then vs = [] else True⌝
      >>>.
    Proof.
    Admitted.

    Lemma mpmc_fqueue_2_push_spec t γ ι v E Φ :
      mpmc_fqueue_2_inv t γ ι -∗
      ▷ (
        |={⊤ ∖ ↑ι, E}=>
        ∃ vs,
        mpmc_fqueue_2_model γ vs ∗
          ∀ b,
          ( if b then
              mpmc_fqueue_2_model γ (vs ++ [v]) ∗
              mpmc_fqueue_2_nonfull γ
            else
              mpmc_fqueue_2_model γ vs ∗
              mpmc_fqueue_2_full γ
          ) ={E}=∗
            ( if b then
                mpmc_fqueue_2_nonfull γ
              else
                True
            ) ∗
              |={E, ⊤ ∖ ↑ι}=>
              Φ #b
      ) -∗
      WP mpmc_fqueue_2_push #t v {{ Φ }}.
    Proof.
    Admitted.

    Lemma mpmc_fqueue_2_pop_spec t γ ι :
      <<<
        mpmc_fqueue_2_inv t γ ι
      | ∀∀ vs,
        mpmc_fqueue_2_model γ vs
      >>>
        mpmc_fqueue_2_pop #t @ ↑ι
      <<<
        ∃∃ o vs',
        mpmc_fqueue_2_model γ vs' ∗
        ⌜ match o with
          | Something v =>
              vs = v :: vs'
          | Nothing =>
              vs' = vs
          | Anything =>
              vs = [] ∧
              vs' = vs
          end
        ⌝
      | RET o;
        if o is Anything then
          mpmc_fqueue_2_finished γ
        else
          True
      >>>.
    Proof.
    Admitted.
  End mpmc_fqueue_2_G.

  #[global] Opaque mpmc_fqueue_2_inv.
  #[global] Opaque mpmc_fqueue_2_model.
  #[global] Opaque mpmc_fqueue_2_full.
  #[global] Opaque mpmc_fqueue_2_nonfull.
  #[global] Opaque mpmc_fqueue_2_finished.
End base.

From zoo_saturn Require
  mpmc_fqueue_2__opaque.

Section mpmc_fqueue_2_G.
  Context `{mpmc_fqueue_2_G : MpmcFqueue2G Σ}.

  Implicit Types 𝑡 : location.
  Implicit Types t : val.

  Definition mpmc_fqueue_2_inv t ι : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.mpmc_fqueue_2_inv 𝑡 γ ι.
  #[local] Instance : CustomIpat "inv" :=
    " ( %𝑡{} &
        %γ{} &
        {%Heq{};->} &
        #Hmeta{_{}} &
        Hinv{_{}}
      )
    ".

  Definition mpmc_fqueue_2_model t vs : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.mpmc_fqueue_2_model γ vs.
  #[local] Instance : CustomIpat "model" :=
    " ( %𝑡{} &
        %γ{} &
        {%Heq{};->} &
        Hmeta{_{}} &
        Hmodel{_{}}
      )
    ".

  Definition mpmc_fqueue_2_full t : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.mpmc_fqueue_2_full γ.
  #[local] Instance : CustomIpat "full" :=
    " ( %𝑡{} &
        %γ{} &
        {%Heq{};->} &
        Hmeta{_{}} &
        Hfull{_{}}
      )
    ".

  Definition mpmc_fqueue_2_nonfull t : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.mpmc_fqueue_2_nonfull γ.
  #[local] Instance : CustomIpat "nonfull" :=
    " ( %𝑡{} &
        %γ{} &
        {%Heq{};->} &
        Hmeta{_{}} &
        Hnonfull{_{}}
      )
    ".

  Definition mpmc_fqueue_2_finished t : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.mpmc_fqueue_2_finished γ.
  #[local] Instance : CustomIpat "finished" :=
    " ( %𝑡{} &
        %γ{} &
        {%Heq{};->} &
        Hmeta{_{}} &
        Hfinished{_{}}
      )
    ".

  #[global] Instance mpmc_fqueue_2_model_timeless t vs :
    Timeless (mpmc_fqueue_2_model t vs).
  Proof.
    apply _.
  Qed.

  #[global] Instance mpmc_fqueue_2_inv_persistent t ι :
    Persistent (mpmc_fqueue_2_inv t ι).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpmc_fqueue_2_full_persistent t :
    Persistent (mpmc_fqueue_2_full t).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpmc_fqueue_2_finished_persistent t :
    Persistent (mpmc_fqueue_2_finished t).
  Proof.
    apply _.
  Qed.

  Lemma mpmc_fqueue_2_model_exclusive t vs1 vs2 :
    mpmc_fqueue_2_model t vs1 -∗
    mpmc_fqueue_2_model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.mpmc_fqueue_2_model_exclusive with "Hmodel_1 Hmodel_2").
  Qed.

  Lemma mpmc_fqueue_2_full_nonfull t :
    mpmc_fqueue_2_full t -∗
    mpmc_fqueue_2_nonfull t -∗
    False.
  Proof.
    iIntros "(:full =1) (:nonfull =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.mpmc_fqueue_2_full_nonfull with "Hfull_1 Hnonfull_2").
  Qed.

  Lemma mpmc_fqueue_2_model_finished t ι vs E :
    ↑ι ⊆ E →
    mpmc_fqueue_2_inv t ι -∗
    mpmc_fqueue_2_model t vs -∗
    mpmc_fqueue_2_finished t ={E}=∗
      ⌜vs = []⌝ ∗
      mpmc_fqueue_2_model t vs.
  Proof.
    iIntros "% (:inv =1) (:model =2) (:finished =3)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iDestruct (meta_agree with "Hmeta_2 Hmeta_3") as %<-.
    iMod (base.mpmc_fqueue_2_model_finished with "Hinv_1 Hmodel_2 Hfinished_3") as "($ & $)"; first done.
    iFrameSteps.
  Qed.

  Lemma mpmc_fqueue_2_create_spec ι cap :
    (0 ≤ cap)%Z →
    {{{
      True
    }}}
      mpmc_fqueue_2_create #cap
    {{{ t,
      RET t;
      mpmc_fqueue_2_inv t ι ∗
      mpmc_fqueue_2_model t []
    }}}.
  Proof.
    iIntros "%Hcap %Φ _ HΦ".

    iApply wp_fupd.
    wp_apply (base.mpmc_fqueue_2_create_spec with "[//]") as (𝑡 γ) "(Hmeta & Hinv & Hmodel)"; first done.
    iMod (meta_set γ with "Hmeta"); first done.
    iSteps.
  Qed.

  Lemma mpmc_fqueue_2_make_spec ι cap v :
    (0 ≤ cap)%Z →
    {{{
      True
    }}}
      mpmc_fqueue_2_make #cap v
    {{{ t,
      RET t;
      mpmc_fqueue_2_inv t ι ∗
      mpmc_fqueue_2_model t [v]
    }}}.
  Proof.
    iIntros "%Hcap %Φ _ HΦ".

    iApply wp_fupd.
    wp_apply (base.mpmc_fqueue_2_make_spec with "[//]") as (𝑡 γ) "(Hmeta & Hinv & Hmodel)"; first done.
    iMod (meta_set γ with "Hmeta"); first done.
    iSteps.
  Qed.

  Lemma mpmc_fqueue_2_is_empty_spec t ι :
    <<<
      mpmc_fqueue_2_inv t ι
    | ∀∀ vs,
      mpmc_fqueue_2_model t vs
    >>>
      mpmc_fqueue_2_is_empty t @ ↑ι
    <<<
      mpmc_fqueue_2_model t vs
    | b,
      RET #b;
      ⌜if b then vs = [] else True⌝
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    awp_apply (base.mpmc_fqueue_2_is_empty_spec with "[$]").
    { iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta_agree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_1"; iSteps.
    }
  Qed.

  Lemma mpmc_fqueue_2_push_spec t ι v E Φ :
    mpmc_fqueue_2_inv t ι -∗
    ▷ (
      |={⊤ ∖ ↑ι, E}=>
      ∃ vs,
      mpmc_fqueue_2_model t vs ∗
        ∀ b,
        ( if b then
            mpmc_fqueue_2_model t (vs ++ [v]) ∗
            mpmc_fqueue_2_nonfull t
          else
            mpmc_fqueue_2_model t vs ∗
            mpmc_fqueue_2_full t
        ) ={E}=∗
          ( if b then
              mpmc_fqueue_2_nonfull t
            else
              True
          ) ∗
            |={E, ⊤ ∖ ↑ι}=>
            Φ #b
    ) -∗
    WP mpmc_fqueue_2_push t v {{ Φ }}.
  Proof.
    iIntros "(:inv) HΦ".

    wp_apply (base.mpmc_fqueue_2_push_spec _ _ _ _ E with "[$]").
    { iMod "HΦ" as (vs) "((:model =1) & HΦ)". simplify.
      iDestruct (meta_agree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
      iFrame. iIntros "!> %b Hb".
      iMod ("HΦ" $! b with "[Hb]") as "(Hb & $)".
      { destruct b; iSteps. }
      destruct b; last iSteps.
      iDestruct "Hb" as "(:nonfull =2)". simplify.
      iDestruct (meta_agree with "Hmeta Hmeta_2") as %<-. iClear "Hmeta_2".
      iFrameSteps.
    }
  Qed.

  Lemma mpmc_fqueue_2_pop_spec t ι :
    <<<
      mpmc_fqueue_2_inv t ι
    | ∀∀ vs,
      mpmc_fqueue_2_model t vs
    >>>
      mpmc_fqueue_2_pop t @ ↑ι
    <<<
      ∃∃ o vs',
      mpmc_fqueue_2_model t vs' ∗
      ⌜ match o with
        | Something v =>
            vs = v :: vs'
        | Nothing =>
            vs' = vs
        | Anything =>
            vs = [] ∧
            vs' = vs
        end
      ⌝
    | RET o;
      if o is Anything then
        mpmc_fqueue_2_finished t
      else
        True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    awp_apply (base.mpmc_fqueue_2_pop_spec with "[$]").
    { iApply (aacc_aupd_commit with "HΦ"); first done. iIntros "%vs (:model =1)". simplify.
      iDestruct (meta_agree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
      iAaccIntro with "Hmodel_1"; first iSteps. iIntros "%o %vs' (Hmodel & $)".
      iFrameSteps. destruct o; iSteps.
    }
  Qed.
End mpmc_fqueue_2_G.

#[global] Opaque mpmc_fqueue_2_inv.
#[global] Opaque mpmc_fqueue_2_model.
#[global] Opaque mpmc_fqueue_2_full.
#[global] Opaque mpmc_fqueue_2_nonfull.
#[global] Opaque mpmc_fqueue_2_finished.
