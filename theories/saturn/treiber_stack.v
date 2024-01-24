From iris.algebra Require Import
  list.

From zebre Require Import
  prelude.
From zebre.iris.base_logic Require Import
  lib.auth_excl.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Import
  opt
  lst.
From zebre.saturn Require Export
  base.
From zebre Require Import
  options.

Implicit Types l : loc.
Implicit Types v t : val.
Implicit Types vs : list val.

Definition treiber_stack_create : val :=
  λ: <>,
    ref &&Nil.

Definition treiber_stack_push : val :=
  rec: "treiber_stack_push" "t" "v" :=
    let: "old" := !"t" in
    let: "new" := &Cons "v" "old" in
    ifnot: Cas "t" "old" "new" then (
      "treiber_stack_push" "t" "v"
    ).

Definition treiber_stack_pop : val :=
  rec: "treiber_stack_pop" "t" :=
    let: "old" := !"t" in
    match: "old" with
    | Nil =>
        &&None
    | Cons "v" "new" =>
        if: Cas "t" "old" "new" then (
          &Some "v"
        ) else (
          "treiber_stack_pop" "t"
        )
    end.

Class TreiberStackG Σ `{zebre_G : !ZebreG Σ} := {
  #[local] treiber_stack_G_model_G :: AuthExclG Σ (listO val) ;
}.

Definition treiber_stack_Σ := #[
  auth_excl_Σ (listO val)
].
#[global] Instance subG_treiber_stack_Σ Σ `{zebre_G : !ZebreG Σ} :
  subG treiber_stack_Σ Σ →
  TreiberStackG Σ.
Proof.
  solve_inG.
Qed.

Section zebre_G.
  Context `{treiber_stack_G : TreiberStackG Σ}.

  #[local] Definition treiber_stack_model₁ γ vs :=
    auth_excl_auth γ (DfracOwn 1) vs.
  #[local] Definition treiber_stack_model₂ γ vs :=
    auth_excl_frag γ vs.

  #[local] Definition treiber_stack_inv_inner l γ : iProp Σ :=
    ∃ vs,
    l ↦ (lst_to_val vs) ∗
    treiber_stack_model₂ γ vs.
  Definition treiber_stack_inv t ι : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    inv ι (treiber_stack_inv_inner l γ).

  Definition treiber_stack_model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    treiber_stack_model₁ γ vs.

  #[global] Instance treiber_stack_model_timeless t vs :
    Timeless (treiber_stack_model t vs).
  Proof.
    apply _.
  Qed.
  #[global] Instance treiber_stack_inv_persistent t ι :
    Persistent (treiber_stack_inv t ι).
  Proof.
    apply _.
  Qed.

  Lemma treiber_stack_create_spec ι :
    {{{ True }}}
      treiber_stack_create #()
    {{{ t,
      RET t;
      treiber_stack_inv t ι ∗
      treiber_stack_model t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    wp_alloc l as "Hmeta" "Hl".
    iMod (auth_excl_alloc' (auth_excl_G := treiber_stack_G_model_G) []) as "(%γ & Hmodel₁ & Hmodel₂)".
    iMod (meta_set with "Hmeta") as "#Hmeta"; first done.
    iApply "HΦ". iSplitR "Hmodel₁"; last iSteps.
    iStep 2. iApply inv_alloc. iExists []. iSteps.
  Qed.

  Lemma treiber_stack_push_spec t ι v :
    <<<
      treiber_stack_inv t ι
    | ∀∀ vs,
      treiber_stack_model t vs
    >>>
      treiber_stack_push t v @ ↑ι
    <<<
      treiber_stack_model t (v :: vs)
    | RET #(); True
    >>>.
  Proof.
    iIntros "!> %Φ (%l & %γ & -> & #Hmeta & #Hinv) HΦ".
    iLöb as "HLöb".

    wp_rec. wp_pures.

    wp_bind (!_)%E.
    iInv "Hinv" as "(%vs & Hl & Hmodel₂)".
    wp_load.
    iSplitR "HΦ"; first iSteps.
    iModIntro.

    wp_pures.

    wp_bind (Cas _ _ _).
    iInv "Hinv" as "(%vs' & Hl & Hmodel₂)".
    wp_cas as _ | ->%(inj _); first iSteps.
    iMod "HΦ" as "(%_vs & (%_l & %_γ & %Heq & _Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iDestruct (auth_excl_agree_L with "Hmodel₁ Hmodel₂") as %->.
    iMod (auth_excl_update' (auth_excl_G := treiber_stack_G_model_G) (v :: vs) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
    iSplitR "HΦ". { iExists (v :: vs). iSteps. }
    iSteps.
  Qed.

  Lemma treiber_stack_pop_spec t ι :
    <<<
      treiber_stack_inv t ι
    | ∀∀ vs,
      treiber_stack_model t vs
    >>>
      treiber_stack_pop t @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          treiber_stack_model t []
      | Some v =>
          ∃ vs',
          ⌜vs = v :: vs'⌝ ∗
          treiber_stack_model t vs'
      end
    | RET o; True
    >>>.
  Proof.
    iIntros "!> %Φ (%l & %γ & -> & #Hmeta & #Hinv) HΦ".
    iLöb as "HLöb".

    wp_rec. wp_pures.

    wp_bind (!_)%E.
    iInv "Hinv" as "(%vs & Hl & Hmodel₂)".
    wp_load.
    destruct vs as [| v vs].

    - iMod "HΦ" as "(%_vs & (%_l & %_γ & %Heq & _Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (auth_excl_agree_L with "Hmodel₁ Hmodel₂") as %->.
      iMod ("HΦ" $! None with "[Hmodel₁]") as "HΦ"; first iSteps.
      iSplitR "HΦ". { iExists []. iSteps. }
      iSteps.

    - iSplitR "HΦ". { iExists (v :: vs). iSteps. }
      iModIntro.

      wp_pures.

      wp_bind (Cas _ _ _).
      iInv "Hinv" as "(%vs' & Hl & Hmodel₂)".
      wp_cas as _ | Hcas; first iSteps.
      destruct vs'; first done. apply (inj lst_to_val _ (_ :: _)) in Hcas as [= -> ->].
      iMod "HΦ" as "(%_vs & (%_l & %_γ & %Heq & _Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (auth_excl_agree_L with "Hmodel₁ Hmodel₂") as %->.
      iMod (auth_excl_update' (auth_excl_G := treiber_stack_G_model_G) vs with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" $! (Some v) with "[Hmodel₁]") as "HΦ"; first iSteps.
      iSplitR "HΦ"; first iSteps.
      iSteps.
  Qed.
End zebre_G.

#[global] Opaque treiber_stack_create.
#[global] Opaque treiber_stack_push.
#[global] Opaque treiber_stack_pop.

#[global] Opaque treiber_stack_inv.
#[global] Opaque treiber_stack_model.
