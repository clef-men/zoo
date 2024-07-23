(* Based on:
   https://github.com/ocaml-multicore/saturn/blob/65211c5176b632bd9ed268c0c608ac483f88a992/src_lockfree/treiber_stack.ml
*)

From zoo Require Import
  prelude.
From zoo.iris.base_logic Require Import
  lib.twins.
From zoo.language Require Import
  notations
  diaframe.
From zoo.std Require Import
  option
  lst.
From zoo.saturn Require Export
  base.
From zoo Require Import
  options.

Implicit Types l : location.
Implicit Types v t : val.
Implicit Types vs : list val.

Definition mpmc_stack_create : val :=
  fun: <> =>
    ref §Nil.

Definition mpmc_stack_push : val :=
  rec: "mpmc_stack_push" "t" "v" =>
    let: "old" := !"t" in
    let: "new" := ‘Cons{ "v", "old" } in
    ifnot: CAS "t" "old" "new" then (
      Yield ;;
      "mpmc_stack_push" "t" "v"
    ).

Definition mpmc_stack_pop : val :=
  rec: "mpmc_stack_pop" "t" =>
    match: !"t" with
    | Nil =>
        §None
    | Cons "v" "new" as "old" =>
        if: CAS "t" "old" "new" then (
          ‘Some{ "v" }
        ) else (
          Yield ;;
          "mpmc_stack_pop" "t"
        )
    end.

Class MpmcStackG Σ `{zoo_G : !ZooG Σ} := {
  #[local] mpmc_stack_G_model_G :: TwinsG Σ (leibnizO (list val)) ;
}.

Definition mpmc_stack_Σ := #[
  twins_Σ (leibnizO (list val))
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
    twins_twin1 γ (DfracOwn 1) vs.
  #[local] Definition mpmc_stack_model₂ γ vs :=
    twins_twin2 γ vs.

  #[local] Definition mpmc_stack_inv_inner l γ : iProp Σ :=
    ∃ vs,
    l ↦ lst_to_val vs ∗
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

  #[local] Lemma mpmc_stack_model_alloc :
    ⊢ |==>
      ∃ γ,
      mpmc_stack_model₁ γ [] ∗
      mpmc_stack_model₂ γ [].
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
  #[local] Lemma mpmc_stack_model_update {γ vs1 vs2} vs :
    mpmc_stack_model₁ γ vs1 -∗
    mpmc_stack_model₂ γ vs2 ==∗
      mpmc_stack_model₁ γ vs ∗
      mpmc_stack_model₂ γ vs.
  Proof.
    apply twins_update'.
  Qed.

  Lemma mpmc_stack_create_spec ι :
    {{{ True }}}
      mpmc_stack_create ()
    {{{ t,
      RET t;
      mpmc_stack_inv t ι ∗
      mpmc_stack_model t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp_rec.
    wp_alloc l as "Hmeta" "Hl".

    iMod mpmc_stack_model_alloc as "(%γ & Hmodel₁ & Hmodel₂)".

    iMod (meta_set with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ". iSplitR "Hmodel₁"; last iSteps.
    iStep 2. iApply inv_alloc. iExists []. iSteps.
  Qed.

  Lemma mpmc_stack_push_spec t ι v :
    <<<
      mpmc_stack_inv t ι
    | ∀∀ vs,
      mpmc_stack_model t vs
    >>>
      mpmc_stack_push t v @ ↑ι
    <<<
      mpmc_stack_model t (v :: vs)
    | RET (); True
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

    wp_bind (CAS _ _ _).
    iInv "Hinv" as "(%vs' & Hl & Hmodel₂)".
    wp_cas as _ | ->%(inj _) _; first iSteps.
    iMod "HΦ" as "(%_vs & (%_l & %_γ & %Heq & _Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iDestruct (mpmc_stack_model_agree with "Hmodel₁ Hmodel₂") as %->.
    iMod (mpmc_stack_model_update (v :: vs) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
    iSplitR "HΦ". { iExists (v :: vs). iSteps. }
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
      mpmc_stack_model t (tail vs)
    | RET head vs; True
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
      iDestruct (mpmc_stack_model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
      iSplitR "HΦ". { iExists []. iSteps. }
      iSteps.

    - iSplitR "HΦ". { iExists (v :: vs). iSteps. }
      iModIntro.

      wp_pures.

      wp_bind (CAS _ _ _).
      iInv "Hinv" as "(%vs' & Hl & Hmodel₂)".
      wp_cas as _ | Hcas _; first iSteps.
      destruct vs'; first done. apply (inj lst_to_val _ (_ :: _)) in Hcas as [= -> ->].
      iMod "HΦ" as "(%_vs & (%_l & %_γ & %Heq & _Hmeta & Hmodel₁) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
      iDestruct (mpmc_stack_model_agree with "Hmodel₁ Hmodel₂") as %->.
      iMod (mpmc_stack_model_update vs with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "[Hmodel₁]") as "HΦ"; first iSteps.
      iSplitR "HΦ"; first iSteps.
      iSteps.
  Qed.
End zoo_G.

#[global] Opaque mpmc_stack_create.
#[global] Opaque mpmc_stack_push.
#[global] Opaque mpmc_stack_pop.

#[global] Opaque mpmc_stack_inv.
#[global] Opaque mpmc_stack_model.
