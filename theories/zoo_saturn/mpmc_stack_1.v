Require Import zoo.prelude.
Require Import zoo.iris.base_logic.lib.twins.
Require Import zoo.base.
Require Import zoo_std.option.
Require Export zoo_saturn.mpmc_stack_1__code.
Require Import zoo_saturn.mpmc_stack_1__types.
Require Import zoo.options.

Implicit Type l : location.
Implicit Type v t : val.
Implicit Type vs : list val.

Class MpmcStack1G Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] mpmc_stack_1۰G۰model۰G :: TwinsG Σ (leibnizO (list val))
  }.

Definition mpmc_stack_1۰Σ :=
  #[twins۰Σ (leibnizO (list val))
  ].
#[global] Instance subGｰmpmc_stack_1۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG mpmc_stack_1۰Σ Σ →
  MpmcStack1G Σ.
Proof.
  solve_inG.
Qed.

Section zoo۰G.
  Context `{mpmc_stack_1۰G : MpmcStack1G Σ}.

  #[local] Definition metadata :=
    gname.
  Implicit Type γ : metadata.

  #[local] Definition model₁ γ vs :=
    twins۰twin₁ γ (DfracOwn 1) vs.
  #[local] Definition model₂ γ vs :=
    twins۰twin₂ γ vs.

  #[local] Definition inv۰inner l γ : iProp Σ :=
    ∃ vs,
    l ↦ᵣ glist۰to_val vs ∗
    model₂ γ vs.
  #[local] Instance : CustomIpat "inv۰inner" :=
    " ( %vs{}
      & Hl
      & Hmodel₂
      )
    ".
  Definition mpmc_stack_1۰inv t ι : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    l ↪ γ ∗
    inv ι (inv۰inner l γ).
  #[local] Instance : CustomIpat "inv" :=
    " ( %l
      & %γ
      & ->
      & #Hmeta
      & #Hinv
      )
    ".

  Definition mpmc_stack_1۰model t vs : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    l ↪ γ ∗
    model₁ γ vs.
  #[local] Instance : CustomIpat "model" :=
    " ( %l{;_}
      & %γ{;_}
      & %Heq{}
      & Hmeta_{}
      & Hmodel₁{_{}}
      )
    ".

  #[global] Instance mpmc_stack_1۰modelｰtimeless t vs :
    Timeless (mpmc_stack_1۰model t vs).
  Proof.
    apply _.
  Qed.

  #[global] Instance mpmc_stack_1۰invｰpersistent t ι :
    Persistent (mpmc_stack_1۰inv t ι).
  Proof.
    apply _.
  Qed.

  #[local] Lemma modelｰalloc :
    ⊢ |==>
      ∃ γ,
      model₁ γ [] ∗
      model₂ γ [].
  Proof.
    apply twinsｰalloc'.
  Qed.
  #[local] Lemma model₁ｰexclusive γ vs1 vs2 :
    model₁ γ vs1 -∗
    model₁ γ vs2 -∗
    False.
  Proof.
    apply twins۰twin₁ｰexclusive.
  Qed.
  #[local] Lemma modelｰagree γ vs1 vs2 :
    model₁ γ vs1 -∗
    model₂ γ vs2 -∗
    ⌜vs1 = vs2⌝.
  Proof.
    apply: twinsｰagreeｰL.
  Qed.
  #[local] Lemma modelｰupdate {γ vs1 vs2} vs :
    model₁ γ vs1 -∗
    model₂ γ vs2 ==∗
      model₁ γ vs ∗
      model₂ γ vs.
  Proof.
    apply twinsｰupdate.
  Qed.

  Lemma mpmc_stack_1۰modelｰexclusive t vs1 vs2 :
    mpmc_stack_1۰model t vs1 -∗
    mpmc_stack_1۰model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simp.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->.
    iApply (model₁ｰexclusive with "Hmodel₁_1 Hmodel₁_2").
  Qed.

  Lemma mpmc_stack_1٠createｰspec ι :
    {{{
      True
    }}}
      mpmc_stack_1٠create ()
    {{{
      t
    , RET t;
      mpmc_stack_1۰inv t ι ∗
      mpmc_stack_1۰model t []
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp۰rec.
    wp۰ref l as "Hmeta" "Hl".

    iMod modelｰalloc as "(%γ & Hmodel₁ & Hmodel₂)".

    iMod (metaｰset γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ". iSplitR "Hmodel₁"; last iSteps.
    iStep 2. iApply inv_alloc. iExists []. iSteps.
  Qed.

  Lemma mpmc_stack_1٠pushｰspec t ι v :
    <<<
      mpmc_stack_1۰inv t ι
    | ∀∀ vs,
      mpmc_stack_1۰model t vs
    >>>
      mpmc_stack_1٠push t v @ ↑ι
    <<<
      mpmc_stack_1۰model t (v :: vs)
    | RET ();
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    iLöb as "HLöb".

    wp۰rec. wp۰pures.

    wp۰bind (!_)%E.
    iInv "Hinv" as "(:inv۰inner)".
    wp۰load.
    iSplitR "HΦ"; first iSteps.
    iModIntro.

    wp۰pures.

    wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
    iInv "Hinv" as "(:inv۰inner =')".
    wp۰cas as _ | ->%(inj _); first iSteps.
    iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
    iMod (modelｰupdate (v :: vs) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iMod ("HΦ" with "[$Hmodel₁]") as "HΦ"; first iSteps.
    iSplitR "HΦ". { iExists (v :: vs). iSteps. }
    iSteps.
  Qed.

  Lemma mpmc_stack_1٠popｰspec t ι :
    <<<
      mpmc_stack_1۰inv t ι
    | ∀∀ vs,
      mpmc_stack_1۰model t vs
    >>>
      mpmc_stack_1٠pop t @ ↑ι
    <<<
      mpmc_stack_1۰model t (tail vs)
    | RET head vs;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    iLöb as "HLöb".

    wp۰rec. wp۰pures.

    wp۰bind (!_)%E.
    iInv "Hinv" as "(:inv۰inner)".
    wp۰load.
    destruct vs as [| v vs].

    - iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
      iMod ("HΦ" with "[$Hmodel₁]") as "HΦ"; first iSteps.
      iSplitR "HΦ". { iExists []. iSteps. }
      iSteps.

    - iSplitR "HΦ". { iExists (v :: vs). iSteps. }
      iModIntro.

      wp۰pures.

      wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
      iInv "Hinv" as "(:inv۰inner =')".
      wp۰cas as _ | Hcas; first iSteps.
      destruct vs'; first done. apply (inj glist۰to_val _ (_ :: _)) in Hcas as [= -> ->].
      iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
      iMod (modelｰupdate vs with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "[$Hmodel₁]") as "HΦ"; first iSteps.
      iSplitR "HΦ"; first iSteps.
      iSteps.
  Qed.

  Lemma mpmc_stack_1٠snapshotｰspec t ι :
    <<<
      mpmc_stack_1۰inv t ι
    | ∀∀ vs,
      mpmc_stack_1۰model t vs
    >>>
      mpmc_stack_1٠snapshot t @ ↑ι
    <<<
      mpmc_stack_1۰model t vs
    | RET glist۰to_val vs;
      True
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec.

    iInv "Hinv" as "(:inv۰inner)".
    wp۰load.
    iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
    iMod ("HΦ" with "[$Hmodel₁]") as "HΦ"; first iSteps.
    iSteps.
  Qed.
End zoo۰G.

Require zoo_saturn.mpmc_stack_1__opaque.

#[global] Opaque mpmc_stack_1۰inv.
#[global] Opaque mpmc_stack_1۰model.
