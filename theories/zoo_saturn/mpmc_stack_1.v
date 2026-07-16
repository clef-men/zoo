Require Import zoo.prelude.
Require Import zoo.iris.base_logic.lib.twins.
Require Import zoo.base.
Require Import zoo_std.option.
Require Import zoo_std.glist.
Require Export zoo_saturn.mpmc_stack_1__code.
Require Import zoo.options.

Implicit Types l : location.
Implicit Types v t : val.
Implicit Types vs : list val.

Class MpmcStack1G Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] mpmc_stack_1۰G۰model۰G :: TwinsG Σ (leibnizO (list val))
  }.

Definition mpmc_stack_1۰Σ :=
  #[twins۰Σ (leibnizO (list val))
  ].
#[global] Instance subG𑁒mpmc_stack_1۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG mpmc_stack_1۰Σ Σ →
  MpmcStack1G Σ.
Proof.
  solve_inG.
Qed.

Section zoo۰G.
  Context `{mpmc_stack_1۰G : MpmcStack1G Σ}.

  #[local] Definition metadata :=
    gname.
  Implicit Types γ : metadata.

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

  #[global] Instance mpmc_stack_1۰model𑁒timeless t vs :
    Timeless (mpmc_stack_1۰model t vs).
  Proof.
    apply _.
  Qed.

  #[global] Instance mpmc_stack_1۰inv𑁒persistent t ι :
    Persistent (mpmc_stack_1۰inv t ι).
  Proof.
    apply _.
  Qed.

  #[local] Lemma model𑁒alloc :
    ⊢ |==>
      ∃ γ,
      model₁ γ [] ∗
      model₂ γ [].
  Proof.
    apply twins𑁒alloc'.
  Qed.
  #[local] Lemma model₁𑁒exclusive γ vs1 vs2 :
    model₁ γ vs1 -∗
    model₁ γ vs2 -∗
    False.
  Proof.
    apply twins۰twin₁𑁒exclusive.
  Qed.
  #[local] Lemma model𑁒agree γ vs1 vs2 :
    model₁ γ vs1 -∗
    model₂ γ vs2 -∗
    ⌜vs1 = vs2⌝.
  Proof.
    apply: twins𑁒agree𑁒L.
  Qed.
  #[local] Lemma model𑁒update {γ vs1 vs2} vs :
    model₁ γ vs1 -∗
    model₂ γ vs2 ==∗
      model₁ γ vs ∗
      model₂ γ vs.
  Proof.
    apply twins𑁒update.
  Qed.

  Lemma mpmc_stack_1۰model𑁒exclusive t vs1 vs2 :
    mpmc_stack_1۰model t vs1 -∗
    mpmc_stack_1۰model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (model₁𑁒exclusive with "Hmodel₁_1 Hmodel₁_2").
  Qed.

  Lemma mpmc_stack_1٠create𑁒spec ι :
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

    iMod model𑁒alloc as "(%γ & Hmodel₁ & Hmodel₂)".

    iMod (meta𑁒set γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ". iSplitR "Hmodel₁"; last iSteps.
    iStep 2. iApply inv_alloc. iExists []. iSteps.
  Qed.

  Lemma mpmc_stack_1٠push𑁒spec t ι v :
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

    wp۰bind (CAS _ _ _).
    iInv "Hinv" as "(:inv۰inner =')".
    wp۰cas as _ | ->%(inj _); first iSteps.
    iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %->.
    iMod (model𑁒update (v :: vs) with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iMod ("HΦ" with "[$Hmodel₁]") as "HΦ"; first iSteps.
    iSplitR "HΦ". { iExists (v :: vs). iSteps. }
    iSteps.
  Qed.

  Lemma mpmc_stack_1٠pop𑁒spec t ι :
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
      iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %->.
      iMod ("HΦ" with "[$Hmodel₁]") as "HΦ"; first iSteps.
      iSplitR "HΦ". { iExists []. iSteps. }
      iSteps.

    - iSplitR "HΦ". { iExists (v :: vs). iSteps. }
      iModIntro.

      wp۰pures.

      wp۰bind (CAS _ _ _).
      iInv "Hinv" as "(:inv۰inner =')".
      wp۰cas as _ | Hcas; first iSteps.
      destruct vs'; first done. apply (inj glist۰to_val _ (_ :: _)) in Hcas as [= -> ->].
      iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %->.
      iMod (model𑁒update vs with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "[$Hmodel₁]") as "HΦ"; first iSteps.
      iSplitR "HΦ"; first iSteps.
      iSteps.
  Qed.

  Lemma mpmc_stack_1٠snapshot𑁒spec t ι :
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
    iDestruct (meta𑁒agree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (model𑁒agree with "Hmodel₁ Hmodel₂") as %->.
    iMod ("HΦ" with "[$Hmodel₁]") as "HΦ"; first iSteps.
    iSteps.
  Qed.
End zoo۰G.

Require zoo_saturn.mpmc_stack_1__opaque.

#[global] Opaque mpmc_stack_1۰inv.
#[global] Opaque mpmc_stack_1۰model.
