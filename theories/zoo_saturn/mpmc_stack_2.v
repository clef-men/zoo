Require Import zoo.prelude.
Require Import zoo.iris.base_logic.lib.twins.
Require Import zoo.base.
Require Import zoo_std.option.
Require Import zoo_std.optional.
Require Import zoo_std.clist.
Require Export zoo_saturn.mpmc_stack_2__code.
Require Import zoo.options.

Implicit Type l : location.
Implicit Type v t : val.
Implicit Type ws : list val.

Class MpmcStack2G Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] mpmc_stack_2۰G۰model۰G :: TwinsG Σ (leibnizO (option $ list val))
  }.

Definition mpmc_stack_2۰Σ :=
  #[twins۰Σ (leibnizO (option $ list val))
  ].
#[global] Instance subGｰmpmc_stack_2۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG mpmc_stack_2۰Σ Σ →
  MpmcStack2G Σ.
Proof.
  solve_inG.
Qed.

Section zoo۰G.
  Context `{mpmc_stack_2۰G : MpmcStack2G Σ}.

  #[local] Definition metadata :=
    gname.
  Implicit Type γ : metadata.

  #[local] Definition model₁ γ vs :=
    twins۰twin₁ γ (if vs is None then DfracDiscarded else DfracOwn 1) vs.
  #[local] Definition model₂ γ vs :=
    twins۰twin₂ γ vs.

  #[local] Definition inv۰inner l γ : iProp Σ :=
    ∃ vs,
    l ↦ᵣ from_option (clist۰to_val ∘ list۰to_clist_open) §ClistClosed vs ∗
    model₂ γ vs.
  #[local] Instance : CustomIpat "inv۰inner" :=
    " ( %vs
      & Hl
      & Hmodel₂
      )
    ".
  Definition mpmc_stack_2۰inv t ι : iProp Σ :=
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

  Definition mpmc_stack_2۰model t vs : iProp Σ :=
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

  Definition mpmc_stack_2۰closed t :=
    mpmc_stack_2۰model t None.

  #[global] Instance mpmc_stack_2۰modelｰtimeless t vs :
    Timeless (mpmc_stack_2۰model t vs).
  Proof.
    apply _.
  Qed.

  #[global] Instance mpmc_stack_2۰invｰpersistent t ι :
    Persistent (mpmc_stack_2۰inv t ι).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpmc_stack_2۰modelｰpersistent t :
    Persistent (mpmc_stack_2۰model t None).
  Proof.
    apply _.
  Qed.

  #[local] Lemma modelｰalloc :
    ⊢ |==>
      ∃ γ,
      model₁ γ (Some []) ∗
      model₂ γ (Some []).
  Proof.
    apply twinsｰalloc'.
  Qed.
  #[local] Lemma model₁ｰexclusive γ vs1 vs2 :
    model₁ γ (Some vs1) -∗
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
  #[local] Lemma modelｰupdate {γ ws1 ws2} ws :
    model₁ γ (Some ws1) -∗
    model₂ γ (Some ws2) ==∗
      model₁ γ (Some ws) ∗
      model₂ γ (Some ws).
  Proof.
    apply twinsｰupdate.
  Qed.
  #[local] Lemma modelｰclose γ ws1 ws2 :
    model₁ γ (Some ws1) -∗
    model₂ γ (Some ws2) ==∗
      model₁ γ None ∗
      model₂ γ None.
  Proof.
    iIntros "Hmodel₁ Hmodel₂".
    iMod (twinsｰupdate with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
    iMod (twins۰twin₁ｰpersist with "Hmodel₁") as "Hmodel₁".
    iSteps.
  Qed.

  Lemma mpmc_stack_2۰modelｰexclusive t vs1 vs2 :
    mpmc_stack_2۰model t (Some vs1) -∗
    mpmc_stack_2۰model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simplify.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->.
    iApply (model₁ｰexclusive with "Hmodel₁_1 Hmodel₁_2").
  Qed.

  Lemma mpmc_stack_2٠createｰspec ι :
    {{{
      True
    }}}
      mpmc_stack_2٠create ()
    {{{
      t
    , RET t;
      mpmc_stack_2۰inv t ι ∗
      mpmc_stack_2۰model t (Some [])
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp۰rec.
    wp۰ref l as "Hmeta" "Hl".

    iMod modelｰalloc as "(%γ & Hmodel₁ & Hmodel₂)".

    iMod (metaｰset γ with "Hmeta") as "#Hmeta"; first done.

    iApply "HΦ".
    iSplitR "Hmodel₁"; last iSteps.
    iStep 2. iApply inv_alloc. iExists (Some []). iSteps.
  Qed.

  Lemma mpmc_stack_2٠pushｰspec t ι v :
    <<<
      mpmc_stack_2۰inv t ι
    | ∀∀ vs,
      mpmc_stack_2۰model t vs
    >>>
      mpmc_stack_2٠push t v @ ↑ι
    <<<
      mpmc_stack_2۰model t (cons v <$> vs)
    | RET #(bool_decide (vs = None));
      £ 1
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    iLöb as "HLöb".

    wp۰rec credit:"H£". wp۰pures.

    wp۰bind (!_)%E.
    iInv "Hinv" as "(:inv۰inner)".
    wp۰load.
    destruct vs as [ws |].

    - iSplitR "H£ HΦ". { iFrameSteps. }
      iIntros "!> {%}".

      wp۰apply+ wpｰmatchｰclistｰopen.
      wp۰pures.

      wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
      iInv "Hinv" as "(:inv۰inner)".
      destruct vs as [vs |].

      + simpl.
        wp۰cas as _ | ->%(inj _)%(inj _).

        * iSplitR "HΦ". { iFrameSteps. }
          iSteps.

        * iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
          iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
          iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
          pose ws' := v :: ws.
          iMod (modelｰupdate ws' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
          iMod ("HΦ" with "[$Hmodel₁] H£") as "HΦ"; first iSteps.
          iSplitR "HΦ". { iFrameSteps. }
          iSteps.

      + wp۰cas as _ | []%(inj clist۰to_val ClistClosed)%list۰to_clist_openｰnotｰclosed'.
        iSplitR "HΦ". { iFrameSteps. }
        iSteps.

    - iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
      iMod ("HΦ" with "[$Hmodel₁] H£") as "HΦ"; first iSteps.
      iSplitR "HΦ". { iFrameSteps. }
      iSteps.
  Qed.
  Lemma mpmc_stack_2٠pushｰspecｰclosed t ι v :
    {{{
      mpmc_stack_2۰inv t ι ∗
      mpmc_stack_2۰closed t
    }}}
      mpmc_stack_2٠push t v
    {{{
      RET true;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hclosed) HΦ".

    iApply wpｰfupd.
    awp۰apply (mpmc_stack_2٠pushｰspec with "Hinv").
    iAaccIntro with "Hclosed"; first iSteps. iIntros "_ !> H£".
    iDestruct (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
    iSteps.
  Qed.

  Lemma mpmc_stack_2٠popｰspec t ι :
    <<<
      mpmc_stack_2۰inv t ι
    | ∀∀ vs,
      mpmc_stack_2۰model t vs
    >>>
      mpmc_stack_2٠pop t @ ↑ι
    <<<
      mpmc_stack_2۰model t (tail <$> vs)
    | RET default Anything (option۰to_optional ∘ head <$> vs);
      £ 1
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    iLöb as "HLöb".

    wp۰rec credit:"H£".

    wp۰bind (!_)%E.
    iInv "Hinv" as "(:inv۰inner)".
    wp۰load.
    destruct vs as [[| v ws] |].

    - iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
      iMod ("HΦ" with "[$Hmodel₁]") as "HΦ"; first iSteps.
      iSplitR "H£ HΦ". { iFrameSteps. }
      iSteps.

    - iSplitR "H£ HΦ". { iFrameSteps. }
      iIntros "!> {%}".

      wp۰pures.

      wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
      iInv "Hinv" as "(:inv۰inner)".
      destruct vs as [vs |].

      + wp۰cas as _ | ->%(inj clist۰to_val _ (ClistCons _ _))%(inj list۰to_clist_open _ (_ :: _)).

        * iSplitR "HΦ". { iFrameSteps. }
          iSteps.

        * iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
          iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
          iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
          iMod (modelｰupdate ws with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
          iMod ("HΦ" with "[$Hmodel₁]") as "HΦ"; first iSteps.
          iSplitR "H£ HΦ". { iFrameSteps. }
          iSteps.

      + wp۰cas as _ | [=].
        iSplitR "HΦ". { iFrameSteps. }
        iSteps.

    - iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
      iMod ("HΦ" with "[$Hmodel₁]") as "HΦ"; first iSteps.
      iSplitR "H£ HΦ". { iFrameSteps. }
      iSteps.
  Qed.
  Lemma mpmc_stack_2٠popｰspecｰclosed t ι v :
    {{{
      mpmc_stack_2۰inv t ι ∗
      mpmc_stack_2۰closed t
    }}}
      mpmc_stack_2٠pop t
    {{{
      RET §Anything;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hclosed) HΦ".

    iApply wpｰfupd.
    awp۰apply (mpmc_stack_2٠popｰspec with "Hinv").
    iAaccIntro with "Hclosed"; first iSteps. iIntros "_ !> H£".
    iDestruct (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
    iSteps.
  Qed.

  Lemma mpmc_stack_2٠is_closedｰspec t ι :
    <<<
      mpmc_stack_2۰inv t ι
    | ∀∀ vs,
      mpmc_stack_2۰model t vs
    >>>
      mpmc_stack_2٠is_closed t @ ↑ι
    <<<
      mpmc_stack_2۰model t vs
    | RET #(bool_decide (vs = None));
      £ 1
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec credit:"H£".

    wp۰bind (!_)%E.
    iInv "Hinv" as "(:inv۰inner)".
    wp۰load.
    iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
    destruct vs as [vs |].

    - iMod ("HΦ" with "[$Hmodel₁] H£") as "HΦ"; first iSteps.
      iSplitR "HΦ". { iFrameSteps. }
      iIntros "!> {%}".

      wp۰equal as _ | []%(inj clist۰to_val _ ClistClosed)%list۰to_clist_openｰnotｰclosed.
      iSteps.

    - iMod ("HΦ" with "[$Hmodel₁] H£") as "HΦ"; first iSteps.
      iSplitR "HΦ". { iFrameSteps. }
      iSteps.
  Qed.
  Lemma mpmc_stack_2٠is_closedｰspecｰclosed t ι :
    {{{
      mpmc_stack_2۰inv t ι ∗
      mpmc_stack_2۰closed t
    }}}
      mpmc_stack_2٠is_closed t
    {{{
      RET true;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hclosed) HΦ".

    iApply wpｰfupd.
    awp۰apply (mpmc_stack_2٠is_closedｰspec with "Hinv").
    iAaccIntro with "Hclosed"; first iSteps. iIntros "_ !> H£".
    iDestruct (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
    iSteps.
  Qed.

  Lemma mpmc_stack_2٠closeｰspec t ι :
    <<<
      mpmc_stack_2۰inv t ι
    | ∀∀ vs,
      mpmc_stack_2۰model t vs
    >>>
      mpmc_stack_2٠close t @ ↑ι
    <<<
      mpmc_stack_2۰model t None
    | RET from_option list۰to_clist_open ClistClosed vs;
      £ 1
    >>>.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec credit:"H£". wp۰pures.

    iInv "Hinv" as "(:inv۰inner)".
    wp۰xchg.
    iMod "HΦ" as "(%vs_ & (:model) & _ & HΦ)". injection Heq as <-.
    iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
    iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
    destruct vs as [vs |].

    - iMod (modelｰclose with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
      iMod ("HΦ" with "[$Hmodel₁] H£") as "HΦ"; first iSteps.
      iSplitR "HΦ". { iFrameSteps. }
      iSteps.

    - iMod ("HΦ" with "[$Hmodel₁] H£") as "HΦ"; first iSteps.
      iSplitR "HΦ". { iFrameSteps. }
      iSteps.
  Qed.
  Lemma mpmc_stack_2٠closedｰspecｰclosed t ι v :
    {{{
      mpmc_stack_2۰inv t ι ∗
      mpmc_stack_2۰closed t
    }}}
      mpmc_stack_2٠close t
    {{{
      RET §ClistClosed;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hclosed) HΦ".

    iApply wpｰfupd.
    awp۰apply (mpmc_stack_2٠closeｰspec with "Hinv").
    iAaccIntro with "Hclosed"; first iSteps. iIntros "_ !> H£".
    iDestruct (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
    iSteps.
  Qed.
End zoo۰G.

Require zoo_saturn.mpmc_stack_2__opaque.

#[global] Opaque mpmc_stack_2۰inv.
#[global] Opaque mpmc_stack_2۰model.
