Require Import zoo.prelude.
Require Import zoo.iris.base_logic.lib.twins.
Require Import zoo.base.
Require Import zoo_std.option.
Require Export zoo_saturn.stack_mpmc_2__code.
Require Import zoo_saturn.stack_mpmc_2__types.
Require Import zoo.options.

Implicit Type l : location.
Implicit Type v t backoff : val.
Implicit Type ws : list val.

Class StackMpmc2G Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] stack_mpmc_2۰G۰model۰G :: TwinsG Σ (leibnizO (option $ list val))
  }.

Definition stack_mpmc_2۰Σ :=
  #[twins۰Σ (leibnizO (option $ list val))
  ].
#[global] Instance subGｰstack_mpmc_2۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG stack_mpmc_2۰Σ Σ →
  StackMpmc2G Σ.
Proof.
  solve_inG.
Qed.

Section zoo۰G.
  Context `{stack_mpmc_2۰G : StackMpmc2G Σ}.

  #[local] Definition metadata :=
    gname.
  Implicit Type γ : metadata.

  #[local] Definition model₁ γ vs :=
    twins۰twin₁ γ (if vs is None then DfracDiscarded else DfracOwn 1) vs.
  #[local] Definition model₂ γ vs :=
    twins۰twin₂ γ vs.

  #[local] Definition inv۰inner l γ : iProp Σ :=
    ∃ vs,
    l ↦ᵣ from_option (clist۰to_val ∘ list۰to_clist_open) §clist٠Closed vs ∗
    model₂ γ vs.
  #[local] Instance : CustomIpat "inv۰inner" :=
    " ( %vs
      & Hl
      & Hmodel₂
      )
    ".
  Definition stack_mpmc_2۰inv t ι : iProp Σ :=
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

  Definition stack_mpmc_2۰model t vs : iProp Σ :=
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

  Definition stack_mpmc_2۰closed t :=
    stack_mpmc_2۰model t None.

  #[global] Instance stack_mpmc_2۰modelｰtimeless t vs :
    Timeless (stack_mpmc_2۰model t vs).
  Proof.
    apply _.
  Qed.

  #[global] Instance stack_mpmc_2۰invｰpersistent t ι :
    Persistent (stack_mpmc_2۰inv t ι).
  Proof.
    apply _.
  Qed.
  #[global] Instance stack_mpmc_2۰modelｰpersistent t :
    Persistent (stack_mpmc_2۰model t None).
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

  Lemma stack_mpmc_2۰modelｰexclusive t vs1 vs2 :
    stack_mpmc_2۰model t (Some vs1) -∗
    stack_mpmc_2۰model t vs2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simp.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->.
    iApply (model₁ｰexclusive with "Hmodel₁_1 Hmodel₁_2").
  Qed.

  Lemma stack_mpmc_2٠createｰspec ι :
    {{{
      True
    }}}
      stack_mpmc_2٠create ()
    {{{
      t
    , RET t;
      stack_mpmc_2۰inv t ι ∗
      stack_mpmc_2۰model t (Some [])
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

  #[local] Lemma stack_mpmc_2٠push₁ｰspec t ι v backoff :
    <<<
      stack_mpmc_2۰inv t ι ∗
      backoff۰model backoff
    | ∀∀ vs,
      stack_mpmc_2۰model t vs
    >>>
      stack_mpmc_2٠push₁ t v backoff
      @ ↑ι
    <<<
      stack_mpmc_2۰model t (cons v <$> vs)
    | RET #(bool_decide (vs = None));
      £ 1
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & Hbackoff) HΦ".

    iLöb as "HLöb" forall (backoff).

    wp۰rec credit:"H£". wp۰pures.

    wp۰bind (!_)%E.
    iInv "Hinv" as "(:inv۰inner)".
    wp۰load.
    destruct vs as [ws |].

    - iSplitR "Hbackoff H£ HΦ". { iFrameSteps. }
      iIntros "!> {%}".

      wp۰apply+ wpｰmatchｰclistｰopen.
      wp۰pures.

      wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
      iInv "Hinv" as "(:inv۰inner)".
      destruct vs as [vs |].

      + simpl.
        wp۰cas as _ | ->%(inj _)%(inj _).

        * iSplitR "Hbackoff HΦ". { iFrameSteps. }
          iSteps.

        * iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
          iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
          iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
          pose ws' := v :: ws.
          iMod (modelｰupdate ws' with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
          iMod ("HΦ" with "[$Hmodel₁] H£") as "HΦ"; first iSteps.
          iSplitR "HΦ". { iFrameSteps. }
          iSteps.

      + wp۰cas as _ | []%(inj clist۰to_val Closed)%list۰to_clist_openｰnotｰclosed'.
        iSplitR "Hbackoff HΦ". { iFrameSteps. }
        iSteps.

    - iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
      iMod ("HΦ" with "[$Hmodel₁] H£") as "HΦ"; first iSteps.
      iSplitR "HΦ". { iFrameSteps. }
      iSteps.
  Qed.

  Lemma stack_mpmc_2٠pushｰspec t ι v :
    <<<
      stack_mpmc_2۰inv t ι
    | ∀∀ vs,
      stack_mpmc_2۰model t vs
    >>>
      stack_mpmc_2٠push t v
      @ ↑ι
    <<<
      stack_mpmc_2۰model t (cons v <$> vs)
    | RET #(bool_decide (vs = None));
      £ 1
    >>>.
  Proof.
    iIntros "%Φ Hinv HΦ".

    wp۰rec.
    wp۰apply+ (stack_mpmc_2٠push₁ｰspec with "[$Hinv] HΦ"). 1: iSteps.
  Qed.
  Lemma stack_mpmc_2٠pushｰspecｰclosed t ι v :
    {{{
      stack_mpmc_2۰inv t ι ∗
      stack_mpmc_2۰closed t
    }}}
      stack_mpmc_2٠push t v
    {{{
      RET true;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hclosed) HΦ".

    iApply wpｰfupd.
    awp۰apply (stack_mpmc_2٠pushｰspec with "Hinv").
    iAaccIntro with "Hclosed"; first iSteps. iIntros "_ !> H£".
    iDestruct (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
    iSteps.
  Qed.

  #[local] Lemma stack_mpmc_2٠pop₁ｰspec t ι backoff :
    <<<
      stack_mpmc_2۰inv t ι ∗
      backoff۰model backoff
    | ∀∀ vs,
      stack_mpmc_2۰model t vs
    >>>
      stack_mpmc_2٠pop₁ t backoff
      @ ↑ι
    <<<
      stack_mpmc_2۰model t (tail <$> vs)
    | RET default Anything (option۰to_optional ∘ head <$> vs);
      £ 1
    >>>.
  Proof.
    iIntros "%Φ ((:inv) & Hbackoff) HΦ".

    iLöb as "HLöb" forall (backoff).

    wp۰rec credit:"H£". wp۰pures.

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

    - iSplitR "Hbackoff H£ HΦ". { iFrameSteps. }
      iIntros "!> {%}".

      wp۰pures.

      wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
      iInv "Hinv" as "(:inv۰inner)".
      destruct vs as [vs |].

      + wp۰cas as _ | ->%(inj clist۰to_val _ (Cons _ _))%(inj list۰to_clist_open _ (_ :: _)).

        * iSplitR "Hbackoff HΦ". { iFrameSteps. }
          iSteps.

        * iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
          iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
          iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
          iMod (modelｰupdate ws with "Hmodel₁ Hmodel₂") as "(Hmodel₁ & Hmodel₂)".
          iMod ("HΦ" with "[$Hmodel₁]") as "HΦ"; first iSteps.
          iSplitR "H£ HΦ". { iFrameSteps. }
          iSteps.

      + wp۰cas as _ | [=].
        iSplitR "Hbackoff HΦ". { iFrameSteps. }
        iSteps.

    - iMod "HΦ" as "(%vs & (:model) & _ & HΦ)". injection Heq as <-.
      iDestruct (metaｰagree with "Hmeta Hmeta_") as %<-. iClear "Hmeta_".
      iDestruct (modelｰagree with "Hmodel₁ Hmodel₂") as %->.
      iMod ("HΦ" with "[$Hmodel₁]") as "HΦ"; first iSteps.
      iSplitR "H£ HΦ". { iFrameSteps. }
      iSteps.
  Qed.

  Lemma stack_mpmc_2٠popｰspec t ι :
    <<<
      stack_mpmc_2۰inv t ι
    | ∀∀ vs,
      stack_mpmc_2۰model t vs
    >>>
      stack_mpmc_2٠pop t
      @ ↑ι
    <<<
      stack_mpmc_2۰model t (tail <$> vs)
    | RET default Anything (option۰to_optional ∘ head <$> vs);
      £ 1
    >>>.
  Proof.
    iIntros "%Φ Hinv HΦ".

    wp۰rec.
    wp۰apply+ (stack_mpmc_2٠pop₁ｰspec with "[$Hinv] HΦ"). 1: iSteps.
  Qed.
  Lemma stack_mpmc_2٠popｰspecｰclosed t ι v :
    {{{
      stack_mpmc_2۰inv t ι ∗
      stack_mpmc_2۰closed t
    }}}
      stack_mpmc_2٠pop t
    {{{
      RET §optional٠Anything;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hclosed) HΦ".

    iApply wpｰfupd.
    awp۰apply (stack_mpmc_2٠popｰspec with "Hinv").
    iAaccIntro with "Hclosed"; first iSteps. iIntros "_ !> H£".
    iDestruct (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
    iSteps.
  Qed.

  Lemma stack_mpmc_2٠is_closedｰspec t ι :
    <<<
      stack_mpmc_2۰inv t ι
    | ∀∀ vs,
      stack_mpmc_2۰model t vs
    >>>
      stack_mpmc_2٠is_closed t
      @ ↑ι
    <<<
      stack_mpmc_2۰model t vs
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

      wp۰equal as _ | []%(inj clist۰to_val _ Closed)%list۰to_clist_openｰnotｰclosed.
      iSteps.

    - iMod ("HΦ" with "[$Hmodel₁] H£") as "HΦ"; first iSteps.
      iSplitR "HΦ". { iFrameSteps. }
      iSteps.
  Qed.
  Lemma stack_mpmc_2٠is_closedｰspecｰclosed t ι :
    {{{
      stack_mpmc_2۰inv t ι ∗
      stack_mpmc_2۰closed t
    }}}
      stack_mpmc_2٠is_closed t
    {{{
      RET true;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hclosed) HΦ".

    iApply wpｰfupd.
    awp۰apply (stack_mpmc_2٠is_closedｰspec with "Hinv").
    iAaccIntro with "Hclosed"; first iSteps. iIntros "_ !> H£".
    iDestruct (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
    iSteps.
  Qed.

  Lemma stack_mpmc_2٠closeｰspec t ι :
    <<<
      stack_mpmc_2۰inv t ι
    | ∀∀ vs,
      stack_mpmc_2۰model t vs
    >>>
      stack_mpmc_2٠close t
      @ ↑ι
    <<<
      stack_mpmc_2۰model t None
    | RET from_option list۰to_clist_open Closed vs;
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
  Lemma stack_mpmc_2٠closedｰspecｰclosed t ι v :
    {{{
      stack_mpmc_2۰inv t ι ∗
      stack_mpmc_2۰closed t
    }}}
      stack_mpmc_2٠close t
    {{{
      RET §clist٠Closed;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hclosed) HΦ".

    iApply wpｰfupd.
    awp۰apply (stack_mpmc_2٠closeｰspec with "Hinv").
    iAaccIntro with "Hclosed"; first iSteps. iIntros "_ !> H£".
    iDestruct (lc_fupd_elim_later with "H£ HΦ") as "HΦ".
    iSteps.
  Qed.
End zoo۰G.

Require zoo_saturn.stack_mpmc_2__opaque.

#[global] Opaque stack_mpmc_2۰inv.
#[global] Opaque stack_mpmc_2۰model.
