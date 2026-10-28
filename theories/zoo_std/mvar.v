Require Import zoo.prelude.
Require Import zoo.iris.base_logic.lib.excl.
Require Import zoo.iris.base_logic.lib.oneshot.
Require Import zoo.base.
Require Import zoo_std.option.
Require Export zoo_std.mvar__code.
Require Import zoo_std.mvar__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type v : val.
Implicit Type o state : option val.

Zoo name :=
  { self : location
  ; lstate : gname
  ; consumer : gname
  }.

Zoo global :=
  { lstate : oneshot unit unit
  ; consumer : excl unitO
  }.

Section mvar۰G.
  Context `{mvar۰G : MvarG Σ}.

  Implicit Type Ψ : val → iProp Σ.

  #[local] Definition lstate۰unset' γ_lstate :=
    oneshot۰pending γ_lstate Own ().
  #[local] Definition lstate۰unset γ :=
    lstate۰unset' γ.(mvar۰name۰lstate).
  #[local] Definition lstate۰set' γ_lstate :=
    oneshot۰shot γ_lstate ().
  #[local] Definition lstate۰set γ :=
    lstate۰set' γ.(mvar۰name۰lstate).

  #[local] Definition consumer' γ_consumer :=
    excl γ_consumer ().
  #[local] Definition consumer γ :=
    consumer' γ.(mvar۰name۰consumer).

  #[local] Definition inv۰state۰unset γ :=
    lstate۰unset γ.
  #[local] Instance : CustomIpat "inv۰state۰unset" :=
    " {>;}Hlstate_unset
    ".
  #[local] Definition inv۰state۰set₁ γ Ψ v : iProp Σ :=
      Ψ v
    ∨ consumer γ.
  #[local] Instance : CustomIpat "inv۰state۰set₁" :=
    " [ HΨ
      | Hconsumer{_{}}
      ]
    ".
  #[local] Definition inv۰state۰set₂ γ Ψ v : iProp Σ :=
    lstate۰set γ ∗
    inv۰state۰set₁ γ Ψ v.
  #[local] Instance : CustomIpat "inv۰state۰set₂" :=
    " ( {>;}#Hlstate_set{_{}}
      & Hstate
      )
    ".
  #[local] Definition inv۰state γ Ψ state :=
    match state with
    | None =>
        inv۰state۰unset γ
    | Some v =>
        inv۰state۰set₂ γ Ψ v
    end.

  #[local] Definition inv۰inner γ Ψ : iProp Σ :=
    ∃ state,
    γ.(mvar۰name۰self) ↦ᵣ state ∗
    inv۰state γ Ψ state.
  #[local] Instance : CustomIpat "inv۰inner" :=
    " ( %state
      & Hself
      & Hstate
      )
    ".
  Please Definition mvar۰inv γ Ψ : iProp Σ :=
    inv nroot (inv۰inner γ Ψ).
  #[local] Instance : CustomIpat "inv" :=
    " #Hinv
    ".

  Please Definition mvar۰consumer :=
    consumer.
  #[local] Instance : CustomIpat "consumer" :=
    " Hconsumer{_{}}
    ".

  Please Definition mvar۰resolved :=
    lstate۰set.
  #[local] Instance : CustomIpat "resolved" :=
    " #Hlstate_set{_{}}
    ".

  #[global] Instance mvar۰invｰcontractive γ n :
    Proper (
      (pointwise_relation _ $ dist_later n) ==>
      (≡{n}≡)
    ) (mvar۰inv γ).
  Proof.
    rewrite /mvar۰inv /inv۰inner /inv۰state /inv۰state۰unset /inv۰state۰set₂ /inv۰state۰set₁.
    solve_contractive.
  Qed.
  #[global] Instance mvar۰invｰproper γ :
    Proper (
      pointwise_relation _ (≡) ==>
      (≡)
    ) (mvar۰inv γ).
  Proof.
    rewrite /mvar۰inv /inv۰inner /inv۰state /inv۰state۰unset /inv۰state۰set₂ /inv۰state۰set₁.
    solve_proper.
  Qed.

  Zoo derive Timeless for mvar۰resolved.

  Zoo derive Persistent for mvar۰inv.
  Zoo derive Persistent for mvar۰resolved.

  #[local] Lemma lstateｰalloc :
    ⊢ |==>
      ∃ γ_lstate,
      lstate۰unset' γ_lstate.
  Proof.
    apply oneshotｰalloc.
  Qed.
  #[local] Lemma lstateｰunsetｰset γ :
    lstate۰unset γ -∗
    lstate۰set γ -∗
    False.
  Proof.
    apply oneshotｰpendingｰshot.
  Qed.
  #[local] Lemma lstateｰupdate γ :
    lstate۰unset γ ⊢ |==>
    lstate۰set γ.
  Proof.
    apply oneshotｰupdateｰshot.
  Qed.

  #[local] Lemma consumerｰalloc :
    ⊢ |==>
      ∃ γ_consumer,
      consumer' γ_consumer.
  Proof.
    apply exclｰalloc.
  Qed.
  #[local] Lemma consumerｰexclusive γ :
    consumer γ -∗
    consumer γ -∗
    False.
  Proof.
    apply exclｰexclusive.
  Qed.

  Lemma mvar۰consumerｰexclusive γ :
    mvar۰consumer γ -∗
    mvar۰consumer γ -∗
    False.
  Proof.
    apply consumerｰexclusive.
  Qed.

  Lemma mvar٠createｰspec Ψ :
    {{{
      True
    }}}
      mvar٠create ()
    {{{
      γ
    , RET γ;
      mvar۰inv γ Ψ ∗
      mvar۰consumer γ
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp۰rec.
    wp۰ref t as "Ht".

    iMod lstateｰalloc as "(%γ_lstate & Hlstate_unset)".
    iMod consumerｰalloc as "(%γ_consumer & Hconsumer)".

    pose γ :=
      {|mvar۰name۰self := t
      ; mvar۰name۰lstate := γ_lstate
      ; mvar۰name۰consumer := γ_consumer
      |}.

    iApply ("HΦ" $! γ).
    iFrameSteps. iExists None. iSteps.
  Qed.

  Lemma mvar٠makeｰspec Ψ v :
    {{{
      ▷ Ψ v
    }}}
      mvar٠make v
    {{{
      γ
    , RET γ;
      mvar۰inv γ Ψ ∗
      mvar۰resolved γ ∗
      mvar۰consumer γ
    }}}.
  Proof.
    iIntros "%Φ HΨ HΦ".

    wp۰rec.
    wp۰ref t as "Ht".

    iMod lstateｰalloc as "(%γ_lstate & Hlstate_unset)".
    iMod consumerｰalloc as "(%γ_consumer & Hconsumer)".

    pose γ :=
      {|mvar۰name۰self := t
      ; mvar۰name۰lstate := γ_lstate
      ; mvar۰name۰consumer := γ_consumer
      |}.

    iMod (lstateｰupdate γ with "Hlstate_unset") as "#Hlstate_set".

    iApply ("HΦ" $! γ).
    iFrameSteps. iExists (Some v). iSteps.
  Qed.

  Lemma mvar٠try_getｰspec γ Ψ :
    {{{
      mvar۰inv γ Ψ
    }}}
      mvar٠try_get γ
    {{{
      o
    , RET o;
      if o then
        mvar۰resolved γ
      else
        True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰rec.

    iInv "Hinv" as "(:inv۰inner)".
    wp۰load.
    iSpecialize ("HΦ" $! state).
    destruct state as [v |].

    - iDestruct "Hstate" as "(:inv۰state۰set₂)".
      iSplitR "HΦ". { iFrameSteps 2. }
      iSteps.

    - iSplitR "HΦ". { iFrameSteps. }
      iSteps.
  Qed.
  Lemma mvar٠try_getｰspecｰresolved γ Ψ :
    {{{
      mvar۰inv γ Ψ ∗
      mvar۰resolved γ
    }}}
      mvar٠try_get γ
    {{{
      v
    , RET Some v;
      True
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & (:resolved)) HΦ".

    wp۰rec.

    iInv "Hinv" as "(:inv۰inner)".
    wp۰load.
    destruct state as [v |].

    - iSplitR "HΦ". { iFrameSteps. }
      iSteps.

    - iDestruct "Hstate" as "(:inv۰state۰unset)".
      iDestruct (lstateｰunsetｰset with "Hlstate_unset Hlstate_set") as %[].
  Qed.
  Lemma mvar٠try_getｰspecｰconsumer γ Ψ :
    {{{
      mvar۰inv γ Ψ ∗
      mvar۰consumer γ
    }}}
      mvar٠try_get γ
    {{{
      o
    , RET o;
      if o is Some v then
        mvar۰resolved γ ∗
        Ψ v
      else
        True
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & (:consumer)) HΦ".

    wp۰rec.

    iInv "Hinv" as "(:inv۰inner)".
    wp۰load.
    iSpecialize ("HΦ" $! state).
    destruct state as [v |].

    - iDestruct "Hstate" as "(:inv۰state۰set₂)".
      iDestruct "Hstate" as "(:inv۰state۰set₁ =1)"; last first.
      { iDestruct (consumerｰexclusive with "Hconsumer Hconsumer_1") as %[]. }
      iSplitR "HΨ HΦ". { iFrameSteps. }
      iSteps.

    - iSplitR "HΦ". { iFrameSteps. }
      iSteps.
  Qed.
  Lemma mvar٠try_getｰspecｰresolvedｰconsumer γ Ψ :
    {{{
      mvar۰inv γ Ψ ∗
      mvar۰resolved γ ∗
      mvar۰consumer γ
    }}}
      mvar٠try_get γ
    {{{
      v
    , RET Some v;
      Ψ v
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & (:resolved) & (:consumer)) HΦ".

    wp۰rec.

    iInv "Hinv" as "(:inv۰inner)".
    wp۰load.
    destruct state as [v |].

    - iDestruct "Hstate" as "(:inv۰state۰set₂ =1)".
      iDestruct "Hstate" as "(:inv۰state۰set₁ =1)"; last first.
      { iDestruct (consumerｰexclusive with "Hconsumer Hconsumer_1") as %[]. }
      iSplitR "HΨ HΦ". { iFrameSteps. }
      iSteps.

    - iDestruct "Hstate" as "(:inv۰state۰unset)".
      iDestruct (lstateｰunsetｰset with "Hlstate_unset Hlstate_set") as %[].
  Qed.

  Lemma mvar٠is_unsetｰspec γ Ψ :
    {{{
      mvar۰inv γ Ψ
    }}}
      mvar٠is_unset γ
    {{{
      b
    , RET #b;
      if b then
        True
      else
        mvar۰resolved γ
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".

    wp۰rec.
    wp۰apply (mvar٠try_getｰspec with "Hinv") as ([v |]) "H".
    all: iSteps.
  Qed.
  Lemma mvar٠is_unsetｰspecｰresolved γ Ψ :
    {{{
      mvar۰inv γ Ψ ∗
      mvar۰resolved γ
    }}}
      mvar٠is_unset γ
    {{{
      RET false;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hresolved) HΦ".

    wp۰rec.
    wp۰apply (mvar٠try_getｰspecｰresolved with "[$Hinv $Hresolved]").
    iSteps.
  Qed.

  Lemma mvar٠is_setｰspec γ Ψ :
    {{{
      mvar۰inv γ Ψ
    }}}
      mvar٠is_set γ
    {{{
      b
    , RET #b;
      if b then
        mvar۰resolved γ
      else
        True
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".

    wp۰rec.
    wp۰apply (mvar٠is_unsetｰspec with "[$]") as (b) "Hb".
    destruct b; iSteps.
  Qed.
  Lemma mvar٠is_setｰspecｰresolved γ Ψ :
    {{{
      mvar۰inv γ Ψ ∗
      mvar۰resolved γ
    }}}
      mvar٠is_set γ
    {{{
      RET true;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & #Hresolved) HΦ".

    wp۰rec.
    wp۰apply (mvar٠is_unsetｰspecｰresolved with "[$]").
    iSteps.
  Qed.

  Lemma mvar٠getｰspec γ Ψ :
    {{{
      mvar۰inv γ Ψ ∗
      mvar۰resolved γ
    }}}
      mvar٠get γ
    {{{
      v
    , RET v;
      True
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & Hresolved) HΦ".

    wp۰rec.
    wp۰apply (mvar٠try_getｰspecｰresolved with "[$Hinv $Hresolved]").
    iSteps.
  Qed.

  Lemma mvar٠setｰspec γ Ψ v :
    {{{
      mvar۰inv γ Ψ ∗
      ▷ Ψ v
    }}}
      mvar٠set γ v
    {{{
      RET ();
      mvar۰resolved γ
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & HΨ) HΦ".

    wp۰rec. wp۰pures.

    iInv "Hinv" as "(:inv۰inner)".
    wp۰store.
    destruct state as [w |].

    - iDestruct "Hstate" as "(:inv۰state۰set₂)".
      iSplitR "HΦ". { iExists (Some v). iFrameSteps. }
      iSteps.

    - iDestruct "Hstate" as "(:inv۰state۰unset)".
      iMod (lstateｰupdate with "Hlstate_unset") as "#Hlstate_set".
      iSplitR "HΦ". { iExists (Some v). iFrameSteps. }
      iSteps.
  Qed.
End mvar۰G.

Require zoo_std.mvar__opaque.

Please opacify.
