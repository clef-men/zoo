Require Import zoo.prelude.
Require Import zoo.iris.base_logic.lib.excl.
Require Import zoo.iris.base_logic.lib.oneshot.
Require Import zoo.base.
Require Export zoo_std.flag_mpsc__code.
Require Import zoo_std.flag_mpsc__types.
Require Import zoo.options.

Implicit Type b : bool.

Zoo name :=
  { self : location
  ; state : gname
  ; consumer : gname
  }.

Zoo global :=
  { state : oneshot () ()
  ; consumer : excl unitO
  }.

Section flag_mpsc۰G.
  Context `{flag_mpsc۰G : FlagMpscG Σ}.

  Implicit Type P : iProp Σ.

  #[local] Definition state۰unset' γ_state :=
    oneshot۰pending γ_state Own ().
  #[local] Definition state۰unset γ :=
    state۰unset' γ.(flag_mpsc۰name۰state).
  #[local] Definition state۰set' γ_state :=
    oneshot۰shot γ_state ().
  #[local] Definition state۰set γ :=
    state۰set' γ.(flag_mpsc۰name۰state).

  #[local] Definition consumer' γ_consumer :=
    excl γ_consumer ().
  #[local] Definition consumer γ :=
    consumer' γ.(flag_mpsc۰name۰consumer).

  #[local] Definition inv۰consumer γ P : iProp Σ :=
    P ∨ consumer γ.
  #[local] Instance : CustomIpat "inv۰consumer" :=
    " [ HP
      | Hconsumer{_{!}}
      ]
    ".
  #[local] Definition inv۰set γ P : iProp Σ :=
    state۰set γ ∗
    inv۰consumer γ P.
  #[local] Instance : CustomIpat "inv۰set" :=
    " ( #Hstate_set
      & Hinv_consumer
      )
    ".
  #[local] Definition inv۰inner γ P : iProp Σ :=
    ∃ b,
    γ.(flag_mpsc۰name۰self) ↦ᵣ #b ∗
    if b then
      inv۰set γ P
    else
      state۰unset γ.
  #[local] Instance : CustomIpat "inv۰inner" :=
    " ( %b
      & >Hself
      & Hb
      )
    ".
  Please Definition flag_mpsc۰inv γ P :=
    inv nroot (inv۰inner γ P).
  #[local] Instance : CustomIpat "inv" :=
    " #Hinv
    ".

  Please Definition flag_mpsc۰consumer :=
    consumer.
  #[local] Instance : CustomIpat "consumer" :=
    " Hconsumer
    ".

  Please Definition flag_mpsc۰resolved :=
    state۰set.
  #[local] Instance : CustomIpat "resolved" :=
    " #Hstate_set
    ".

  #[global] Instance flag_mpsc۰invｰcontractive γ :
    Contractive (flag_mpsc۰inv γ).
  Proof.
    rewrite /flag_mpsc۰inv /inv۰inner /inv۰set  /inv۰consumer.
    solve_contractive.
  Qed.
  #[global] Instance flag_mpsc۰invｰne γ :
    NonExpansive (flag_mpsc۰inv γ).
  Proof.
    apply _.
  Qed.
  #[global] Instance flag_mpsc۰invｰproper γ :
    Proper ((≡) ==> (≡)) (flag_mpsc۰inv γ).
  Proof.
    apply _.
  Qed.

  Zoo derive Timeless for flag_mpsc۰consumer.
  Zoo derive Timeless for flag_mpsc۰resolved.

  Zoo derive Persistent for flag_mpsc۰inv.
  Zoo derive Persistent for flag_mpsc۰resolved.

  #[local] Lemma stateｰalloc :
    ⊢ |==>
      ∃ γ_state,
      state۰unset' γ_state.
  Proof.
    apply: oneshotｰalloc.
  Qed.
  #[local] Lemma stateｰunsetｰset γ :
    state۰unset γ -∗
    state۰set γ -∗
    False.
  Proof.
    apply oneshotｰpendingｰshot.
  Qed.
  #[local] Lemma stateｰupdate γ :
    state۰unset γ ⊢ |==>
    state۰set γ.
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

  Lemma flag_mpsc۰consumerｰexclusive γ :
    flag_mpsc۰consumer γ -∗
    flag_mpsc۰consumer γ -∗
    False.
  Proof.
    apply consumerｰexclusive.
  Qed.

  Lemma flag_mpsc٠createｰspec P :
    {{{
      True
    }}}
      flag_mpsc٠create ()
    {{{
      γ
    , RET γ;
      flag_mpsc۰inv γ P ∗
      flag_mpsc۰consumer γ
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp۰rec.
    wp۰ref t as "Ht".

    iMod stateｰalloc as "(%γ_state & Hstate_unset)".
    iMod consumerｰalloc as "(%γ_consumer & Hconsumer)".

    pose γ :=
      {|flag_mpsc۰name۰self := t
      ; flag_mpsc۰name۰state := γ_state
      ; flag_mpsc۰name۰consumer := γ_consumer
      |}.

    iApply ("HΦ" $! γ).
    iFrameSteps.
  Qed.

  Lemma flag_mpsc٠getｰspec γ P :
    {{{
      flag_mpsc۰inv γ P ∗
      flag_mpsc۰consumer γ
    }}}
      flag_mpsc٠get γ
    {{{
      b
    , RET #b;
      if b then
        P
      else
        flag_mpsc۰consumer γ
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & (:consumer)) HΦ".

    wp۰rec credit:"H£".

    iInv "Hinv" as "(:inv۰inner)".
    wp۰load.
    destruct b.

    - iDestruct "Hb" as "(:inv۰set)".
      iDestruct "Hinv_consumer" as "(:inv۰consumer !=)".
      + iFrameSteps.
      + iDestruct (consumerｰexclusive with "Hconsumer Hconsumer_") as %[].

    - iFrameSteps.
  Qed.

  Lemma flag_mpsc٠setｰspec γ P :
    {{{
      flag_mpsc۰inv γ P ∗
      ▷ P
    }}}
      flag_mpsc٠set γ
    {{{
      RET ();
      flag_mpsc۰resolved γ
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & HP) HΦ".

    wp۰rec.

    iInv "Hinv" as "(:inv۰inner)".
    wp۰store.
    destruct b. 1: iFrameSteps.
    iMod (stateｰupdate with "Hb") as "#Hstate_set".
    iFrameSteps.
  Qed.
End flag_mpsc۰G.

Require zoo_std.flag_mpsc__opaque.

Please opacify.
