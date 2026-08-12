Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Import zoo.iris.base_logic.lib.excl.
Require Import zoo.iris.base_logic.lib.oneshot.
Require Import zoo.base.
Require Export zoo_std.mpsc_flag__code.
Require Import zoo_std.mpsc_flag__types.
Require Import zoo.options.

Implicit Type b : bool.

Class MpscFlagG Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] mpsc_flag۰G۰state۰G :: OneshotG Σ () ()
  ; #[local] mpsc_flag۰G۰consumer۰G :: ExclG Σ unitO
  }.

Definition mpsc_flag۰Σ :=
  #[oneshot۰Σ () ()
  ; excl۰Σ unitO
  ].
#[global] Instance subGｰmpsc_flag۰Σ `{zoo۰G : !ZooG Σ} :
  subG mpsc_flag۰Σ Σ →
  MpscFlagG Σ.
Proof.
  solve_inG.
Qed.

Module base.
  Section mpsc_flag۰G.
    Context `{mpsc_flag۰G : MpscFlagG Σ}.

    Implicit Type t : location.
    Implicit Type P : iProp Σ.

    Record mpsc_flag۰name :=
      { mpsc_flag۰name۰state : gname
      ; mpsc_flag۰name۰consumer : gname
      }.
    Implicit Type γ : mpsc_flag۰name.

    #[global] Instance mpsc_flag۰nameｰeq_dec : EqDecision mpsc_flag۰name :=
      ltac:(solve_decision).
    #[global] Instance mpsc_flag۰nameｰcountable :
      Countable mpsc_flag۰name.
    Proof.
      solve_countable.
    Qed.

    #[local] Definition state۰unset' γ_state :=
      oneshot۰pending γ_state Own ().
    #[local] Definition state۰unset γ :=
      state۰unset' γ.(mpsc_flag۰name۰state).
    #[local] Definition state۰set' γ_state :=
      oneshot۰shot γ_state ().
    #[local] Definition state۰set γ :=
      state۰set' γ.(mpsc_flag۰name۰state).

    #[local] Definition consumer' γ_consumer :=
      excl γ_consumer ().
    #[local] Definition consumer γ :=
      consumer' γ.(mpsc_flag۰name۰consumer).

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
    #[local] Definition inv۰inner t γ P : iProp Σ :=
      ∃ b,
      t ↦ᵣ #b ∗
      if b then
        inv۰set γ P
      else
        state۰unset γ.
    #[local] Instance : CustomIpat "inv۰inner" :=
      " ( %b
        & >Ht
        & Hb
        )
      ".
    Definition mpsc_flag۰inv t γ P :=
      inv nroot (inv۰inner t γ P).
    #[local] Instance : CustomIpat "inv" :=
      " #Hinv
      ".

    Definition mpsc_flag۰consumer :=
      consumer.
    #[local] Instance : CustomIpat "consumer" :=
      " Hconsumer
      ".

    Definition mpsc_flag۰resolved :=
      state۰set.
    #[local] Instance : CustomIpat "resolved" :=
      " #Hstate_set
      ".

    #[global] Instance mpsc_flag۰invｰcontractive t γ :
      Contractive (mpsc_flag۰inv t γ).
    Proof.
      rewrite /mpsc_flag۰inv /inv۰inner /inv۰set  /inv۰consumer.
      solve_contractive.
    Qed.
    #[global] Instance mpsc_flag۰invｰne t γ :
      NonExpansive (mpsc_flag۰inv t γ).
    Proof.
      apply _.
    Qed.
    #[global] Instance mpsc_flag۰invｰproper t γ :
      Proper ((≡) ==> (≡)) (mpsc_flag۰inv t γ).
    Proof.
      apply _.
    Qed.

    #[global] Instance mpsc_flag۰consumerｰtimeless γ :
      Timeless (mpsc_flag۰consumer γ).
    Proof.
      apply _.
    Qed.
    #[global] Instance mpsc_flag۰resolvedｰtimeless γ :
      Timeless (mpsc_flag۰resolved γ).
    Proof.
      apply _.
    Qed.

    #[global] Instance mpsc_flag۰invｰpersistent t γ P :
      Persistent (mpsc_flag۰inv t γ P).
    Proof.
      apply _.
    Qed.
    #[global] Instance mpsc_flag۰resolvedｰpersistent γ :
      Persistent (mpsc_flag۰resolved γ).
    Proof.
      apply _.
    Qed.

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

    Lemma mpsc_flag۰consumerｰexclusive γ :
      mpsc_flag۰consumer γ -∗
      mpsc_flag۰consumer γ -∗
      False.
    Proof.
      apply consumerｰexclusive.
    Qed.

    Lemma mpsc_flag٠createｰspec P :
      {{{
        True
      }}}
        mpsc_flag٠create ()
      {{{
        t γ
      , RET #t;
        meta_token t ⊤ ∗
        mpsc_flag۰inv t γ P ∗
        mpsc_flag۰consumer γ
      }}}.
    Proof.
      iIntros "%Φ _ HΦ".

      wp۰rec.
      wp۰ref t as "Ht" "Hmeta".

      iMod stateｰalloc as "(%γ_state & Hstate_unset)".
      iMod consumerｰalloc as "(%γ_consumer & Hconsumer)".

      pose γ :=
        {|mpsc_flag۰name۰state := γ_state
        ; mpsc_flag۰name۰consumer := γ_consumer
        |}.

      iApply ("HΦ" $! t γ).
      iFrameSteps.
    Qed.

    Lemma mpsc_flag٠getｰspec t γ P :
      {{{
        mpsc_flag۰inv t γ P ∗
        mpsc_flag۰consumer γ
      }}}
        mpsc_flag٠get #t
      {{{
        b
      , RET #b;
        if b then
          P
        else
          mpsc_flag۰consumer γ
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

    Lemma mpsc_flag٠setｰspec t γ P :
      {{{
        mpsc_flag۰inv t γ P ∗
        ▷ P
      }}}
        mpsc_flag٠set #t
      {{{
        RET ();
        mpsc_flag۰resolved γ
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
  End mpsc_flag۰G.

  #[global] Opaque mpsc_flag۰inv.
  #[global] Opaque mpsc_flag۰consumer.
  #[global] Opaque mpsc_flag۰resolved.
End base.

Require zoo_std.mpsc_flag__opaque.

Section mpsc_flag۰G.
  Context `{mpsc_flag۰G : MpscFlagG Σ}.

  Implicit Type 𝑡 : location.
  Implicit Type t : val.
  Implicit Type P : iProp Σ.

  Definition mpsc_flag۰inv t P : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.mpsc_flag۰inv 𝑡 γ P.
  #[local] Instance : CustomIpat "inv" :=
    " ( %l{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hinv{_{}}
      )
    ".

  Definition mpsc_flag۰consumer t : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.mpsc_flag۰consumer γ.
  #[local] Instance : CustomIpat "consumer" :=
    " ( %l{;_}
      & %γ{;_}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hconsumer{_{}}
      )
    ".

  Definition mpsc_flag۰resolved t : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.mpsc_flag۰resolved γ.
  #[local] Instance : CustomIpat "resolved" :=
    " ( %l{;_}
      & %γ{;_}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hresolved{_{}}
      )
    ".

  #[global] Instance mpsc_flag۰invｰcontractive t :
    Contractive (mpsc_flag۰inv t).
  Proof.
    solve_contractive.
  Qed.
  #[global] Instance mpsc_flag۰invｰne t :
    NonExpansive (mpsc_flag۰inv t).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpsc_flag۰invｰproper t :
    Proper ((≡) ==> (≡)) (mpsc_flag۰inv t).
  Proof.
    apply _.
  Qed.

  #[global] Instance mpsc_flag۰consumerｰtimeless t :
    Timeless (mpsc_flag۰consumer t).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpsc_flag۰resolvedｰtimeless t :
    Timeless (mpsc_flag۰resolved t).
  Proof.
    apply _.
  Qed.

  #[global] Instance mpsc_flag۰invｰpersistent t P :
    Persistent (mpsc_flag۰inv t P).
  Proof.
    apply _.
  Qed.
  #[global] Instance mpsc_flag۰resolvedｰpersistent t :
    Persistent (mpsc_flag۰resolved t).
  Proof.
    apply _.
  Qed.

  Lemma mpsc_flag۰consumerｰexclusive t :
    mpsc_flag۰consumer t -∗
    mpsc_flag۰consumer t -∗
    False.
  Proof.
    iIntros "(:consumer =1) (:consumer =2)". simp.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.mpsc_flag۰consumerｰexclusive with "Hconsumer_1 Hconsumer_2").
  Qed.

  Lemma mpsc_flag٠createｰspec P :
    {{{
      True
    }}}
      mpsc_flag٠create ()
    {{{
      t
    , RET t;
      mpsc_flag۰inv t P ∗
      mpsc_flag۰consumer t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    iApply wpｰfupd.
    wp۰apply (base.mpsc_flag٠createｰspec with "[//]") as (𝑡 γ) "(Hmeta & Hinv & Hconsumer)".
    iMod (metaｰset γ with "Hmeta") as "#Hmeta"; first done.
    iSteps.
  Qed.

  Lemma mpsc_flag٠getｰspec t P :
    {{{
      mpsc_flag۰inv t P ∗
      mpsc_flag۰consumer t
    }}}
      mpsc_flag٠get t
    {{{
      b
    , RET #b;
      if b then
        P
      else
        mpsc_flag۰consumer t
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:consumer =2)) HΦ". simp.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp۰apply (base.mpsc_flag٠getｰspec with "[$]") as (b) "Hb".
    destruct b; iSteps.
  Qed.

  Lemma mpsc_flag٠setｰspec t P :
    {{{
      mpsc_flag۰inv t P ∗
      ▷ P
    }}}
      mpsc_flag٠set t
    {{{
      RET ();
      mpsc_flag۰resolved t
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & HP) HΦ".

    wp۰apply (base.mpsc_flag٠setｰspec _ _ P with "[$]").
    iSteps.
  Qed.
End mpsc_flag۰G.

#[global] Opaque mpsc_flag۰inv.
#[global] Opaque mpsc_flag۰consumer.
#[global] Opaque mpsc_flag۰resolved.
