Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Import zoo.iris.base_logic.lib.excl.
Require Import zoo.iris.base_logic.lib.oneshot.
Require Import zoo.base.
Require Export zoo_std.flag_mpsc__code.
Require Import zoo_std.flag_mpsc__types.
Require Import zoo.options.

Implicit Type b : bool.

Class FlagMpscG Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] flag_mpsc۰G۰state۰G :: OneshotG Σ () ()
  ; #[local] flag_mpsc۰G۰consumer۰G :: ExclG Σ unitO
  }.

Definition flag_mpsc۰Σ :=
  #[oneshot۰Σ () ()
  ; excl۰Σ unitO
  ].
#[global] Instance subGｰflag_mpsc۰Σ `{zoo۰G : !ZooG Σ} :
  subG flag_mpsc۰Σ Σ →
  FlagMpscG Σ.
Proof.
  solve_inG.
Qed.

Module base.
  Section flag_mpsc۰G.
    Context `{flag_mpsc۰G : FlagMpscG Σ}.

    Implicit Type t : location.
    Implicit Type P : iProp Σ.

    Record flag_mpsc۰name :=
      { flag_mpsc۰name۰state : gname
      ; flag_mpsc۰name۰consumer : gname
      }.
    Implicit Type γ : flag_mpsc۰name.

    #[global] Instance flag_mpsc۰nameｰeq_dec : EqDecision flag_mpsc۰name :=
      ltac:(solve_decision).
    #[global] Instance flag_mpsc۰nameｰcountable :
      Countable flag_mpsc۰name.
    Proof.
      solve_countable.
    Qed.

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
    Definition flag_mpsc۰inv t γ P :=
      inv nroot (inv۰inner t γ P).
    #[local] Instance : CustomIpat "inv" :=
      " #Hinv
      ".

    Definition flag_mpsc۰consumer :=
      consumer.
    #[local] Instance : CustomIpat "consumer" :=
      " Hconsumer
      ".

    Definition flag_mpsc۰resolved :=
      state۰set.
    #[local] Instance : CustomIpat "resolved" :=
      " #Hstate_set
      ".

    #[global] Instance flag_mpsc۰invｰcontractive t γ :
      Contractive (flag_mpsc۰inv t γ).
    Proof.
      rewrite /flag_mpsc۰inv /inv۰inner /inv۰set  /inv۰consumer.
      solve_contractive.
    Qed.
    #[global] Instance flag_mpsc۰invｰne t γ :
      NonExpansive (flag_mpsc۰inv t γ).
    Proof.
      apply _.
    Qed.
    #[global] Instance flag_mpsc۰invｰproper t γ :
      Proper ((≡) ==> (≡)) (flag_mpsc۰inv t γ).
    Proof.
      apply _.
    Qed.

    #[global] Instance flag_mpsc۰consumerｰtimeless γ :
      Timeless (flag_mpsc۰consumer γ).
    Proof.
      apply _.
    Qed.
    #[global] Instance flag_mpsc۰resolvedｰtimeless γ :
      Timeless (flag_mpsc۰resolved γ).
    Proof.
      apply _.
    Qed.

    #[global] Instance flag_mpsc۰invｰpersistent t γ P :
      Persistent (flag_mpsc۰inv t γ P).
    Proof.
      apply _.
    Qed.
    #[global] Instance flag_mpsc۰resolvedｰpersistent γ :
      Persistent (flag_mpsc۰resolved γ).
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
        t γ
      , RET #t;
        meta_token t ⊤ ∗
        flag_mpsc۰inv t γ P ∗
        flag_mpsc۰consumer γ
      }}}.
    Proof.
      iIntros "%Φ _ HΦ".

      wp۰rec.
      wp۰ref t as "Ht" "Hmeta".

      iMod stateｰalloc as "(%γ_state & Hstate_unset)".
      iMod consumerｰalloc as "(%γ_consumer & Hconsumer)".

      pose γ :=
        {|flag_mpsc۰name۰state := γ_state
        ; flag_mpsc۰name۰consumer := γ_consumer
        |}.

      iApply ("HΦ" $! t γ).
      iFrameSteps.
    Qed.

    Lemma flag_mpsc٠getｰspec t γ P :
      {{{
        flag_mpsc۰inv t γ P ∗
        flag_mpsc۰consumer γ
      }}}
        flag_mpsc٠get #t
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

    Lemma flag_mpsc٠setｰspec t γ P :
      {{{
        flag_mpsc۰inv t γ P ∗
        ▷ P
      }}}
        flag_mpsc٠set #t
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

  #[global] Opaque flag_mpsc۰inv.
  #[global] Opaque flag_mpsc۰consumer.
  #[global] Opaque flag_mpsc۰resolved.
End base.

Require zoo_std.flag_mpsc__opaque.

Section flag_mpsc۰G.
  Context `{flag_mpsc۰G : FlagMpscG Σ}.

  Implicit Type 𝑡 : location.
  Implicit Type t : val.
  Implicit Type P : iProp Σ.

  Definition flag_mpsc۰inv t P : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.flag_mpsc۰inv 𝑡 γ P.
  #[local] Instance : CustomIpat "inv" :=
    " ( %l{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hinv{_{}}
      )
    ".

  Definition flag_mpsc۰consumer t : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.flag_mpsc۰consumer γ.
  #[local] Instance : CustomIpat "consumer" :=
    " ( %l{;_}
      & %γ{;_}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hconsumer{_{}}
      )
    ".

  Definition flag_mpsc۰resolved t : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.flag_mpsc۰resolved γ.
  #[local] Instance : CustomIpat "resolved" :=
    " ( %l{;_}
      & %γ{;_}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hresolved{_{}}
      )
    ".

  #[global] Instance flag_mpsc۰invｰcontractive t :
    Contractive (flag_mpsc۰inv t).
  Proof.
    solve_contractive.
  Qed.
  #[global] Instance flag_mpsc۰invｰne t :
    NonExpansive (flag_mpsc۰inv t).
  Proof.
    apply _.
  Qed.
  #[global] Instance flag_mpsc۰invｰproper t :
    Proper ((≡) ==> (≡)) (flag_mpsc۰inv t).
  Proof.
    apply _.
  Qed.

  #[global] Instance flag_mpsc۰consumerｰtimeless t :
    Timeless (flag_mpsc۰consumer t).
  Proof.
    apply _.
  Qed.
  #[global] Instance flag_mpsc۰resolvedｰtimeless t :
    Timeless (flag_mpsc۰resolved t).
  Proof.
    apply _.
  Qed.

  #[global] Instance flag_mpsc۰invｰpersistent t P :
    Persistent (flag_mpsc۰inv t P).
  Proof.
    apply _.
  Qed.
  #[global] Instance flag_mpsc۰resolvedｰpersistent t :
    Persistent (flag_mpsc۰resolved t).
  Proof.
    apply _.
  Qed.

  Lemma flag_mpsc۰consumerｰexclusive t :
    flag_mpsc۰consumer t -∗
    flag_mpsc۰consumer t -∗
    False.
  Proof.
    iIntros "(:consumer =1) (:consumer =2)". simp.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.flag_mpsc۰consumerｰexclusive with "Hconsumer_1 Hconsumer_2").
  Qed.

  Lemma flag_mpsc٠createｰspec P :
    {{{
      True
    }}}
      flag_mpsc٠create ()
    {{{
      t
    , RET t;
      flag_mpsc۰inv t P ∗
      flag_mpsc۰consumer t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    iApply wpｰfupd.
    wp۰apply (base.flag_mpsc٠createｰspec with "[//]") as (𝑡 γ) "(Hmeta & Hinv & Hconsumer)".
    iMod (metaｰset γ with "Hmeta") as "#Hmeta"; first done.
    iSteps.
  Qed.

  Lemma flag_mpsc٠getｰspec t P :
    {{{
      flag_mpsc۰inv t P ∗
      flag_mpsc۰consumer t
    }}}
      flag_mpsc٠get t
    {{{
      b
    , RET #b;
      if b then
        P
      else
        flag_mpsc۰consumer t
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:consumer =2)) HΦ". simp.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp۰apply (base.flag_mpsc٠getｰspec with "[$]") as (b) "Hb".
    destruct b; iSteps.
  Qed.

  Lemma flag_mpsc٠setｰspec t P :
    {{{
      flag_mpsc۰inv t P ∗
      ▷ P
    }}}
      flag_mpsc٠set t
    {{{
      RET ();
      flag_mpsc۰resolved t
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & HP) HΦ".

    wp۰apply (base.flag_mpsc٠setｰspec _ _ P with "[$]").
    iSteps.
  Qed.
End flag_mpsc۰G.

#[global] Opaque flag_mpsc۰inv.
#[global] Opaque flag_mpsc۰consumer.
#[global] Opaque flag_mpsc۰resolved.
