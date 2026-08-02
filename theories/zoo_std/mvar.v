Require Import zoo.prelude.
Require Import zoo.common.countable.
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

Class MvarG Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] mvar۰G۰lstate۰G :: OneshotG Σ unit unit
  ; #[local] mvar۰G۰consumer۰G :: ExclG Σ unitO
  }.

Definition mvar۰Σ :=
  #[oneshot۰Σ unit unit
  ; excl۰Σ unitO
  ].
#[global] Instance subGｰmvar۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG mvar۰Σ Σ →
  MvarG Σ .
Proof.
  solve_inG.
Qed.

Module base.
  Section mvar۰G.
    Context `{mvar۰G : MvarG Σ}.

    Implicit Type t : location.
    Implicit Type Ψ : val → iProp Σ.

    Record mvar۰name :=
      { mvar۰name۰lstate : gname
      ; mvar۰name۰consumer : gname
      }.
    Implicit Type γ : mvar۰name.

    #[global] Instance mvar۰nameｰeq_dec : EqDecision mvar۰name :=
      ltac:(solve_decision).
    #[global] Instance mvar۰nameｰcountable :
      Countable mvar۰name.
    Proof.
      solve_countable.
    Qed.

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

    #[local] Definition inv۰inner t γ Ψ : iProp Σ :=
      ∃ state,
      t ↦ᵣ state ∗
      inv۰state γ Ψ state.
    #[local] Instance : CustomIpat "inv۰inner" :=
      " ( %state
        & Ht
        & Hstate
        )
      ".
    Definition mvar۰inv t γ Ψ : iProp Σ :=
      inv nroot (inv۰inner t γ Ψ).
    #[local] Instance : CustomIpat "inv" :=
      " #Hinv
      ".

    Definition mvar۰consumer :=
      consumer.
    #[local] Instance : CustomIpat "consumer" :=
      " Hconsumer{_{}}
      ".

    Definition mvar۰resolved :=
      lstate۰set.
    #[local] Instance : CustomIpat "resolved" :=
      " #Hlstate_set{_{}}
      ".

    #[global] Instance mvar۰invｰcontractive t γ n :
      Proper (
        (pointwise_relation _ (dist_later n)) ==>
        (≡{n}≡)
      ) (mvar۰inv t γ).
    Proof.
      rewrite /mvar۰inv /inv۰inner /inv۰state /inv۰state۰unset /inv۰state۰set₂ /inv۰state۰set₁.
      solve_contractive.
    Qed.
    #[global] Instance mvar۰invｰproper t γ :
      Proper (
        (pointwise_relation _ (≡)) ==>
        (≡)
      ) (mvar۰inv t γ).
    Proof.
      rewrite /mvar۰inv /inv۰inner /inv۰state /inv۰state۰unset /inv۰state۰set₂ /inv۰state۰set₁.
      solve_proper.
    Qed.

    #[global] Instance mvar۰resolvedｰtimeless γ :
      Timeless (mvar۰resolved γ).
    Proof.
      apply _.
    Qed.

    #[global] Instance mvar۰invｰpersistent t γ Ψ :
      Persistent (mvar۰inv t γ Ψ).
    Proof.
      apply _.
    Qed.
    #[global] Instance mvar۰resolvedｰpersistent γ :
      Persistent (mvar۰resolved γ).
    Proof.
      apply _.
    Qed.

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
        t γ
      , RET #t;
        meta_token t ⊤ ∗
        mvar۰inv t γ Ψ ∗
        mvar۰consumer γ
      }}}.
    Proof.
      iIntros "%Φ _ HΦ".

      wp۰rec.
      wp۰ref t as "Hmeta" "Ht".

      iMod lstateｰalloc as "(%γ_lstate & Hlstate_unset)".
      iMod consumerｰalloc as "(%γ_consumer & Hconsumer)".

      pose γ :=
        {|mvar۰name۰lstate := γ_lstate
        ; mvar۰name۰consumer := γ_consumer
        |}.

      iApply ("HΦ" $! t γ).
      iFrameSteps. iExists None. iSteps.
    Qed.

    Lemma mvar٠makeｰspec Ψ v :
      {{{
        ▷ Ψ v
      }}}
        mvar٠make v
      {{{
        t γ
      , RET #t;
        meta_token t ⊤ ∗
        mvar۰inv t γ Ψ ∗
        mvar۰resolved γ ∗
        mvar۰consumer γ
      }}}.
    Proof.
      iIntros "%Φ HΨ HΦ".

      wp۰rec.
      wp۰ref t as "Hmeta" "Ht".

      iMod lstateｰalloc as "(%γ_lstate & Hlstate_unset)".
      iMod consumerｰalloc as "(%γ_consumer & Hconsumer)".

      pose γ :=
        {|mvar۰name۰lstate := γ_lstate
        ; mvar۰name۰consumer := γ_consumer
        |}.

      iMod (lstateｰupdate γ with "Hlstate_unset") as "#Hlstate_set".

      iApply ("HΦ" $! t γ).
      iFrameSteps. iExists (Some v). iSteps.
    Qed.

    Lemma mvar٠try_getｰspec t γ Ψ :
      {{{
        mvar۰inv t γ Ψ
      }}}
        mvar٠try_get #t
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
    Lemma mvar٠try_getｰspecｰresolved t γ Ψ :
      {{{
        mvar۰inv t γ Ψ ∗
        mvar۰resolved γ
      }}}
        mvar٠try_get #t
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
    Lemma mvar٠try_getｰspecｰconsumer t γ Ψ :
      {{{
        mvar۰inv t γ Ψ ∗
        mvar۰consumer γ
      }}}
        mvar٠try_get #t
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
    Lemma mvar٠try_getｰspecｰresolvedｰconsumer t γ Ψ :
      {{{
        mvar۰inv t γ Ψ ∗
        mvar۰resolved γ ∗
        mvar۰consumer γ
      }}}
        mvar٠try_get #t
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

    Lemma mvar٠is_unsetｰspec t γ Ψ :
      {{{
        mvar۰inv t γ Ψ
      }}}
        mvar٠is_unset #t
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
    Lemma mvar٠is_unsetｰspecｰresolved t γ Ψ :
      {{{
        mvar۰inv t γ Ψ ∗
        mvar۰resolved γ
      }}}
        mvar٠is_unset #t
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

    Lemma mvar٠is_setｰspec t γ Ψ :
      {{{
        mvar۰inv t γ Ψ
      }}}
        mvar٠is_set #t
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
    Lemma mvar٠is_setｰspecｰresolved t γ Ψ :
      {{{
        mvar۰inv t γ Ψ ∗
        mvar۰resolved γ
      }}}
        mvar٠is_set #t
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

    Lemma mvar٠getｰspec t γ Ψ :
      {{{
        mvar۰inv t γ Ψ ∗
        mvar۰resolved γ
      }}}
        mvar٠get #t
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

    Lemma mvar٠setｰspec t γ Ψ v :
      {{{
        mvar۰inv t γ Ψ ∗
        ▷ Ψ v
      }}}
        mvar٠set #t v
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

  #[global] Opaque mvar۰inv.
  #[global] Opaque mvar۰consumer.
  #[global] Opaque mvar۰resolved.
End base.

Require zoo_std.mvar__opaque.

Section mvar۰G.
  Context `{mvar۰G : MvarG Σ}.

  Implicit Type 𝑡 : location.
  Implicit Type t : val.
  Implicit Type γ : base.mvar۰name.
  Implicit Type Ψ : val → iProp Σ.

  Definition mvar۰inv t Ψ : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.mvar۰inv 𝑡 γ Ψ.
  #[local] Instance : CustomIpat "inv" :=
    " ( %l{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hinv{_{}}
      )
    ".

  Definition mvar۰consumer t : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.mvar۰consumer γ.
  #[local] Instance : CustomIpat "consumer" :=
    " ( %l{;_}
      & %γ{;_}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hconsumer{_{}}
      )
    ".

  Definition mvar۰resolved t : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.mvar۰resolved γ.
  #[local] Instance : CustomIpat "resolved" :=
    " ( %l{;_}
      & %γ{;_}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hresolved{_{}}
      )
    ".

  #[global] Instance mvar۰inv_contractive t n :
    Proper (
      (pointwise_relation _ (dist_later n)) ==>
      (≡{n}≡)
    ) (mvar۰inv t).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance mvar۰invｰproper t :
    Proper (
      (pointwise_relation _ (≡)) ==>
      (≡)
    ) (mvar۰inv t).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance mvar۰resolvedｰtimeless t :
    Timeless (mvar۰resolved t).
  Proof.
    apply _.
  Qed.

  #[global] Instance mvar۰invｰpersistent t Ψ :
    Persistent (mvar۰inv t Ψ).
  Proof.
    apply _.
  Qed.
  #[global] Instance mvar۰resolvedｰpersistent t :
    Persistent (mvar۰resolved t).
  Proof.
    apply _.
  Qed.

  Lemma mvar۰consumerｰexclusive t :
    mvar۰consumer t -∗
    mvar۰consumer t -∗
    False.
  Proof.
    iIntros "(:consumer =1) (:consumer =2)". simplify.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.mvar۰consumerｰexclusive with "Hconsumer_1 Hconsumer_2").
  Qed.

  Lemma mvar٠createｰspec Ψ :
    {{{
      True
    }}}
      mvar٠create ()
    {{{
      t
    , RET t;
      mvar۰inv t Ψ ∗
      mvar۰consumer t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    iApply wpｰfupd.
    wp۰apply (base.mvar٠createｰspec with "[//]") as (𝑡 γ) "(Hmeta & Hinv & Hconsumer)".
    iMod (metaｰset γ with "Hmeta") as "#Hmeta"; first done.
    iSteps.
  Qed.

  Lemma mvar٠makeｰspec Ψ v :
    {{{
      ▷ Ψ v
    }}}
      mvar٠make v
    {{{
      t
    , RET t;
      mvar۰inv t Ψ ∗
      mvar۰resolved t ∗
      mvar۰consumer t
    }}}.
  Proof.
    iIntros "%Φ HΨ HΦ".

    iApply wpｰfupd.
    wp۰apply (base.mvar٠makeｰspec Ψ with "[$]") as (𝑡 γ) "(Hmeta & Hinv & Hproducer & Hconsumer)".
    iMod (metaｰset γ with "Hmeta") as "#Hmeta"; first done.
    iSteps.
  Qed.

  Lemma mvar٠try_getｰspec t Ψ :
    {{{
      mvar۰inv t Ψ
    }}}
      mvar٠try_get t
    {{{
      o
    , RET o;
      if o is Some v then
        mvar۰resolved t
      else
        True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰apply (base.mvar٠try_getｰspec with "[$]") as (o) "Ho".
    iSpecialize ("HΦ" $! o).
    destruct o; iSteps.
  Qed.
  Lemma mvar٠try_getｰspecｰresolved t Ψ :
    {{{
      mvar۰inv t Ψ ∗
      mvar۰resolved t
    }}}
      mvar٠try_get t
    {{{
      v
    , RET Some v;
      True
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:resolved =2)) HΦ". simplify.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp۰apply (base.mvar٠try_getｰspecｰresolved with "[$] HΦ").
  Qed.
  Lemma mvar٠try_getｰspecｰconsumer t Ψ :
    {{{
      mvar۰inv t Ψ ∗
      mvar۰consumer t
    }}}
      mvar٠try_get t
    {{{
      o
    , RET o;
      if o is Some v then
        mvar۰resolved t ∗
        Ψ v
      else
        True
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:consumer =2)) HΦ". simplify.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp۰apply (base.mvar٠try_getｰspecｰconsumer with "[$]") as (o) "Ho".
    iSpecialize ("HΦ" $! o).
    destruct o; iSteps.
  Qed.
  Lemma mvar٠try_getｰspecｰresolvedｰconsumer t Ψ :
    {{{
      mvar۰inv t Ψ ∗
      mvar۰resolved t ∗
      mvar۰consumer t
    }}}
      mvar٠try_get t
    {{{
      v
    , RET Some v;
      Ψ v
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:resolved =2) & (:consumer =3)) HΦ". simplify.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".
    iDestruct (metaｰagree with "Hmeta_2 Hmeta_3") as %<-. iClear "Hmeta_3".

    wp۰apply (base.mvar٠try_getｰspecｰresolvedｰconsumer with "[$] HΦ").
  Qed.

  Lemma mvar٠is_unsetｰspec t Ψ :
    {{{
      mvar۰inv t Ψ
    }}}
      mvar٠is_unset t
    {{{
      b
    , RET #b;
      if b then
        True
      else
        mvar۰resolved t
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰apply (base.mvar٠is_unsetｰspec with "[$]") as (b) "Hb".
    rewrite /mvar۰resolved. destruct b; iSteps.
  Qed.
  Lemma mvar٠is_unsetｰspecｰresolved t Ψ :
    {{{
      mvar۰inv t Ψ ∗
      mvar۰resolved t
    }}}
      mvar٠is_unset t
    {{{
      RET false;
      True
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:resolved =2)) HΦ". simplify.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp۰apply (base.mvar٠is_unsetｰspecｰresolved with "[$] HΦ").
  Qed.

  Lemma mvar٠is_setｰspec t Ψ :
    {{{
      mvar۰inv t Ψ
    }}}
      mvar٠is_set t
    {{{
      b
    , RET #b;
      if b then
        mvar۰resolved t
      else
        True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp۰apply (base.mvar٠is_setｰspec with "[$]") as (b) "Hb".
    rewrite /mvar۰resolved. destruct b; iSteps.
  Qed.
  Lemma mvar٠is_setｰspecｰresolved t Ψ :
    {{{
      mvar۰inv t Ψ ∗
      mvar۰resolved t
    }}}
      mvar٠is_set t
    {{{
      RET true;
      True
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:resolved =2)) HΦ". simplify.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp۰apply (base.mvar٠is_setｰspecｰresolved with "[$] HΦ").
  Qed.

  Lemma mvar٠getｰspec t Ψ :
    {{{
      mvar۰inv t Ψ ∗
      mvar۰resolved t
    }}}
      mvar٠get t
    {{{
      v
    , RET v;
      True
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:resolved =2)) HΦ". simplify.
    iDestruct (metaｰagree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp۰apply (base.mvar٠getｰspec with "[$] HΦ").
  Qed.

  Lemma mvar٠setｰspec t Ψ v :
    {{{
      mvar۰inv t Ψ ∗
      ▷ Ψ v
    }}}
      mvar٠set t v
    {{{
      RET ();
      mvar۰resolved t
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & HΨ) HΦ".

    wp۰apply (base.mvar٠setｰspec _ _ Ψ with "[$]").
    iSteps.
  Qed.
End mvar۰G.

#[global] Opaque mvar۰inv.
#[global] Opaque mvar۰consumer.
#[global] Opaque mvar۰resolved.
