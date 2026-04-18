From zoo Require Import
  prelude.
From zoo.common Require Import
  countable.
From zoo.iris.base_logic Require Import
  lib.excl
  lib.oneshot.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
  base
  mvar__code.
From zoo_std Require Import
  option.
From zoo Require Import
  options.

Implicit Types b : bool.
Implicit Types v : val.
Implicit Types o state : option val.

Class MvarG Σ `{zoo_G : !ZooG Σ} :=
  { #[local] mvar_G_lstate_G :: OneshotG Σ unit unit
  ; #[local] mvar_G_consumer_G :: ExclG Σ unitO
  }.

Definition mvar_Σ :=
  #[oneshot_Σ unit unit
  ; excl_Σ unitO
  ].
#[global] Instance subG_mvar_Σ Σ `{zoo_G : !ZooG Σ} :
  subG mvar_Σ Σ →
  MvarG Σ .
Proof.
  solve_inG.
Qed.

Module base.
  Section mvar_G.
    Context `{mvar_G : MvarG Σ}.

    Implicit Types t : location.
    Implicit Types Ψ : val → iProp Σ.

    Record mvar_name :=
      { mvar_name_lstate : gname
      ; mvar_name_consumer : gname
      }.
    Implicit Types γ : mvar_name.

    #[global] Instance mvar_name_eq_dec : EqDecision mvar_name :=
      ltac:(solve_decision).
    #[global] Instance mvar_name_countable :
      Countable mvar_name.
    Proof.
      solve_countable.
    Qed.

    #[local] Definition lstate_unset' γ_lstate :=
      oneshot_pending γ_lstate Own ().
    #[local] Definition lstate_unset γ :=
      lstate_unset' γ.(mvar_name_lstate).
    #[local] Definition lstate_set' γ_lstate :=
      oneshot_shot γ_lstate ().
    #[local] Definition lstate_set γ :=
      lstate_set' γ.(mvar_name_lstate).

    #[local] Definition consumer' γ_consumer :=
      excl γ_consumer ().
    #[local] Definition consumer γ :=
      consumer' γ.(mvar_name_consumer).

    #[local] Definition inv_state_unset γ :=
      lstate_unset γ.
    #[local] Instance : CustomIpat "inv_state_unset" :=
      " {>;}Hlstate_unset
      ".
    #[local] Definition inv_state_set_1 γ Ψ v : iProp Σ :=
        Ψ v
      ∨ consumer γ.
    #[local] Instance : CustomIpat "inv_state_set_1" :=
      " [ HΨ
        | Hconsumer{_{}}
        ]
      ".
    #[local] Definition inv_state_set_2 γ Ψ v : iProp Σ :=
      lstate_set γ ∗
      inv_state_set_1 γ Ψ v.
    #[local] Instance : CustomIpat "inv_state_set_2" :=
      " ( {>;}#Hlstate_set{_{}}
        & Hstate
        )
      ".
    #[local] Definition inv_state γ Ψ state :=
      match state with
      | None =>
          inv_state_unset γ
      | Some v =>
          inv_state_set_2 γ Ψ v
      end.

    #[local] Definition inv_inner t γ Ψ : iProp Σ :=
      ∃ state,
      t ↦ᵣ state ∗
      inv_state γ Ψ state.
    #[local] Instance : CustomIpat "inv_inner" :=
      " ( %state
        & Ht
        & Hstate
        )
      ".
    Definition mvar_inv t γ Ψ : iProp Σ :=
      inv nroot (inv_inner t γ Ψ).
    #[local] Instance : CustomIpat "inv" :=
      " #Hinv
      ".

    Definition mvar_consumer :=
      consumer.
    #[local] Instance : CustomIpat "consumer" :=
      " Hconsumer{_{}}
      ".

    Definition mvar_resolved :=
      lstate_set.
    #[local] Instance : CustomIpat "resolved" :=
      " #Hlstate_set{_{}}
      ".

    #[global] Instance mvar_inv_contractive t γ n :
      Proper (
        (pointwise_relation _ (dist_later n)) ==>
        (≡{n}≡)
      ) (mvar_inv t γ).
    Proof.
      rewrite /mvar_inv /inv_inner /inv_state /inv_state_unset /inv_state_set_2 /inv_state_set_1.
      solve_contractive.
    Qed.
    #[global] Instance mvar_inv_proper t γ :
      Proper (
        (pointwise_relation _ (≡)) ==>
        (≡)
      ) (mvar_inv t γ).
    Proof.
      rewrite /mvar_inv /inv_inner /inv_state /inv_state_unset /inv_state_set_2 /inv_state_set_1.
      solve_proper.
    Qed.

    #[global] Instance mvar_resolved_timeless γ :
      Timeless (mvar_resolved γ).
    Proof.
      apply _.
    Qed.

    #[global] Instance mvar_inv_persistent t γ Ψ :
      Persistent (mvar_inv t γ Ψ).
    Proof.
      apply _.
    Qed.
    #[global] Instance mvar_resolved_persistent γ :
      Persistent (mvar_resolved γ).
    Proof.
      apply _.
    Qed.

    #[local] Lemma lstate_alloc :
      ⊢ |==>
        ∃ γ_lstate,
        lstate_unset' γ_lstate.
    Proof.
      apply oneshot_alloc.
    Qed.
    #[local] Lemma lstate_unset_set γ :
      lstate_unset γ -∗
      lstate_set γ -∗
      False.
    Proof.
      apply oneshot_pending_shot.
    Qed.
    #[local] Lemma lstate_update γ :
      lstate_unset γ ⊢ |==>
      lstate_set γ.
    Proof.
      apply oneshot_update_shot.
    Qed.

    #[local] Lemma consumer_alloc :
      ⊢ |==>
        ∃ γ_consumer,
        consumer' γ_consumer.
    Proof.
      apply excl_alloc.
    Qed.
    #[local] Lemma consumer_exclusive γ :
      consumer γ -∗
      consumer γ -∗
      False.
    Proof.
      apply excl_exclusive.
    Qed.

    Lemma mvar_consumer_exclusive γ :
      mvar_consumer γ -∗
      mvar_consumer γ -∗
      False.
    Proof.
      apply consumer_exclusive.
    Qed.

    Lemma mvar_create𑁒spec Ψ :
      {{{
        True
      }}}
        mvar_create ()
      {{{
        t γ
      , RET #t;
        meta_token t ⊤ ∗
        mvar_inv t γ Ψ ∗
        mvar_consumer γ
      }}}.
    Proof.
      iIntros "%Φ _ HΦ".

      wp_rec.
      wp_ref t as "Hmeta" "Ht".

      iMod lstate_alloc as "(%γ_lstate & Hlstate_unset)".
      iMod consumer_alloc as "(%γ_consumer & Hconsumer)".

      pose γ :=
        {|mvar_name_lstate := γ_lstate
        ; mvar_name_consumer := γ_consumer
        |}.

      iApply ("HΦ" $! t γ).
      iFrameSteps. iExists None. iSteps.
    Qed.

    Lemma mvar_make𑁒spec Ψ v :
      {{{
        ▷ Ψ v
      }}}
        mvar_make v
      {{{
        t γ
      , RET #t;
        meta_token t ⊤ ∗
        mvar_inv t γ Ψ ∗
        mvar_resolved γ ∗
        mvar_consumer γ
      }}}.
    Proof.
      iIntros "%Φ HΨ HΦ".

      wp_rec.
      wp_ref t as "Hmeta" "Ht".

      iMod lstate_alloc as "(%γ_lstate & Hlstate_unset)".
      iMod consumer_alloc as "(%γ_consumer & Hconsumer)".

      pose γ :=
        {|mvar_name_lstate := γ_lstate
        ; mvar_name_consumer := γ_consumer
        |}.

      iMod (lstate_update γ with "Hlstate_unset") as "#Hlstate_set".

      iApply ("HΦ" $! t γ).
      iFrameSteps. iExists (Some v). iSteps.
    Qed.

    Lemma mvar_try_get𑁒spec t γ Ψ :
      {{{
        mvar_inv t γ Ψ
      }}}
        mvar_try_get #t
      {{{
        o
      , RET o;
        if o then
          mvar_resolved γ
        else
          True
      }}}.
    Proof.
      iIntros "%Φ (:inv) HΦ".

      wp_rec.

      iInv "Hinv" as "(:inv_inner)".
      wp_load.
      iSpecialize ("HΦ" $! state).
      destruct state as [v |].

      - iDestruct "Hstate" as "(:inv_state_set_2)".
        iSplitR "HΦ". { iFrameSteps 2. }
        iSteps.

      - iSplitR "HΦ". { iFrameSteps. }
        iSteps.
    Qed.
    Lemma mvar_try_get𑁒spec_resolved t γ Ψ :
      {{{
        mvar_inv t γ Ψ ∗
        mvar_resolved γ
      }}}
        mvar_try_get #t
      {{{
        v
      , RET Some v;
        True
      }}}.
    Proof.
      iIntros "%Φ ((:inv) & (:resolved)) HΦ".

      wp_rec.

      iInv "Hinv" as "(:inv_inner)".
      wp_load.
      destruct state as [v |].

      - iSplitR "HΦ". { iFrameSteps. }
        iSteps.

      - iDestruct "Hstate" as "(:inv_state_unset)".
        iDestruct (lstate_unset_set with "Hlstate_unset Hlstate_set") as %[].
    Qed.
    Lemma mvar_try_get𑁒spec_consumer t γ Ψ :
      {{{
        mvar_inv t γ Ψ ∗
        mvar_consumer γ
      }}}
        mvar_try_get #t
      {{{
        o
      , RET o;
        if o is Some v then
          mvar_resolved γ ∗
          Ψ v
        else
          True
      }}}.
    Proof.
      iIntros "%Φ ((:inv) & (:consumer)) HΦ".

      wp_rec.

      iInv "Hinv" as "(:inv_inner)".
      wp_load.
      iSpecialize ("HΦ" $! state).
      destruct state as [v |].

      - iDestruct "Hstate" as "(:inv_state_set_2)".
        iDestruct "Hstate" as "(:inv_state_set_1 =1)"; last first.
        { iDestruct (consumer_exclusive with "Hconsumer Hconsumer_1") as %[]. }
        iSplitR "HΨ HΦ". { iFrameSteps. }
        iSteps.

      - iSplitR "HΦ". { iFrameSteps. }
        iSteps.
    Qed.
    Lemma mvar_try_get𑁒spec_resolved_consumer t γ Ψ :
      {{{
        mvar_inv t γ Ψ ∗
        mvar_resolved γ ∗
        mvar_consumer γ
      }}}
        mvar_try_get #t
      {{{
        v
      , RET Some v;
        Ψ v
      }}}.
    Proof.
      iIntros "%Φ ((:inv) & (:resolved) & (:consumer)) HΦ".

      wp_rec.

      iInv "Hinv" as "(:inv_inner)".
      wp_load.
      destruct state as [v |].

      - iDestruct "Hstate" as "(:inv_state_set_2 =1)".
        iDestruct "Hstate" as "(:inv_state_set_1 =1)"; last first.
        { iDestruct (consumer_exclusive with "Hconsumer Hconsumer_1") as %[]. }
        iSplitR "HΨ HΦ". { iFrameSteps. }
        iSteps.

      - iDestruct "Hstate" as "(:inv_state_unset)".
        iDestruct (lstate_unset_set with "Hlstate_unset Hlstate_set") as %[].
    Qed.

    Lemma mvar_is_unset𑁒spec t γ Ψ :
      {{{
        mvar_inv t γ Ψ
      }}}
        mvar_is_unset #t
      {{{
        b
      , RET #b;
        if b then
          True
        else
          mvar_resolved γ
      }}}.
    Proof.
      iIntros "%Φ #Hinv HΦ".

      wp_rec.
      wp_apply (mvar_try_get𑁒spec with "Hinv") as ([v |]) "H".
      all: iSteps.
    Qed.
    Lemma mvar_is_unset𑁒spec_resolved t γ Ψ :
      {{{
        mvar_inv t γ Ψ ∗
        mvar_resolved γ
      }}}
        mvar_is_unset #t
      {{{
        RET false;
        True
      }}}.
    Proof.
      iIntros "%Φ (#Hinv & #Hresolved) HΦ".

      wp_rec.
      wp_apply (mvar_try_get𑁒spec_resolved with "[$Hinv $Hresolved]").
      iSteps.
    Qed.

    Lemma mvar_is_set𑁒spec t γ Ψ :
      {{{
        mvar_inv t γ Ψ
      }}}
        mvar_is_set #t
      {{{
        b
      , RET #b;
        if b then
          mvar_resolved γ
        else
          True
      }}}.
    Proof.
      iIntros "%Φ #Hinv HΦ".

      wp_rec.
      wp_apply (mvar_is_unset𑁒spec with "[$]") as (b) "Hb".
      destruct b; iSteps.
    Qed.
    Lemma mvar_is_set𑁒spec_resolved t γ Ψ :
      {{{
        mvar_inv t γ Ψ ∗
        mvar_resolved γ
      }}}
        mvar_is_set #t
      {{{
        RET true;
        True
      }}}.
    Proof.
      iIntros "%Φ (#Hinv & #Hresolved) HΦ".

      wp_rec.
      wp_apply (mvar_is_unset𑁒spec_resolved with "[$]").
      iSteps.
    Qed.

    Lemma mvar_get𑁒spec t γ Ψ :
      {{{
        mvar_inv t γ Ψ ∗
        mvar_resolved γ
      }}}
        mvar_get #t
      {{{
        v
      , RET v;
        True
      }}}.
    Proof.
      iIntros "%Φ (#Hinv & Hresolved) HΦ".

      wp_rec.
      wp_apply (mvar_try_get𑁒spec_resolved with "[$Hinv $Hresolved]").
      iSteps.
    Qed.

    Lemma mvar_set𑁒spec t γ Ψ v :
      {{{
        mvar_inv t γ Ψ ∗
        ▷ Ψ v
      }}}
        mvar_set #t v
      {{{
        RET ();
        mvar_resolved γ
      }}}.
    Proof.
      iIntros "%Φ ((:inv) & HΨ) HΦ".

      wp_rec. wp_pures.

      iInv "Hinv" as "(:inv_inner)".
      wp_store.
      destruct state as [w |].

      - iDestruct "Hstate" as "(:inv_state_set_2)".
        iSplitR "HΦ". { iExists (Some v). iFrameSteps. }
        iSteps.

      - iDestruct "Hstate" as "(:inv_state_unset)".
        iMod (lstate_update with "Hlstate_unset") as "#Hlstate_set".
        iSplitR "HΦ". { iExists (Some v). iFrameSteps. }
        iSteps.
    Qed.
  End mvar_G.

  #[global] Opaque mvar_inv.
  #[global] Opaque mvar_consumer.
  #[global] Opaque mvar_resolved.
End base.

From zoo_std Require
  mvar__opaque.

Section mvar_G.
  Context `{mvar_G : MvarG Σ}.

  Implicit Types 𝑡 : location.
  Implicit Types t : val.
  Implicit Types γ : base.mvar_name.
  Implicit Types Ψ : val → iProp Σ.

  Definition mvar_inv t Ψ : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.mvar_inv 𝑡 γ Ψ.
  #[local] Instance : CustomIpat "inv" :=
    " ( %l{}
      & %γ{}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hinv{_{}}
      )
    ".

  Definition mvar_consumer t : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.mvar_consumer γ.
  #[local] Instance : CustomIpat "consumer" :=
    " ( %l{;_}
      & %γ{;_}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hconsumer{_{}}
      )
    ".

  Definition mvar_resolved t : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    meta 𝑡 nroot γ ∗
    base.mvar_resolved γ.
  #[local] Instance : CustomIpat "resolved" :=
    " ( %l{;_}
      & %γ{;_}
      & {%Heq{};->}
      & #Hmeta{_{}}
      & Hresolved{_{}}
      )
    ".

  #[global] Instance mvar_inv_contractive t n :
    Proper (
      (pointwise_relation _ (dist_later n)) ==>
      (≡{n}≡)
    ) (mvar_inv t).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance mvar_inv_proper t :
    Proper (
      (pointwise_relation _ (≡)) ==>
      (≡)
    ) (mvar_inv t).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance mvar_resolved_timeless t :
    Timeless (mvar_resolved t).
  Proof.
    apply _.
  Qed.

  #[global] Instance mvar_inv_persistent t Ψ :
    Persistent (mvar_inv t Ψ).
  Proof.
    apply _.
  Qed.
  #[global] Instance mvar_resolved_persistent t :
    Persistent (mvar_resolved t).
  Proof.
    apply _.
  Qed.

  Lemma mvar_consumer_exclusive t :
    mvar_consumer t -∗
    mvar_consumer t -∗
    False.
  Proof.
    iIntros "(:consumer =1) (:consumer =2)". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->.
    iApply (base.mvar_consumer_exclusive with "Hconsumer_1 Hconsumer_2").
  Qed.

  Lemma mvar_create𑁒spec Ψ :
    {{{
      True
    }}}
      mvar_create ()
    {{{
      t
    , RET t;
      mvar_inv t Ψ ∗
      mvar_consumer t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    iApply wp_fupd.
    wp_apply (base.mvar_create𑁒spec with "[//]") as (𝑡 γ) "(Hmeta & Hinv & Hconsumer)".
    iMod (meta_set γ with "Hmeta") as "#Hmeta"; first done.
    iSteps.
  Qed.

  Lemma mvar_make𑁒spec Ψ v :
    {{{
      ▷ Ψ v
    }}}
      mvar_make v
    {{{
      t
    , RET t;
      mvar_inv t Ψ ∗
      mvar_resolved t ∗
      mvar_consumer t
    }}}.
  Proof.
    iIntros "%Φ HΨ HΦ".

    iApply wp_fupd.
    wp_apply (base.mvar_make𑁒spec Ψ with "[$]") as (𝑡 γ) "(Hmeta & Hinv & Hproducer & Hconsumer)".
    iMod (meta_set γ with "Hmeta") as "#Hmeta"; first done.
    iSteps.
  Qed.

  Lemma mvar_try_get𑁒spec t Ψ :
    {{{
      mvar_inv t Ψ
    }}}
      mvar_try_get t
    {{{
      o
    , RET o;
      if o is Some v then
        mvar_resolved t
      else
        True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_apply (base.mvar_try_get𑁒spec with "[$]") as (o) "Ho".
    iSpecialize ("HΦ" $! o).
    destruct o; iSteps.
  Qed.
  Lemma mvar_try_get𑁒spec_resolved t Ψ :
    {{{
      mvar_inv t Ψ ∗
      mvar_resolved t
    }}}
      mvar_try_get t
    {{{
      v
    , RET Some v;
      True
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:resolved =2)) HΦ". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp_apply (base.mvar_try_get𑁒spec_resolved with "[$] HΦ").
  Qed.
  Lemma mvar_try_get𑁒spec_consumer t Ψ :
    {{{
      mvar_inv t Ψ ∗
      mvar_consumer t
    }}}
      mvar_try_get t
    {{{
      o
    , RET o;
      if o is Some v then
        mvar_resolved t ∗
        Ψ v
      else
        True
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:consumer =2)) HΦ". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp_apply (base.mvar_try_get𑁒spec_consumer with "[$]") as (o) "Ho".
    iSpecialize ("HΦ" $! o).
    destruct o; iSteps.
  Qed.
  Lemma mvar_try_get𑁒spec_resolved_consumer t Ψ :
    {{{
      mvar_inv t Ψ ∗
      mvar_resolved t ∗
      mvar_consumer t
    }}}
      mvar_try_get t
    {{{
      v
    , RET Some v;
      Ψ v
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:resolved =2) & (:consumer =3)) HΦ". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".
    iDestruct (meta_agree with "Hmeta_2 Hmeta_3") as %<-. iClear "Hmeta_3".

    wp_apply (base.mvar_try_get𑁒spec_resolved_consumer with "[$] HΦ").
  Qed.

  Lemma mvar_is_unset𑁒spec t Ψ :
    {{{
      mvar_inv t Ψ
    }}}
      mvar_is_unset t
    {{{
      b
    , RET #b;
      if b then
        True
      else
        mvar_resolved t
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_apply (base.mvar_is_unset𑁒spec with "[$]") as (b) "Hb".
    rewrite /mvar_resolved. destruct b; iSteps.
  Qed.
  Lemma mvar_is_unset𑁒spec_resolved t Ψ :
    {{{
      mvar_inv t Ψ ∗
      mvar_resolved t
    }}}
      mvar_is_unset t
    {{{
      RET false;
      True
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:resolved =2)) HΦ". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp_apply (base.mvar_is_unset𑁒spec_resolved with "[$] HΦ").
  Qed.

  Lemma mvar_is_set𑁒spec t Ψ :
    {{{
      mvar_inv t Ψ
    }}}
      mvar_is_set t
    {{{
      b
    , RET #b;
      if b then
        mvar_resolved t
      else
        True
    }}}.
  Proof.
    iIntros "%Φ (:inv) HΦ".

    wp_apply (base.mvar_is_set𑁒spec with "[$]") as (b) "Hb".
    rewrite /mvar_resolved. destruct b; iSteps.
  Qed.
  Lemma mvar_is_set𑁒spec_resolved t Ψ :
    {{{
      mvar_inv t Ψ ∗
      mvar_resolved t
    }}}
      mvar_is_set t
    {{{
      RET true;
      True
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:resolved =2)) HΦ". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp_apply (base.mvar_is_set𑁒spec_resolved with "[$] HΦ").
  Qed.

  Lemma mvar_get𑁒spec t Ψ :
    {{{
      mvar_inv t Ψ ∗
      mvar_resolved t
    }}}
      mvar_get t
    {{{
      v
    , RET v;
      True
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:resolved =2)) HΦ". simplify.
    iDestruct (meta_agree with "Hmeta_1 Hmeta_2") as %->. iClear "Hmeta_1".

    wp_apply (base.mvar_get𑁒spec with "[$] HΦ").
  Qed.

  Lemma mvar_set𑁒spec t Ψ v :
    {{{
      mvar_inv t Ψ ∗
      ▷ Ψ v
    }}}
      mvar_set t v
    {{{
      RET ();
      mvar_resolved t
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & HΨ) HΦ".

    wp_apply (base.mvar_set𑁒spec _ _ Ψ with "[$]").
    iSteps.
  Qed.
End mvar_G.

#[global] Opaque mvar_inv.
#[global] Opaque mvar_consumer.
#[global] Opaque mvar_resolved.
