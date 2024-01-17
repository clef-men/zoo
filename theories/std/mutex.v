From zebre Require Import
  prelude.
From zebre.iris.base_logic Require Import
  excl.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Export
  base.
From zebre Require Import
  options.

Implicit Types b : bool.
Implicit Types l : loc.
Implicit Types t fn : val.

Definition mutex_create : val :=
  λ: <>,
    ref #false.

Definition mutex_lock : val :=
  rec: "mutex_lock" "t" :=
    ifnot: Cas "t" #false #true then (
      "mutex_lock" "t"
    ).

Definition mutex_unlock : val :=
  λ: "t",
    "t" <- #false.

Definition mutex_protect : val :=
  λ: "t" "fn",
    mutex_lock "t" ;;
    let: "res" := "fn" #() in
    mutex_unlock "t" ;;
    "res".

Class MutexG Σ `{zebre_G : !ZebreG Σ} := {
  #[local] mutex_G :: ExclG Σ unitO ;
}.

Definition mutex_Σ := #[
  excl_Σ unitO
].
#[global] Instance subG_mutex_Σ Σ `{zebre_G : !ZebreG Σ} :
  subG mutex_Σ Σ →
  MutexG Σ.
Proof.
  solve_inG.
Qed.

Section mutex_G.
  Context `{mutex_G : MutexG Σ}.

  #[local] Definition mutex_locked' γ :=
    excl γ ().

  #[local] Definition mutex_inv_inner l γ P : iProp Σ :=
    ∃ b,
    l ↦ #b ∗
    match b with
    | true =>
        True
    | false =>
        mutex_locked' γ ∗
        P
    end.
  Definition mutex_inv t P : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    inv nroot (mutex_inv_inner l γ P).

  Definition mutex_locked t : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    meta l nroot γ ∗
    mutex_locked' γ.

  #[global] Instance mutex_inv_contractive t :
    Contractive (mutex_inv t).
  Proof.
    rewrite /mutex_inv /mutex_inv_inner. solve_contractive.
  Qed.
  #[global] Instance mutex_inv_ne t :
    NonExpansive (mutex_inv t).
  Proof.
    apply _.
  Qed.
  #[global] Instance mutex_inv_proper t :
    Proper ((≡) ==> (≡)) (mutex_inv t).
  Proof.
    apply _.
  Qed.

  #[global] Instance mutex_inv_persistent t P :
    Persistent (mutex_inv t P).
  Proof.
    apply _.
  Qed.
  #[global] Instance mutex_locked_timeless t :
    Timeless (mutex_locked t).
  Proof.
    apply _.
  Qed.

  Lemma mutex_locked_exclusive t :
    mutex_locked t -∗
    mutex_locked t -∗
    False.
  Proof.
    iIntros "(%l & %γ & -> & #Hmeta & Hlocked1) (%_l & %_γ & %Heq & _Hmeta & Hlocked2)". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iDestruct (excl_exclusive with "Hlocked1 Hlocked2") as %[].
  Qed.

  Lemma mutex_create_spec P :
    {{{
      P
    }}}
      mutex_create #()
    {{{ t,
      RET t;
      mutex_inv t P
    }}}.
  Proof.
    iIntros "%Φ HP HΦ".
    wp_rec.
    iApply wp_fupd. wp_apply (wp_ref with "[//]") as "%l (Hmeta & Hl)".
    iMod excl_alloc as "(%γ & Hlocked)".
    iMod (meta_set _ _ γ with "Hmeta") as "#Hmeta"; first done.
    iSteps.
  Qed.

  Lemma mutex_lock_spec t P :
    {{{
      mutex_inv t P
    }}}
      mutex_lock t
    {{{
      RET #();
      mutex_locked t ∗
      P
    }}}.
  Proof.
    iIntros "%Φ (%l & %γ & -> & #Hmeta & #Hinv) HΦ".
    iLöb as "HLöb".
    wp_rec.
    wp_bind (Cas _ _ _).
    iInv "Hinv" as "(%b & Hl & Hb)".
    destruct b.
    - wp_cas_fail.
      iModIntro. iSplitR "HΦ"; first iSteps.
      wp_pures.
      iApply ("HLöb" with "HΦ").
    - wp_cas_suc.
      iSteps.
  Qed.

  Lemma mutex_unlock_spec t P :
    {{{
      mutex_inv t P ∗
      mutex_locked t ∗
      P
    }}}
      mutex_unlock t
    {{{
      RET #(); True
    }}}.
  Proof.
    iIntros "%Φ ((%l & %γ & -> & #Hmeta & #Hinv) & (%_l & %_γ & %Heq & #_Hmeta & Hlocked) & HP) HΦ". injection Heq as <-.
    iDestruct (meta_agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iSteps.
  Qed.

  Lemma mutex_protect_spec Ψ t P fn :
    {{{
      mutex_inv t P ∗
      ( mutex_locked t -∗
        P -∗
        WP fn #() {{ v,
          mutex_locked t ∗
          P ∗
          Ψ v
        }}
      )
    }}}
      mutex_protect t fn
    {{{ v,
      RET v;
      Ψ v
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & Hfn) HΦ".
    wp_rec.
    wp_smart_apply (mutex_lock_spec with "Hinv") as "(Hlocked & HP)".
    wp_smart_apply (wp_wand with "(Hfn Hlocked HP)") as "%v (Hlocked & HP & HΨ)".
    wp_smart_apply (mutex_unlock_spec with "[$Hinv $Hlocked $HP]").
    iSteps.
  Qed.
End mutex_G.

#[global] Opaque mutex_create.
#[global] Opaque mutex_lock.
#[global] Opaque mutex_unlock.
#[global] Opaque mutex_protect.

#[global] Opaque mutex_inv.
#[global] Opaque mutex_locked.
