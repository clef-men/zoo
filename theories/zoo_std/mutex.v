Require Import zoo.prelude.
Require Import zoo.iris.base_logic.lib.excl.
Require Import zoo.base.
Require Export zoo_std.mutex__code.
Require Import zoo_std.mutex__types.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type fn : val.

Zoo name :=
  { self : location
  ; locked : gname
  }.

Zoo global :=
  { locked : excl unitO
  }.

Section mutex۰G.
  Context `{mutex۰G : MutexG Σ}.

  #[local] Definition locked' γ۰locked :=
    excl γ۰locked ().
  #[local] Definition locked γ :=
    locked' γ.(mutex۰name۰locked).

  Please Definition mutex۰init γ b : iProp Σ :=
    γ.(mutex۰name۰self) ↦ᵣ #b ∗
    if b then True%I else locked γ.

  #[local] Definition inv۰inner γ P : iProp Σ :=
    ∃ b,
    γ.(mutex۰name۰self) ↦ᵣ #b ∗
    match b with
    | true =>
        True
    | false =>
        locked γ ∗
        P
    end.
  Please Definition mutex۰inv γ P :=
    inv nroot (inv۰inner γ P).

  Please Definition mutex۰locked :=
    locked.

  #[global] Instance mutex۰invｰcontractive γ :
    Contractive (mutex۰inv γ).
  Proof.
    rewrite /mutex۰inv /inv۰inner.
    solve_contractive.
  Qed.
  #[global] Instance mutex۰invｰne γ :
    NonExpansive (mutex۰inv γ).
  Proof.
    apply _.
  Qed.
  #[global] Instance mutex۰invｰproper γ :
    Proper ((≡) ==> (≡)) (mutex۰inv γ).
  Proof.
    apply _.
  Qed.

  Zoo derive Timeless for mutex۰init.
  Zoo derive Timeless for mutex۰locked.

  Zoo derive Persistent for mutex۰inv.

  Lemma mutex۰initｰexclusive γ b1 b2 :
    mutex۰init γ b1 -∗
    mutex۰init γ b2 -∗
    False.
  Proof.
    iSteps.
  Qed.
  Lemma mutex۰initｰtoｰinv {γ b} P E :
    mutex۰init γ b -∗
    (if b then True else ▷ P) ={E}=∗
    mutex۰inv γ P.
  Proof.
    destruct b; iSteps.
  Qed.

  Lemma mutex۰lockedｰexclusive γ :
    mutex۰locked γ -∗
    mutex۰locked γ -∗
    False.
  Proof.
    apply exclｰexclusive.
  Qed.

  Lemma mutex٠createｰspecｰinit :
    {{{
      True
    }}}
      mutex٠create ()
    {{{
      γ
    , RET γ;
      mutex۰init γ false
    }}}.
  Proof.
    iIntros "%Φ HP HΦ".

    wp۰rec.
    wp۰ref t as "Ht".

    iMod exclｰalloc as "(%γ۰locked & Hlocked)".

    pose γ :=
      {|mutex۰name۰self := t
      ; mutex۰name۰locked := γ۰locked
      |}.

    iApply ("HΦ" $! γ).
    iFrameSteps.
  Qed.
  Lemma mutex٠createｰspec P :
    {{{
      P
    }}}
      mutex٠create ()
    {{{
      γ
    , RET γ;
      mutex۰inv γ P
    }}}.
  Proof.
    iIntros "%Φ HP HΦ".

    iApply wpｰfupd.
    wp۰apply (mutex٠createｰspecｰinit with "[//]") as (γ) "Hinit".
    iMod (mutex۰initｰtoｰinv with "Hinit HP") as "Hinv".
    iApply ("HΦ" with "Hinv").
  Qed.

  Lemma mutex٠create_lockｰspecｰinit :
    {{{
      True
    }}}
      mutex٠create_lock ()
    {{{
      γ
    , RET γ;
      mutex۰init γ true ∗
      mutex۰locked γ
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp۰rec.
    wp۰ref t as "Ht".

    iMod exclｰalloc as "(%γ۰locked & Hlocked)".

    pose γ :=
      {|mutex۰name۰self := t
      ; mutex۰name۰locked := γ۰locked
      |}.

    iApply ("HΦ" $! γ).
    iFrameSteps.
  Qed.
  Lemma mutex٠create_lockｰspec P :
    {{{
      True
    }}}
      mutex٠create_lock ()
    {{{
      γ
    , RET γ;
      mutex۰inv γ P ∗
      mutex۰locked γ
    }}}.
  Proof.
    iIntros "%Φ HP HΦ".

    iApply wpｰfupd.
    wp۰apply (mutex٠create_lockｰspecｰinit with "[//]") as (γ) "(Hinit & Hlocked)".
    iMod (mutex۰initｰtoｰinv P with "Hinit [//]") as "Hinv".
    iApply ("HΦ" with "[$]").
  Qed.

  Lemma mutex٠lockｰspec γ P :
    {{{
      mutex۰inv γ P
    }}}
      mutex٠lock γ
    {{{
      RET ();
      mutex۰locked γ ∗
      P
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".
    iLöb as "HLöb".

    wp۰rec. wp۰pures.

    wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
    iInv "Hinv" as "(%b & Hl & Hb)".
    destruct b; last iSteps.
    wp۰cas as _ | [=].
    iSplitR "HΦ"; first iSteps.
    iModIntro.

    wp۰pures.
    iApply ("HLöb" with "HΦ").
  Qed.
  Lemma mutex٠lockｰspecｰinit γ :
    {{{
      mutex۰init γ false
    }}}
      mutex٠lock γ
    {{{
      RET ();
      mutex۰init γ true ∗
      mutex۰locked γ
    }}}.
  Proof.
    rewrite /mutex٠lock. iSteps.
  Qed.

  Lemma mutex٠unlockｰspec γ P :
    {{{
      mutex۰inv γ P ∗
      mutex۰locked γ ∗
      P
    }}}
      mutex٠unlock γ
    {{{
      RET ();
      True
    }}}.
  Proof.
    iSteps.
  Qed.
  Lemma mutex٠unlockｰspecｰinit γ :
    {{{
      mutex۰init γ true ∗
      mutex۰locked γ
    }}}
      mutex٠unlock γ
    {{{
      RET ();
      mutex۰init γ false
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma mutex٠synchronizeｰspec γ P :
    {{{
      mutex۰inv γ P
    }}}
      mutex٠synchronize γ
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".

    wp۰rec.
    wp۰apply (mutex٠lockｰspec with "Hinv") as "(Hlocked & HP)".
    wp۰apply+ (mutex٠unlockｰspec with "[$Hinv $Hlocked $HP] HΦ").
  Qed.
  #[global] Instance mutex٠synchronizeｰdiaspec γ P :
    DIASPEC
    {{
      mutex۰inv γ P
    }}
      mutex٠synchronize γ
    {{
      RET ();
      True
    }}.
  Proof.
    iStep.
    iApply mutex٠synchronizeｰspec.
  Qed.

  Lemma mutex٠protectｰspec Ψ γ P fn :
    {{{
      mutex۰inv γ P ∗
      ( mutex۰locked γ -∗
        P -∗
        WP fn () {{ v,
          mutex۰locked γ ∗
          P ∗
          Ψ v
        }}
      )
    }}}
      mutex٠protect γ fn
    {{{
      v
    , RET v;
      Ψ v
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & Hfn) HΦ".

    wp۰rec.
    wp۰apply+ (mutex٠lockｰspec with "Hinv") as "(Hlocked & HP)".
    wp۰apply+ (wpｰwand with "(Hfn Hlocked HP)") as "%v (Hlocked & HP & HΨ)".
    wp۰apply+ (mutex٠unlockｰspec with "[$Hinv $Hlocked $HP]").
    iSteps.
  Qed.
End mutex۰G.

Require zoo_std.mutex__opaque.

Please opacify.
