Require Import zoo.prelude.
Require Import zoo.iris.base_logic.lib.excl.
Require Import zoo.base.
Require Export zoo_std.mutex__code.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type l : location.
Implicit Type t fn : val.

Class MutexG Σ `{zoo۰G : !ZooG Σ} :=
  { #[local] mutex۰G۰excl۰G :: ExclG Σ unitO
  }.

Definition mutex۰Σ :=
  #[excl۰Σ unitO
  ].
#[global] Instance subG𑁒mutex۰Σ Σ `{zoo۰G : !ZooG Σ} :
  subG mutex۰Σ Σ →
  MutexG Σ.
Proof.
  solve_inG.
Qed.

Section mutex۰G.
  Context `{mutex۰G : MutexG Σ}.

  #[local] Definition metadata :=
    gname.
  Implicit Type γ : metadata.

  #[local] Definition locked γ :=
    excl γ ().

  Definition mutex۰init t b : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    l ↪ γ ∗
    l ↦ᵣ #b ∗
    if b then True else locked γ.

  #[local] Definition inv۰inner l γ P : iProp Σ :=
    ∃ b,
    l ↦ᵣ #b ∗
    match b with
    | true =>
        True
    | false =>
        locked γ ∗
        P
    end.
  Definition mutex۰inv t P : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    l ↪ γ ∗
    inv nroot (inv۰inner l γ P).

  Definition mutex۰locked t : iProp Σ :=
    ∃ l γ,
    ⌜t = #l⌝ ∗
    l ↪ γ ∗
    locked γ.

  #[global] Instance mutex۰inv𑁒contractive t :
    Contractive (mutex۰inv t).
  Proof.
    rewrite /mutex۰inv /inv۰inner.
    solve_contractive.
  Qed.
  #[global] Instance mutex۰inv𑁒ne t :
    NonExpansive (mutex۰inv t).
  Proof.
    apply _.
  Qed.
  #[global] Instance mutex۰inv𑁒proper t :
    Proper ((≡) ==> (≡)) (mutex۰inv t).
  Proof.
    apply _.
  Qed.

  #[global] Instance mutex۰init𑁒timeless t b :
    Timeless (mutex۰init t b).
  Proof.
    apply _.
  Qed.
  #[global] Instance mutex۰locked𑁒timeless t :
    Timeless (mutex۰locked t).
  Proof.
    apply _.
  Qed.

  #[global] Instance mutex۰inv𑁒persistent t P :
    Persistent (mutex۰inv t P).
  Proof.
    apply _.
  Qed.

  Lemma mutex۰init𑁒exclusive t b1 b2 :
    mutex۰init t b1 -∗
    mutex۰init t b2 -∗
    False.
  Proof.
    iSteps.
  Qed.
  Lemma mutex۰init𑁒to𑁒inv {t b} P E :
    mutex۰init t b -∗
    (if b then True else ▷ P) ={E}=∗
    mutex۰inv t P.
  Proof.
    destruct b; iSteps.
  Qed.

  Lemma mutex۰locked𑁒exclusive t :
    mutex۰locked t -∗
    mutex۰locked t -∗
    False.
  Proof.
    iIntros "(%l & %γ & -> & #Hmeta & Hlocked1) (%_l & %_γ & %Heq & _Hmeta & Hlocked2)". injection Heq as <-.
    iDestruct (meta𑁒agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".
    iDestruct (excl𑁒exclusive with "Hlocked1 Hlocked2") as %[].
  Qed.

  Lemma mutex٠create𑁒spec𑁒init :
    {{{
      True
    }}}
      mutex٠create ()
    {{{
      t
    , RET t;
      mutex۰init t false
    }}}.
  Proof.
    iIntros "%Φ HP HΦ".

    wp۰rec.
    wp۰ref l as "Hmeta" "Hl".

    iMod excl𑁒alloc as "(%γ & Hlocked)".
    iMod (meta𑁒set γ with "Hmeta") as "#Hmeta"; first done.

    iSteps.
  Qed.
  Lemma mutex٠create𑁒spec P :
    {{{
      P
    }}}
      mutex٠create ()
    {{{
      t
    , RET t;
      mutex۰inv t P
    }}}.
  Proof.
    iIntros "%Φ HP HΦ".

    iApply wp𑁒fupd.
    wp۰apply (mutex٠create𑁒spec𑁒init with "[//]") as (t) "Hinit".
    iMod (mutex۰init𑁒to𑁒inv with "Hinit HP") as "Hinv".
    iApply ("HΦ" with "Hinv").
  Qed.

  Lemma mutex٠create_lock𑁒spec𑁒init :
    {{{
      True
    }}}
      mutex٠create_lock ()
    {{{
      t
    , RET t;
      mutex۰init t true ∗
      mutex۰locked t
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    wp۰rec.
    wp۰ref l as "Hmeta" "Hl".

    iMod excl𑁒alloc as "(%γ & Hlocked)".
    iMod (meta𑁒set γ with "Hmeta") as "#Hmeta"; first done.

    iSteps.
  Qed.
  Lemma mutex٠create_lock𑁒spec P :
    {{{
      True
    }}}
      mutex٠create_lock ()
    {{{
      t
    , RET t;
      mutex۰inv t P ∗
      mutex۰locked t
    }}}.
  Proof.
    iIntros "%Φ HP HΦ".

    iApply wp𑁒fupd.
    wp۰apply (mutex٠create_lock𑁒spec𑁒init with "[//]") as (t) "(Hinit & Hlocked)".
    iMod (mutex۰init𑁒to𑁒inv P with "Hinit [//]") as "Hinv".
    iApply ("HΦ" with "[$]").
  Qed.

  Lemma mutex٠lock𑁒spec t P :
    {{{
      mutex۰inv t P
    }}}
      mutex٠lock t
    {{{
      RET ();
      mutex۰locked t ∗
      P
    }}}.
  Proof.
    iIntros "%Φ (%l & %γ & -> & #Hmeta & #Hinv) HΦ".
    iLöb as "HLöb".

    wp۰rec. wp۰pures.

    wp۰bind (CAS _ _ _).
    iInv "Hinv" as "(%b & Hl & Hb)".
    destruct b; last iSteps.
    wp۰cas as _ | [=].
    iSplitR "HΦ"; first iSteps.
    iModIntro.

    wp۰pures.
    iApply ("HLöb" with "HΦ").
  Qed.
  Lemma mutex٠lock𑁒spec𑁒init t :
    {{{
      mutex۰init t false
    }}}
      mutex٠lock t
    {{{
      RET ();
      mutex۰init t true ∗
      mutex۰locked t
    }}}.
  Proof.
    rewrite /mutex٠lock. iSteps.
  Qed.

  Lemma mutex٠unlock𑁒spec t P :
    {{{
      mutex۰inv t P ∗
      mutex۰locked t ∗
      P
    }}}
      mutex٠unlock t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ ((%l & %γ & -> & #Hmeta & #Hinv) & (%_l & %_γ & %Heq & #_Hmeta & Hlocked) & HP) HΦ". injection Heq as <-.
    iDestruct (meta𑁒agree with "Hmeta _Hmeta") as %<-. iClear "_Hmeta".

    iSteps.
  Qed.
  Lemma mutex٠unlock𑁒spec𑁒init t :
    {{{
      mutex۰init t true ∗
      mutex۰locked t
    }}}
      mutex٠unlock t
    {{{
      RET ();
      mutex۰init t false
    }}}.
  Proof.
    iSteps.
  Qed.

  Lemma mutex٠synchronize𑁒spec t P :
    {{{
      mutex۰inv t P
    }}}
      mutex٠synchronize t
    {{{
      RET ();
      True
    }}}.
  Proof.
    iIntros "%Φ #Hinv HΦ".

    wp۰rec.
    wp۰apply (mutex٠lock𑁒spec with "Hinv") as "(Hlocked & HP)".
    wp۰apply+ (mutex٠unlock𑁒spec with "[$Hinv $Hlocked $HP] HΦ").
  Qed.
  #[global] Instance mutex٠synchronize𑁒diaspec t P :
    DIASPEC
    {{
      mutex۰inv t P
    }}
      mutex٠synchronize t
    {{
      RET ();
      True
    }}.
  Proof.
    iStep.
    iApply mutex٠synchronize𑁒spec.
  Qed.

  Lemma mutex٠protect𑁒spec Ψ t P fn :
    {{{
      mutex۰inv t P ∗
      ( mutex۰locked t -∗
        P -∗
        WP fn () {{ v,
          mutex۰locked t ∗
          P ∗
          Ψ v
        }}
      )
    }}}
      mutex٠protect t fn
    {{{
      v
    , RET v;
      Ψ v
    }}}.
  Proof.
    iIntros "%Φ (#Hinv & Hfn) HΦ".

    wp۰rec.
    wp۰apply+ (mutex٠lock𑁒spec with "Hinv") as "(Hlocked & HP)".
    wp۰apply+ (wp𑁒wand with "(Hfn Hlocked HP)") as "%v (Hlocked & HP & HΨ)".
    wp۰apply+ (mutex٠unlock𑁒spec with "[$Hinv $Hlocked $HP]").
    iSteps.
  Qed.
End mutex۰G.

Require zoo_std.mutex__opaque.

#[global] Opaque mutex۰init.
#[global] Opaque mutex۰inv.
#[global] Opaque mutex۰locked.
