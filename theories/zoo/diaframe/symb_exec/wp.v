From iris.proofmode Require Import
  ltac_tactics.

From diaframe Require Import
  util_classes
  solve_defs.

From zoo Require Import
  prelude.
From zoo.program_logic Require Import
  wp.
From zoo.diaframe Require Export
  symb_exec.defs.
From zoo Require Import
  options.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Implicit Types TT : tele.

  #[global] Instance absorb_modal_fupd_wp e tid E1 E2 Φ :
    SolveSepSideCondition (E2 ⊆ E1) →
    AbsorbModal
      (WP e ∷ tid @ E1 {{ Φ }})
      (fupd E2 E2)
      (WP e ∷ tid @ E1 {{ Φ }}).
  Proof.
    rewrite /AbsorbModal. auto.
  Qed.

  #[global] Instance dia_wp_value e v E Φ :
    AsVal e v →
    HINT1 ε₀ ✱ [
      |={E}=> Φ v
    ] ⊫ [id];
      WP e @ E {{ Φ }}
  | 10.
  Proof.
    rewrite /AsVal /Abduct /= empty_hyp_first_eq left_id => He.
    apply wp_value_fupd. done.
  Qed.

  #[global] Instance dia_wp_mono e1 K e2 e2' tid E Φ1 Φ2 :
    ReshapeExprAnd _ e1 K e2' (TCEq e2' e2) →
    Context K →
    HINT1
      WP e2 ∷ tid @ E {{ Φ2 }}
    ✱ [
      ∀ v2,
      Φ2 v2 -∗
      WP K (of_val v2) ∷ tid @ E {{ Φ1 }}
    ] ⊫ [id];
      WP e1 ∷ tid @ E {{ Φ1 }}.
  Proof.
    iIntros ((-> & ->) HK) "(HΦ2 & HΦ1)".
    iApply wp_bind'.
    iApply (wp_wand with "HΦ2"). iIntros "%v2 HΦ2".
    iApply ("HΦ1" with "HΦ2").
  Qed.

  Class DiaSpec TT1 TT2 P e E ret Q :=
    dia_spec Φ :
      ∀.. tt1 : TT1,
      tele_app P tt1 -∗
      ▷ (
        ∀.. tt2 : TT2,
        tele_app (tele_app Q tt1) tt2 -∗
        Φ (tele_app (tele_app ret tt1) tt2)
      ) -∗
      WP e @ E {{ Φ }}.
  #[global] Arguments dia_spec _ _ _ _ _ _ _ {_} _ : assert.

  #[global] Instance dia_spec_as_emp_valid_weak TT1 TT2 P e E ret Q :
    AsEmpValidWeak
      (DiaSpec TT1 TT2 P e E ret Q)
      ( ∀ Φ,
        ∀.. tt1 : TT1,
        tele_app P tt1 -∗
        ▷ (
          ∀.. tt2 : TT2,
          tele_app (tele_app Q tt1) tt2 -∗
          Φ (tele_app (tele_app ret tt1) tt2)
        ) -∗
        WP e @ E {{ Φ }}
      ).
  Proof.
    rewrite /DiaSpec. iIntros "%". done.
  Qed.

  #[global] Instance dia_wp_spec e K e' TT1 TT2 P ret Q tid E1 E2 Φ :
    ReshapeExprAnd _ e K e' (
      TCOr (
        TCAnd
          (Atomic e')
          (DiaSpec TT1 TT2 P e' E2 ret Q)
      ) (
        TCAnd
          (TCEq E1 E2)
          (DiaSpec TT1 TT2 P e' E1 ret Q)
      )
    ) →
    Context K →
    HINT1 ε₀ ✱ [
      |={E1,E2}=>
      ∃.. tt1,
      tele_app P tt1 ∗
      ▷ ∀.. tt2,
        tele_app (tele_app Q tt1) tt2 ={E2,E1}=∗
        WP K $ of_val $ tele_app (tele_app ret tt1) tt2 ∷ tid @ E1 {{ Φ }}
    ] ⊫ [id];
      WP e ∷ tid @ E1 {{ Φ }}.
  Proof.
    rewrite /Abduct /=.
    iIntros ((-> & Hspec) HK) "(_ & H)".
    iApply wp_bind'.
    iApply wp_thread_id_mono.
    destruct Hspec as [(Hatomic & Hspec) | (<- & Hspec)].
    all: iMod "H" as "(%tt1 & HP & H)".
    all: iApply (Hspec with "HP").
    all: iIntros "!> %tt2 HQ".
    all: iMod ("H" with "HQ") as "H".
    all: iApply "H".
  Qed.
End zoo_G.

Declare Custom Entry dia_spec_mask.
Notation "" := (
  @top coPset _
)(in custom dia_spec_mask
).
Notation "@ E" :=
  E
( in custom dia_spec_mask at level 200,
  E constr,
  format "'/  ' @  E "
).

Notation "'DIASPEC' {{ P } } e E {{ 'RET' v ; Q } }" := (
  DiaSpec
    TeleO
    TeleO
    P%I
    e%E
    E
    v%V
    Q%I
)(at level 20,
  P at level 200,
  e at level 200,
  E custom dia_spec_mask at level 200,
  Q at level 200,
  format "'[hv' DIASPEC  {{  '/  ' '[' P ']'  '/' } }  '/  ' '[' e ']'  E '/' {{  '/  ' RET  v ;  '/  ' '[' Q ']'  '/' } } ']'"
) : stdpp_scope.
Notation "'DIASPEC' x1 .. xn {{ P } } e E {{ 'RET' v ; Q } }" := (
  DiaSpec
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) ..))
    TeleO
    (λ x1, .. (λ xn, P%I) ..)
    e%E
    E
    (λ x1, .. (λ xn, v%V) ..)
    (λ x1, .. (λ xn, Q%I) ..)
)(at level 20,
  x1 binder,
  xn binder,
  P at level 200,
  e at level 200,
  E custom dia_spec_mask at level 200,
  Q at level 200,
  format "'[hv' DIASPEC  x1  ..  xn  {{  '/  ' '[' P ']'  '/' } }  '/  ' '[' e ']'  E '/' {{  '/  ' RET  v ;  '/  ' '[' Q ']'  '/' } } ']'"
) : stdpp_scope.
Notation "'DIASPEC' {{ P } } e E {{ y1 .. yn , 'RET' v ; Q } }" := (
  DiaSpec
    TeleO
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) ..))
    P%I
    e%E
    E
    (λ y1, .. (λ yn, v%V) ..)
    (λ y1, .. (λ yn, Q%I) ..)
)(at level 20,
  P at level 200,
  e at level 200,
  E custom dia_spec_mask at level 200,
  y1 binder,
  yn binder,
  Q at level 200,
  format "'[hv' DIASPEC  {{  '/  ' '[' P ']'  '/' } }  '/  ' '[' e ']'  E '/' {{  y1  ..  yn ,  '/  ' RET  v ;  '/  ' '[' Q ']'  '/' } } ']'"
) : stdpp_scope.
Notation "'DIASPEC' x1 .. xn {{ P } } e E {{ y1 .. yn , 'RET' v ; Q } }" := (
  DiaSpec
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) ..))
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) ..))
    (λ x1, .. (λ xn, P%I) ..)
    e%E
    E
    (λ x1, .. (λ xn, λ y1, .. (λ yn, v%V) ..) ..)
    (λ x1, .. (λ xn, λ y1, .. (λ yn, Q%I) ..) ..)
)(at level 20,
  x1 binder,
  xn binder,
  P at level 200,
  e at level 200,
  E custom dia_spec_mask at level 200,
  y1 binder,
  yn binder,
  Q at level 200,
  format "'[hv' DIASPEC  x1  ..  xn  {{  '/  ' '[' P ']'  '/' } }  '/  ' '[' e ']'  E '/' {{  y1  ..  yn ,  '/  ' RET  v ;  '/  ' '[' Q ']'  '/' } } ']'"
) : stdpp_scope.
