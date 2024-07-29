From iris.bi Require Import
  telescopes.
From iris.bi Require Export
  lib.atomic.
From iris.base_logic Require Import
  lib.invariants.

From zoo Require Import
  prelude.
From zoo.iris Require Import
  diaframe.
From zoo.iris.program_logic Require Export
  wp.
From zoo Require Import
  options.

Section atomic_acc.
  Context `{BiFUpd PROP} {TA TB : tele}.

  Implicit Types α : TA → PROP.
  Implicit Types P : PROP.
  Implicit Types β Ψ : TA → TB → PROP.

  #[global] Instance atomic_acc_proper Eo Ei :
    Proper (
      pointwise_relation TA (≡) ==>
      (≡) ==>
      pointwise_relation TA (pointwise_relation TB (≡)) ==>
      pointwise_relation TA (pointwise_relation TB (≡)) ==>
      (≡)
    ) (atomic_acc (PROP := PROP) Eo Ei).
  Proof.
    solve_proper.
  Qed.

  Lemma atomic_acc_frame_l R Eo Ei α P β Ψ :
    R ∗ atomic_acc Eo Ei α P β Ψ ⊢
    atomic_acc Eo Ei α (R ∗ P) β (λ.. x y, R ∗ Ψ x y).
  Proof.
    iIntros "(HR & H)".
    iApply (atomic_acc_wand with "[HR] H").
    iSplit; first iSteps. iIntros "%x %y HΨ". rewrite !tele_app_bind.
    iSteps.
  Qed.
  Lemma atomic_acc_frame_r R Eo Ei α P β Ψ :
    atomic_acc Eo Ei α P β Ψ ∗ R ⊢
    atomic_acc Eo Ei α (P ∗ R) β (λ.. x y, Ψ x y ∗ R).
  Proof.
    iIntros "(H & HR)".
    iApply (atomic_acc_wand with "[HR] H").
    iSplit; first iSteps. iIntros "%x %y HΨ". rewrite !tele_app_bind.
    iSteps.
  Qed.

  #[global] Instance frame_atomic_acc p R Eo Ei α P1 P2 β Ψ1 Ψ2 :
    Frame p R P1 P2 →
    (∀ x y, Frame p R (Ψ1 x y) (Ψ2 x y)) →
    Frame p R (atomic_acc Eo Ei α P1 β (λ.. x y, Ψ1 x y)) (atomic_acc Eo Ei α P2 β (λ.. x y, Ψ2 x y)).
  Proof.
    rewrite /Frame atomic_acc_frame_l => HR HΨ.
    iApply atomic_acc_wand. iSplit.
    - iApply HR.
    - iIntros "%x %y". rewrite !tele_app_bind.
      iApply HΨ.
  Qed.

  #[global] Instance is_except_0_atomic_acc Eo Ei α P β Ψ :
    IsExcept0 (atomic_acc Eo Ei α P β Ψ).
  Proof.
    rewrite /atomic_acc. apply _.
  Qed.
End atomic_acc.

Section atomic_update.
  Context `{BiFUpd PROP} {TA TB : tele}.

  Implicit Types α : TA → PROP.
  Implicit Types β Ψ : TA → TB → PROP.

  #[global] Instance atomic_update_proper Eo Ei :
    Proper (
      pointwise_relation TA (≡) ==>
      pointwise_relation TA (pointwise_relation TB (≡)) ==>
      pointwise_relation TA (pointwise_relation TB (≡)) ==>
      (≡)
    ) (atomic_update (PROP := PROP) Eo Ei).
  Proof.
    rewrite atomic.atomic_update_unseal /atomic.atomic_update_def /atomic_update_pre.
    solve_proper.
  Qed.

  Lemma atomic_update_mono Eo Ei α β Ψ1 Ψ2 :
    (∀.. x y, Ψ1 x y -∗ Ψ2 x y) -∗
    atomic_update Eo Ei α β Ψ1 -∗
    atomic_update Eo Ei α β Ψ2.
  Proof.
    iIntros "HΨ H".
    iEval (rewrite atomic.atomic_update_unseal /atomic.atomic_update_def /atomic_update_pre).
    set Φ := (λ (_ : ()), (∀.. x y, Ψ1 x y -∗ Ψ2 x y) ∗ atomic_update Eo Ei α β Ψ1)%I.
    iApply (fixpoint.greatest_fixpoint_coiter _ Φ); last iFrame.
    iIntros "!>" ([]) "(HΨ & H)". rewrite atomic.aupd_unfold /atomic_acc.
    iMod "H" as "(%x & Hα & H)".
    iModIntro. iExists x. iFrame. iSplit.
    - iIntros "Hα". iFrame.
      iApply ("H" with "Hα").
    - iIntros "%y Hβ".
      iMod ("H" with "Hβ") as "HΨ1".
      iApply "HΨ".
      iSteps.
  Qed.
  Lemma atomic_update_wand Eo Ei α β Ψ1 Ψ2 :
    atomic_update Eo Ei α β Ψ1 -∗
    (∀.. x y, Ψ1 x y -∗ Ψ2 x y) -∗
    atomic_update Eo Ei α β Ψ2.
  Proof.
    iIntros "H HΨ".
    iApply (atomic_update_mono with "HΨ H").
  Qed.

  Lemma atomic_update_frame_l R Eo Ei α β Ψ :
    R ∗ atomic_update Eo Ei α β Ψ ⊢
    atomic_update Eo Ei α β (λ.. x y, R ∗ Ψ x y).
  Proof.
    iIntros "(HR & H)".
    iApply (atomic_update_wand with "H"). iIntros "%x %y HΨ". rewrite !tele_app_bind.
    iSteps.
  Qed.
  Lemma atomic_update_frame_r R Eo Ei α β Ψ :
    atomic_update Eo Ei α β Ψ ∗ R ⊢
    atomic_update Eo Ei α β (λ.. x y, Ψ x y ∗ R).
  Proof.
    iIntros "(H & HR)".
    iApply (atomic_update_wand with "H"). iIntros "%x %y HΨ". rewrite !tele_app_bind.
    iSteps.
  Qed.

  #[global] Instance frame_atomic_update p R Eo Ei α β Ψ1 Ψ2 :
    (∀ x y, Frame p R (Ψ1 x y) (Ψ2 x y)) →
    Frame p R (atomic_update Eo Ei α β (λ.. x y, Ψ1 x y)) (atomic_update Eo Ei α β (λ.. x y, Ψ2 x y)).
  Proof.
    rewrite /Frame atomic_update_frame_l => HΨ.
    iApply atomic_update_mono. iIntros "%x %y". rewrite !tele_app_bind.
    iApply HΨ.
  Qed.

  #[global] Instance is_except_0_atomic_update Eo Ei α β Ψ :
    IsExcept0 (atomic_update Eo Ei α β Ψ).
  Proof.
    rewrite /IsExcept0 atomic.aupd_unfold is_except_0 //.
  Qed.
End atomic_update.

Section atomic_wp.
  Context `{iris_GS : !IrisG Λ Σ} {TA TB : tele}.

  Implicit Types α : TA → iProp Σ.
  Implicit Types β Ψ : TA → TB → iProp Σ.
  Implicit Types f : TA → TB → val Λ.

  Definition atomic_wp e E α β Ψ f : iProp Σ :=
    ∀ Φ,
    atomic_update (⊤ ∖ E) ∅ α β (λ.. x y, Ψ x y -∗ Φ (f x y)) -∗
    WP e {{ Φ }}.
  #[global] Arguments atomic_wp e%E E (α β Ψ f)%I : assert.

  #[global] Instance atomic_wp_ne e E n :
    Proper (
      pointwise_relation TA (≡{n}≡) ==>
      pointwise_relation TA (pointwise_relation TB (≡{n}≡)) ==>
      pointwise_relation TA (pointwise_relation TB (≡{n}≡)) ==>
      pointwise_relation TA (pointwise_relation TB (=)) ==>
      (≡{n}≡)
    ) (atomic_wp e E).
  Proof.
    intros α1 α2 Hα β1 β2 Hβ Ψ1 Ψ2 HΨ f1 f2 Hf. rewrite /atomic_wp.
    f_equiv. intros Φ. do 2 f_equiv; [done.. |]. intros x y.
    rewrite !tele_app_bind. solve_proper.
  Qed.
  #[global] Instance atomic_wp_proper e E :
    Proper (
      pointwise_relation TA (≡) ==>
      pointwise_relation TA (pointwise_relation TB (≡)) ==>
      pointwise_relation TA (pointwise_relation TB (≡)) ==>
      pointwise_relation TA (pointwise_relation TB (=)) ==>
      (≡)
    ) (atomic_wp e E).
  Proof.
    intros α1 α2 Hα β1 β2 Hβ Ψ1 Ψ2 HΨ f1 f2 Hf. rewrite /atomic_wp.
    f_equiv. intros Φ. do 2 f_equiv; [done.. |]. intros x y.
    rewrite !tele_app_bind. f_equiv; first solve_proper. f_equiv. apply Hf.
  Qed.

  Lemma atomic_wp_mono e E α β Ψ1 Ψ2 f :
    (∀.. x y, Ψ1 x y -∗ Ψ2 x y) -∗
    atomic_wp e E α β Ψ1 f -∗
    atomic_wp e E α β Ψ2 f.
  Proof.
    iIntros "HΨ H %Φ HΦ".
    iApply "H".
    iApply (atomic_update_wand with "HΦ"). iIntros "%x %y HΨ2". rewrite !tele_app_bind. iIntros "HΨ1".
    iApply "HΨ2".
    iApply "HΨ".
    iSteps.
  Qed.
  Lemma atomic_wp_wand e E α β Ψ1 Ψ2 f :
    atomic_wp e E α β Ψ1 f -∗
    (∀.. x y, Ψ1 x y -∗ Ψ2 x y) -∗
    atomic_wp e E α β Ψ2 f.
  Proof.
    iIntros "H HΨ".
    iApply (atomic_wp_mono with "HΨ H").
  Qed.

  Lemma atomic_wp_frame_l R e E α β Ψ f :
    R ∗ atomic_wp e E α β Ψ f ⊢
    atomic_wp e E α β (λ x y, R ∗ Ψ x y) f.
  Proof.
    iIntros "(HR & H)".
    iApply (atomic_wp_wand with "H").
    iSteps.
  Qed.
  Lemma atomic_wp_frame_r R e E α β Ψ f :
    atomic_wp e E α β Ψ f ∗ R ⊢
    atomic_wp e E α β (λ x y, Ψ x y ∗ R) f.
  Proof.
    iIntros "(H & HR)".
    iApply (atomic_wp_wand with "H").
    iSteps.
  Qed.

  Lemma atomic_wp_mask_weaken E1 E2 e α β Ψ f :
    E1 ⊆ E2 →
    atomic_wp e E1 α β Ψ f ⊢
    atomic_wp e E2 α β Ψ f.
  Proof.
    rewrite /atomic_wp => HE.
    iIntros "H %Φ HΦ".
    iDestruct (atomic_update_mask_weaken _ (⊤ ∖ E1) with "HΦ") as "HΦ"; first solve_ndisj.
    iSteps.
  Qed.

  #[global] Instance frame_atomic_wp p R e E α β Ψ1 Ψ2 f :
    (∀ x y, Frame p R (Ψ1 x y) (Ψ2 x y)) →
    Frame p R (atomic_wp e E α β (λ.. x y, Ψ1 x y) f) (atomic_wp e E α β (λ.. x y, Ψ2 x y) f).
  Proof.
    rewrite /Frame atomic_wp_frame_l => HΨ.
    iApply atomic_wp_mono. iIntros "%x %y". rewrite !tele_app_bind.
    iApply HΨ.
  Qed.

  #[global] Instance is_except_0_atomic_wp e E α β Ψ f :
    IsExcept0 (atomic_wp e E α β Ψ f).
  Proof.
    rewrite /IsExcept0. iIntros ">$".
  Qed.
End atomic_wp.

Notation "'AWP' '<<' ∀∀ x1 .. xn , α '>>' e @ E '<<' ∃∃ y1 .. yn , β | 'RET' v ; Q '>>'" := (
  atomic_wp
    (TA := TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TB := TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    e%E
    E
    (tele_app $ λ x1, .. (λ xn, α%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app (λ y1, .. (λ yn, β%I) .. )) .. )
    (tele_app $ λ x1, .. (λ xn, tele_app (λ y1, .. (λ yn, Q%I) .. )) .. )
    (tele_app $ λ x1, .. (λ xn, tele_app (λ y1, .. (λ yn, v%V) .. )) .. )
)(at level 20,
  α, e, E, β, v, Q at level 200,
  x1 binder,
  xn binder,
  y1 binder,
  yn binder,
  format "'[hv' '[' 'AWP'  '<<'  ∀∀  x1  ..  xn ,  '/  ' '[' α ']'  '/' '>>' ']'  '/  ' e  '/  ' @  E  '/' '[' '<<'  ∃∃ y1  ..  yn ,  '/  ' '[' β  |  '/' RET v ;  Q ']'  '/' '>>' ']' ']'"
) : bi_scope.
Notation "'AWP' '<<' α '>>' e @ E '<<' ∃∃ y1 .. yn , β | 'RET' v ; Q '>>'" := (
  atomic_wp
    (TA := TeleO)
    (TB := TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    e%E
    E
    (tele_app α%I)
    (tele_app $ tele_app (λ y1, .. (λ yn, β%I) .. ))
    (tele_app $ tele_app (λ y1, .. (λ yn, Q%I) .. ))
    (tele_app $ tele_app (λ y1, .. (λ yn, v%V) .. ))
)(at level 20,
  α, e, E, β, v, Q at level 200,
  y1 binder,
  yn binder,
  format "'[hv' '[' 'AWP'  '<<'  '/  ' '[' α ']'  '/' '>>' ']'  '/  ' e  '/  ' @  E  '/' '[' '<<'  ∃∃ y1  ..  yn ,  '/  ' '[' β  |  '/' RET v ;  Q ']'  '/' '>>' ']' ']'"
) : bi_scope.
Notation "'AWP' '<<' ∀∀ x1 .. xn , α '>>' e @ E '<<' β | 'RET' v ; Q '>>'" := (
  atomic_wp
    (TA := TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TB := TeleO)
    e%E
    E
    (tele_app $ λ x1, .. (λ xn, α%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app β%I) .. )
    (tele_app $ λ x1, .. (λ xn, tele_app Q%I) .. )
    (tele_app $ λ x1, .. (λ xn, tele_app v%V) .. )
)(at level 20,
  α, e, E, β, v, Q at level 200,
  x1 binder,
  xn binder,
  format "'[hv' '[' 'AWP'  '<<'  ∀∀  x1  ..  xn ,  '/  ' '[' α ']'  '/' '>>' ']'  '/  ' e  '/  ' @  E  '/' '[' '<<'  '/  ' '[' β  |  '/' RET v ;  Q ']'  '/' '>>' ']' ']'"
) : bi_scope.
Notation "'AWP' '<<' α '>>' e @ E '<<' β | 'RET' v ; Q '>>'" := (
  atomic_wp
    (TA := TeleO)
    (TB := TeleO)
    e%E
    E
    (tele_app α%I)
    (tele_app $ tele_app β%I)
    (tele_app $ tele_app Q%I)
    (tele_app $ tele_app v%V)
)(at level 20,
  α, e, E, β, v, Q at level 200,
  format "'[hv' '[' 'AWP'  '<<'  '/  ' '[' α ']'  '/' '>>' ']'  '/  ' e  '/  ' @  E  '/' '[' '<<'  '/  ' '[' β  |  '/' RET v ;  Q ']'  '/' '>>' ']' ']'"
) : bi_scope.
Notation "'AWP' '<<' ∀∀ x1 .. xn , α '>>' e '<<' ∃∃ y1 .. yn , β | 'RET' v ; Q '>>'" := (
  atomic_wp
    (TA := TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TB := TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    e%E
    ∅
    (tele_app $ λ x1, .. (λ xn, α%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app (λ y1, .. (λ yn, β%I) .. )) .. )
    (tele_app $ λ x1, .. (λ xn, tele_app (λ y1, .. (λ yn, Q%I) .. )) .. )
    (tele_app $ λ x1, .. (λ xn, tele_app (λ y1, .. (λ yn, v%V) .. )) .. )
)(at level 20,
  α, e, β, v, Q at level 200,
  x1 binder,
  xn binder,
  y1 binder,
  yn binder,
  format "'[hv' '[' 'AWP'  '<<'  ∀∀  x1  ..  xn ,  '/  ' '[' α ']'  '/' '>>' ']'  '/  ' e  '/' '[' '<<'  ∃∃ y1  ..  yn ,  '/  ' '[' β  |  '/' RET v ;  Q ']'  '/' '>>' ']' ']'"
) : bi_scope.
Notation "'AWP' '<<' α '>>' e '<<' ∃∃ y1 .. yn , β | 'RET' v ; Q '>>'" := (
  atomic_wp
    (TA := TeleO)
    (TB := TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    e%E
    ∅
    (tele_app α%I)
    (tele_app $ tele_app (λ y1, .. (λ yn, β%I) .. ))
    (tele_app $ tele_app (λ y1, .. (λ yn, Q%I) .. ))
    (tele_app $ tele_app (λ y1, .. (λ yn, v%V) .. ))
)(at level 20,
  α, e, β, v, Q at level 200,
  y1 binder,
  yn binder,
  format "'[hv' '[' 'AWP'  '<<'  '/  ' '[' α ']'  '/' '>>' ']'  '/  ' e  '/' '[' '<<'  ∃∃ y1  ..  yn ,  '/  ' '[' β  |  '/' RET v ;  Q ']'  '/' '>>' ']' ']'"
) : bi_scope.
Notation "'AWP' '<<' ∀∀ x1 .. xn , α '>>' e '<<' β | 'RET' v ; Q '>>'" := (
  atomic_wp
    (TA := TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TB := TeleO)
    e%E
    ∅
    (tele_app $ λ x1, .. (λ xn, α%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app β%I) .. )
    (tele_app $ λ x1, .. (λ xn, tele_app Q%I) .. )
    (tele_app $ λ x1, .. (λ xn, tele_app v%V) .. )
)(at level 20,
  α, e, β, v, Q at level 200,
  x1 binder,
  xn binder,
  format "'[hv' '[' 'AWP'  '<<'  ∀∀  x1  ..  xn ,  '/  ' '[' α ']'  '/' '>>' ']'  '/  ' e  '/' '[' '<<'  '/  ' '[' β  |  '/' RET v ;  Q ']'  '/' '>>' ']' ']'"
) : bi_scope.
Notation "'AWP' '<<' α '>>' e '<<' β | 'RET' v ; Q '>>'" := (
  atomic_wp
    (TA := TeleO)
    (TB := TeleO)
    e%E
    ∅
    (tele_app α%I)
    (tele_app $ tele_app β%I)
    (tele_app $ tele_app Q%I)
    (tele_app $ tele_app v%V)
)(at level 20,
  α, e, β, v, Q at level 200,
  format "'[hv' '[' 'AWP'  '<<'  '/  ' '[' α ']'  '/' '>>' ']'  '/  ' e  '/' '[' '<<'  '/  ' '[' β  |  '/' RET v ;  Q ']'  '/' '>>' ']' ']'"
) : bi_scope.

Section atomic_triple.
  Context `{iris_G : !IrisG Λ Σ} {TA TB : tele}.

  Implicit Types P : iProp Σ.
  Implicit Types α : TA → iProp Σ.
  Implicit Types β Ψ : TA → TB → iProp Σ.
  Implicit Types f : TA → TB → val Λ.

  Definition atomic_triple e E P α β Ψ f : iProp Σ :=
    □ (
      ∀ Φ,
      P -∗
      atomic_update (⊤ ∖ E) ∅ α β (λ.. x y, Ψ x y -∗ Φ (f x y)) -∗
      WP e {{ Φ }}
    ).
  #[global] Arguments atomic_triple e%E E (P α β Ψ f)%I : assert.

  #[global] Instance atomic_triple_ne e E n :
    Proper (
      (≡{n}≡) ==>
      pointwise_relation TA (≡{n}≡) ==>
      pointwise_relation TA (pointwise_relation TB (≡{n}≡)) ==>
      pointwise_relation TA (pointwise_relation TB (≡{n}≡)) ==>
      pointwise_relation TA (pointwise_relation TB (=)) ==>
      (≡{n}≡)
    ) (atomic_triple e E).
  Proof.
    intros P1 P2 HP α1 α2 Hα β1 β2 Hβ Ψ1 Ψ2 HΨ f1 f2 Hf. rewrite /atomic_triple.
    do 2 f_equiv. intros Φ. f_equiv; first done. do 2 f_equiv; [done.. |]. intros x y.
    rewrite !tele_app_bind. solve_proper.
  Qed.
  #[global] Instance atomic_triple_proper e E :
    Proper (
      (≡) ==>
      pointwise_relation TA (≡) ==>
      pointwise_relation TA (pointwise_relation TB (≡)) ==>
      pointwise_relation TA (pointwise_relation TB (≡)) ==>
      pointwise_relation TA (pointwise_relation TB (=)) ==>
      (≡)
    ) (atomic_triple e E).
  Proof.
    intros P1 P2 HP α1 α2 Hα β1 β2 Hβ Ψ1 Ψ2 HΨ f1 f2 Hf. rewrite /atomic_triple.
    do 2 f_equiv. intros Φ. f_equiv; first done. do 2 f_equiv; [done.. |]. intros x y.
    rewrite !tele_app_bind. f_equiv; first solve_proper. f_equiv.
    rewrite leibniz_equiv_iff. solve_proper.
  Qed.

  Lemma atomic_triple_mono e E P α β Ψ1 Ψ2 f :
    □ (∀.. x y, Ψ1 x y -∗ Ψ2 x y) -∗
    atomic_triple e E P α β Ψ1 f -∗
    atomic_triple e E P α β Ψ2 f.
  Proof.
    iIntros "#HΨ #H !> %Φ HP HΦ".
    iApply ("H" with "HP").
    iApply (atomic_update_wand with "HΦ"). iIntros "%x %y HΨ2". rewrite !tele_app_bind. iIntros "HΨ1".
    iApply "HΨ2".
    iApply "HΨ".
    iSteps.
  Qed.
  Lemma atomic_triple_wand e E P α β Ψ1 Ψ2 f :
    atomic_triple e E P α β Ψ1 f -∗
    □ (∀.. x y, Ψ1 x y -∗ Ψ2 x y) -∗
    atomic_triple e E P α β Ψ2 f.
  Proof.
    iIntros "#H #HΨ".
    iApply (atomic_triple_mono with "HΨ H").
  Qed.

  Lemma atomic_triple_frame_l R e E P α β Ψ f :
    atomic_triple e E P α β Ψ f ⊢
    atomic_triple e E (R ∗ P) α β (λ x y, R ∗ Ψ x y) f.
  Proof.
    iIntros "#H !> %Φ (HR & HP) HΦ".
    iApply ("H" with "HP").
    iApply (atomic_update_wand with "HΦ"). iIntros "%x %y HΦ". rewrite !tele_app_bind.
    iSteps.
  Qed.
  Lemma atomic_triple_frame_r R e E P α β Ψ f :
    atomic_triple e E P α β Ψ f ⊢
    atomic_triple e E (P ∗ R) α β (λ x y, Ψ x y ∗ R) f.
  Proof.
    iIntros "#H !> %Φ (HP & HR) HΦ".
    iApply ("H" with "HP").
    iApply (atomic_update_wand with "HΦ"). iIntros "%x %y HΦ". rewrite !tele_app_bind.
    iSteps.
  Qed.

  Lemma atomic_triple_mask_weaken E1 E2 e P α β Ψ f :
    E1 ⊆ E2 →
    atomic_triple e E1 P α β Ψ f ⊢
    atomic_triple e E2 P α β Ψ f.
  Proof.
    rewrite /atomic_triple => HE.
    iIntros "#H !> %Φ HP HΦ".
    iDestruct (atomic_update_mask_weaken _ (⊤ ∖ E1) with "HΦ") as "HΦ"; first solve_ndisj.
    iSteps.
  Qed.

  #[global] Instance frame_atomic_triple R e E P α β Ψ1 Ψ2 f :
    (∀ x y, Frame true R (Ψ1 x y) (Ψ2 x y)) →
    Frame true R (atomic_triple e E P α β (λ.. x y, Ψ1 x y) f) (atomic_triple e E P α β (λ.. x y, Ψ2 x y) f).
  Proof.
    rewrite /Frame.
    iIntros "/= %HΨ (#HR & H)".
    iApply (atomic_triple_wand with "H"). iIntros "!> %x %y HΨ2". rewrite !tele_app_bind.
    iApply HΨ.
    iSteps.
  Qed.
End atomic_triple.

Notation "'<<<' P | ∀∀ x1 .. xn , α '>>>' e @ E '<<<' ∃∃ y1 .. yn , β | 'RET' v ; Q '>>>'" := (
  atomic_triple
    (TA := TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TB := TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    e%E
    E
    P%I
    (tele_app $ λ x1, .. (λ xn, α%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app (λ y1, .. (λ yn, β%I) .. )) .. )
    (tele_app $ λ x1, .. (λ xn, tele_app (λ y1, .. (λ yn, Q%I) .. )) .. )
    (tele_app $ λ x1, .. (λ xn, tele_app (λ y1, .. (λ yn, v%V) .. )) .. )
)(at level 20,
  P, α, e, E, β, v, Q at level 200,
  x1 binder,
  xn binder,
  y1 binder,
  yn binder,
  format "'[hv' <<<  '/  ' '[' P ']'  '/' |  ∀∀  x1  ..  xn ,  '/  ' '[' α ']'  '/' >>>  '/  ' '[hv' e  '/' @  E ']'  '/' <<<  '/  ' ∃∃  y1  ..  yn ,  '/  ' '[' β ']'  '/' |  RET  v ;  '/  ' '[' Q ']'  '/' >>> ']'"
) : bi_scope.
Notation "'<<<' P | α '>>>' e @ E '<<<' ∃∃ y1 .. yn , β | 'RET' v ; Q '>>>'" := (
  atomic_triple
    (TA := TeleO)
    (TB := TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    e%E
    E
    P%I
    (tele_app α%I)
    (tele_app $ tele_app (λ y1, .. (λ yn, β%I) .. ))
    (tele_app $ tele_app (λ y1, .. (λ yn, Q%I) .. ))
    (tele_app $ tele_app (λ y1, .. (λ yn, v%V) .. ))
)(at level 20,
  P, α, e, E, β, v, Q at level 200,
  y1 binder,
  yn binder,
  format "'[hv' <<<  '/  ' '[' P ']'  '/' |  '[' α ']'  '/' >>>  '/  ' '[hv' e  '/' @  E ']'  '/' <<<  '/  ' ∃∃  y1  ..  yn ,  '/  ' '[' β ']'  '/' |  RET  v ;  '/  ' '[' Q ']'  '/' >>> ']'"
) : bi_scope.
Notation "'<<<' P | ∀∀ x1 .. xn , α '>>>' e @ E '<<<' β | 'RET' v ; Q '>>>'" := (
  atomic_triple
    (TA := TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TB := TeleO)
    e%E
    E
    P%I
    (tele_app $ λ x1, .. (λ xn, α%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app β%I) .. )
    (tele_app $ λ x1, .. (λ xn, tele_app Q%I) .. )
    (tele_app $ λ x1, .. (λ xn, tele_app v%V) .. )
)(at level 20,
  P, α, e, E, β, v, Q at level 200,
  x1 binder,
  xn binder,
  format "'[hv' <<<  '/  ' '[' P ']'  '/' |  ∀∀  x1  ..  xn ,  '/  ' '[' α ']'  '/' >>>  '/  ' '[hv' e  '/' @  E ']'  '/' <<<  '/  ' '[' β ']'  '/' |  RET  v ;  '/  ' '[' Q ']'  '/' >>> ']'"
) : bi_scope.
Notation "'<<<' P | α '>>>' e @ E '<<<' β | 'RET' v ; Q '>>>'" := (
  atomic_triple
    (TA := TeleO)
    (TB := TeleO)
    e%E
    E
    P%I
    (tele_app α%I)
    (tele_app $ tele_app β%I)
    (tele_app $ tele_app Q%I)
    (tele_app $ tele_app v%V)
)(at level 20,
  P, α, e, E, β, v, Q at level 200,
  format "'[hv' <<<  '/  ' '[' P ']'  '/' |  '[' α ']'  '/' >>>  '/  ' '[hv' e  '/' @  E ']'  '/' <<<  '/  ' '[' β ']'  '/' |  RET  v ;  '/  ' '[' Q ']'  '/' >>> ']'"
) : bi_scope.

Notation "'<<<' P | ∀∀ x1 .. xn , α '>>>' e @ E '<<<' ∃∃ y1 .. yn , β | 'RET' v ; Q '>>>'" := (
  ⊢ atomic_triple
    (TA := TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TB := TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    e%E
    E
    P%I
    (tele_app $ λ x1, .. (λ xn, α%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app (λ y1, .. (λ yn, β%I) .. )) .. )
    (tele_app $ λ x1, .. (λ xn, tele_app (λ y1, .. (λ yn, Q%I) .. )) .. )
    (tele_app $ λ x1, .. (λ xn, tele_app (λ y1, .. (λ yn, v%V) .. )) .. )
) : stdpp_scope.
Notation "'<<<' P | α '>>>' e @ E '<<<' ∃∃ y1 .. yn , β | 'RET' v ; Q '>>>'" := (
  ⊢ atomic_triple
    (TA := TeleO)
    (TB := TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    e%E
    E
    P%I
    (tele_app α%I)
    (tele_app $ tele_app (λ y1, .. (λ yn, β%I) .. ))
    (tele_app $ tele_app (λ y1, .. (λ yn, Q%I) .. ))
    (tele_app $ tele_app (λ y1, .. (λ yn, v%V) .. ))
) : stdpp_scope.
Notation "'<<<' P | ∀∀ x1 .. xn , α '>>>' e @ E '<<<' β | 'RET' v ; Q '>>>'" := (
  ⊢ atomic_triple
    (TA := TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TB := TeleO)
    e%E
    E
    P%I
    (tele_app $ λ x1, .. (λ xn, α%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app β%I) .. )
    (tele_app $ λ x1, .. (λ xn, tele_app Q%I) .. )
    (tele_app $ λ x1, .. (λ xn, tele_app v%V) .. )
) : stdpp_scope.
Notation "'<<<' P | α '>>>' e @ E '<<<' β | 'RET' v ; Q '>>>'" := (
  ⊢ atomic_triple
    (TA := TeleO)
    (TB := TeleO)
    e%E
    E
    P%I
    (tele_app α%I)
    (tele_app $ tele_app β%I)
    (tele_app $ tele_app Q%I)
    (tele_app $ tele_app v%V)
) : stdpp_scope.

Notation "'<<<' P | ∀∀ x1 .. xn , α '>>>' e '<<<' ∃∃ y1 .. yn , β | 'RET' v ; Q '>>>'" := (
  atomic_triple
    (TA := TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TB := TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    e%E
    ∅
    P%I
    (tele_app $ λ x1, .. (λ xn, α%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app (λ y1, .. (λ yn, β%I) .. )) .. )
    (tele_app $ λ x1, .. (λ xn, tele_app (λ y1, .. (λ yn, Q%I) .. )) .. )
    (tele_app $ λ x1, .. (λ xn, tele_app (λ y1, .. (λ yn, v%V) .. )) .. )
)(at level 20,
  P, α, e, β, v, Q at level 200,
  x1 binder,
  xn binder,
  y1 binder,
  yn binder,
  format "'[hv' <<<  '/  ' '[' P ']'  '/' |  ∀∀  x1  ..  xn ,  '/  ' '[' α ']'  '/' >>>  '/  ' '[' e ']'  '/' <<<  '/  ' ∃∃  y1  ..  yn ,  '/  ' '[' β ']'  '/' |  RET  v ;  '/  ' '[' Q ']'  '/' >>> ']'"
) : bi_scope.
Notation "'<<<' P | α '>>>' e '<<<' ∃∃ y1 .. yn , β | 'RET' v ; Q '>>>'" := (
  atomic_triple
    (TA := TeleO)
    (TB := TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    e%E
    ∅
    P%I
    (tele_app α%I)
    (tele_app $ tele_app (λ y1, .. (λ yn, β%I) .. ))
    (tele_app $ tele_app (λ y1, .. (λ yn, Q%I) .. ))
    (tele_app $ tele_app (λ y1, .. (λ yn, v%V) .. ))
)(at level 20,
  P, α, e, β, v, Q at level 200,
  y1 binder,
  yn binder,
  format "'[hv' <<<  '/  ' '[' P ']'  '/' |  '[' α ']'  '/' >>>  '/  ' '[' e ']'  '/' <<<  '/  ' ∃∃  y1  ..  yn ,  '/  ' '[' β ']'  '/' |  RET  v ;  '/  ' '[' Q ']'  '/' >>> ']'"
) : bi_scope.
Notation "'<<<' P | ∀∀ x1 .. xn , α '>>>' e '<<<' β | 'RET' v ; Q '>>>'" := (
  atomic_triple
    (TA := TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TB := TeleO)
    e%E
    ∅
    P%I
    (tele_app $ λ x1, .. (λ xn, α%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app β%I) .. )
    (tele_app $ λ x1, .. (λ xn, tele_app Q%I) .. )
    (tele_app $ λ x1, .. (λ xn, tele_app v%V) .. )
)(at level 20,
  P, α, e, β, v, Q at level 200,
  x1 binder,
  xn binder,
  format "'[hv' <<<  '/  ' '[' P ']'  '/' |  ∀∀  x1  ..  xn ,  '/  ' '[' α ']'  '/' >>>  '/  ' '[' e ']'  '/' <<<  '/  ' '[' β ']'  '/' |  RET  v ;  '/  ' '[' Q ']'  '/' >>> ']'"
) : bi_scope.
Notation "'<<<' P | α '>>>' e '<<<' β | 'RET' v ; Q '>>>'" := (
  atomic_triple
    (TA := TeleO)
    (TB := TeleO)
    e%E
    ∅
    P%I
    (tele_app α%I)
    (tele_app $ tele_app β%I)
    (tele_app $ tele_app Q%I)
    (tele_app $ tele_app v%V)
)(at level 20,
  P, α, e, β, v, Q at level 200,
  format "'[hv' <<<  '/  ' '[' P ']'  '/' |  '[' α ']'  '/' >>>  '/  ' '[' e ']'  '/' <<<  '/  ' '[' β ']'  '/' |  RET  v ;  '/  ' '[' Q ']'  '/' >>> ']'"
) : bi_scope.

Notation "'<<<' P | ∀∀ x1 .. xn , α '>>>' e '<<<' ∃∃ y1 .. yn , β | 'RET' v ; Q '>>>'" := (
  ⊢ atomic_triple
    (TA := TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TB := TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    e%E
    ∅
    P%I
    (tele_app $ λ x1, .. (λ xn, α%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app (λ y1, .. (λ yn, β%I) .. )) .. )
    (tele_app $ λ x1, .. (λ xn, tele_app (λ y1, .. (λ yn, Q%I) .. )) .. )
    (tele_app $ λ x1, .. (λ xn, tele_app (λ y1, .. (λ yn, v%V) .. )) .. )
) : stdpp_scope.
Notation "'<<<' P | α '>>>' e '<<<' ∃∃ y1 .. yn , β | 'RET' v ; Q '>>>'" := (
  ⊢ atomic_triple
    (TA := TeleO)
    (TB := TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    e%E
    ∅
    P%I
    (tele_app α%I)
    (tele_app $ tele_app (λ y1, .. (λ yn, β%I) .. ))
    (tele_app $ tele_app (λ y1, .. (λ yn, Q%I) .. ))
    (tele_app $ tele_app (λ y1, .. (λ yn, v%V) .. ))
) : stdpp_scope.
Notation "'<<<' P | ∀∀ x1 .. xn , α '>>>' e '<<<' β | 'RET' v ; Q '>>>'" := (
  ⊢ atomic_triple
    (TA := TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TB := TeleO)
    e%E
    ∅
    P%I
    (tele_app $ λ x1, .. (λ xn, α%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app β%I) .. )
    (tele_app $ λ x1, .. (λ xn, tele_app Q%I) .. )
    (tele_app $ λ x1, .. (λ xn, tele_app v%V) .. )
) : stdpp_scope.
Notation "'<<<' P | α '>>>' e '<<<' β | 'RET' v ; Q '>>>'" := (
  ⊢ atomic_triple
    (TA := TeleO)
    (TB := TeleO)
    e%E
    ∅
    P%I
    (tele_app α%I)
    (tele_app $ tele_app β%I)
    (tele_app $ tele_app Q%I)
    (tele_app $ tele_app v%V)
) : stdpp_scope.
