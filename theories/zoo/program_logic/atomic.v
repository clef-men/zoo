Require Import zoo.prelude.
Require Import zoo.iris.diaframe.
Require Export zoo.iris.bi.lib.atomic.
Require Export zoo.program_logic.wp.
Require Import zoo.options.

Section atomic_acc.
  Context `{BiFUpd PROP} {TA TB : tele}.

  Implicit Type α : TA → PROP.
  Implicit Type P : PROP.
  Implicit Type β Ψ : TA → TB → PROP.

  #[global] Instance atomic_accｰproper Eo Ei :
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

  Lemma atomic_accｰframeｰl R Eo Ei α P β Ψ :
    R ∗ atomic_acc Eo Ei α P β Ψ ⊢
    atomic_acc Eo Ei α (R ∗ P) β (λ.. x y, R ∗ Ψ x y).
  Proof.
    iIntros "(HR & H)".
    iApply (atomic_accｰwand with "[HR] H").
    iSplit; first iSteps. iIntros "%x %y HΨ". rewrite !tele_app_bind.
    iSteps.
  Qed.
  Lemma atomic_accｰframeｰr R Eo Ei α P β Ψ :
    atomic_acc Eo Ei α P β Ψ ∗ R ⊢
    atomic_acc Eo Ei α (P ∗ R) β (λ.. x y, Ψ x y ∗ R).
  Proof.
    iIntros "(H & HR)".
    iApply (atomic_accｰwand with "[HR] H").
    iSplit; first iSteps. iIntros "%x %y HΨ". rewrite !tele_app_bind.
    iSteps.
  Qed.

  #[global] Instance frameｰatomic_acc p R Eo Ei α P1 P2 β Ψ1 Ψ2 :
    Frame p R P1 P2 →
    (∀ x y, Frame p R (Ψ1 x y) (Ψ2 x y)) →
    Frame p R (atomic_acc Eo Ei α P1 β (λ.. x y, Ψ1 x y)) (atomic_acc Eo Ei α P2 β (λ.. x y, Ψ2 x y)).
  Proof.
    rewrite /Frame atomic_accｰframeｰl => HR HΨ.
    iApply atomic_accｰwand. iSplit.
    - iApply HR.
    - iIntros "%x %y". rewrite !tele_app_bind.
      iApply HΨ.
  Qed.

  #[global] Instance is_except_0ｰatomic_acc Eo Ei α P β Ψ :
    IsExcept0 (atomic_acc Eo Ei α P β Ψ).
  Proof.
    rewrite /atomic_acc. apply _.
  Qed.
End atomic_acc.

Section atomic_update.
  Context `{BiFUpd PROP} {TA TB : tele}.

  Implicit Type α : TA → PROP.
  Implicit Type β Ψ : TA → TB → PROP.

  #[global] Instance atomic_updateｰproper Eo Ei :
    Proper (
      pointwise_relation TA (≡) ==>
      pointwise_relation TA (pointwise_relation TB (≡)) ==>
      pointwise_relation TA (pointwise_relation TB (≡)) ==>
      (≡)
    ) (atomic_update (PROP := PROP) Eo Ei).
  Proof.
    rewrite atomic.atomic_updateｰunseal /atomic.atomic_update۰def /atomic_update۰pre.
    solve_proper.
  Qed.

  Lemma atomic_updateｰmono Eo Ei α β Ψ1 Ψ2 :
    (∀.. x y, Ψ1 x y -∗ Ψ2 x y) -∗
    atomic_update Eo Ei α β Ψ1 -∗
    atomic_update Eo Ei α β Ψ2.
  Proof.
    iIntros "HΨ H".
    iEval (rewrite atomic.atomic_updateｰunseal /atomic.atomic_update۰def /atomic_update۰pre).
    set Φ := (λ (_ : ()), (∀.. x y, Ψ1 x y -∗ Ψ2 x y) ∗ atomic_update Eo Ei α β Ψ1)%I.
    iApply (fixpoint_mono.greatest_fixpoint_coiter _ Φ); last iFrame.
    iIntros "!>" ([]) "(HΨ & H)". rewrite atomic.aupdｰunfold /atomic_acc.
    iMod "H" as "(%x & Hα & H)".
    iModIntro. iExists x. iFrame. iSplit.
    - iIntros "Hα". iFrame.
      iApply ("H" with "Hα").
    - iIntros "%y Hβ".
      iMod ("H" with "Hβ") as "HΨ1".
      iApply "HΨ".
      iSteps.
  Qed.
  Lemma atomic_updateｰwand Eo Ei α β Ψ1 Ψ2 :
    atomic_update Eo Ei α β Ψ1 -∗
    (∀.. x y, Ψ1 x y -∗ Ψ2 x y) -∗
    atomic_update Eo Ei α β Ψ2.
  Proof.
    iIntros "H HΨ".
    iApply (atomic_updateｰmono with "HΨ H").
  Qed.

  Lemma atomic_updateｰframeｰl R Eo Ei α β Ψ :
    R ∗ atomic_update Eo Ei α β Ψ ⊢
    atomic_update Eo Ei α β (λ.. x y, R ∗ Ψ x y).
  Proof.
    iIntros "(HR & H)".
    iApply (atomic_updateｰwand with "H"). iIntros "%x %y HΨ". rewrite !tele_app_bind.
    iSteps.
  Qed.
  Lemma atomic_updateｰframeｰr R Eo Ei α β Ψ :
    atomic_update Eo Ei α β Ψ ∗ R ⊢
    atomic_update Eo Ei α β (λ.. x y, Ψ x y ∗ R).
  Proof.
    iIntros "(H & HR)".
    iApply (atomic_updateｰwand with "H"). iIntros "%x %y HΨ". rewrite !tele_app_bind.
    iSteps.
  Qed.

  #[global] Instance frameｰatomic_update p R Eo Ei α β Ψ1 Ψ2 :
    (∀ x y, Frame p R (Ψ1 x y) (Ψ2 x y)) →
    Frame p R (atomic_update Eo Ei α β (λ.. x y, Ψ1 x y)) (atomic_update Eo Ei α β (λ.. x y, Ψ2 x y)).
  Proof.
    rewrite /Frame atomic_updateｰframeｰl => HΨ.
    iApply atomic_updateｰmono. iIntros "%x %y". rewrite !tele_app_bind.
    iApply HΨ.
  Qed.

  #[global] Instance is_except_0ｰatomic_update Eo Ei α β Ψ :
    IsExcept0 (atomic_update Eo Ei α β Ψ).
  Proof.
    rewrite /IsExcept0 atomic.aupdｰunfold is_except_0 //.
  Qed.
End atomic_update.

Section atomic_triple.
  Context `{zoo۰G : !ZooG Σ} {TA TB TP : tele}.

  Implicit Type P : iProp Σ.
  Implicit Type α : TA → iProp Σ.
  Implicit Type β : TA → TB → iProp Σ.
  Implicit Type Ψ : TA → TB → TP → iProp Σ.
  Implicit Type f : TA → TB → TP → val.

  Definition atomic_triple e tid E P α β Ψ f : iProp Σ :=
    ∀ Φ,
    P -∗
    atomic_update (⊤ ∖ E) ∅ α β (λ.. x y, ∀.. z, Ψ x y z -∗ Φ (f x y z)) -∗
    WP e ∷ tid {{ Φ }}.
  #[global] Arguments atomic_triple e%_E tid E (P α β Ψ f)%_I : assert.

  #[global] Instance atomic_tripleｰne e tid E n :
    Proper (
      (≡{n}≡) ==>
      pointwise_relation TA (≡{n}≡) ==>
      pointwise_relation TA (pointwise_relation TB (≡{n}≡)) ==>
      pointwise_relation TA (pointwise_relation TB (pointwise_relation TP (≡{n}≡))) ==>
      pointwise_relation TA (pointwise_relation TB (pointwise_relation TP (=))) ==>
      (≡{n}≡)
    ) (atomic_triple e tid E).
  Proof.
    rewrite /atomic_triple => P1 P2 HP α1 α2 Hα β1 β2 Hβ Ψ1 Ψ2 HΨ f1 f2 Hf.
    do 3 f_equiv; first done.
    do 2 f_equiv; [done.. |].
    intros x y. rewrite !tele_app_bind.
    do 3 f_equiv; first apply HΨ.
    f_equiv. apply Hf.
  Qed.
  #[global] Instance atomic_tripleｰproper e tid E :
    Proper (
      (≡) ==>
      pointwise_relation TA (≡) ==>
      pointwise_relation TA (pointwise_relation TB (≡)) ==>
      pointwise_relation TA (pointwise_relation TB (pointwise_relation TP (≡))) ==>
      pointwise_relation TA (pointwise_relation TB (pointwise_relation TP (=))) ==>
      (≡)
    ) (atomic_triple e tid E).
  Proof.
    rewrite /atomic_triple => P1 P2 HP α1 α2 Hα β1 β2 Hβ Ψ1 Ψ2 HΨ f1 f2 Hf.
    do 3 f_equiv; first done.
    do 2 f_equiv; [done.. |].
    intros x y. rewrite !tele_app_bind.
    do 3 f_equiv; first apply HΨ.
    f_equiv. apply Hf.
  Qed.

  Lemma atomic_tripleｰmono e tid E P α β Ψ1 Ψ2 f :
    (∀.. x y z, Ψ1 x y z -∗ Ψ2 x y z) -∗
    atomic_triple e tid E P α β Ψ1 f -∗
    atomic_triple e tid E P α β Ψ2 f.
  Proof.
    iIntros "HΨ H %Φ HP HΦ".
    iApply ("H" with "HP").
    iApply (atomic_updateｰwand with "HΦ"). iIntros "%x %y HΨ2". rewrite !tele_app_bind. iIntros "%z HΨ1".
    iApply "HΨ2".
    iApply "HΨ".
    iSteps.
  Qed.
  Lemma atomic_tripleｰwand e tid E P α β Ψ1 Ψ2 f :
    atomic_triple e tid E P α β Ψ1 f -∗
    (∀.. x y z, Ψ1 x y z -∗ Ψ2 x y z) -∗
    atomic_triple e tid E P α β Ψ2 f.
  Proof.
    iIntros "H HΨ".
    iApply (atomic_tripleｰmono with "HΨ H").
  Qed.

  #[global] Instance frameｰatomic_triple p R e tid E P α β Ψ1 Ψ2 f :
    (∀ x y z, Frame p R (Ψ1 x y z) (Ψ2 x y z)) →
    Frame p R (atomic_triple e tid E P α β (λ.. x y, Ψ1 x y) f) (atomic_triple e tid E P α β (λ.. x y, Ψ2 x y) f).
  Proof.
    iIntros "/= %HΨ (HR & H)".
    iApply (atomic_tripleｰwand with "H"). iIntros "%x %y %z HΨ2". rewrite !tele_app_bind.
    iApply HΨ.
    iSteps.
  Qed.
End atomic_triple.

Declare Custom Entry atomic_triple_mask.
Notation "" := (
  @empty coPset _
)(in custom atomic_triple_mask
).
Notation "@ E" :=
  E
( in custom atomic_triple_mask at level 200,
  E constr,
  format "'/  ' @  E "
).

Notation "'<<<' P | ∀∀ x1 .. xn , α '>>>' e tid E '<<<' ∃∃ y1 .. yn , β | z1 .. zn , 'RET' v ; Q '>>>'" := (
  atomic_triple
    (TA := TeleS (λ x1, .. (TeleS (λ xn, TeleO)) ..))
    (TB := TeleS (λ y1, .. (TeleS (λ yn, TeleO)) ..))
    (TP := TeleS (λ z1, .. (TeleS (λ zn, TeleO)) ..))
    e%E
    tid
    E
    P%I
    (tele_app $ λ x1, .. (λ xn, α%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, β%I) ..) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, tele_app $ λ z1, .. (λ zn, Q%I) ..) ..) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, tele_app $ λ z1, .. (λ zn, (v%V : val)) ..) ..) ..)
)(at level 20,
  P, α, e, β, v, Q at level 200,
  tid custom wp۰thread_id at level 200,
  E custom atomic_triple_mask at level 200,
  x1 binder,
  xn binder,
  y1 binder,
  yn binder,
  z1 binder,
  zn binder,
  format "'[hv' <<<  '/  ' '[' P ']'  '/' |  ∀∀  x1  ..  xn ,  '/  ' '[' α ']'  '/' >>>  '/  ' '[' e ']'  tid E '/' <<<  '/  ' ∃∃  y1  ..  yn ,  '/  ' '[' β ']'  '/' |  z1  ..  zn ,  '/  ' RET  v ;  '/  ' '[' Q ']'  '/' >>> ']'"
) : bi_scope.
Notation "'<<<' P | ∀∀ x1 .. xn , α '>>>' e tid E '<<<' ∃∃ y1 .. yn , β | 'RET' v ; Q '>>>'" := (
  atomic_triple
    (TA := TeleS (λ x1, .. (TeleS (λ xn, TeleO)) ..))
    (TB := TeleS (λ y1, .. (TeleS (λ yn, TeleO)) ..))
    (TP := TeleO)
    e%E
    tid
    E
    P%I
    (tele_app $ λ x1, .. (λ xn, α%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, β%I) ..) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, tele_app Q%I) ..) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, tele_app (v%V : val)) ..) ..)
)(at level 20,
  P, α, e, β, v, Q at level 200,
  tid custom wp۰thread_id at level 200,
  E custom atomic_triple_mask at level 200,
  x1 binder,
  xn binder,
  y1 binder,
  yn binder,
  format "'[hv' <<<  '/  ' '[' P ']'  '/' |  ∀∀  x1  ..  xn ,  '/  ' '[' α ']'  '/' >>>  '/  ' '[' e ']'  tid E '/' <<<  '/  ' ∃∃  y1  ..  yn ,  '/  ' '[' β ']'  '/' |  RET  v ;  '/  ' '[' Q ']'  '/' >>> ']'"
) : bi_scope.
Notation "'<<<' P | ∀∀ x1 .. xn , α '>>>' e tid E '<<<' β | z1 .. zn , 'RET' v ; Q '>>>'" := (
  atomic_triple
    (TA := TeleS (λ x1, .. (TeleS (λ xn, TeleO)) ..))
    (TB := TeleO)
    (TP := TeleS (λ z1, .. (TeleS (λ zn, TeleO)) ..))
    e%E
    tid
    E
    P%I
    (tele_app $ λ x1, .. (λ xn, α%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app β%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app $ λ z1, .. (λ zn, Q%I) ..) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app $ λ z1, .. (λ zn, (v%V : val)) ..) ..)
)(at level 20,
  P, α, e, β, v, Q at level 200,
  tid custom wp۰thread_id at level 200,
  E custom atomic_triple_mask at level 200,
  x1 binder,
  xn binder,
  z1 binder,
  zn binder,
  format "'[hv' <<<  '/  ' '[' P ']'  '/' |  ∀∀  x1  ..  xn ,  '/  ' '[' α ']'  '/' >>>  '/  ' '[' e ']'  tid E '/' <<<  '/  ' '[' β ']'  '/' |  z1  ..  zn ,  '/  ' RET  v ;  '/  ' '[' Q ']'  '/' >>> ']'"
) : bi_scope.
Notation "'<<<' P | ∀∀ x1 .. xn , α '>>>' e tid E '<<<' β | 'RET' v ; Q '>>>'" := (
  atomic_triple
    (TA := TeleS (λ x1, .. (TeleS (λ xn, TeleO)) ..))
    (TB := TeleO)
    (TP := TeleO)
    e%E
    tid
    E
    P%I
    (tele_app $ λ x1, .. (λ xn, α%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app β%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app Q%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app (v%V : val)) ..)
)(at level 20,
  P, α, e, β, v, Q at level 200,
  tid custom wp۰thread_id at level 200,
  E custom atomic_triple_mask at level 200,
  x1 binder,
  xn binder,
  format "'[hv' <<<  '/  ' '[' P ']'  '/' |  ∀∀  x1  ..  xn ,  '/  ' '[' α ']'  '/' >>>  '/  ' '[' e ']'  tid E '/' <<<  '/  ' '[' β ']'  '/' |  RET  v ;  '/  ' '[' Q ']'  '/' >>> ']'"
) : bi_scope.
Notation "'<<<' P | α '>>>' e tid E '<<<' ∃∃ y1 .. yn , β | z1 .. zn , 'RET' v ; Q '>>>'" := (
  atomic_triple
    (TA := TeleO)
    (TB := TeleS (λ y1, .. (TeleS (λ yn, TeleO)) ..))
    (TP := TeleS (λ z1, .. (TeleS (λ zn, TeleO)) ..))
    e%E
    tid
    E
    P%I
    (tele_app α%I)
    (tele_app $ tele_app $ λ y1, .. (λ yn, β%I) ..)
    (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app $ λ z1, .. (λ zn, Q%I) ..) ..)
    (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app (v%V : val)) ..)
)(at level 20,
  P, α, e, β, v, Q at level 200,
  tid custom wp۰thread_id at level 200,
  E custom atomic_triple_mask at level 200,
  y1 binder,
  yn binder,
  z1 binder,
  zn binder,
  format "'[hv' <<<  '/  ' '[' P ']'  '/' |  '[' α ']'  '/' >>>  '/  ' '[' e ']'  tid E '/' <<<  '/  ' ∃∃  y1  ..  yn ,  '/  ' '[' β ']'  '/' |  z1  ..  zn ,  '/  ' RET  v ;  '/  ' '[' Q ']'  '/' >>> ']'"
) : bi_scope.
Notation "'<<<' P | α '>>>' e tid E '<<<' ∃∃ y1 .. yn , β | 'RET' v ; Q '>>>'" := (
  atomic_triple
    (TA := TeleO)
    (TB := TeleS (λ y1, .. (TeleS (λ yn, TeleO)) ..))
    (TP := TeleO)
    e%E
    tid
    E
    P%I
    (tele_app α%I)
    (tele_app $ tele_app $ λ y1, .. (λ yn, β%I) ..)
    (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app Q%I) ..)
    (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app (v%V : val)) ..)
)(at level 20,
  P, α, e, β, v, Q at level 200,
  tid custom wp۰thread_id at level 200,
  E custom atomic_triple_mask at level 200,
  y1 binder,
  yn binder,
  format "'[hv' <<<  '/  ' '[' P ']'  '/' |  '[' α ']'  '/' >>>  '/  ' '[' e ']'  tid E '/' <<<  '/  ' ∃∃  y1  ..  yn ,  '/  ' '[' β ']'  '/' |  RET  v ;  '/  ' '[' Q ']'  '/' >>> ']'"
) : bi_scope.
Notation "'<<<' P | α '>>>' e tid E '<<<' β | z1 .. zn , 'RET' v ; Q '>>>'" := (
  atomic_triple
    (TA := TeleO)
    (TB := TeleO)
    (TP := TeleS (λ z1, .. (TeleS (λ zn, TeleO)) ..))
    e%E
    tid
    E
    P%I
    (tele_app α%I)
    (tele_app $ tele_app β%I)
    (tele_app $ tele_app $ tele_app $ λ z1, .. (λ zn, Q%I) ..)
    (tele_app $ tele_app $ tele_app $ λ z1, .. (λ zn, (v%V : val)) ..)
)(at level 20,
  P, α, e, β, v, Q at level 200,
  tid custom wp۰thread_id at level 200,
  E custom atomic_triple_mask at level 200,
  z1 binder,
  zn binder,
  format "'[hv' <<<  '/  ' '[' P ']'  '/' |  '[' α ']'  '/' >>>  '/  ' '[' e ']'  tid E '/' <<<  '/  ' '[' β ']'  '/' |  z1  ..  zn ,  '/  ' RET  v ;  '/  ' '[' Q ']'  '/' >>> ']'"
) : bi_scope.
Notation "'<<<' P | α '>>>' e tid E '<<<' β | 'RET' v ; Q '>>>'" := (
  atomic_triple
    (TA := TeleO)
    (TB := TeleO)
    (TP := TeleO)
    e%E
    tid
    E
    P%I
    (tele_app α%I)
    (tele_app $ tele_app β%I)
    (tele_app $ tele_app $ tele_app Q%I)
    (tele_app $ tele_app $ tele_app (v%V : val))
)(at level 20,
  P, α, e, β, v, Q at level 200,
  tid custom wp۰thread_id at level 200,
  E custom atomic_triple_mask at level 200,
  format "'[hv' <<<  '/  ' '[' P ']'  '/' |  '[' α ']'  '/' >>>  '/  ' '[' e ']'  tid E '/' <<<  '/  ' '[' β ']'  '/' |  RET  v ;  '/  ' '[' Q ']'  '/' >>> ']'"
) : bi_scope.

Notation "'<<<' P | ∀∀ x1 .. xn , α '>>>' e tid E '<<<' ∃∃ y1 .. yn , β | z1 .. zn , 'RET' v ; Q '>>>'" := (
  ⊢ atomic_triple
    (TA := TeleS (λ x1, .. (TeleS (λ xn, TeleO)) ..))
    (TB := TeleS (λ y1, .. (TeleS (λ yn, TeleO)) ..))
    (TP := TeleS (λ z1, .. (TeleS (λ zn, TeleO)) ..))
    e%E
    tid
    E
    P%I
    (tele_app $ λ x1, .. (λ xn, α%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, β%I) ..) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, tele_app $ λ z1, .. (λ zn, Q%I) ..) ..) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, tele_app $ λ z1, .. (λ zn, (v%V : val)) ..) ..) ..)
) : stdpp_scope.
Notation "'<<<' P | ∀∀ x1 .. xn , α '>>>' e tid E '<<<' ∃∃ y1 .. yn , β | 'RET' v ; Q '>>>'" := (
  ⊢ atomic_triple
    (TA := TeleS (λ x1, .. (TeleS (λ xn, TeleO)) ..))
    (TB := TeleS (λ y1, .. (TeleS (λ yn, TeleO)) ..))
    (TP := TeleO)
    e%E
    tid
    E
    P%I
    (tele_app $ λ x1, .. (λ xn, α%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, β%I) ..) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, tele_app Q%I) ..) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, tele_app (v%V : val)) ..) ..)
) : stdpp_scope.
Notation "'<<<' P | ∀∀ x1 .. xn , α '>>>' e tid E '<<<' β | z1 .. zn , 'RET' v ; Q '>>>'" := (
  ⊢ atomic_triple
    (TA := TeleS (λ x1, .. (TeleS (λ xn, TeleO)) ..))
    (TB := TeleO)
    (TP := TeleS (λ z1, .. (TeleS (λ zn, TeleO)) ..))
    e%E
    tid
    E
    P%I
    (tele_app $ λ x1, .. (λ xn, α%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app β%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app $ λ z1, .. (λ zn, Q%I) ..) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app $ λ z1, .. (λ zn, (v%V : val)) ..) ..)
) : stdpp_scope.
Notation "'<<<' P | ∀∀ x1 .. xn , α '>>>' e tid E '<<<' β | 'RET' v ; Q '>>>'" := (
  ⊢ atomic_triple
    (TA := TeleS (λ x1, .. (TeleS (λ xn, TeleO)) ..))
    (TB := TeleO)
    (TP := TeleO)
    e%E
    tid
    E
    P%I
    (tele_app $ λ x1, .. (λ xn, α%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app β%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app Q%I) ..)
    (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app (v%V : val)) ..)
) : stdpp_scope.
Notation "'<<<' P | α '>>>' e tid E '<<<' ∃∃ y1 .. yn , β | z1 .. zn , 'RET' v ; Q '>>>'" := (
  ⊢ atomic_triple
    (TA := TeleO)
    (TB := TeleS (λ y1, .. (TeleS (λ yn, TeleO)) ..))
    (TP := TeleS (λ z1, .. (TeleS (λ zn, TeleO)) ..))
    e%E
    tid
    E
    P%I
    (tele_app α%I)
    (tele_app $ tele_app $ λ y1, .. (λ yn, β%I) ..)
    (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app $ λ z1, .. (λ zn, Q%I) ..) ..)
    (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app (v%V : val)) ..)
) : stdpp_scope.
Notation "'<<<' P | α '>>>' e tid E '<<<' ∃∃ y1 .. yn , β | 'RET' v ; Q '>>>'" := (
  ⊢ atomic_triple
    (TA := TeleO)
    (TB := TeleS (λ y1, .. (TeleS (λ yn, TeleO)) ..))
    (TP := TeleO)
    e%E
    tid
    E
    P%I
    (tele_app α%I)
    (tele_app $ tele_app $ λ y1, .. (λ yn, β%I) ..)
    (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app Q%I) ..)
    (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app (v%V : val)) ..)
) : stdpp_scope.
Notation "'<<<' P | α '>>>' e tid E '<<<' β | z1 .. zn , 'RET' v ; Q '>>>'" := (
  ⊢ atomic_triple
    (TA := TeleO)
    (TB := TeleO)
    (TP := TeleS (λ z1, .. (TeleS (λ zn, TeleO)) ..))
    e%E
    tid
    E
    P%I
    (tele_app α%I)
    (tele_app $ tele_app β%I)
    (tele_app $ tele_app $ tele_app $ λ z1, .. (λ zn, Q%I) ..)
    (tele_app $ tele_app $ tele_app $ λ z1, .. (λ zn, (v%V : val)) ..)
) : stdpp_scope.
Notation "'<<<' P | α '>>>' e tid E '<<<' β | 'RET' v ; Q '>>>'" := (
  ⊢ atomic_triple
    (TA := TeleO)
    (TB := TeleO)
    (TP := TeleO)
    e%E
    tid
    E
    P%I
    (tele_app α%I)
    (tele_app $ tele_app β%I)
    (tele_app $ tele_app $ tele_app Q%I)
    (tele_app $ tele_app $ tele_app (v%V : val))
) : stdpp_scope.
