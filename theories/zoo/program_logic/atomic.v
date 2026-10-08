Require Import zoo.prelude.
Require Import zoo.iris.diaframe.
Require Export zoo.iris.bi.lib.atomic.
Require Export zoo.program_logic.wp.
Require Import zoo.options.

Section aacc.
  Context `{BiFUpd PROP} {TA TB : tele}.

  Implicit Type α : TA → PROP.
  Implicit Type P : PROP.
  Implicit Type β Ψ : TA → TB → PROP.

  #[global] Instance aaccｰproper Eo Ei :
    Proper (
      pointwise_relation TA (≡) ==>
      (≡) ==>
      (pointwise_relation TA $ pointwise_relation TB (≡)) ==>
      (pointwise_relation TA $ pointwise_relation TB (≡)) ==>
      (≡)
    ) (aacc (PROP := PROP) Eo Ei).
  Proof.
    solve_proper.
  Qed.

  Lemma aaccｰframeｰl R Eo Ei α P β Ψ :
    R ∗ aacc Eo Ei α P β Ψ ⊢
    aacc Eo Ei α (R ∗ P) β (λ.. x y, R ∗ Ψ x y).
  Proof.
    iIntros "(HR & H)".
    iApply (aaccｰwand with "[HR] H").
    iSplit; first iSteps. iIntros "%x %y HΨ". rewrite !tele_app_bind.
    iSteps.
  Qed.
  Lemma aaccｰframeｰr R Eo Ei α P β Ψ :
    aacc Eo Ei α P β Ψ ∗ R ⊢
    aacc Eo Ei α (P ∗ R) β (λ.. x y, Ψ x y ∗ R).
  Proof.
    iIntros "(H & HR)".
    iApply (aaccｰwand with "[HR] H").
    iSplit; first iSteps. iIntros "%x %y HΨ". rewrite !tele_app_bind.
    iSteps.
  Qed.

  #[global] Instance frameｰaacc p R Eo Ei α P1 P2 β Ψ1 Ψ2 :
    Frame p R P1 P2 →
    (∀ x y, Frame p R (Ψ1 x y) (Ψ2 x y)) →
    Frame p R (aacc Eo Ei α P1 β (λ.. x y, Ψ1 x y)) (aacc Eo Ei α P2 β (λ.. x y, Ψ2 x y)).
  Proof.
    rewrite /Frame aaccｰframeｰl => HR HΨ.
    iApply aaccｰwand. iSplit.
    - iApply HR.
    - iIntros "%x %y". rewrite !tele_app_bind.
      iApply HΨ.
  Qed.

  #[global] Instance is_except_0ｰaacc Eo Ei α P β Ψ :
    IsExcept0 (aacc Eo Ei α P β Ψ).
  Proof.
    rewrite /aacc. apply _.
  Qed.
End aacc.

Section aupd.
  Context `{BiFUpd PROP} {TA TB : tele}.

  Implicit Type α : TA → PROP.
  Implicit Type β Ψ : TA → TB → PROP.

  #[global] Instance aupdｰproper Eo Ei :
    Proper (
      pointwise_relation TA (≡) ==>
      (pointwise_relation TA $ pointwise_relation TB (≡)) ==>
      (pointwise_relation TA $ pointwise_relation TB (≡)) ==>
      (≡)
    ) (aupd (PROP := PROP) Eo Ei).
  Proof.
    rewrite atomic.aupdｰunseal /atomic.aupd۰def /aupd۰pre.
    solve_proper.
  Qed.

  Lemma aupdｰmono Eo Ei α β Ψ1 Ψ2 :
    (∀.. x y, Ψ1 x y -∗ Ψ2 x y) -∗
    aupd Eo Ei α β Ψ1 -∗
    aupd Eo Ei α β Ψ2.
  Proof.
    iIntros "HΨ H".
    iEval (rewrite atomic.aupdｰunseal /atomic.aupd۰def /aupd۰pre).
    set Φ := (λ (_ : ()), (∀.. x y, Ψ1 x y -∗ Ψ2 x y) ∗ aupd Eo Ei α β Ψ1)%I.
    iApply (fixpoint_mono.greatest_fixpoint_coiter _ Φ); last iFrame.
    iIntros "!>" ([]) "(HΨ & H)". rewrite atomic.aupdｰunfold /aacc.
    iMod "H" as "(%x & Hα & H)".
    iModIntro. iExists x. iFrame. iSplit.
    - iIntros "Hα". iFrame.
      iApply ("H" with "Hα").
    - iIntros "%y Hβ".
      iMod ("H" with "Hβ") as "HΨ1".
      iApply "HΨ".
      iSteps.
  Qed.
  Lemma aupdｰwand Eo Ei α β Ψ1 Ψ2 :
    aupd Eo Ei α β Ψ1 -∗
    (∀.. x y, Ψ1 x y -∗ Ψ2 x y) -∗
    aupd Eo Ei α β Ψ2.
  Proof.
    iIntros "H HΨ".
    iApply (aupdｰmono with "HΨ H").
  Qed.

  Lemma aupdｰframeｰl R Eo Ei α β Ψ :
    R ∗ aupd Eo Ei α β Ψ ⊢
    aupd Eo Ei α β (λ.. x y, R ∗ Ψ x y).
  Proof.
    iIntros "(HR & H)".
    iApply (aupdｰwand with "H"). iIntros "%x %y HΨ". rewrite !tele_app_bind.
    iSteps.
  Qed.
  Lemma aupdｰframeｰr R Eo Ei α β Ψ :
    aupd Eo Ei α β Ψ ∗ R ⊢
    aupd Eo Ei α β (λ.. x y, Ψ x y ∗ R).
  Proof.
    iIntros "(H & HR)".
    iApply (aupdｰwand with "H"). iIntros "%x %y HΨ". rewrite !tele_app_bind.
    iSteps.
  Qed.

  #[global] Instance frameｰaupd p R Eo Ei α β Ψ1 Ψ2 :
    (∀ x y, Frame p R (Ψ1 x y) (Ψ2 x y)) →
    Frame p R (aupd Eo Ei α β (λ.. x y, Ψ1 x y)) (aupd Eo Ei α β (λ.. x y, Ψ2 x y)).
  Proof.
    rewrite /Frame aupdｰframeｰl => HΨ.
    iApply aupdｰmono. iIntros "%x %y". rewrite !tele_app_bind.
    iApply HΨ.
  Qed.

  #[global] Instance is_except_0ｰaupd Eo Ei α β Ψ :
    IsExcept0 (aupd Eo Ei α β Ψ).
  Proof.
    rewrite /IsExcept0 atomic.aupdｰunfold is_except_0 //.
  Qed.
End aupd.

Section atriple.
  Context `{zoo۰G : !ZooG Σ} {TA TB TP : tele}.

  Implicit Type P : iProp Σ.
  Implicit Type α : TA → iProp Σ.
  Implicit Type β : TA → TB → iProp Σ.
  Implicit Type Ψ : TA → TB → TP → iProp Σ.
  Implicit Type f : TA → TB → TP → val.

  Definition atriple e tid E P α β Ψ f : iProp Σ :=
    ∀ Φ,
    P -∗
    aupd (⊤ ∖ E) ∅ α β (λ.. x y, ∀.. z, Ψ x y z -∗ Φ (f x y z)) -∗
    WP e ∷ tid {{ Φ }}.
  #[global] Arguments atriple e%_E tid E (P α β Ψ f)%_I : assert.

  #[global] Instance atripleｰne e tid E n :
    Proper (
      (≡{n}≡) ==>
      pointwise_relation TA (≡{n}≡) ==>
      (pointwise_relation TA $ pointwise_relation TB (≡{n}≡)) ==>
      (pointwise_relation TA $ pointwise_relation TB $ pointwise_relation TP (≡{n}≡)) ==>
      (pointwise_relation TA $ pointwise_relation TB $ pointwise_relation TP (=)) ==>
      (≡{n}≡)
    ) (atriple e tid E).
  Proof.
    rewrite /atriple => P1 P2 HP α1 α2 Hα β1 β2 Hβ Ψ1 Ψ2 HΨ f1 f2 Hf.
    do 3 f_equiv; first done.
    do 2 f_equiv; [done.. |].
    intros x y. rewrite !tele_app_bind.
    do 3 f_equiv; first apply HΨ.
    f_equiv. apply Hf.
  Qed.
  #[global] Instance atripleｰproper e tid E :
    Proper (
      (≡) ==>
      pointwise_relation TA (≡) ==>
      (pointwise_relation TA $ pointwise_relation TB (≡)) ==>
      (pointwise_relation TA $ pointwise_relation TB $ pointwise_relation TP (≡)) ==>
      (pointwise_relation TA $ pointwise_relation TB $ pointwise_relation TP (=)) ==>
      (≡)
    ) (atriple e tid E).
  Proof.
    rewrite /atriple => P1 P2 HP α1 α2 Hα β1 β2 Hβ Ψ1 Ψ2 HΨ f1 f2 Hf.
    do 3 f_equiv; first done.
    do 2 f_equiv; [done.. |].
    intros x y. rewrite !tele_app_bind.
    do 3 f_equiv; first apply HΨ.
    f_equiv. apply Hf.
  Qed.

  Lemma atripleｰmono e tid E P α β Ψ1 Ψ2 f :
    (∀.. x y z, Ψ1 x y z -∗ Ψ2 x y z) -∗
    atriple e tid E P α β Ψ1 f -∗
    atriple e tid E P α β Ψ2 f.
  Proof.
    iIntros "HΨ H %Φ HP HΦ".
    iApply ("H" with "HP").
    iApply (aupdｰwand with "HΦ"). iIntros "%x %y HΨ2". rewrite !tele_app_bind. iIntros "%z HΨ1".
    iApply "HΨ2".
    iApply "HΨ".
    iSteps.
  Qed.
  Lemma atripleｰwand e tid E P α β Ψ1 Ψ2 f :
    atriple e tid E P α β Ψ1 f -∗
    (∀.. x y z, Ψ1 x y z -∗ Ψ2 x y z) -∗
    atriple e tid E P α β Ψ2 f.
  Proof.
    iIntros "H HΨ".
    iApply (atripleｰmono with "HΨ H").
  Qed.

  #[global] Instance frameｰatriple p R e tid E P α β Ψ1 Ψ2 f :
    (∀ x y z, Frame p R (Ψ1 x y z) (Ψ2 x y z)) →
    Frame p R (atriple e tid E P α β (λ.. x y, Ψ1 x y) f) (atriple e tid E P α β (λ.. x y, Ψ2 x y) f).
  Proof.
    iIntros "/= %HΨ (HR & H)".
    iApply (atripleｰwand with "H"). iIntros "%x %y %z HΨ2". rewrite !tele_app_bind.
    iApply HΨ.
    iSteps.
  Qed.
End atriple.

Declare Custom Entry atriple_mask.
Notation "" := (
  @empty coPset _
)(in custom atriple_mask
).
Notation "@ E" :=
  E
( in custom atriple_mask at level 200,
  E constr,
  format "'/  ' @  E "
).

Set Warnings "-closed-notation-not-level-0".
Notation "'<<<' P | ∀∀ x1 .. xn , α '>>>' e tid E '<<<' ∃∃ y1 .. yn , β | z1 .. zn , 'RET' v ; Q '>>>'" := (
  atriple
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
  E custom atriple_mask at level 200,
  x1 binder,
  xn binder,
  y1 binder,
  yn binder,
  z1 binder,
  zn binder,
  format "'[hv' <<<  '/  ' '[' P ']'  '/' |  ∀∀  x1  ..  xn ,  '/  ' '[' α ']'  '/' >>>  '/  ' '[' e ']'  tid E '/' <<<  '/  ' ∃∃  y1  ..  yn ,  '/  ' '[' β ']'  '/' |  z1  ..  zn ,  '/  ' RET  v ;  '/  ' '[' Q ']'  '/' >>> ']'"
) : bi_scope.
Notation "'<<<' P | ∀∀ x1 .. xn , α '>>>' e tid E '<<<' ∃∃ y1 .. yn , β | 'RET' v ; Q '>>>'" := (
  atriple
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
  E custom atriple_mask at level 200,
  x1 binder,
  xn binder,
  y1 binder,
  yn binder,
  format "'[hv' <<<  '/  ' '[' P ']'  '/' |  ∀∀  x1  ..  xn ,  '/  ' '[' α ']'  '/' >>>  '/  ' '[' e ']'  tid E '/' <<<  '/  ' ∃∃  y1  ..  yn ,  '/  ' '[' β ']'  '/' |  RET  v ;  '/  ' '[' Q ']'  '/' >>> ']'"
) : bi_scope.
Notation "'<<<' P | ∀∀ x1 .. xn , α '>>>' e tid E '<<<' β | z1 .. zn , 'RET' v ; Q '>>>'" := (
  atriple
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
  E custom atriple_mask at level 200,
  x1 binder,
  xn binder,
  z1 binder,
  zn binder,
  format "'[hv' <<<  '/  ' '[' P ']'  '/' |  ∀∀  x1  ..  xn ,  '/  ' '[' α ']'  '/' >>>  '/  ' '[' e ']'  tid E '/' <<<  '/  ' '[' β ']'  '/' |  z1  ..  zn ,  '/  ' RET  v ;  '/  ' '[' Q ']'  '/' >>> ']'"
) : bi_scope.
Notation "'<<<' P | ∀∀ x1 .. xn , α '>>>' e tid E '<<<' β | 'RET' v ; Q '>>>'" := (
  atriple
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
  E custom atriple_mask at level 200,
  x1 binder,
  xn binder,
  format "'[hv' <<<  '/  ' '[' P ']'  '/' |  ∀∀  x1  ..  xn ,  '/  ' '[' α ']'  '/' >>>  '/  ' '[' e ']'  tid E '/' <<<  '/  ' '[' β ']'  '/' |  RET  v ;  '/  ' '[' Q ']'  '/' >>> ']'"
) : bi_scope.
Notation "'<<<' P | α '>>>' e tid E '<<<' ∃∃ y1 .. yn , β | z1 .. zn , 'RET' v ; Q '>>>'" := (
  atriple
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
  E custom atriple_mask at level 200,
  y1 binder,
  yn binder,
  z1 binder,
  zn binder,
  format "'[hv' <<<  '/  ' '[' P ']'  '/' |  '[' α ']'  '/' >>>  '/  ' '[' e ']'  tid E '/' <<<  '/  ' ∃∃  y1  ..  yn ,  '/  ' '[' β ']'  '/' |  z1  ..  zn ,  '/  ' RET  v ;  '/  ' '[' Q ']'  '/' >>> ']'"
) : bi_scope.
Notation "'<<<' P | α '>>>' e tid E '<<<' ∃∃ y1 .. yn , β | 'RET' v ; Q '>>>'" := (
  atriple
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
  E custom atriple_mask at level 200,
  y1 binder,
  yn binder,
  format "'[hv' <<<  '/  ' '[' P ']'  '/' |  '[' α ']'  '/' >>>  '/  ' '[' e ']'  tid E '/' <<<  '/  ' ∃∃  y1  ..  yn ,  '/  ' '[' β ']'  '/' |  RET  v ;  '/  ' '[' Q ']'  '/' >>> ']'"
) : bi_scope.
Notation "'<<<' P | α '>>>' e tid E '<<<' β | z1 .. zn , 'RET' v ; Q '>>>'" := (
  atriple
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
  E custom atriple_mask at level 200,
  z1 binder,
  zn binder,
  format "'[hv' <<<  '/  ' '[' P ']'  '/' |  '[' α ']'  '/' >>>  '/  ' '[' e ']'  tid E '/' <<<  '/  ' '[' β ']'  '/' |  z1  ..  zn ,  '/  ' RET  v ;  '/  ' '[' Q ']'  '/' >>> ']'"
) : bi_scope.
Notation "'<<<' P | α '>>>' e tid E '<<<' β | 'RET' v ; Q '>>>'" := (
  atriple
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
  E custom atriple_mask at level 200,
  format "'[hv' <<<  '/  ' '[' P ']'  '/' |  '[' α ']'  '/' >>>  '/  ' '[' e ']'  tid E '/' <<<  '/  ' '[' β ']'  '/' |  RET  v ;  '/  ' '[' Q ']'  '/' >>> ']'"
) : bi_scope.
Set Warnings "+closed-notation-not-level-0".

Notation "'<<<' P | ∀∀ x1 .. xn , α '>>>' e tid E '<<<' ∃∃ y1 .. yn , β | z1 .. zn , 'RET' v ; Q '>>>'" := (
  ⊢ atriple
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
  ⊢ atriple
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
  ⊢ atriple
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
  ⊢ atriple
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
  ⊢ atriple
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
  ⊢ atriple
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
  ⊢ atriple
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
  ⊢ atriple
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
