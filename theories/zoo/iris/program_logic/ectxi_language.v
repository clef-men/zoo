From zoo Require Import
  prelude.
From zoo.iris.program_logic Require Import
  language
  ectx_language.
From zoo Require Import
  options.

Section ectxi_language_mixin.
  Context {expr val ectx_item state observation : Type}.
  Context (of_val : val → expr).
  Context (to_val : expr → option val).
  Context (fill_item : ectx_item → expr → expr).
  Context (base_step : thread_id → expr → state → list observation → expr → state → list expr → Prop).

  Record EctxiLanguageMixin := {
    mixin_to_of_val v :
      to_val (of_val v) = Some v ;
    mixin_of_to_val e v :
      to_val e = Some v →
      of_val v = e ;
    mixin_val_stuck tid e1 σ1 κ e2 σ2 es :
      base_step tid e1 σ1 κ e2 σ2 es →
      to_val e1 = None ;

    mixin_fill_item_val Ki e :
      is_Some (to_val (fill_item Ki e)) →
      is_Some (to_val e) ;
    mixin_fill_item_inj Ki :
      Inj (=) (=) (fill_item Ki) ;
    mixin_fill_item_no_val_inj Ki1 Ki2 e1 e2 :
      to_val e1 = None →
      to_val e2 = None →
      fill_item Ki1 e1 = fill_item Ki2 e2 →
      Ki1 = Ki2 ;

    mixin_base_ctx_step_val tid Ki e σ1 κ e2 σ2 es :
      base_step tid (fill_item Ki e) σ1 κ e2 σ2 es →
      is_Some (to_val e) ;
  }.
End ectxi_language_mixin.

Structure ectxi_language := {
  expr : Type ;
  val : Type ;
  ectx_item : Type ;
  state : Type ;
  observation : Type ;

  of_val : val → expr ;
  to_val : expr → option val ;
  fill_item : ectx_item → expr → expr ;
  base_step : thread_id → expr → state → list observation → expr → state → list expr → Prop ;

  ectxi_language_mixin : EctxiLanguageMixin of_val to_val fill_item base_step ;
}.

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

#[global] Arguments Build_ectxi_language {_ _ _ _ _ _ _ _ _} _ : assert.
#[global] Arguments of_val {_} _ : assert.
#[global] Arguments to_val {_} _ : assert.
#[global] Arguments fill_item {_} _ _ : assert.
#[global] Arguments base_step {_} _ _ _ _ _ _ _ : assert.

Section ectxi_language.
  Context {Λ : ectxi_language}.

  Notation ectx := (
    list (ectx_item Λ)
  ).

  Implicit Types e : expr Λ.
  Implicit Types Ki : ectx_item Λ.
  Implicit Types K : ectx.

  Definition fill K e :=
    foldl (flip fill_item) e K.

  #[global] Instance fill_item_inj Ki :
    Inj (=) (=) (fill_item Ki).
  Proof.
    apply ectxi_language_mixin.
  Qed.
  Lemma fill_item_val Ki e :
    is_Some (to_val (fill_item Ki e)) →
    is_Some (to_val e).
  Proof.
    apply ectxi_language_mixin.
  Qed.
  Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
    to_val e1 = None →
    to_val e2 = None →
    fill_item Ki1 e1 = fill_item Ki2 e2 →
    Ki1 = Ki2.
  Proof.
    apply ectxi_language_mixin.
  Qed.
  Lemma base_ctx_step_val tid Ki e σ1 κ e2 σ2 es :
    base_step tid (fill_item Ki e) σ1 κ e2 σ2 es →
    is_Some (to_val e).
  Proof.
    apply ectxi_language_mixin.
  Qed.

  Lemma fill_app K1 K2 e :
    fill (K1 ++ K2) e = fill K2 (fill K1 e).
  Proof.
    apply foldl_app.
  Qed.

  Definition ectxi_lang_ectx_mixin :
    EctxLanguageMixin of_val to_val [] (flip (++)) fill base_step.
  Proof.
    assert (fill_val : ∀ K e, is_Some (to_val (fill K e)) → is_Some (to_val e)).
    { intros K. induction K as [| Ki K IH]=> e //=. intros ?%IH%fill_item_val. done. }
    assert (fill_not_val : ∀ K e, to_val e = None → to_val (fill K e) = None).
    { intros K e. rewrite !eq_None_not_Some. eauto. }
    split.
    - apply ectxi_language_mixin.
    - apply ectxi_language_mixin.
    - apply ectxi_language_mixin.
    - done.
    - intros K1 K2 e. rewrite /fill /= foldl_app //.
    - intros K; induction K as [| Ki K IH]; rewrite /Inj; naive_solver.
    - done.
    - intros tid K K' e1 κ e1' σ1 e2 σ2 es Hfill Hred Hstep; revert K' Hfill.
      induction K as [| Ki K IH] using rev_ind=> /= K' Hfill; eauto using app_nil_r.
      destruct K' as [| Ki' K' _] using @rev_ind; simplify_eq/=.
      { rewrite fill_app in Hstep. apply base_ctx_step_val in Hstep.
        apply fill_val in Hstep. apply not_eq_None_Some in Hstep. done.
      }
      rewrite !fill_app /= in Hfill.
      assert (Ki = Ki') as ->.
      { eapply fill_item_no_val_inj, Hfill; eauto using base_step_not_val.
        apply fill_not_val. revert Hstep. apply ectxi_language_mixin. }
      simplify_eq. destruct (IH K') as [K'' ->]; auto.
      exists K''. rewrite assoc //.
    - intros tid K e1 σ1 κ e2 σ2 es.
      destruct K as [| Ki K _] using rev_ind; simpl; first by auto.
      rewrite fill_app /=.
      intros ?%base_ctx_step_val; eauto using fill_val.
  Qed.

  Canonical ectxi_lang_ectx :=
    Build_ectx_language ectxi_lang_ectx_mixin.
  Canonical ectxi_lang :=
    LanguageOfEctx ectxi_lang_ectx.

  Lemma fill_not_val K e :
    to_val e = None →
    to_val (fill K e) = None.
  Proof.
    rewrite !eq_None_not_Some. eauto using fill_val.
  Qed.

  Lemma ectxi_language_sub_redexes_are_values e :
    ( ∀ Ki e',
      e = fill_item Ki e' →
      is_Some (to_val e')
    ) →
    sub_redexes_are_values e.
  Proof.
    intros Hsub K e' ->. destruct K as [| Ki K _] using @rev_ind=> //=.
    intros []%eq_None_not_Some. eapply fill_val, Hsub. rewrite /= fill_app //.
  Qed.

  #[global] Instance ectxi_lang_ctx_item Ki :
    LanguageCtx (fill_item Ki).
  Proof.
    change (LanguageCtx (fill [Ki])). apply _.
  Qed.
End ectxi_language.

#[global] Arguments ectxi_lang_ectx : clear implicits.
Coercion ectxi_lang_ectx : ectxi_language >-> ectx_language.

#[global] Arguments ectxi_lang : clear implicits.
Coercion ectxi_lang : ectxi_language >-> language.

Definition EctxLanguageOfEctxi '(Build_ectxi_language mixin) : ectx_language :=
  Eval simpl in
  Build_ectx_language (@ectxi_lang_ectx_mixin (Build_ectxi_language mixin)).
#[global] Arguments EctxLanguageOfEctxi : simpl never.
