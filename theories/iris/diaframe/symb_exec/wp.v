From iris.bi Require Export
  bi
  telescopes.
From iris.proofmode Require Import
  tactics
  notation
  reduction.

From diaframe Require Import
  util_classes
  tele_utils
  solve_defs.

From zoo.iris.program_logic Require Import
  wp
  wp_lifting.
From zoo.iris.diaframe Require Import
  symb_exec.defs.

Import bi.

(* This file instantiates the symbolic execution interface defined in defs for weakest preconditions *)

Set Universe Polymorphism.
Lemma to_tforall {TT : tele} (Ψ : TT → Prop) :
  tforall Ψ → (∀ x, Ψ x).
Proof.
  apply tforall_forall.
Qed.
Unset Universe Polymorphism.

Ltac drop_telescope_tac tele_name intro_pat :=
  revert tele_name; refine (to_tforall _ _); intros intro_pat.

Tactic Notation "drop_telescope" constr(R) "as" simple_intropattern_list(intro_pat) :=
  drop_telescope_tac R intro_pat.

(* useful for pure execution: skips solving a trivial precondition *)
Definition template_I {PROP : bi} n (M : PROP → PROP) {TT : tele} : (TT → PROP) → PROP
  := (λ Q, ▷^n (emp -∗ ∀.. (tt : TT), M $ Q tt))%I.
#[global] Arguments template_I {_} n M {TT} /.

Section template_I_props.
  Context {PROP : bi}.

  Lemma template_I_strong_mono n TT (M : PROP → PROP) :
    (∀ P Q, (P -∗ Q) -∗ M P -∗ M Q) →
    template_strong_mono (template_I n M (TT := TT)).
  Proof.
    move => HM P Q /=.
    iIntros "HPQ HMP !> _" (tt).
    rewrite left_id bi_tforall_elim.
    iRevert "HMP". by iApply HM.
  Qed.

  Lemma template_I_mono TT n (M : PROP → PROP) :
    ModalityMono M →
    template_mono (template_I n M (TT := TT)).
  Proof.
    move => HM P Q /= HPQ.
    iIntros "HMP !> _" (tt).
    rewrite left_id bi_tforall_elim.
    iApply HM; last done. done.
  Qed.
End template_I_props.

Section wp_executor.
  Context `{iris_G : !IrisG Λ Σ}.

  Instance wp_execute_op : ExecuteOp (iPropI Σ) (expr Λ) [tele_pair coPset; val Λ → iPropI Σ] :=
    λ e, (λᵗ E Φ, WP e @ E {{ Φ }})%I.
  #[global] Arguments wp_execute_op e !R /.

  #[global] Instance as_wp_execution e E Φ :
    AsExecutionOf (WP e @ E {{ Φ }})%I wp_execute_op e [tele_arg3 E; Φ].
  Proof.
    done.
  Qed.

  Instance wp_red_cond : ReductionCondition (iPropI Σ) (expr Λ) [tele_pair coPset] := (
    λ A, λᵗ E, λ e e' M,
      ∀ Φ,
      M (λ a, WP e' a @ E {{ Φ }}) -∗
      WP e @ E {{ Φ }}
  )%I.
  #[global] Arguments wp_red_cond A !R e e' M /.

  #[global] Instance wp_red_cond_well_behaved_equiv A :
    Proper (
      (=) ==> (=) ==>
      (pointwise_relation _ (=)) ==>
      ((pointwise_relation _ (⊣⊢)) ==> (⊣⊢)) ==> (⊣⊢)
    ) (wp_red_cond A).
  Proof.
    move => w1 w -> {w1} e1 e -> {e1} e'' e' Hee' M1 M2 HM.
    drop_telescope w as E => /=.
    apply (anti_symm _).
    all: apply forall_mono=> Φ.
    all: rewrite HM // => a.
    all: by rewrite Hee'.
  Qed.
  #[global] Instance wp_red_cond_well_behaved_ent A :
    Proper (
      (=) ==> (=) ==>
      (pointwise_relation _ (=)) ==>
      ((pointwise_relation _ (flip (⊢))) ==> (flip (⊢))) ==> (⊢)
    ) (wp_red_cond A).
  Proof.
    move => w1 w -> {w1} e1 e -> {e1} e'' e' Hee' M1 M2 HM.
    drop_telescope w as E => /=.
    apply forall_mono=> Φ.
    apply wand_mono => //.
    apply HM => a /=.
    by rewrite Hee'.
  Qed.
  #[global] Instance wp_red_cond_well_behaved_tne A :
    Proper (
      (=) ==> (=) ==>
      (pointwise_relation _ (=)) ==>
      ((pointwise_relation _ (⊢)) ==> (⊢)) ==> (flip (⊢))
    ) (wp_red_cond A).
  Proof.
    move => w1 w -> {w1} e1 e -> {e1} e'' e' Hee' M1 M2 HM.
    drop_telescope w as E => /=.
    apply forall_mono=> Φ.
    apply wand_mono => //.
    apply HM => a.
    by rewrite Hee'.
  Qed.

  Instance language_ctx_condition : ContextCondition (expr Λ) :=
    λ K,
      LanguageCtx K.

  #[global] Instance language_ctx_satisfies K :
    LanguageCtx K →
    SatisfiesContextCondition language_ctx_condition K.
  Proof.
    auto.
  Qed.
  #[global] Arguments language_ctx_condition K /.

  Instance wp_template_condition : TemplateCondition (iPropI Σ) [tele_pair coPset; val Λ  → iPropI Σ] :=
    λ A R M R' M',
      template_mono M ∧ R = R' ∧ M = M'.
  #[global] Arguments wp_template_condition _ _ _ /.

  #[global] Instance templateM_satisfies_wp_template_condition R n M1 M2 TT1 TT2 Ps Qs :
    ModalityMono M1 →
    ModalityMono M2 →
    SatisfiesTemplateCondition wp_template_condition R (template_M n M1 M2 TT1 TT2 Ps Qs) R (template_M n M1 M2 TT1 TT2 Ps Qs).
  Proof.
    rewrite /SatisfiesTemplateCondition /= => HM1 HM2.
    split => //.
    by apply template_M_is_mono.
  Qed.

  #[global] Instance wp_execute_reduction_compat :
    ExecuteReductionCompatibility wp_execute_op (λᵗ E _, [tele_arg3 E]) wp_red_cond language_ctx_condition wp_template_condition.
  Proof.
    move => K e A e' M /= HK R R' M' [HM [<- <-]].
    drop_telescope R as E Φ => /=.
    rewrite -wp_bind.
    apply wand_elim_l'.
    rewrite forall_elim /=.
    apply wand_mono => //.
    apply HM => a /=.
    by apply wp_bind_inv.
  Qed.

  Lemma pure_wp_step_exec `(e : expr Λ) φ n e' E P :
    Inhabited (state Λ) →
    PureExec φ n e e' →
    ReductionStep (wp_red_cond, [tele_arg3 E]) e ⊣ ⟨id⟩ ⌜φ⌝ ; P =[▷^n]=> ⟨id⟩ e' ⊣ emp.
  Proof.
    rewrite /ReductionStep' => HS H1 /=.
    apply forall_intro => Φ.
    apply wand_intro_l.
    rewrite -assoc.
    apply wand_elim_l', pure_elim' => Hφ.
    apply wand_intro_r.
    rewrite !left_id (affine P) right_id /=.
    rewrite -wp_lifting.wp_pure_step_later //.
    apply laterN_mono, wand_mono => //. eauto.
  Qed.

  Lemma pure_wp_step_exec_lc `(e : expr Λ) φ n e' E P :
    Inhabited (state Λ) →
    PureExec φ n e e' →
    ReductionStep (wp_red_cond, [tele_arg3 E]) e ⊣ ⟨id⟩ ⌜φ⌝ ; P =[▷^n]=> ⟨id⟩ e' ⊣ £ n.
  Proof.
    rewrite /ReductionStep' => HS H1 /=.
    apply forall_intro => Φ.
    apply wand_intro_l.
    rewrite -assoc.
    apply wand_elim_l', pure_elim' => Hφ.
    apply wand_intro_r.
    rewrite !left_id (affine P) right_id /=.
    by rewrite -wp_lifting.wp_pure_step_later.
  Qed.

  Lemma pure_wp_step_exec_lc_fupd `(e : expr Λ) φ n e' E P :
    Inhabited (state Λ) →
    PureExec φ n e e' →
    ReductionStep (wp_red_cond, [tele_arg3 E]) e ⊣ ⟨fupd E E⟩ ⌜φ⌝ ; P =[▷^n]=> ⟨fupd E E⟩ e' ⊣ £ n.
  Proof.
    rewrite /ReductionStep' => HS H1 /=.
    apply forall_intro => Φ.
    apply wand_intro_l => /=.
    iIntros "[>H1 H2]"; iStopProof.
    rewrite -assoc.
    apply wand_elim_l', pure_elim' => Hφ.
    apply wand_intro_r.
    rewrite !left_id (affine P) right_id /=.
    rewrite -wp_lifting.wp_pure_step_later //.
    apply bi.laterN_mono.
    apply bi.wand_mono; first done.
    by iMod 1.
  Qed.

  Lemma pure_wp_step_exec2 `(e : expr Λ) φ n e' E P :
    Inhabited (state Λ) →
    PureExec φ n e e' →
    SolveSepSideCondition φ →
    ReductionTemplateStep wp_red_cond [tele] P [tele_arg3 E] e (tele_app (TT := [tele]) e') (template_I n (fupd E E)).
  Proof.
    rewrite /ReductionTemplateStep /SolveSepSideCondition => HS H1 Hφ /=.
    apply forall_intro => Φ.
    apply wand_intro_l.
    rewrite (affine P) right_id.
    rewrite -wp_lifting.wp_pure_step_later //.
    apply bi.laterN_mono, wand_mono, fupd_wp. eauto.
  Qed.

  #[global] Instance later_forall_satisfies_template_condition n R (TT : tele) M :
    ModalityMono M →
    SatisfiesTemplateCondition wp_template_condition R (template_I n M (TT := TT)) R (template_I n M).
  Proof.
    rewrite /SatisfiesTemplateCondition /=.
    split => //. by apply template_I_mono.
  Qed.

  Lemma as_unit_fun_texan P e v Q E :
    {{{ P }}} e @ E {{{ RET v; Q }}} →
    {{{ P }}} e @ E {{{ (_ : ()), RET v; Q }}}.
  Proof.
    move => HT Φ.
    iIntros "HP HΦ". iApply (HT with "HP").
    iIntros "!> HQ". by iApply ("HΦ" $! tt).
  Qed.

  Lemma later_if_laterN_if {PROP : bi} (P : PROP) (p : bool) :
    ▷^ (if p then 1 else 0) P ⊣⊢@{PROP} ▷?p P.
  Proof.
    done.
  Qed.

  Lemma later_if_sep {PROP : bi} (P Q : PROP) (p : bool) :
    ▷?p (P ∗ Q) ⊣⊢@{PROP} ▷?p P ∗ ▷?p Q.
  Proof.
    case: p => //=. apply later_sep.
  Qed.

  Lemma if_bool_as_nat (n : nat) (p : bool) :
    TCOr (TCAnd (TCEq n 1) (TCEq p true)) (TCAnd (TCEq n 0) (TCEq p false)) →
    n = if p then 1 else 0.
  Proof.
    by case => [[-> ->] | [-> ->]].
  Qed.

  (* this is basically sym-ex-fupd-exist, but stated in terms of ReductionStep' *)
  Lemma texan_to_red_cond (A B : tele) n p P e Q (f : A -t> B -t> val Λ) f' E1 E2 :
    TCOr (TCAnd (TCEq n 1) (TCEq p true)) (TCAnd (TCEq n 0) (TCEq p false)) →
    (∀.. (a : A) (b : B), tele_app (tele_app f' a) b = of_val (tele_app (tele_app f a) b)) →
    TCOr (Atomic e) (TCEq E1 E2) →
    (* the following rule reduces to texan triple notation when B is a constructor. *)
    (∀.. a : A, ∀ Φ,
      tele_app P a -∗ ▷ (∀.. (b : B), tele_app (tele_app Q a) b -∗ Φ (tele_app (tele_app f a) b)) -∗ WP e @ E2 {{ Φ } }) →
    ReductionStep' wp_red_cond (ε₀)%I n (fupd E1 E2) (fupd E2 E1) A B P Q e f' [tele_arg3 E1].
  Proof.
    rewrite /ReductionStep' => /if_bool_as_nat ->
      /tforall_forall Hf' HeE /tforall_forall HT.
    apply forall_intro => Φ.
    apply wand_intro_r.
    rewrite empty_hyp_first_eq left_id /=.
    match goal with
    | |- (fupd ?E1 ?E2 ?Hp ⊢ wp ?e E1 ?Φ) =>
      enough (Hp ⊢ wp e E2 (fupd E2 E1 ∘ Φ))
    end.
    - destruct HeE as [He | <-].
      * rewrite -wp_atomic.
        by apply fupd_mono.
      * rewrite -fupd_wp -wp_fupd.
        by apply fupd_mono.
    - apply bi_texist_elim => a.
      rewrite later_if_laterN_if.
      wlog:p /(p = true) => [ | -> /=].
      { case: p; [ move => H; by apply H | (move => <-; last done) => /=; by rewrite -bi.later_intro ]. }
      iIntros "[HP HΦ]". iApply (HT with "HP").
      iStopProof. apply later_mono, bi_tforall_mono => b.
      apply wand_mono; first done => /=.
      specialize (Hf' a); apply to_tforall with _ b in Hf'; rewrite Hf' => /=.
      erewrite wp_value_fupd => //. rewrite fupd_trans //.
  Qed.

  (* here is a slightly more readable version: *)
  Lemma sym_ex_fupd_exist (A B : tele) P e Q (f : A -t> B -t> val Λ) E1 E2 K `{LanguageCtx Λ K} Ψ :
    Atomic e ∨ (E1 = E2) →
    (* the following rule reduces to texan triple notation when B is a constructor. *)
    (∀.. a : A, ∀ Φ,
      tele_app P a -∗ ▷ (∀.. (b : B), tele_app (tele_app Q a) b -∗ Φ (tele_app (tele_app f a) b)) -∗ WP e @ E2 {{ Φ } }) →
    (|={E1,E2}=> ∃.. (a : A), tele_app P a ∗ ▷ (∀.. (b : B), tele_app (tele_app Q a) b -∗ |={E2, E1}=> WP (K $ of_val (tele_app (tele_app f a) b)) @ E1 {{ Ψ }}))
      ⊢ WP (K e) @ E1 {{ Ψ }}.
  Proof.
    move => Hmask He.
    rewrite -wp_bind.
    match goal with
    | |- (fupd ?E1 ?E2 ?Hp ⊢ wp ?e E1 ?Φ) =>
      enough (Hp ⊢ wp e E2 (fupd E2 E1 ∘ Φ))
    end.
    - destruct Hmask as [Hat | <-].
      * rewrite -wp_atomic.
        by apply fupd_mono.
      * rewrite -fupd_wp -wp_fupd.
        by apply fupd_mono.
    - apply bi_texist_elim => a.
      revert He => /(dep_eval_tele a) HT.
      iIntros "[HP HΦ]". by iApply (HT with "HP").
  Qed.

  #[global] Instance reduction_step_from e E Φ :
    ReductionStep (wp_red_cond, [tele_arg3 E]) e ⊣ ⟨fupd E E⟩ emp; WP e @ E {{ Φ }} =[▷^0]=> ∃ v, ⟨fupd E E⟩ of_val v ⊣ Φ v.
  Proof.
    rewrite /ReductionStep' /ReductionTemplateStep /=.
    apply forall_intro => Ψ.
    apply wand_intro_l.
    eapply entails_po; [ | apply wand_elim_l'; by iApply wp_strong_mono ].
    rewrite sep_comm.
    apply sep_mono_r.
    apply forall_intro => v.
    rewrite (forall_elim v) => /=.
    erewrite wp_value_fupd => //. rewrite !left_id fupd_trans.
    iIntros "HΦΨ HΦ".
    by iMod ("HΦΨ" with "HΦ") as "H".
  Qed.

  Lemma iris_goal_to_red_cond (A B : tele) n P e Q f' E1 E2 pre (POST : (val Λ → iProp Σ) → A -t> B -t> iProp Σ) :
    TCOr (TCAnd (Atomic e) $
                (∃ fv, ∀.. (a : A), ∀.. (b : B), (AsVal (tele_app (tele_app f' a) b) (tele_app (tele_app fv a) b)))
      )
      (TCEq E1 E2) →
    (∃ fv, (∀.. (a : A), ∀.. (b : B), (AsVal (tele_app (tele_app f' a) b) (tele_app (tele_app fv a) b))) ∧
          (TCEq POST (λ Φ, tele_map (tele_map Φ) fv))) ∨
          (TCEq POST (λ Φ, tele_map (tele_map (λ fe, WP fe @ E2 {{ Φ }}))%I f')) →
    (* the following rule reduces to texan triple notation when B is a constructor. *)
    (∀.. a : A, ∀ Φ,
      pre ∗ tele_app P a -∗ ▷^n (∀.. (b : B), tele_app (tele_app Q a) b -∗ (tele_app (tele_app (POST Φ) a) b)) -∗ WP e @ E2 {{ Φ } }) →
    ReductionStep' wp_red_cond pre n (fupd E1 E2) (fupd E2 E1) A B P Q e f' [tele_arg3 E1].
  Proof.
    rewrite /ReductionStep' => HeE HPOST /tforall_forall HT.
    apply forall_intro => Φ.
    apply wand_intro_r => /=.
    rewrite fupd_frame_l.
    match goal with
    | |- (fupd ?E1 ?E2 ?Hp ⊢ wp ?e E1 ?Φ) =>
      enough (Hp ⊢ wp e E2 (fupd E2 E1 ∘ Φ))
    end.
    - destruct HeE as [[He1 _] | <-].
      * rewrite -wp_atomic.
        by apply fupd_mono.
      * rewrite -fupd_wp -wp_fupd.
        by apply fupd_mono.
    - apply wand_elim_r', bi_texist_elim => a.
      apply wand_intro_l. rewrite assoc.
      iIntros "[HP HΦ]". iApply (HT with "HP").
      iStopProof.
      apply laterN_mono, bi_tforall_mono => b.
      apply wand_mono => //.
      destruct HeE as [[_ He2] | <-]; last first.
      * rewrite fupd_wp.
        destruct HPOST as [[fv [Hf ->]] | ->].
        + rewrite !tele_map_app /=.
          revert Hf => /(dep_eval_tele a) /(dep_eval_tele b) <-.
          rewrite wp_value_fupd' //.
        + rewrite !tele_map_app /=.
          apply wp_mono => //= v.
          exact: fupd_intro.
      * destruct HPOST as [[fv' [Hf ->]] | ->].
        + revert Hf => /(dep_eval_tele a) /(dep_eval_tele b) <-.
          rewrite !wp_value_fupd' /= fupd_trans !tele_map_app //=.
        + rewrite !tele_map_app /=.
          case: He2 => fv /(dep_eval_tele a) /(dep_eval_tele b) <-.
          rewrite !wp_value_fupd' => /=.
          rewrite fupd_trans.
          exact: fupd_intro.
  Qed.

  #[global] Instance red_cond_emp_valid_atomic_no_Φ (A B : tele) P e Q f' fv w E1 E2 pre :
    TCEq (tele_app (TT := [tele_pair coPset]) (λ E, E) w) E1 →
    Atomic e →
    TCEq (to_val e) None →
    (∀.. (a : A), ∀.. (b : B), (AsVal (tele_app (tele_app f' a) b) (tele_app (tele_app fv a) b))) →
    (* the following rule reduces to texan triple notation when B is a constructor. *)
    AsEmpValidWeak
      (ReductionStep' wp_red_cond pre 1 (fupd E1 E2) (fupd E2 E1) A B P Q e f' w)
      ((∀.. a : A,
      pre ∗ tele_app P a -∗ WP e @ E2 {{ λ v, ∃.. (b : B), ⌜v = tele_app (tele_app fv a) b⌝ ∗ tele_app (tele_app Q a) b } })) | 10.
  Proof.
    drop_telescope w as E' => /= ->.
    rewrite /AsEmpValidWeak.
    move => He1 He2 Hfv HPQ.
    eapply iris_goal_to_red_cond.
    - left. split => //. exists fv. done.
    - left. exists fv. done.
    - apply tforall_forall => a Φ /=.
      iIntros "Hpre Hlater".
      iApply (wp_step_fupd with "[Hlater]"); first done.
      { iIntros "!> !>". iApply "Hlater". } iStopProof.
      revert HPQ.
      rewrite bi_tforall_forall.
      rewrite (bi.forall_elim a) => /wand_entails ->.
      apply wp_mono => v /=.
      iIntros "[%b [-> HQ]] HΦ".
      iSpecialize ("HΦ" $! b).
      rewrite !tele_map_app.
      by iApply "HΦ".
  Qed.

  #[global] Instance red_cond_emp_valid_value (A B : tele) n P e Q f' fv E1 pre w :
    TCEq (tele_app (TT := [tele_pair coPset]) (λ E, E) w) E1 →
    (∀.. (a : A), ∀.. (b : B), (AsVal (tele_app (tele_app f' a) b) (tele_app (tele_app fv a) b))) →
    (* the following rule reduces to texan triple notation when B is a constructor. *)
    AsEmpValidWeak
      (ReductionStep' wp_red_cond pre n (fupd E1 E1) (fupd E1 E1) A B P Q e f' w)
      ((∀.. a : A, ∀ Φ,
      pre ∗ tele_app P a -∗ ▷^n (∀.. (b : B), tele_app (tele_app Q a) b -∗ Φ (tele_app (tele_app fv a) b)) -∗ WP e @ E1 {{ Φ } })) | 50.
  Proof.
    drop_telescope w as E' => /= ->.
    rewrite /AsEmpValidWeak.
    move => Hfv HPQ.
    eapply iris_goal_to_red_cond.
    - tc_solve.
    - left. exists fv. done.
    - apply tforall_forall => a Φ.
      revert HPQ.
      rewrite bi_tforall_forall.
      rewrite (bi.forall_elim a).
      rewrite (bi.forall_elim Φ) => /wand_entails ->.
      iIntros "HWP HΦ". iApply "HWP". iStopProof.
      by do 2 setoid_rewrite tele_map_app.
  Qed.

  Lemma red_cond_emp_valid_value_no_Φ (A B : tele) P e Q f' fv E1 pre :
    (∀.. (a : A), ∀.. (b : B), (AsVal (tele_app (tele_app f' a) b) (tele_app (tele_app fv a) b))) →
    (* the following rule reduces to texan triple notation when B is a constructor. *)
    AsEmpValidWeak
      (ReductionStep' wp_red_cond pre 0 (fupd E1 E1) (fupd E1 E1) A B P Q e f' [tele_arg3 E1])
      ((∀.. a : A,
      pre ∗ tele_app P a -∗ WP e @ E1 {{ λ v, ∃.. (b : B), ⌜v = tele_app (tele_app fv a) b⌝ ∗ tele_app (tele_app Q a) b }})).
  Proof. (* so.. the texan version is stronger, since it allows us to eliminate laters? *)
    rewrite /AsEmpValidWeak.
    move => Hfv HPQ.
    eapply iris_goal_to_red_cond.
    - tc_solve.
    - left. exists fv. done.
    - apply tforall_forall => a Φ.
      revert HPQ.
      rewrite bi_tforall_forall.
      rewrite (bi.forall_elim a).
      move => /wand_entails -> /=.
      iIntros "HWP HΦ". iApply (wp_wand with "HWP").
      iIntros (v) "[%b [-> HQ]]".
      iSpecialize ("HΦ" with "HQ"). by rewrite !tele_map_app.
  Qed.

  #[global] Instance red_cond_emp_valid_value_no_Φ_not_value (A B : tele) P e Q f' fv E1 pre w :
    TCEq (tele_app (TT := [tele_pair coPset]) (λ E, E) w) E1 →
    TCEq (to_val e) None →
    (∀.. (a : A), ∀.. (b : B), (AsVal (tele_app (tele_app f' a) b) (tele_app (tele_app fv a) b))) →
    (* the following rule reduces to texan triple notation when B is a constructor. *)
    AsEmpValidWeak
      (ReductionStep' wp_red_cond pre 1 (fupd E1 E1) (fupd E1 E1) A B P Q e f' w)
      ((∀.. a : A,
      pre ∗ tele_app P a -∗ WP e @ E1 {{ λ v, ∃.. (b : B), ⌜v = tele_app (tele_app fv a) b⌝ ∗ tele_app (tele_app Q a) b }})) | 20.
  Proof. (* so.. the texan version is stronger, since it allows us to eliminate laters? *)
    drop_telescope w as E' => /= ->.
    rewrite /AsEmpValidWeak.
    move => He Hfv HPQ.
    eapply iris_goal_to_red_cond.
    - tc_solve.
    - left. exists fv. done.
    - apply tforall_forall => a Φ /=.
      iIntros "Hpre Hlater".
      iApply (wp_step_fupd with "[Hlater]"); first done.
      { iIntros "!> !>". iApply "Hlater". } iStopProof.
      revert HPQ.
      rewrite bi_tforall_forall.
      rewrite (bi.forall_elim a).
      move => /wand_entails ->.
      iApply wp_mono => v /=.
      iIntros "[%b [-> HQ]] HΦ".
      iSpecialize ("HΦ" $! b).
      rewrite !tele_map_app.
      by iApply "HΦ".
  Qed.

  #[global] Instance red_cond_emp_valid_not_value (A B : tele) n P e Q f' E1 pre w :
    TCEq (tele_app (TT := [tele_pair coPset]) (λ E, E) w) E1 →
    AsEmpValidWeak
      (ReductionStep' wp_red_cond pre n (fupd E1 E1) (fupd E1 E1) A B P Q e f' w)
      ((∀.. a : A, ∀ Φ,
      pre ∗ tele_app P a -∗ ▷^n (∀.. (b : B), tele_app (tele_app Q a) b -∗ WP (tele_app (tele_app f' a) b) @ E1 {{ Φ }}) -∗ WP e @ E1 {{ Φ } })) | 25.
  Proof.
    drop_telescope w as E' => /= ->.
    rewrite /AsEmpValidWeak.
    move => HPQ.
    eapply iris_goal_to_red_cond.
    - tc_solve.
    - right. tc_solve.
    - apply tforall_forall => a Φ.
      revert HPQ.
      rewrite bi_tforall_forall.
      rewrite (bi.forall_elim a).
      rewrite (bi.forall_elim Φ) => /wand_entails ->.
      do 2 setoid_rewrite tele_map_app.
      by iIntros "$".
  Qed.
End wp_executor.

(* this instance makes iSteps work on goals built by Program, which for some reason unfolds ReductionStep' goals *)
#[global] Instance template_step_emp_valid {PROP : bi} (pre : PROP) `(red_cond : ReductionCondition PROP E W) e n M1 M2 (A B : tele) P' f'  Q w G :
  AsEmpValidWeak (PROP := PROP) (ReductionStep' red_cond pre n M1 M2 A B P' Q e f' w) G →
  AsEmpValidWeak (PROP := PROP) (ReductionTemplateStep red_cond (qprod A B) pre w e
    (λ pr, tele_app (tele_app f' $ qfst pr) $ qsnd pr) (template_M (PROP := PROP) n M1 M2 A B P' Q)) G.
Proof.
  done.
Qed.

Section abducts.
  Context `{iris_G : !IrisG Λ Σ}.

  #[global] Instance abduct_from_execution P Q e R K e_in' T e_out' MT MT' R' :
    AsExecutionOf P wp_execute_op e R →
    ReshapeExprAnd (expr Λ) e K e_in' (ReductionTemplateStep wp_red_cond T Q%I ((λᵗ E _, [tele_arg3 E]) R) e_in' e_out' MT) →
    SatisfiesContextCondition language_ctx_condition K →
    SatisfiesTemplateCondition wp_template_condition R MT R' MT' →
    HINT1 Q ✱ [MT' $ flip wp_execute_op R' ∘ K ∘ e_out'] ⊫ [id]; P.
  Proof.
    intros. eapply execution_abduct_lem => //. tc_solve.
  Qed.

  #[global] Instance collect_modal_wp_value e v E Φ :
    AsVal e v →
    HINT1 ε₀ ✱ [fupd E E $ Φ v] ⊫ [id]; WP e @ E {{ Φ }} | 10.
  Proof.
    rewrite /AsVal /Abduct /= empty_hyp_first_eq left_id => <-.
    erewrite wp_value_fupd => //.
  Qed.

  #[global] Instance prepend_modal_wp_expr e E Φ :
    PrependModality (WP e @ E {{ Φ }})%I (fupd E E) (WP e @ E {{ Φ }})%I | 20.
  Proof.
    rewrite /PrependModality.
    apply (anti_symm _).
    - rewrite -{2}fupd_wp //.
    - apply fupd_intro.
  Qed.
End abducts.
