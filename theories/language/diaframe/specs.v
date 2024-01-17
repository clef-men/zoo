From iris.bi Require Export
  bi
  telescopes
  derived_laws.
From iris.proofmode Require Import
  proofmode.

From diaframe Require Import
  proofmode_base
  symb_exec.defs
  symb_exec.weakestpre
  lib.iris_hints.
From diaframe Require Export
  spec_notation.

From zebre Require Import
  prelude.
From zebre.language Require Import
  notations
  proofmode.
From zebre Require Import
  options.

Class PureExecNoRec ϕ n e1 e2 :=
  is_pure_exec : PureExec (Λ := zebre) ϕ n e1 e2.

Unset Universe Polymorphism.

Section instances.
  Context `{zebre_G : !ZebreG Σ}.

  Open Scope expr_scope.

  #[global] Instance pure_wp_step_exec_inst1 (e : expr) ϕ n e' E :
    (* TODO: prevent unfolding explicit recs *)
    PureExecNoRec ϕ n e e' →
    ReductionTemplateStep wp_red_cond (TeleO*TeleO) (ε₀)%I [tele_arg3 E; NotStuck] e
      (λ pr, tele_app (TT := [tele]) (tele_app (TT := [tele]) e' pr.1) pr.2)
      (template_M n id id TeleO TeleO ⌜ϕ⌝%I emp%I)
  | 80.
      (* used when ϕ is an equality on a new evar: this will cause SolveSepSideCondition to fail *)
      (* this is a ReductionTemplateStep: if it were a ReductionStep, the priority of as_template_step would be considered, not that of this instance *)
  Proof.
    intros.
    refine (pure_wp_step_exec _ _ _ _ _ _ _ _ _). exact H.
  Qed.

  #[global] Instance pure_wp_step_exec_inst2 (e : expr) ϕ n e' E :
    PureExecNoRec ϕ n e e' →
    SolveSepSideCondition ϕ →
    ReductionTemplateStep wp_red_cond [tele] (ε₀)%I [tele_arg3 E; NotStuck] e (tele_app (TT := [tele]) e') (template_I n (fupd E E))%I
  | 8.
  Proof.
    intros. eapply pure_wp_step_exec2 => //. tc_solve.
  Qed.

  #[global] Instance load_step_wp l E1 E2 :
    SPEC ⟨E1, E2⟩ v dq, {{ ▷ l ↦{dq} v }} !#l {{ RET v; l ↦{dq} v }}.
  Proof.
    iSteps as (v dq) "Hl".
    iApply (wp_load with "Hl").
    iSteps.
  Qed.

  #[global] Instance ref_step_wp e v :
    IntoVal e v →
    SPEC {{ True }} ref e {{ l, RET #l; l ↦ v }}
  | 20.
  Proof.
    move => <-.
    iSteps.
    iApply wp_alloc => //.
    iSteps. rewrite loc_add_0. iSteps.
  Qed.

  #[global] Instance alloc_step_wp e v E1 E2 n :
    IntoVal e v →
    SPEC ⟨E1, E2⟩ {{ ⌜0 < n⌝%Z }} Alloc #n e {{ l, RET #l; l ↦∗ replicate (Z.to_nat n) v }}
  | 30.
  Proof.
    move => <- /=.
    iSteps.
    iApply wp_alloc => //.
    iSteps.
  Qed.

  #[global] Instance store_step_wp l v' E1 E2 :
    SPEC ⟨E1, E2⟩ v, {{ ▷ l ↦ v }} #l <- v' {{ RET #(); l ↦ v' }}.
  Proof.
    iSteps as (v) "Hl".
    iApply (wp_store with "Hl").
    iSteps.
  Qed.

  #[global] Instance proph_step :
    SPEC {{ True }} Proph {{ pvs (p : prophecy_id), RET #p; proph p pvs }}.
  Proof.
    iSteps.
    iApply wp_proph; iSteps.
  Qed.

  (* #[global] Instance abduct_resolve_atomic_spec K (e e_in : expr) (p : prophecy_id) (v : val) Φ pre n E1 E2 (TT1 TT2 : tele) *)
  (*     L e' v' U M1 M2 : *)
  (*   ReshapeExprAnd expr e_in K (Resolve e #p v) (TCAnd (LanguageCtx K) $ *)
  (*                                                TCAnd (Atomic StronglyAtomic e) $ *)
  (*                                                TCAnd (Atomic WeaklyAtomic e) $ (SolveSepSideCondition (to_val e = None))) → *)
  (*   ReductionStep' wp_red_cond pre n M1 M2 TT1 TT2 L U e e' [tele_arg3 E2; NotStuck] → (1* does not work for pure since that is a ReductionTemplateStep *1) *)
  (*   IntroducableModality M1 → IntroducableModality M2 → *)
  (*   (TC∀.. ttl, TC∀.. ttr, IntoVal (tele_app (tele_app e' ttl) ttr) (tele_app (tele_app v' ttl) ttr)) → *)
  (*   HINT1 pre ✱ [|={E1, E2}=> ∃ pvs, proph p pvs ∗ ∃.. ttl, tele_app L ttl ∗ *)
  (*     ▷^n (∀ pvs', ∀.. ttr, ⌜pvs = (pair (tele_app (tele_app v' ttl) ttr) v)::pvs'⌝ ∗ proph p pvs' ∗ tele_app (tele_app U ttl) ttr ={E2,E1}=∗ *)
  (*           WP K $ tele_app (tele_app e' ttl) ttr @ E1 {{ Φ }} ) ] *)
  (*         ⊫ [id]; WP e_in @ E1 {{ Φ }} *)
  (* | 45. *)
  (* Proof. *)
  (*   case => -> [HK [He1 [He3 He2]]] HLU HM1 HM2 Hev'. *)
  (*   iStep as "Hpre HL". iApply wp_bind. iMod "HL" as (pvs) "[Hp Hwp]". *)
  (*   { apply resolve_atomic. destruct s; try tc_solve. } *)
  (*   iApply (wp_resolve with "Hp"). apply He2. simpl. *)
  (*   iDestruct "Hwp" as (ttl) "[Hl HΦ]". *)
  (*   rewrite /ReductionStep' /ReductionTemplateStep in HLU. *)
  (*   iPoseProof (HLU with "Hpre") as "HWP". simpl. *)
  (*   iApply "HWP". iApply HM1 => /=. *)
  (*   iExists ttl. iFrame. iIntros "!>" (tt2) "HU". iApply HM2 => /=. *)
  (*   revert Hev'. rewrite /TCTForall /IntoVal => /(dep_eval_tele ttl) /(dep_eval_tele tt2) => Hev'. *)
  (*   rewrite -Hev'. *)
  (*   iApply wp_value. iIntros (pvs'). *)
  (*   iStep 2 as "Hpost Hproph". *)
  (*   iSpecialize ("Hpost" $! pvs' tt2). rewrite -Hev'. iApply "Hpost". *)
  (*   iSteps. *)
  (* Qed. *)

  (* #[global] Instance abduct_resolve_skip K (e_in : expr) (p : proph_id) (v : val) s E1 E2 Φ : *)
  (*   ReshapeExprAnd expr e_in K (Resolve Skip #p v) (LanguageCtx K) → *)
  (*   HINT1 ε₀ ✱ [|={E1, E2}=> ∃ pvs, proph p pvs ∗ *)
  (*     ▷ (∀ pvs', ⌜pvs = (pair (#()) v)::pvs'⌝ ∗ proph p pvs' ={E2,E1}=∗ *)
  (*           WP K $ #() @ s ; E1 {{ Φ }} ) ] *)
  (*         ⊫ [id]; WP e_in @ s ; E1 {{ Φ }} | 45. *)
  (* Proof. *)
  (*   case => -> HK. *)
  (*   iStep as "H". iApply wp_bind. iMod "H". iDecompose "H" as (ps) "Hproph Hpost". *)
  (*   iApply (wp_resolve with "Hproph"). done. *)
  (*   wp_pures. iStep 3 as (ps') "Hpost Hproph". *)
  (*   iMod ("Hpost" with "[Hproph]"); iSteps. *)
  (* Qed. *)

  Opaque val_comparable.

  #[global] Instance cas_step_wp_stronger l v1 v2 E1 E2 :
    SPEC ⟨E1, E2⟩ (v : val),
      {{ ▷ l ↦ v ∗ ⌜val_comparable v v1⌝ }}
        Cas #l v1 v2
      {{ (b : bool), RET #b;
          ⌜b = true⌝ ∗ ⌜v = v1⌝ ∗ l ↦ v2 ∨
          ⌜b = false⌝ ∗ ⌜v ≠ v1⌝ ∗ l ↦ v }}.
  Proof.
    iStep 2 as (v Hv1) "Hl".
    - destruct (decide (v = v1)) as [->|Hneq].
      + iApply (wp_cas_suc with "Hl") => //.
        iSteps.
      + iApply (wp_cas_fail with "Hl") => //.
        iSteps.
  Qed.

  #[global] Instance faa_step_wp l i E1 E2 :
    SPEC ⟨E1, E2⟩ (z : Z), {{ ▷ l ↦ #z }} Faa #l #i {{ RET #z; l ↦ #(z + i) }}.
  Proof.
    iSteps as (z) "Hl".
    iApply (wp_faa with "Hl").
    iSteps.
  Qed.

  #[global] Instance if_step_bool_decide P `{Decision P} e1 e2 E :
    ReductionStep (wp_red_cond, [tele_arg3 E; NotStuck]) if: #(bool_decide P) then e1 else e2 ⊣ ⟨id⟩ emp; ε₀ =[▷^1]=>
      ∃ b : bool, ⟨id⟩ (if b then e1 else e2)%V ⊣ ⌜b = true⌝ ∗ ⌜P⌝ ∨ ⌜b = false⌝ ∗ ⌜¬P⌝
  | 50.
  Proof.
    rewrite /ReductionStep' /=.
    apply bi.forall_intro => Φ.
    iIntros "_ [_ H]".
    case_bool_decide; wp_pures => /=.
    - iApply ("H" $! true). eauto.
    - iApply ("H" $! false). eauto.
  Qed.

  #[global] Instance if_step_bool_decide_neg P `{Decision P} e1 e2 E :
    ReductionStep (wp_red_cond, [tele_arg3 E; NotStuck]) if: #(bool_decide (¬P)) then e1 else e2 ⊣ ⟨id⟩ emp; ε₀ =[▷^1]=>
      ∃ b : bool, ⟨id⟩ (if b then e1 else e2)%V ⊣ ⌜b = true⌝ ∗ ⌜¬P⌝ ∨ ⌜b = false⌝ ∗ ⌜P⌝
  | 49.
  Proof.
    rewrite /ReductionStep' /=.
    apply bi.forall_intro => Φ.
    iIntros "_ [_ H]".
    case_bool_decide => /=.
    - wp_pures.
      iApply ("H" $! true). eauto.
    - wp_pures.
      iApply ("H" $! false). eauto.
  Qed.

  #[global] Instance if_step_negb_bool_decide P `{Decision P} e1 e2 E :
    ReductionStep (wp_red_cond, [tele_arg3 E; NotStuck]) if: #(negb $ bool_decide P) then e1 else e2 ⊣ ⟨id⟩ emp; ε₀ =[▷^1]=>
      ∃ b : bool, ⟨id⟩ (if b then e1 else e2)%V ⊣ ⌜b = true⌝ ∗ ⌜¬P⌝ ∨ ⌜b = false⌝ ∗ ⌜P⌝ | 49.
  Proof.
    rewrite /ReductionStep' /=.
    apply bi.forall_intro => Φ.
    iIntros "_ [_ H]".
    case_bool_decide => /=.
    - wp_pures.
      iApply ("H" $! false). eauto.
    - wp_pures.
      iApply ("H" $! true). eauto.
  Qed.
End instances.

Section unfold_functions.
  Context `{zebre_G : !ZebreG Σ}.

  Fixpoint occurs_in (s : string) (body : expr) : bool :=
    match body with
    | Val _ =>
        false
    | Var s' =>
        if decide (s = s') then true else false
    | Rec b x e =>
        if decide (BNamed s ≠ b ∧ BNamed s ≠ x) then occurs_in s e else false
    | App f a =>
        (occurs_in s f) || (occurs_in s a)
    | Unop _ e =>
        occurs_in s e
    | Binop _ l r =>
        (occurs_in s l) || (occurs_in s r)
    | If c t e =>
        (occurs_in s c) || (occurs_in s t) || (occurs_in s e)
    | Pair l r =>
        (occurs_in s l) || (occurs_in s r)
    | Fst e =>
        occurs_in s e
    | Snd e =>
        occurs_in s e
    | Injl e =>
        occurs_in s e
    | Injr e =>
        occurs_in s e
    | Case c l r =>
        (occurs_in s c) || (occurs_in s l) || (occurs_in s r)
    | Fork e =>
        (occurs_in s e)
    | Alloc n e =>
        (occurs_in s n) || (occurs_in s e)
    | Load e =>
        occurs_in s e
    | Store l e =>
        (occurs_in s l) || (occurs_in s e)
    | Cas l e1 e2 =>
        (occurs_in s l) || (occurs_in s e1) || (occurs_in s e2)
    | Faa l n =>
        (occurs_in s l) || (occurs_in s n)
    | Proph =>
        false
    | Resolve a1 a2 a3 =>
        (occurs_in s a1) || (occurs_in s a2) || (occurs_in s a3)
    end.

  Definition is_recursive_fun (v : val) :=
    match v with
    | ValRec (BNamed f) x e =>
        occurs_in f e
    | _ =>
        false
    end.

  #[global] Instance pure_wp_step_exec_inst_last (e : expr) ϕ n e' E s :
    ( ( ∀ f x e,
        SolveSepSideCondition (is_recursive_fun (ValRec f x e) = false) →
        AsValRec (ValRec f x e) f x e
      ) →
      PureExec ϕ n e e'
    ) →
    SolveSepSideCondition ϕ →
    ReductionTemplateStep wp_red_cond [tele] (ε₁)%I [tele_arg3 E; s] e (tele_app (TT := [tele]) e') (template_I n (fupd E E)).
  Proof.
    intros. eapply pure_wp_step_exec2 => //. tc_solve.
    apply H. intros. exact eq_refl.
  Qed.
End unfold_functions.

Ltac find_reshape e K e' TC :=
  lazymatch e with
  | fill ?Kabs ?e_inner =>
      reshape_expr e_inner ltac:(fun K' e'' =>
        unify K (fill Kabs ∘ fill K');
        unify e' e'';
        notypeclasses refine (ConstructReshape e (fill Kabs ∘ fill K') e'' _ (eq_refl) _);
        tc_solve
      )
  | _ =>
      reshape_expr e ltac:(fun K' e'' =>
        unify K (fill K');
        unify e' e'';
        notypeclasses refine (ConstructReshape e (fill K') e'' _ (eq_refl) _);
        tc_solve
      )
  end.

#[global] Hint Extern 4 (
  ReshapeExprAnd expr ?e ?K ?e' ?TC
) =>
  find_reshape e K e' TC
: typeclass_instances.

#[global] Hint Extern 4 (
  ReshapeExprAnd (language.expr ?L) ?e ?K ?e' ?TC
) =>
  unify L zebre;
  find_reshape e K e' TC
: typeclass_instances.

#[global] Arguments zebre : simpl never.

Unset Universe Polymorphism.

#[global] Hint Extern 4 (
  PureExecNoRec _ _ ?e1 _
) =>
  lazymatch e1 with
  | (App (Val ?v1) (Val ?v2)) =>
      assert_fails (assert (∃ f x erec,
        TCAnd (AsValRec v1 f x erec) $
        TCAnd (TCIf (TCEq f BAnon) False TCTrue) $
        SolveSepSideCondition (is_recursive_fun (ValRec f x erec) = true)
      )
      by (do 3 eexists; tc_solve));
      unfold PureExecNoRec;
      tc_solve
  | _ =>
      unfold PureExecNoRec;
      tc_solve
  end
: typeclass_instances.
