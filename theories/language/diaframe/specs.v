From iris.bi Require Export
  bi
  telescopes
  derived_laws.

From diaframe Require Import
  proofmode_base
  lib.iris_hints.

From zoo Require Import
  prelude.
From zoo.iris.diaframe Require Import
  symb_exec.defs
  symb_exec.wp.
From zoo.iris.diaframe Require Export
  symb_exec.spec_notations.
From zoo.language Require Import
  metatheory
  notations
  proofmode.
From zoo Require Import
  options.

Implicit Types pid : prophet_id.
Implicit Types e : expr.

Class PureExecNoRec ϕ n e1 e2 :=
  is_pure_exec : PureExec (Λ := zoo) ϕ n e1 e2.

Unset Universe Polymorphism.

Section instances.
  Context `{zoo_G : !ZooG Σ}.

  Open Scope expr_scope.

  #[global] Instance pure_wp_step_exec_inst1 e ϕ n e' E :
    (* TODO: prevent unfolding explicit recs *)
    PureExecNoRec ϕ n e e' →
    ReductionTemplateStep wp_red_cond (TeleO*TeleO) (ε₀)%I [tele_arg3 E] e
      (λ pr, tele_app (TT := [tele]) (tele_app (TT := [tele]) e' pr.1) pr.2)
      (template_M n id id TeleO TeleO ⌜ϕ⌝%I emp%I)
  | 80.
      (* used when ϕ is an equality on a new evar: this will cause SolveSepSideCondition to fail *)
      (* this is a ReductionTemplateStep: if it were a ReductionStep, the priority of as_template_step would be considered, not that of this instance *)
  Proof.
    intros.
    refine (pure_wp_step_exec _ _ _ _ _ _ _ _). exact H.
  Qed.

  #[global] Instance pure_wp_step_exec_inst2 e ϕ n e' E :
    PureExecNoRec ϕ n e e' →
    SolveSepSideCondition ϕ →
    ReductionTemplateStep wp_red_cond [tele] (ε₀)%I [tele_arg3 E] e (tele_app (TT := [tele]) e') (template_I n (fupd E E))%I
  | 8.
  Proof.
    intros. eapply pure_wp_step_exec2 => //. tc_solve.
  Qed.

  #[global] Instance reveal_step_wp tag vs :
    SPEC
    {{ True }}
      Reveal $ ValConstr None tag vs
    {{ cid,
      RET ValConstr (Some cid) tag vs; True
    }}.
  Proof.
    iSteps.
    wp_reveal cid.
    iSteps.
  Qed.

  #[global] Instance record_step_wp es :
    SPEC vs,
    {{
      ⌜0 < length es⌝%nat ∗
      ⌜to_vals es = Some vs⌝
    }}
      Record es
    {{ l,
      RET #l;
      l ↦∗ vs
    }}.
  Proof.
    iSteps.
    wp_record l as "Hl".
    iSteps.
  Qed.

  #[global] Instance ref_step_wp e v :
    AsVal e v →
    SPEC
    {{ True }}
      ref e
    {{ l,
      RET #l;
      meta_token l ⊤ ∗
      l ↦ v
    }}
  | 20.
  Proof.
    move=> <-.
    iSteps.
    wp_alloc l as "Hmeta" "Hl".
    iSteps.
  Qed.

  #[global] Instance alloc_step_wp e v E1 E2 n :
    AsVal e v →
    SPEC ⟨E1, E2⟩
    {{
      ⌜0 < n⌝%Z
    }}
      Alloc #n e
    {{ l,
      RET #l;
      meta_token l ⊤ ∗
      l ↦∗ replicate (Z.to_nat n) v
    }}
  | 30.
  Proof.
    move=> <- /=.
    iSteps.
    wp_alloc l as "Hmeta" "Hl"; first done.
    iSteps.
  Qed.

  #[global] Instance load_step_wp l E1 E2 :
    SPEC ⟨E1, E2⟩ v dq,
    {{
      ▷ l ↦{dq} v
    }}
      !#l
    {{
      RET v;
      l ↦{dq} v
    }}.
  Proof.
    iSteps as (v dq) "Hl".
    wp_load.
    iSteps.
  Qed.

  #[global] Instance store_step_wp l v E1 E2 :
    SPEC ⟨E1, E2⟩ w,
    {{
      ▷ l ↦ w
    }}
      #l <- v
    {{
      RET ();
      l ↦ v
    }}.
  Proof.
    iSteps as (w) "Hl".
    wp_store.
    iSteps.
  Qed.

  #[global] Instance xchg_step_wp l v E1 E2 :
    SPEC ⟨E1, E2⟩ w,
    {{
      ▷ l ↦ w
    }}
      Xchg #l v
    {{
      RET w;
      l ↦ v
    }}.
  Proof.
    iSteps as (w) "Hl".
    wp_xchg.
    iSteps.
  Qed.

  #[global] Instance cas_step_wp l v1 v2 E1 E2 :
    SPEC ⟨E1, E2⟩ v dq,
    {{
      ▷ l ↦{dq} v ∗
      ⌜val_physical v⌝ ∗
      ⌜val_physical v1⌝ ∗
      ⌜dq = DfracOwn 1 ∨ ¬ val_eq v v1⌝
    }}
      CAS #l v1 v2
    {{ (b : bool),
      RET #b;
        ⌜b = false⌝ ∗
        ⌜val_neq v v1⌝ ∗
        l ↦{dq} v
      ∨ ⌜b = true⌝ ∗
        ⌜val_eq v v1⌝ ∗
        ⌜val_consistency v v1⌝ ∗
        l ↦ v2
    }}.
  Proof.
    iStep as (lit). iIntros "%dq (_ & Hl & %Hlit & %Hlit1 & %H)".
    wp_cas as ? | ? ?; iSteps.
    destruct H; last done. iSteps.
  Qed.

  #[global] Instance faa_step_wp l i E1 E2 :
    SPEC ⟨E1, E2⟩ (z : Z),
    {{
      ▷ l ↦ #z
    }}
      FAA #l #i
    {{
      RET #z;
      l ↦ #(z + i)
    }}.
  Proof.
    iSteps as (z) "Hl".
    wp_faa.
    iSteps.
  Qed.

  #[global] Instance proph_step :
    SPEC
    {{ True }}
      Proph
    {{ prophs pid,
      RET #pid;
      prophet_model pid prophs
    }}.
  Proof.
    iSteps.
    iApply (wp_proph with "[//]").
    iSteps.
  Qed.

  (* #[global] Instance abduct_resolve_atomic_spec K (e e_in : expr) (p : prophet_id) (v : val) Φ pre n E1 E2 (TT1 TT2 : tele) *)
  (*     L e' v' U M1 M2 : *)
  (*   ReshapeExprAnd expr e_in K (Resolve e #p v) (TCAnd (LanguageCtx K) $ *)
  (*                                                TCAnd (Atomic StronglyAtomic e) $ *)
  (*                                                TCAnd (Atomic WeaklyAtomic e) $ (SolveSepSideCondition (to_val e = None))) → *)
  (*   ReductionStep' wp_red_cond pre n M1 M2 TT1 TT2 L U e e' [tele_arg3 E2; NotStuck] → (1* does not work for pure since that is a ReductionTemplateStep *1) *)
  (*   IntroducableModality M1 → IntroducableModality M2 → *)
  (*   (TC∀.. ttl, TC∀.. ttr, AsVal (tele_app (tele_app e' ttl) ttr) (tele_app (tele_app v' ttl) ttr)) → *)
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
  (*   revert Hev'. rewrite /TCTForall /AsVal => /(dep_eval_tele ttl) /(dep_eval_tele tt2) => Hev'. *)
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

  #[global] Instance if_step_bool_decide P `{Decision P} e1 e2 E :
    ReductionStep (wp_red_cond, [tele_arg3 E]) if: #(bool_decide P) then e1 else e2 ⊣ ⟨id⟩ emp; ε₀ =[▷^1]=>
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
    ReductionStep (wp_red_cond, [tele_arg3 E]) if: #(bool_decide (¬P)) then e1 else e2 ⊣ ⟨id⟩ emp; ε₀ =[▷^1]=>
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
    ReductionStep (wp_red_cond, [tele_arg3 E]) if: #(negb $ bool_decide P) then e1 else e2 ⊣ ⟨id⟩ emp; ε₀ =[▷^1]=>
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
  Context `{zoo_G : !ZooG Σ}.

  #[global] Instance pure_wp_step_exec_inst_last e ϕ n e' E :
    ( ( ∀ f x e,
        SolveSepSideCondition (val_recursive (ValRec f x e) = false) →
        AsValRec (ValRec f x e) f x e
      ) →
      PureExec ϕ n e e'
    ) →
    SolveSepSideCondition ϕ →
    ReductionTemplateStep wp_red_cond [tele] (ε₁)%I [tele_arg3 E] e (tele_app (TT := [tele]) e') (template_I n (fupd E E)).
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
  unify L zoo;
  find_reshape e K e' TC
: typeclass_instances.

#[global] Arguments zoo : simpl never.

Unset Universe Polymorphism.

#[global] Hint Extern 4 (
  PureExecNoRec _ _ ?e1 _
) =>
  lazymatch e1 with
  | (App (Val ?v1) (Val ?v2)) =>
      assert_fails (assert (∃ f x erec,
        TCAnd (AsValRec v1 f x erec) $
        TCAnd (TCIf (TCEq f BAnon) False TCTrue) $
        SolveSepSideCondition (val_recursive (ValRec f x erec) = true)
      )
      by (do 3 eexists; tc_solve));
      unfold PureExecNoRec;
      tc_solve
  | _ =>
      unfold PureExecNoRec;
      tc_solve
  end
: typeclass_instances.
