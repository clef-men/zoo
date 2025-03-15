From zoo Require Import
  prelude.
From zoo.iris Require Import
  diaframe.
From zoo.iris.diaframe Require Export
  symb_exec.wp.
From zoo.language Require Import
  notations.
From zoo.program_logic Require Import
  proofmode.
From zoo Require Import
  options.

Implicit Types l : location.
Implicit Types pid : prophet_id.
Implicit Types e : expr.
Implicit Types v : val.

(* relax hint mode (set to "+" by Diaframe) *)
Hint Mode SolveSepSideCondition ! : typeclass_instances.

Class PureExecNorec ϕ n e1 e2 :=
  pure_exec_norec : PureExec ϕ n e1 e2.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Implicit Types Φ : val → iProp Σ.

  #[global] Instance pure_step_diaspec_1 e K ϕ n e1 e2 tid E Φ :
    ReshapeExprAnd _ e K e1 (
      TCAnd
        (PureExecNorec ϕ n e1 e2)
        (SolveSepSideCondition ϕ)
    ) →
    LanguageCtx K →
    HINT1 ε₀ ✱ [
      ▷^n (
        emp -∗
        WP K e2 ∷ tid @ E {{ Φ }}
      )
    ] ⊫ [id];
      WP e ∷ tid @ E {{ Φ }}
  | 8.
  Proof.
    rewrite /PureExecNorec.
    pose proof @pure_exec_ctx.
    intros (-> & Hexec & Hϕ) HK.
    iSteps.
    iApply wp_pure_step_later; [done.. |].
    iSteps.
  Qed.
  #[global] Instance pure_step_diaspec_2 e K ϕ n e1 e2 tid E Φ :
    ReshapeExprAnd _ e K e1 (
      TCAnd
        ( ( ∀ x e v,
            PureExec True 1 (App (ValFun x e) v) (subst' x v e)
          ) →
          PureExec ϕ n e1 e2
        )
        (SolveSepSideCondition ϕ)
    ) →
    LanguageCtx K →
    HINT1 ε₀ ✱ [
      ▷^n (
        emp -∗
        WP K e2 ∷ tid @ E {{ Φ }}
      )
    ] ⊫ [id];
      WP e ∷ tid @ E {{ Φ }}.
  Proof.
    intros (-> & Hexec & Hϕ) HK.
    eapply pure_step_diaspec_1; try done.
    split; first done. split.
    - rewrite /PureExecNorec.
      apply Hexec => * _.
      apply nsteps_once, pure_base_step_pure_step.
      split.
      + auto with zoo.
      + intros. invert_base_step. done.
    - done.
  Qed.

  #[global] Instance alloc_diaspec tag n E :
    DIASPEC
    {{
      ⌜0 ≤ tag⌝%Z ∗
      ⌜0 ≤ n⌝%Z
    }}
      Alloc #tag #n @ E
    {{ l,
      RET #l;
      l ↦ₕ Header ₊tag ₊n ∗
      meta_token l ⊤ ∗
      l ↦∗ replicate ₊n ()%V
    }}.
  Proof.
    iSteps.
    wp_alloc l as "Hheader" "Hmeta" "Hl"; [done.. |].
    iSteps.
  Qed.

  #[global] Instance block_diaspec tag es E :
    DIASPEC vs
    {{
      ⌜0 < length es⌝%nat ∗
      ⌜to_vals es = Some vs⌝
    }}
      Block Mutable tag es @ E
    {{ l,
      RET #l;
      l ↦ₕ Header tag (length es) ∗
      meta_token l ⊤ ∗
      l ↦∗ vs
    }}
  | 30.
  Proof.
    iSteps.
    wp_block l as "Hheader" "Hmeta" "Hl".
    iSteps.
  Qed.

  #[global] Instance ref_diaspec e v E :
    AsVal e v →
    DIASPEC
    {{
      True
    }}
      ref e @ E
    {{ l,
      RET #l;
      l ↦ₕ Header 0 1 ∗
      meta_token l ⊤ ∗
      l ↦ᵣ v
    }}
  | 20.
  Proof.
    move=> <-.
    iSteps.
    wp_ref l as "Hheader" "Hmeta" "Hl".
    iSteps.
  Qed.

  #[global] Instance block_generative_diaspec tag es E :
    DIASPEC vs
    {{
      ⌜to_vals es = Some vs⌝
    }}
      Block ImmutableGenerativeStrong tag es @ E
    {{ bid,
      RET ValBlock (Generative (Some bid)) tag vs;
      True
    }}.
  Proof.
    iSteps.
    wp_block_generative bid.
    iSteps.
  Qed.

  #[global] Instance get_tag_diaspec l E :
    DIASPEC hdr
    {{
      l ↦ₕ hdr
    }}
      GetTag #l @ E
    {{
      RET #hdr.(header_tag);
      True
    }}.
  Proof.
    iSteps.
    wp_get_tag.
    iSteps.
  Qed.

  #[global] Instance get_size_diaspec l E :
    DIASPEC hdr
    {{
      l ↦ₕ hdr
    }}
      GetSize #l @ E
    {{
      RET #hdr.(header_size);
      True
    }}.
  Proof.
    iSteps.
    wp_get_size.
    iSteps.
  Qed.

  #[global] Instance load_diaspec l fld E :
    DIASPEC v dq
    {{
      ▷ (l +ₗ fld) ↦{dq} v
    }}
      Load #l #fld @ E
    {{
      RET v;
      (l +ₗ fld) ↦{dq} v
    }}.
  Proof.
    iSteps.
    wp_load.
    iSteps.
  Qed.

  #[global] Instance store_diaspec l fld v E :
    DIASPEC w
    {{
      ▷ (l +ₗ fld) ↦ w
    }}
      Store #l #fld v @ E
    {{
      RET ();
      (l +ₗ fld) ↦ v
    }}.
  Proof.
    iSteps.
    wp_store.
    iSteps.
  Qed.

  #[global] Instance xchg_diaspec l fld v E :
    DIASPEC w
    {{
      ▷ (l +ₗ fld) ↦ w
    }}
      Xchg (#l, #fld)%V v @ E
    {{
      RET w;
      (l +ₗ fld) ↦ v
    }}.
  Proof.
    iSteps.
    wp_xchg.
    iSteps.
  Qed.

  #[global] Instance cas_diaspec l fld v1 v2 E :
    DIASPEC v dq
    {{
      ▷ (l +ₗ fld) ↦{dq} v ∗
      ⌜dq = DfracOwn 1 ∨ ¬ v ≈ v1⌝
    }}
      CAS (#l, #fld)%V v1 v2 @ E
    {{ (b : bool),
      RET #b;
        ⌜b = false⌝ ∗
        ⌜v ≉ v1⌝ ∗
        (l +ₗ fld) ↦{dq} v
      ∨ ⌜b = true⌝ ∗
        ⌜v ≈ v1⌝ ∗
        (l +ₗ fld) ↦ v2
    }}.
  Proof.
    iSteps.
    all: wp_cas.
    all: iSteps.
  Qed.

  #[global] Instance faa_diaspec l fld (n : Z) E :
    DIASPEC (z : Z)
    {{
      ▷ (l +ₗ fld) ↦ #z
    }}
      FAA (#l, #fld)%V #n @ E
    {{
      RET #z;
      (l +ₗ fld) ↦ #(z + n)
    }}.
  Proof.
    iSteps.
    wp_faa.
    iSteps.
  Qed.

  #[global] Instance proph_diaspec E :
    DIASPEC
    {{
      True
    }}
      Proph @ E
    {{ prophs pid,
      RET #pid;
      prophet_model' pid prophs
    }}.
  Proof.
    iSteps.
    iApply (wp_proph with "[//]").
    iSteps.
  Qed.

  #[global] Instance match_diaspec e K l x_fb e_fb brs tid E Φ :
    ReshapeExprAnd _ e K (Match #l x_fb e_fb brs) TCTrue →
    LanguageCtx K →
    HINT1 ε₀ ✱ [
      ∃ hdr e,
      ▷ l ↦ₕ hdr ∗
      ⌜eval_match hdr.(header_tag) hdr.(header_size) (inl l) x_fb e_fb brs = Some e⌝ ∗
      ▷ (
        emp -∗
        WP K e ∷ tid @ E {{ Φ }}
      )
    ] ⊫ [id];
      WP e ∷ tid @ E {{ Φ }}.
  Proof.
    intros (->, _) HK.
    iSteps as (hdr e He) "Hl_header H".
    iApply (wp_match_ctx with "Hl_header"); first done.
    iSteps.
  Qed.

  #[global] Instance if_bool_decide_diaspec e K P `{!Decision P} e1 e2 tid E Φ :
    ReshapeExprAnd _ e K (if: #(bool_decide P) then e1 else e2)%E TCTrue →
    LanguageCtx K →
    HINT1 ε₀ ✱ [
      ∀ b,
      (⌜b = true⌝ ∗ ⌜P⌝ ∨ ⌜b = false⌝ ∗ ⌜¬ P⌝) -∗
      ▷ (
        emp -∗
        WP K (if b then e1 else e2) ∷ tid @ E {{ Φ }}
      )
    ] ⊫ [id];
      WP e ∷ tid @ E {{ Φ }}
  | 50.
  Proof.
    rewrite /PureExecNorec.
    pose proof @pure_exec_ctx.
    intros (->, _) HK.
    iSteps as "H".
    case_bool_decide.
    all: iApply wp_pure_step_later; first done.
    1: iSpecialize ("H" $! true with "[]"); first iSteps.
    2: iSpecialize ("H" $! false with "[]"); first iSteps.
    all: iSteps.
  Qed.
  #[global] Instance if_bool_decide_neg_diaspec e K P `{!Decision P} e1 e2 tid E Φ :
    ReshapeExprAnd _ e K (if: #(bool_decide (¬ P)) then e1 else e2)%E TCTrue →
    LanguageCtx K →
    HINT1 ε₀ ✱ [
      ∀ b,
      (⌜b = true⌝ ∗ ⌜¬ P⌝ ∨ ⌜b = false⌝ ∗ ⌜P⌝) -∗
      ▷ (
        emp -∗
        WP K (if b then e1 else e2) ∷ tid @ E {{ Φ }}
      )
    ] ⊫ [id];
      WP e ∷ tid @ E {{ Φ }}
  | 49.
  Proof.
    rewrite /PureExecNorec.
    pose proof @pure_exec_ctx.
    intros (->, _) HK.
    iSteps as "H".
    case_bool_decide.
    all: iApply wp_pure_step_later; first done.
    1: iSpecialize ("H" $! true with "[]"); first iSteps.
    2: iSpecialize ("H" $! false with "[]"); first iSteps.
    all: iSteps.
  Qed.
  #[global] Instance if_negb_bool_decide_diaspec e K P `{!Decision P} e1 e2 tid E Φ :
    ReshapeExprAnd _ e K (if: #(negb $ bool_decide P) then e1 else e2)%E TCTrue →
    LanguageCtx K →
    HINT1 ε₀ ✱ [
      ∀ b,
      (⌜b = true⌝ ∗ ⌜¬ P⌝ ∨ ⌜b = false⌝ ∗ ⌜P⌝) -∗
      ▷ (
        emp -∗
        WP K (if b then e1 else e2) ∷ tid @ E {{ Φ }}
      )
    ] ⊫ [id];
      WP e ∷ tid @ E {{ Φ }}
  | 49.
  Proof.
    rewrite /PureExecNorec.
    pose proof @pure_exec_ctx.
    intros (->, _) HK.
    iSteps as "H".
    case_bool_decide.
    all: iApply wp_pure_step_later; first done.
    1: iSpecialize ("H" $! false with "[]"); first iSteps.
    2: iSpecialize ("H" $! true with "[]"); first iSteps.
    all: iSteps.
  Qed.
End zoo_G.

Ltac find_reshape e K e' :=
  lazymatch e with
  | fill ?Kabs ?e_inner =>
      reshape_expr e_inner ltac:(fun K' e'' =>
        unify K (fill Kabs ∘ fill K');
        unify e' e'';
        notypeclasses refine (ConstructReshape e (fill Kabs ∘ fill K') e'' _ eq_refl _);
        tc_solve
      )
  | _ =>
      reshape_expr e ltac:(fun K' e'' =>
        unify K (fill K');
        unify e' e'';
        notypeclasses refine (ConstructReshape e (fill K') e'' _ eq_refl _);
        tc_solve
      )
  end.

#[global] Hint Extern 4 (
  ReshapeExprAnd expr ?e ?K ?e' _
) =>
  find_reshape e K e'
: typeclass_instances.
#[global] Hint Extern 4 (
  ReshapeExprAnd (language.expr ?Λ) ?e ?K ?e' _
) =>
  unify Λ zoo;
  find_reshape e K e'
: typeclass_instances.

#[global] Hint Extern 4 (
  PureExecNorec _ _ ?e1 _
) =>
  lazymatch e1 with
  | App (Val ?v1) (Val ?v2) =>
      assert_succeeds (
        assert (
          SolveSepSideCondition (val_recursive v1 = false)
        ) by tc_solve
      )
  | _ =>
      idtac
  end;
  unfold PureExecNorec;
  tc_solve
: typeclass_instances.
