Require Import zoo.prelude.
Require Export zoo.iris.diaframe.
Require Import zoo.language.notations.
Require Import zoo.proofmode.
Require Export zoo.diaframe.symb_exec.wp.
Require Import zoo.options.

Implicit Type l : location.
Implicit Type pid : prophet_id.
Implicit Type e : expr.
Implicit Type v : val.

(* relax hint mode (set to "+" by Diaframe) *)
Hint Mode SolveSepSideCondition ! : typeclass_instances.

Class PureExecNorec ϕ n e1 e2 :=
  pure_exec_norec : PureExec ϕ n e1 e2.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Implicit Type Φ : val → iProp Σ.

  #[global] Instance pure_step𑁒diaspec₁ e K ϕ n e1 e2 tid E Φ :
    ReshapeExprAnd _ e K e1 (
      TCAnd
        (PureExecNorec ϕ n e1 e2)
        (SolveSepSideCondition ϕ)
    ) →
    Context K →
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
    pose proof @pure_exec𑁒context.
    intros (-> & Hexec & Hϕ) HK.
    iSteps.
    iApply wp𑁒pure_step; [done.. |].
    iSteps.
  Qed.
  #[global] Instance pure_step𑁒diaspec₂ e K ϕ n e1 e2 tid E Φ :
    ReshapeExprAnd _ e K e1 (
      TCAnd
        ( ( ∀ x e v,
            PureExec True 1 (App (ValFun x e) v) (subst' x v e)
          ) →
          PureExec ϕ n e1 e2
        )
        (SolveSepSideCondition ϕ)
    ) →
    Context K →
    HINT1 ε₀ ✱ [
      ▷^n (
        emp -∗
        WP K e2 ∷ tid @ E {{ Φ }}
      )
    ] ⊫ [id];
      WP e ∷ tid @ E {{ Φ }}.
  Proof.
    intros (-> & Hexec & Hϕ) HK.
    eapply pure_step𑁒diaspec₁; try done.
    split; first done. split.
    - rewrite /PureExecNorec.
      apply Hexec => * _.
      apply nsteps_once, pure_base_step𑁒pure_step.
      split.
      + auto with zoo.
      + intros. invert_base_step. done.
    - done.
  Qed.

  #[global] Instance alloc𑁒diaspec tag n E :
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
    wp۰alloc l as "Hheader" "Hmeta" "Hl"; [done.. |].
    iSteps.
  Qed.

  #[global] Instance block𑁒diaspec tag es E :
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
    wp۰block l as "Hheader" "Hmeta" "Hl".
    iSteps.
  Qed.

  #[global] Instance ref𑁒diaspec e v E :
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
    wp۰ref l as "Hheader" "Hmeta" "Hl".
    iSteps.
  Qed.

  #[global] Instance block𑁒generative𑁒diaspec tag es E :
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
    wp۰block۰generative bid.
    iSteps.
  Qed.

  #[global] Instance get_tag𑁒diaspec l E :
    DIASPEC hdr
    {{
      l ↦ₕ hdr
    }}
      GetTag #l @ E
    {{
      RET #(encode_tag hdr.(header۰tag));
      True
    }}.
  Proof.
    iSteps.
    wp۰tag.
    iSteps.
  Qed.

  #[global] Instance get_size𑁒diaspec l E :
    DIASPEC hdr
    {{
      l ↦ₕ hdr
    }}
      GetSize #l @ E
    {{
      RET #hdr.(header۰size);
      True
    }}.
  Proof.
    iSteps.
    wp۰size.
    iSteps.
  Qed.

  #[global] Instance load𑁒diaspec l fld E :
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
    wp۰load.
    iSteps.
  Qed.

  #[global] Instance store𑁒diaspec l fld v E :
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
    wp۰store.
    iSteps.
  Qed.

  #[global] Instance xchg𑁒diaspec l fld v E :
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
    wp۰xchg.
    iSteps.
  Qed.

  #[global] Instance cas𑁒diaspec l fld v1 v2 E :
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
    all: wp۰cas.
    all: iSteps.
  Qed.

  #[global] Instance faa𑁒diaspec l fld (n : Z) E :
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
    wp۰faa.
    iSteps.
  Qed.

  #[global] Instance proph𑁒diaspec E :
    DIASPEC
    {{
      True
    }}
      Proph @ E
    {{ prophs pid,
      RET #pid;
      prophet۰model pid prophs
    }}.
  Proof.
    iSteps.
    iApply (wp𑁒proph with "[//]").
    iSteps.
  Qed.

  #[global] Instance match𑁒diaspec e K l x_fb e_fb brs tid E Φ :
    ReshapeExprAnd _ e K (Match #l x_fb e_fb brs) TCTrue →
    Context K →
    HINT1 ε₀ ✱ [
      ∃ hdr e,
      ▷ l ↦ₕ hdr ∗
      ⌜eval_match hdr.(header۰tag) hdr.(header۰size) (SubjectLoc l) x_fb e_fb brs = Some e⌝ ∗
      ▷ (
        emp -∗
        WP K e ∷ tid @ E {{ Φ }}
      )
    ] ⊫ [id];
      WP e ∷ tid @ E {{ Φ }}.
  Proof.
    intros (->, _) HK.
    iSteps as (hdr e He) "Hl_header H".
    iApply (wp𑁒match𑁒context with "Hl_header"); first done.
    iSteps.
  Qed.

  #[global] Instance if𑁒bool𑁒decide𑁒diaspec e K P `{!Decision P} e1 e2 tid E Φ :
    ReshapeExprAnd _ e K (if: #(bool_decide P) then e1 else e2)%E TCTrue →
    Context K →
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
    pose proof @pure_exec𑁒context.
    intros (->, _) HK.
    iSteps as "H".
    case_bool_decide.
    all: iApply wp𑁒pure_step; first done.
    1: iSpecialize ("H" $! true with "[]"); first iSteps.
    2: iSpecialize ("H" $! false with "[]"); first iSteps.
    all: iSteps.
  Qed.
  #[global] Instance if𑁒bool𑁒decide𑁒neg𑁒diaspec e K P `{!Decision P} e1 e2 tid E Φ :
    ReshapeExprAnd _ e K (if: #(bool_decide (¬ P)) then e1 else e2)%E TCTrue →
    Context K →
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
    pose proof @pure_exec𑁒context.
    intros (->, _) HK.
    iSteps as "H".
    case_bool_decide.
    all: iApply wp𑁒pure_step; first done.
    1: iSpecialize ("H" $! true with "[]"); first iSteps.
    2: iSpecialize ("H" $! false with "[]"); first iSteps.
    all: iSteps.
  Qed.
  #[global] Instance if𑁒negb𑁒bool𑁒decide𑁒diaspec e K P `{!Decision P} e1 e2 tid E Φ :
    ReshapeExprAnd _ e K (if: #(negb $ bool_decide P) then e1 else e2)%E TCTrue →
    Context K →
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
    pose proof @pure_exec𑁒context.
    intros (->, _) HK.
    iSteps as "H".
    case_bool_decide.
    all: iApply wp𑁒pure_step; first done.
    1: iSpecialize ("H" $! false with "[]"); first iSteps.
    2: iSpecialize ("H" $! true with "[]"); first iSteps.
    all: iSteps.
  Qed.
End zoo۰G.

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
  ReshapeExprAnd expr ?e ?K ?e' _
) =>
  find_reshape e K e'
: typeclass_instances.

#[global] Hint Extern 4 (
  PureExecNorec _ _ ?e1 _
) =>
  lazymatch e1 with
  | App (Val ?v1) (Val ?v2) =>
      assert_succeeds (
        assert (
          SolveSepSideCondition (val۰recursive v1 = false)
        ) by tc_solve
      )
  | _ =>
      idtac
  end;
  unfold PureExecNorec;
  tc_solve
: typeclass_instances.
