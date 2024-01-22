From zebre Require Import
  prelude.
From zebre.language Require Export
  language.
From zebre.language Require Import
  tactics
  metatheory
  notations.
From zebre Require Import
  options.

Implicit Types e : expr.
Implicit Types v : val.

#[global] Instance into_val_val v :
  IntoVal (Val v) v.
Proof.
  done.
Qed.
#[global] Instance as_val_val v :
  AsVal (Val v).
Proof.
  by eexists.
Qed.

Section atomic.
  #[local] Ltac solve_atomic :=
    apply strongly_atomic_atomic, ectx_language_atomic;
    [ inversion 1; naive_solver
    | apply ectxi_language_sub_redexes_are_values; intros [] **; naive_solver
    ].

  #[global] Instance rec_atomic a f x e :
    Atomic a (Rec f x e).
  Proof.
    solve_atomic.
  Qed.

  #[global] Instance beta_atomic a f x v1 v2 :
    Atomic a (App (ValRec f x (Val v1)) (Val v2)).
  Proof.
    destruct f, x; solve_atomic.
  Qed.

  #[global] Instance unop_atomic a op v :
    Atomic a (Unop op $ Val v).
  Proof.
    solve_atomic.
  Qed.
  #[global] Instance binop_atomic a op v1 v2 :
    Atomic a (Binop op (Val v1) (Val v2)).
  Proof.
    solve_atomic.
  Qed.

  #[global] Instance equal_atomic a v1 v2 :
    Atomic a (Equal (Val v1) (Val v2)).
  Proof.
    solve_atomic.
  Qed.

  #[global] Instance if_true_atomic a v1 e2 :
    Atomic a (If (Val $ ValLiteral $ LiteralBool true) (Val v1) e2).
  Proof.
    solve_atomic.
  Qed.
  #[global] Instance if_false_atomic a e1 v2 :
    Atomic a (If (Val $ ValLiteral $ LiteralBool false) e1 (Val v2)).
  Proof.
    solve_atomic.
  Qed.

  #[global] Instance pair_atomic a v1 v2 :
    Atomic a (Pair (Val v1) (Val v2)).
  Proof.
    solve_atomic.
  Qed.
  #[global] Instance fst_atomic a v :
    Atomic a (Fst $ Val v).
  Proof.
    solve_atomic.
  Qed.
  #[global] Instance snd_atomic a v :
    Atomic a (Snd $ Val v).
  Proof.
    solve_atomic.
  Qed.

  #[global] Instance constr_atomic a b v :
    Atomic a (Constr b $ Val v).
  Proof.
    solve_atomic.
  Qed.

  #[global] Instance alloc_atomic a v w :
    Atomic a (Alloc (Val v) (Val w)).
  Proof.
    solve_atomic.
  Qed.
  #[global] Instance load_atomic a v :
    Atomic a (Load $ Val v).
  Proof.
    solve_atomic.
  Qed.
  #[global] Instance store_atomic a v1 v2 :
    Atomic a (Store (Val v1) (Val v2)).
  Proof.
    solve_atomic.
  Qed.

  #[global] Instance xchg_atomic a v1 v2 :
    Atomic a (Xchg (Val v1) (Val v2)).
  Proof.
    solve_atomic.
  Qed.

  #[global] Instance cas_atomic a v0 v1 v2 :
    Atomic a (Cas (Val v0) (Val v1) (Val v2)).
  Proof.
    solve_atomic.
  Qed.

  #[global] Instance faa_atomic a v1 v2 :
    Atomic a (Faa (Val v1) (Val v2)).
  Proof.
    solve_atomic.
  Qed.

  #[global] Instance fork_atomic a e :
    Atomic a (Fork e).
  Proof.
    solve_atomic.
  Qed.

  #[global] Instance proph_atomic a :
    Atomic a Proph.
  Proof.
    solve_atomic.
  Qed.
  #[global] Instance resolve_atomic a e v1 v2 :
    Atomic a e →
    Atomic a (Resolve e (Val v1) (Val v2)).
  Proof.
    rename e into e1. intros H σ1 e2 κ σ2 es [K e1' e2' Hfill -> step].
    simpl in *. induction K as [| k K _] using rev_ind; simpl in Hfill.
    - subst. inversion_clear step. by eapply (H σ1 (Val _) _ σ2 es), head_prim_step.
    - rewrite fill_app. rewrite fill_app in Hfill.
      assert (∀ v, Val v = fill K e1' → False) as fill_absurd.
      { intros v Hv. assert (to_val (fill K e1') = Some v) as Htv by by rewrite -Hv.
        apply to_val_fill_some in Htv. destruct Htv as [-> ->]. inversion step. }
      destruct k; (inversion Hfill; clear Hfill; subst; try
        match goal with | H : Val ?v = fill K e1' |- _ => by apply fill_absurd in H end).
      refine (_ (H σ1 (fill (K ++ [_]) e2') _ σ2 es _)).
      + destruct a; intro Hs; simpl in *.
        * destruct Hs as [v Hs]. apply to_val_fill_some in Hs. by destruct Hs, K.
        * apply irreducible_resolve. by rewrite fill_app in Hs.
      + econstructor; try done. simpl. by rewrite fill_app.
  Qed.
End atomic.

Class AsValRec v f x e :=
  as_ValRec : v = ValRec f x e.
#[global] Hint Mode AsValRec ! - - - : typeclass_instances.

Definition ValRec_as_ValRec f x e : AsValRec (ValRec f x e) f x e :=
  eq_refl.
#[global] Hint Extern 0 (
  AsValRec (ValRec _ _ _) _ _ _
) =>
  apply ValRec_as_ValRec
: typeclass_instances.

Section pure_exec.
  #[local] Ltac solve_exec_safe :=
    intros; subst;
    eauto 10 with zebre.
  #[local] Ltac solve_exec_puredet :=
    intros;
    invert_head_step; done.
  #[local] Ltac solve_pure_exec :=
    intros ?; destruct_and?;
    apply nsteps_once, pure_head_step_pure_step;
    try (case_bool_decide; first subst);
    (split; [solve_exec_safe | solve_exec_puredet]).

  #[global] Instance pure_rec f x e :
    PureExec
      True
      1
      (Rec f x e)
      (Val $ ValRec f x e).
  Proof.
    solve_pure_exec.
  Qed.

  #[global] Instance pure_beta f x e v1 v2 `{!AsValRec v1 f x e} :
    PureExec
      True
      1
      (App (Val v1) (Val v2))
      (subst' f v1 (subst' x v2 e)).
  Proof.
    unfold AsValRec in *. solve_pure_exec.
  Qed.

  #[global] Instance pure_unop op v v' :
    PureExec
      (unop_eval op v = Some v')
      1
      (Unop op (Val v))
      (Val v').
  Proof.
    solve_pure_exec.
  Qed.
  #[global] Instance pure_binop op v1 v2 v' :
    PureExec
      (binop_eval op v1 v2 = Some v')
      1
      (Binop op (Val v1) (Val v2))
      (Val v').
  Proof.
    solve_pure_exec.
  Qed.

  #[global] Instance pure_equal lit1 lit2 :
    PureExec
      (literal_physical lit1 ∧ literal_physical lit2)
      1
      (Equal (Val $ ValLiteral lit1) (Val $ ValLiteral lit2))
      (Val $ ValLiteral $ LiteralBool $ bool_decide (lit1 = lit2)).
  Proof.
    solve_pure_exec.
  Qed.

  #[global] Instance pure_if_true e1 e2 :
    PureExec
      True
      1
      (If (Val $ ValLiteral $ LiteralBool true) e1 e2)
      e1.
  Proof.
    solve_pure_exec.
  Qed.
  #[global] Instance pure_if_false e1 e2 :
    PureExec
      True
      1
      (If (Val $ ValLiteral  $ LiteralBool false) e1 e2)
      e2.
  Proof.
    solve_pure_exec.
  Qed.

  #[global] Instance pure_pair v1 v2 :
    PureExec
      True
      1
      (Pair (Val v1) (Val v2))
      (Val $ ValPair v1 v2).
  Proof.
    solve_pure_exec.
  Qed.
  #[global] Instance pure_fst v1 v2 :
    PureExec
      True
      1
      (Fst (Val $ ValPair v1 v2))
      (Val v1).
  Proof.
    solve_pure_exec.
  Qed.
  #[global] Instance pure_snd v1 v2 :
    PureExec
      True
      1
      (Snd (Val $ ValPair v1 v2))
      (Val v2).
  Proof.
    solve_pure_exec.
  Qed.

  #[global] Instance pure_constr b v :
    PureExec
      True
      1
      (Constr b $ Val v)
      (Val $ ValConstr b v).
  Proof.
    solve_pure_exec.
  Qed.
  #[global] Instance pure_case b v e1 e2 :
    PureExec
      True
      1
      (Case (Val $ ValConstr b v) e1 e2)
      (App (App (if b then e1 else e2) (Val v)) (Val $ ValConstr b v)).
  Proof.
    solve_pure_exec.
  Qed.
End pure_exec.

Lemma pure_exec_0 {Λ} ϕ (e : language.expr Λ) :
  PureExec ϕ 0 e e.
Proof.
  intros _. apply nsteps_O.
Qed.
Lemma pure_exec_add {n} {ϕ : Prop} {e1} ψ m e2 e3 :
  PureExec ψ m e1 e2 →
  (ϕ → ψ) →
  m ≤ n →
  PureExec ϕ (n - m) e2 e3 →
  PureExec ϕ n e1 e3.
Proof.
  intros Hpure1 Hψ Hle Hpure2 Hϕ.
  rewrite (Nat.le_add_sub m n) //. eapply nsteps_trans; naive_solver.
Qed.

#[local] Ltac solve_pure_exec' :=
  simpl;
  match goal with |- PureExec True ?n ?e1 ?e2 =>
    lazymatch n with
    | O =>
        apply pure_exec_0
    | S _ =>
        eapply pure_exec_add;
        [ reshape_expr e1 ltac:(fun K e1_foc =>
            apply (pure_exec_fill K _ _ e1_foc);
            apply _
          )
        | naive_solver
        | lia
        | idtac
        ]
    end
  end.
Ltac solve_pure_exec :=
  let H := fresh in
  pose (H := ValRec_as_ValRec);
  repeat solve_pure_exec';
  simpl;
  clear H.

#[global] Instance pure_exec_subst_lam x1 v1 x2 v2 e :
  PureExec True 2
    ((subst' x1 v1 (λ: x2, e)) v2)
    (subst' x1 v1 (subst' x2 v2 e)).
Proof.
  destruct (decide (x1 = x2)) as [<- |].
  - rewrite subst_subst' subst_rec'; first naive_solver.
    solve_pure_exec.
  - rewrite (subst_subst_ne' _ x1 x2) // subst_rec_ne'; [naive_solver.. |].
    solve_pure_exec.
Qed.
#[global] Instance pure_exec_subst2_lam x1 v1 x2 v2 x3 v3 e :
  PureExec True 2
    ((subst' x1 v1 (subst' x2 v2 (λ: x3, e))) v3)
    (subst' x1 v1 (subst' x2 v2 (subst' x3 v3 e))).
Proof.
  destruct (decide (x2 = x3)) as [<- |].
  - rewrite subst_subst' subst_rec'; first naive_solver.
    solve_pure_exec.
  - rewrite (subst_subst_ne' _ x2 x3) // subst_rec_ne'; [naive_solver.. |].
    solve_pure_exec.
Qed.
#[global] Instance pure_exec_subst3_lam x1 v1 x2 v2 x3 v3 x4 v4 e :
  PureExec True 2
    ((subst' x1 v1 (subst' x2 v2 (subst' x3 v3 (λ: x4, e)))) v4)
    (subst' x1 v1 (subst' x2 v2 (subst' x3 v3 (subst' x4 v4 e)))).
Proof.
  destruct (decide (x3 = x4)) as [<- |].
  - rewrite subst_subst' subst_rec'; first naive_solver.
    solve_pure_exec.
  - rewrite (subst_subst_ne' _ x3 x4) // subst_rec_ne'; [naive_solver.. |].
    solve_pure_exec.
Qed.
