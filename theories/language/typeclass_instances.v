From zoo Require Import
  prelude.
From zoo.language Require Export
  language.
From zoo.language Require Import
  tactics
  notations.
From zoo Require Import
  options.

Implicit Types e : expr.
Implicit Types v : val.

#[global] Instance val_as_val v :
  AsVal (Val v) v.
Proof.
  done.
Qed.

Section atomic.
  #[local] Ltac solve_atomic :=
    apply ectx_language_atomic;
    [ inversion 1; naive_solver
    | apply ectxi_language_sub_redexes_are_values; intros [] **; naive_solver
    ].

  #[global] Instance rec_atomic f x e :
    Atomic (Rec f x e).
  Proof.
    solve_atomic.
  Qed.

  #[global] Instance beta_atomic f x v1 v2 :
    Atomic (App (ValRec f x (Val v1)) (Val v2)).
  Proof.
    destruct f, x; solve_atomic.
  Qed.

  #[global] Instance unop_atomic op v :
    Atomic (Unop op $ Val v).
  Proof.
    solve_atomic.
  Qed.
  #[global] Instance binop_atomic op v1 v2 :
    Atomic (Binop op (Val v1) (Val v2)).
  Proof.
    solve_atomic.
  Qed.

  #[global] Instance equal_atomic v1 v2 :
    Atomic (Equal (Val v1) (Val v2)).
  Proof.
    solve_atomic.
  Qed.

  #[global] Instance if_true_atomic v1 e2 :
    Atomic (If (Val $ ValBool true) (Val v1) e2).
  Proof.
    solve_atomic.
  Qed.
  #[global] Instance if_false_atomic e1 v2 :
    Atomic (If (Val $ ValBool false) e1 (Val v2)).
  Proof.
    solve_atomic.
  Qed.

  #[global] Instance proj_atomic proj tag vs :
    Atomic (Proj proj $ Val $ ValBlock tag vs).
  Proof.
    solve_atomic.
  Qed.

  #[global] Instance alloc_atomic v w :
    Atomic (Alloc (Val v) (Val w)).
  Proof.
    solve_atomic.
  Qed.
  #[global] Instance load_atomic v :
    Atomic (Load $ Val v).
  Proof.
    solve_atomic.
  Qed.
  #[global] Instance store_atomic v1 v2 :
    Atomic (Store (Val v1) (Val v2)).
  Proof.
    solve_atomic.
  Qed.

  #[global] Instance xchg_atomic v1 v2 :
    Atomic (Xchg (Val v1) (Val v2)).
  Proof.
    solve_atomic.
  Qed.

  #[global] Instance cas_atomic v0 v1 v2 :
    Atomic (CAS (Val v0) (Val v1) (Val v2)).
  Proof.
    solve_atomic.
  Qed.

  #[global] Instance faa_atomic v1 v2 :
    Atomic (FAA (Val v1) (Val v2)).
  Proof.
    solve_atomic.
  Qed.

  #[global] Instance fork_atomic e :
    Atomic (Fork e).
  Proof.
    solve_atomic.
  Qed.

  #[global] Instance yield_atomic :
    Atomic Yield.
  Proof.
    solve_atomic.
  Qed.

  #[global] Instance proph_atomic :
    Atomic Proph.
  Proof.
    solve_atomic.
  Qed.
  #[global] Instance resolve_atomic e v1 v2 :
    Atomic e →
    Atomic (Resolve e (Val v1) (Val v2)).
  Proof.
    rename e into e1. intros H σ1 e2 κ σ2 es [K e1' e2' Hfill -> Hstep].
    simpl in *. induction K as [| k K _] using rev_ind; simpl in Hfill.
    - subst. inversion_clear Hstep.
      eapply (H σ1 (Val _) _ σ2 es), base_prim_step. done.
    - rewrite fill_app. rewrite fill_app in Hfill.
      assert (∀ v, Val v = fill K e1' → False) as Hfill_absurd.
      { intros v Hv.
        assert (to_val (fill K e1') = Some v) as Htv by by rewrite -Hv.
        apply to_val_fill_some in Htv. destruct Htv as [-> ->]. inversion Hstep.
      }
      destruct k; (
        inversion Hfill; clear Hfill; subst;
        try match goal with H : Val ?v = fill K e1' |- _ =>
          apply Hfill_absurd in H; done
        end
      ).
      refine (_ (H σ1 (fill (K ++ [_]) e2') _ σ2 es _)).
      + intro Hs. simpl in *.
        destruct Hs as [v Hs]. apply to_val_fill_some in Hs. destruct Hs, K; done.
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
    eauto with zoo.
  #[local] Ltac solve_exec_puredet :=
    intros;
    invert_base_step;
    naive_solver.
  #[local] Ltac solve_pure_exec :=
    intros ?; destruct_and?;
    apply nsteps_once, pure_base_step_pure_step;
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

  #[global] Instance pure_equal_bool b1 b2 :
    PureExec
      True
      1
      (Equal (Val $ ValBool b1) (Val $ ValBool b2))
      (Val $ ValBool (bool_decide (b1 = b2))).
  Proof.
    solve_pure_exec.
  Qed.
  #[global] Instance pure_equal_int i1 i2 :
    PureExec
      True
      1
      (Equal (Val $ ValInt i1) (Val $ ValInt i2))
      (Val $ ValBool (bool_decide (i1 = i2))).
  Proof.
    solve_pure_exec.
  Qed.
  #[global] Instance pure_equal_location l1 l2 :
    PureExec
      True
      1
      (Equal (Val $ ValLoc l1) (Val $ ValLoc l2))
      (Val $ ValBool (bool_decide (l1 = l2))).
  Proof.
    solve_pure_exec.
  Qed.
  #[global] Instance pure_equal_block tag1 tag2 :
    PureExec
      True
      1
      (Equal (Val $ ValBlock tag1 []) (Val $ ValBlock tag2 []))
      (Val $ ValBool (bool_decide (tag1 = tag2))).
  Proof.
    solve_pure_exec.
  Qed.
  #[global] Instance pure_equal_block_1 tag1 tag2 v2 vs2 :
    PureExec
      True
      1
      (Equal (Val $ ValBlock tag1 []) (Val $ ValBlock tag2 (v2 :: vs2)))
      (Val $ ValBool false).
  Proof.
    solve_pure_exec.
  Qed.
  #[global] Instance pure_equal_block_2 tag1 v1 vs1 tag2 :
    PureExec
      True
      1
      (Equal (Val $ ValBlock tag1 (v1 :: vs1)) (Val $ ValBlock tag2 []))
      (Val $ ValBool false).
  Proof.
    solve_pure_exec.
  Qed.
  #[global] Instance pure_equal_location_block l tag vs :
    PureExec
      True
      1
      (Equal (Val $ ValLoc l) (Val $ ValBlock tag vs))
      (Val $ ValBool false).
  Proof.
    solve_pure_exec.
  Qed.
  #[global] Instance pure_equal_block_location tag l vs :
    PureExec
      True
      1
      (Equal (Val $ ValBlock tag vs) (Val $ ValLoc l))
      (Val $ ValBool false).
  Proof.
    solve_pure_exec.
  Qed.

  #[global] Instance pure_if_true e1 e2 :
    PureExec
      True
      1
      (If (Val $ ValBool true) e1 e2)
      e1.
  Proof.
    solve_pure_exec.
  Qed.
  #[global] Instance pure_if_false e1 e2 :
    PureExec
      True
      1
      (If (Val $ ValBool false) e1 e2)
      e2.
  Proof.
    solve_pure_exec.
  Qed.

  #[global] Instance pure_block tag es vs :
    PureExec
      (to_vals es = Some vs)
      1
      (Block Abstract tag es)
      (Val $ ValBlock tag vs).
  Proof.
    intros <-%of_to_vals.
    apply nsteps_once, pure_base_step_pure_step.
    split; [solve_exec_safe | solve_exec_puredet].
  Qed.
  #[global] Instance pure_proj proj tag vs v :
    PureExec
      (vs !! proj = Some v)
      1
      (Proj proj $ Val $ ValBlock tag vs)
      (Val v).
  Proof.
    solve_pure_exec.
  Qed.
  #[global] Instance pure_match tag vs x e brs e' :
    PureExec
      (match_apply None tag vs x e brs = Some e')
      1
      (Match (Val $ ValBlock tag vs) x e brs)
      e'.
  Proof.
    solve_pure_exec.
  Qed.

  Lemma pure_for n1 n2 e :
    PureExec
      True
      1
      (For (Val $ ValInt n1) (Val $ ValInt n2) e)
      (if decide (n2 ≤ n1)%Z then Unit else Seq (App e (Val $ ValInt n1)) (For (Val $ ValInt (1 + n1)) (Val $ ValInt n2) e)).
  Proof.
    solve_pure_exec.
  Qed.

  #[global] Instance pure_yield :
    PureExec
      True
      1
      Yield
      Unit.
  Proof.
    solve_pure_exec.
  Qed.
End pure_exec.
