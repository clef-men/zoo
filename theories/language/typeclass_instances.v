From zoo Require Import
  prelude.
From zoo.common Require Export
  list.
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

  #[global] Instance app_atomic f x v1 v2 :
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

  #[global] Instance alloc_atomic v1 v2 :
    Atomic (Alloc (Val v1) (Val v2)).
  Proof.
    solve_atomic.
  Qed.

  #[global] Instance get_tag_atomic v :
    Atomic (GetTag (Val v)).
  Proof.
    solve_atomic.
  Qed.
  #[global] Instance get_size_atomic v :
    Atomic (GetSize (Val v)).
  Proof.
    solve_atomic.
  Qed.

  #[global] Instance load_atomic v1 v2 :
    Atomic (Load (Val v1) (Val v2)).
  Proof.
    solve_atomic.
  Qed.
  #[global] Instance store_atomic v1 v2 v3 :
    Atomic (Store (Val v1) (Val v2) (Val v3)).
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

Lemma ValRec_as_ValRec f x e :
  AsValRec (ValRec f x e) f x e.
Proof.
  done.
Qed.
#[global] Hint Extern 0 (
  AsValRec (ValRec _ _ _) _ _ _
) =>
  apply ValRec_as_ValRec
: typeclass_instances.

Class AsValRecs v i recs vs :=
  as_ValRecs :
    Foralli (λ i v, v = ValRecs i recs) vs ∧
    v = ValRecs i recs ∧
    length recs = length vs.
#[global] Hint Mode AsValRecs ! - - - : typeclass_instances.

#[global] Instance as_ValRec_as_ValRecs v f x e :
  AsValRec v f x e →
  AsValRecs v 0 [(f, x, e)] [v].
Proof.
  done.
Qed.

Class AsValRecs' v i recs vs :=
  as_ValRecs' : AsValRecs v i recs vs.

Lemma as_ValRecs'_as_ValRecs v i recs vs :
  AsValRecs' v i recs vs →
  AsValRecs v i recs vs.
Proof.
  done.
Qed.

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

  #[global] Instance pure_app v1 i recs rec vs v2 `{HAsValRecs : !AsValRecs v1 i recs vs} :
    PureExec
      (recs !! i = Some rec)
      1
      (App (Val v1) (Val v2))
      (foldr2 (λ rec v, subst' rec.1.1 v) (subst' rec.1.2 v2 rec.2) recs vs).
  Proof.
    destruct HAsValRecs as (Hvs & -> & Hlength) => Hlookup.
    apply nsteps_once, pure_base_step_pure_step.
    split; first solve_exec_safe.
    intros σ1 κ e σ2 es Hstep.
    invert_base_step.
    split_and!; try done.
    cut (
      ∀ recs1 recs2 vs1 vs2 e,
      recs = recs1 ++ recs2 →
      vs = vs1 ++ vs2 →
      length recs1 = length vs1 →
        foldri (λ i rec, subst' rec.1.1 (ValRecs i recs)) e recs1 =
        foldr2 (λ rec v, subst' rec.1.1 v) e recs1 vs1
    ). {
      intros H. apply (H _ [] _ []); last done.
      all: rewrite right_id //.
    }
    clear- Hvs Hlength.
    induction recs1 as [| rec recs1 IH] using rev_ind => recs2 vs1 vs2 e Hrecs_eq Hvs_eq Hlength1; first done.
    destruct (rev_elim vs1) as [-> | (vs1' & v & ->)].
    { rewrite length_app /= in Hlength1. lia. }
    rewrite !length_app /= in Hlength1.
    rewrite foldri_app foldr2_app /=; first lia.
    assert (ValRecs (length recs1) recs = v) as ->.
    { eapply Foralli_lookup in Hvs; first done.
      rewrite Hvs_eq lookup_app_l.
      { rewrite length_app /=. lia. }
      rewrite lookup_snoc_Some. naive_solver lia.
    }
    apply (IH (rec :: recs2) vs1' (v :: vs2)).
    { rewrite Hrecs_eq -assoc //. }
    { rewrite Hvs_eq -assoc //. }
    { lia. }
  Qed.

  #[global] Instance pure_let x v1 e2 :
    PureExec
      True
      1
      (Let x (Val v1) e2)
      (subst' x v1 e2).
    Proof.
      solve_pure_exec.
    Qed.

  #[global] Instance pure_unop op v v' :
    PureExec
      (eval_unop op v = Some v')
      1
      (Unop op (Val v))
      (Val v').
  Proof.
    solve_pure_exec.
  Qed.
  #[global] Instance pure_binop op v1 v2 v' :
    PureExec
      (eval_binop op v1 v2 = Some v')
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
      (Equal (Val $ ValBlock None tag1 []) (Val $ ValBlock None tag2 []))
      (Val $ ValBool (bool_decide (tag1 = tag2))).
  Proof.
    solve_pure_exec.
  Qed.
  #[global] Instance pure_equal_block_1 bid1 tag1 bid2 tag2 v2 vs2 :
    PureExec
      True
      1
      (Equal (Val $ ValBlock bid1 tag1 []) (Val $ ValBlock bid2 tag2 (v2 :: vs2)))
      (Val $ ValBool false).
  Proof.
    solve_pure_exec.
  Qed.
  #[global] Instance pure_equal_block_2 bid1 tag1 v1 vs1 bid2 tag2 :
    PureExec
      True
      1
      (Equal (Val $ ValBlock bid1 tag1 (v1 :: vs1)) (Val $ ValBlock bid2 tag2 []))
      (Val $ ValBool false).
  Proof.
    solve_pure_exec.
  Qed.
  #[global] Instance pure_equal_location_block l bid tag vs :
    PureExec
      True
      1
      (Equal (Val $ ValLoc l) (Val $ ValBlock bid tag vs))
      (Val $ ValBool false).
  Proof.
    solve_pure_exec.
  Qed.
  #[global] Instance pure_equal_block_location bid tag vs l :
    PureExec
      True
      1
      (Equal (Val $ ValBlock bid tag vs) (Val $ ValLoc l))
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

  Lemma pure_for n1 n2 e :
    PureExec
      True
      1
      (For (Val $ ValInt n1) (Val $ ValInt n2) e)
      (if decide (n2 ≤ n1)%Z then Unit else Seq (App e (Val $ ValInt n1)) (For (Val $ ValInt (n1 + 1)) (Val $ ValInt n2) e)).
  Proof.
    solve_pure_exec.
  Qed.

  #[global] Instance pure_block tag es vs :
    PureExec
      (to_vals es = Some vs)
      1
      (Block Immutable tag es)
      (Val $ ValBlock None tag vs).
  Proof.
    intros <-%of_to_vals.
    apply nsteps_once, pure_base_step_pure_step.
    split; [solve_exec_safe | solve_exec_puredet].
  Qed.

  #[global] Instance pure_match bid tag vs x_fb e_fb brs e :
    PureExec
      (eval_match bid tag (length vs) (inr vs) x_fb e_fb brs = Some e)
      1
      (Match (Val $ ValBlock bid tag vs) x_fb e_fb brs)
      e.
  Proof.
    solve_pure_exec.
  Qed.

  #[global] Instance pure_get_tag bid tag vs :
    PureExec
      (0 < length vs)
      1
      (GetTag $ Val $ ValBlock bid tag vs)
      (Val $ ValInt tag).
  Proof.
    solve_pure_exec.
  Qed.
  #[global] Instance pure_get_size bid tag vs :
    PureExec
      (0 < length vs)
      1
      (GetSize $ Val $ ValBlock bid tag vs)
      (Val $ ValInt (length vs)).
  Proof.
    solve_pure_exec.
  Qed.

  #[global] Instance pure_load bid tag vs (fld : nat) v :
    PureExec
      (vs !! fld = Some v)
      1
      (Load (Val $ ValBlock bid tag vs) (Val $ ValInt fld))
      (Val v).
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
