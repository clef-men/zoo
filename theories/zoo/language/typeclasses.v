Require Import zoo.prelude.
Require Export zoo.common.list.
Require Export zoo.language.language.
Require Export zoo.language.metatheory.
Require Import zoo.language.tactics.
Require Import zoo.options.

Implicit Type e : expr.
Implicit Type v : val.

#[global] Instance val۰as_val v :
  AsVal (Val v) v.
Proof.
  done.
Qed.

Section atomic.
  #[local] Ltac solve_atomic :=
    apply base_atomicｰatomic;
    [ inversion 1; naive_solver
    | apply sub_redexes_are_valuesｰalt; intros [] **; naive_solver
    ].

  #[global] Instance pureｰatomic e v :
    PureExec True 1 e (Val v) →
    Atomic e.
  Proof.
    intros Hpure%nsteps_once_inv tid σ κ e' σ' es Hstep; last done.
    eapply pure_stepｰdet in Hstep; last done.
    naive_solver.
  Qed.

  #[global] Instance get_sizeｰatomic v :
    Atomic (GetSize (Val v)).
  Proof.
    solve_atomic.
  Qed.

  #[global] Instance loadｰatomic v1 v2 :
    Atomic (Load (Val v1) (Val v2)).
  Proof.
    solve_atomic.
  Qed.

  #[global] Instance storeｰatomic v1 v2 v3 :
    Atomic (Store (Val v1) (Val v2) (Val v3)).
  Proof.
    solve_atomic.
  Qed.

  #[global] Instance xchgｰatomic v1 v2 :
    Atomic (Xchg (Val v1) (Val v2)).
  Proof.
    solve_atomic.
  Qed.

  #[global] Instance casｰatomic v0 v1 v2 :
    Atomic (CAS (Val v0) (Val v1) (Val v2)).
  Proof.
    solve_atomic.
  Qed.

  #[global] Instance faaｰatomic v1 v2 :
    Atomic (FAA (Val v1) (Val v2)).
  Proof.
    solve_atomic.
  Qed.

  #[global] Instance resolveｰatomic e v1 v2 :
    Atomic e →
    Atomic (Resolve e (Val v1) (Val v2)).
  Proof.
    rename e into e1.
    intros H tid σ1 e2 κ σ2 es [K e1' e2' Hfill -> Hstep].
    simpl in *. induction K as [| k K _] using rev_ind; simpl in Hfill.
    - subst. inversion_clear Hstep.
      eapply (H tid σ1 (Val _) _ σ2 es), base_stepｰprim_step. done.
    - rewrite fillｰapp. rewrite fillｰapp in Hfill.
      assert (∀ v, Val v = fill K e1' → False) as Hfill_absurd.
      { intros v Hv.
        assert (to_val (fill K e1') = Some v) as Htv by by rewrite -Hv.
        apply to_valｰfillｰSome in Htv. destruct Htv as [-> ->]. inversion Hstep.
      }
      destruct k; (
        inversion Hfill; clear Hfill; subst;
        try match goal with H : Val ?v = fill K e1' |- _ =>
          apply Hfill_absurd in H; done
        end
      ).
      refine (_ (H tid σ1 (fill (K ++ [_]) e2') _ σ2 es _)).
      + intro Hs. simpl in *.
        destruct Hs as [v Hs]. apply to_valｰfillｰSome in Hs. destruct Hs, K; done.
      + econstructor; try done. simpl. by rewrite fillｰapp.
  Qed.
End atomic.

Class AsValRec v f x e :=
  as_ValRec : v = ValRec f x e.
#[global] Hint Mode AsValRec ! - - - : typeclass_instances.

Lemma ValRecｰas_ValRec f x e :
  AsValRec (ValRec f x e) f x e.
Proof.
  done.
Qed.
#[global] Hint Extern 0 (
  AsValRec (ValRec _ _ _) _ _ _
) =>
  apply ValRecｰas_ValRec
: typeclass_instances.

Class AsValRecs v i recs vs :=
  as_ValRecs :
    Foralli (λ i v, v = ValRecs i recs) vs ∧
    v = ValRecs i recs ∧
    length recs = length vs.
#[global] Hint Mode AsValRecs ! - - - : typeclass_instances.

#[global] Instance as_ValRecｰas_ValRecs v f x e :
  AsValRec v f x e →
  AsValRecs v 0 [(f, x, e)] [v].
Proof.
  done.
Qed.

Class AsValRecs' v i recs vs :=
  as_ValRecs' : AsValRecs v i recs vs.

Lemma as_ValRecs'ｰas_ValRecs v i recs vs :
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
    try naive_solver.
  #[local] Ltac solve_pure_exec :=
    intros ?; destruct_and?;
    apply nsteps_once, pure_base_stepｰpure_step;
    try (case_bool_decide; first subst);
    (split; [solve_exec_safe | solve_exec_puredet]).

  #[global] Instance pureｰrec f x e :
    PureExec
      True
      1
      (Rec f x e)
      (Val $ ValRec f x e).
  Proof.
    solve_pure_exec.
  Qed.

  #[global] Instance pureｰapp v1 i recs rec vs v2 `{HAsValRecs : !AsValRecs v1 i recs vs} :
    PureExec
      (recs !! i = Some rec)
      1
      (App (Val v1) (Val v2))
      (foldr2 (λ rec v, subst' rec.1.1 v) (subst' rec.1.2 v2 rec.2) recs vs).
  Proof.
    destruct HAsValRecs as (Hvs & -> & Hlength) => Hlookup.
    apply nsteps_once, pure_base_stepｰpure_step.
    split; first solve_exec_safe.
    intros tid σ1 κ e σ2 es Hstep.
    invert_base_step.
    split_and!; try done.
    enough (
      ∀ recs1 recs2 vs1 vs2 e,
      recs = recs1 ++ recs2 →
      vs = vs1 ++ vs2 →
      length recs1 = length vs1 →
        foldri (λ i rec, subst' rec.1.1 (ValRecs i recs)) e recs1 =
        foldr2 (λ rec v, subst' rec.1.1 v) e recs1 vs1
    ) as H.
    { apply (H _ [] _ []); last done.
      all: rewrite right_id //.
    }
    clear- Hvs Hlength.
    induction recs1 as [| rec recs1 IH] using rev_ind => recs2 vs1 vs2 e Hrecs_eq Hvs_eq Hlength1; first done.
    destruct vs1 as [| v vs1 _] using rev_ind.
    all: simp_length/= in Hlength1.
    1: lia.
    rewrite foldriｰapp foldr2ｰapp /=; first lia.
    assert (ValRecs (length recs1) recs = v) as ->.
    { eapply Foralliｰlookup₁ in Hvs; first done.
      rewrite Hvs_eq lookup_app_l.
      { simp_length/=. lia. }
      rewrite lookup_snoc_Some. naive_solver lia.
    }
    apply (IH (rec :: recs2) vs1 (v :: vs2)).
    { rewrite Hrecs_eq -assoc //. }
    { rewrite Hvs_eq -assoc //. }
    { lia. }
  Qed.
  #[global] Instance pureｰappｰrec f x v1 v2 :
    PureExec True 1 (App (Val $ ValRec f x (Val v1)) (Val v2)) (Val v1).
  Proof.
    pose proof (pureｰapp (ValRec f x (Val v1)) 0 [(f, x, Val v1)] (f, x, Val v1) [ValRec f x (Val v1)] v2) as H.
    rewrite /= !subst'ｰval in H.
    intros _. naive_solver.
  Qed.

  #[global] Instance pureｰlet x v1 e2 :
    PureExec
      True
      1
      (Let x (Val v1) e2)
      (subst' x v1 e2).
    Proof.
      solve_pure_exec.
    Qed.

  #[global] Instance pureｰunop op v v' :
    PureExec
      (eval_unop op v = Some v')
      1
      (Unop op (Val v))
      (Val v').
  Proof.
    solve_pure_exec.
  Qed.

  #[global] Instance pureｰbinop op v1 v2 v' :
    PureExec
      (eval_binop op v1 v2 = Some v')
      1
      (Binop op (Val v1) (Val v2))
      (Val v').
  Proof.
    solve_pure_exec.
  Qed.

  #[global] Instance pureｰequalｰbool b1 b2 :
    PureExec
      True
      1
      (Equal (Val $ ValBool b1) (Val $ ValBool b2))
      (Val $ ValBool (bool_decide (b1 = b2))).
  Proof.
    solve_pure_exec.
  Qed.
  #[global] Instance pureｰequalｰint i1 i2 :
    PureExec
      True
      1
      (Equal (Val $ ValInt i1) (Val $ ValInt i2))
      (Val $ ValBool (bool_decide (i1 = i2))).
  Proof.
    solve_pure_exec.
  Qed.
  #[global] Instance pureｰequalｰlocation l1 l2 :
    PureExec
      True
      1
      (Equal (Val $ ValLoc l1) (Val $ ValLoc l2))
      (Val $ ValBool (bool_decide (l1 = l2))).
  Proof.
    solve_pure_exec.
  Qed.
  #[global] Instance pureｰequalｰlocationｰblock l gen tag vs :
    PureExec
      True
      1
      (Equal (Val $ ValLoc l) (Val $ ValBlock gen tag vs))
      (Val $ ValBool false).
  Proof.
    solve_pure_exec.
  Qed.
  #[global] Instance pureｰequalｰblockｰlocation gen tag vs l :
    PureExec
      True
      1
      (Equal (Val $ ValBlock gen tag vs) (Val $ ValLoc l))
      (Val $ ValBool false).
  Proof.
    solve_pure_exec.
  Qed.
  #[global] Instance pureｰequalｰblockｰgenerative bid tag vs :
    PureExec
      True
      1
      (Equal (Val $ ValBlock (Generative (Some bid)) tag vs) (Val $ ValBlock (Generative (Some bid)) tag vs))
      (Val $ ValBool true).
  Proof.
    destruct vs; solve_pure_exec.
  Qed.
  #[global] Instance pureｰequalｰblockｰgenerativeｰnongenerative bid1 tag1 vs1 tag2 vs2 :
    PureExec
      (length vs1 ≠ 0 ∨ length vs2 ≠ 0)
      1
      (Equal (Val $ ValBlock (Generative bid1) tag1 vs1) (Val $ ValBlock Nongenerative tag2 vs2))
      (Val $ ValBool false).
  Proof.
    solve_pure_exec.
  Qed.
  #[global] Instance pureｰequalｰblockｰnongenerativeｰgenerative tag1 vs1 bid2 tag2 vs2 :
    PureExec
      (length vs1 ≠ 0 ∨ length vs2 ≠ 0)
      1
      (Equal (Val $ ValBlock Nongenerative tag1 vs1) (Val $ ValBlock (Generative bid2) tag2 vs2))
      (Val $ ValBool false).
  Proof.
    solve_pure_exec.
  Qed.
  #[global] Instance pureｰequalｰblockｰempty tag1 tag2 :
    PureExec
      True
      1
      (Equal (Val $ ValBlock Nongenerative tag1 []) (Val $ ValBlock Nongenerative tag2 []))
      (Val $ ValBool (bool_decide (tag1 = tag2))).
  Proof.
    solve_pure_exec.
  Qed.
  #[global] Instance pureｰequalｰblockｰempty₁ gen1 tag1 gen2 tag2 v2 vs2 :
    PureExec
      True
      1
      (Equal (Val $ ValBlock gen1 tag1 []) (Val $ ValBlock gen2 tag2 (v2 :: vs2)))
      (Val $ ValBool false).
  Proof.
    solve_pure_exec.
  Qed.
  #[global] Instance pureｰequalｰblockｰempty₂ gen1 tag1 v1 vs1 gen2 tag2 :
    PureExec
      True
      1
      (Equal (Val $ ValBlock gen1 tag1 (v1 :: vs1)) (Val $ ValBlock gen2 tag2 []))
      (Val $ ValBool false).
  Proof.
    solve_pure_exec.
  Qed.

  #[global] Instance pureｰifｰtrue e1 e2 :
    PureExec
      True
      1
      (If (Val $ ValBool true) e1 e2)
      e1.
  Proof.
    solve_pure_exec.
  Qed.
  #[global] Instance pureｰifｰfalse e1 e2 :
    PureExec
      True
      1
      (If (Val $ ValBool false) e1 e2)
      e2.
  Proof.
    solve_pure_exec.
  Qed.

  Lemma pureｰfor n1 n2 e :
    PureExec
      True
      1
      (For (Val $ ValInt n1) (Val $ ValInt n2) e)
      (if decide (n2 ≤ n1)%Z then Unit else Seq (App e (Val $ ValInt n1)) (For (Val $ ValInt (n1 + 1)) (Val $ ValInt n2) e)).
  Proof.
    solve_pure_exec.
  Qed.

  #[global] Instance pureｰblockｰimmutableｰnongenerative tag es vs :
    PureExec
      (to_vals es = Some vs)
      1
      (Block ImmutableNongenerative tag es)
      (Val $ ValBlock Nongenerative tag vs).
  Proof.
    intros <-%of_valsｰto_vals.
    apply nsteps_once, pure_base_stepｰpure_step.
    split; [solve_exec_safe | solve_exec_puredet].
  Qed.
  #[global] Instance pureｰblockｰimmutableｰgenerative tag es vs :
    PureExec
      (to_vals es = Some vs)
      1
      (Block ImmutableGenerativeWeak tag es)
      (Val $ ValBlock (Generative None) tag vs).
  Proof.
    intros <-%of_valsｰto_vals.
    apply nsteps_once, pure_base_stepｰpure_step.
    split; [solve_exec_safe | solve_exec_puredet].
  Qed.

  #[global] Instance pureｰmatch gen tag vs x_fb e_fb brs e :
    PureExec
      (eval_match tag (length vs) (SubjectBlock gen vs) x_fb e_fb brs = Some e)
      1
      (Match (Val $ ValBlock gen tag vs) x_fb e_fb brs)
      e.
  Proof.
    solve_pure_exec.
  Qed.

  #[global] Instance pureｰget_tag gen tag vs :
    PureExec
      (0 < length vs)
      1
      (GetTag $ Val $ ValBlock gen tag vs)
      (Val $ ValNat (encode_tag tag)).
  Proof.
    solve_pure_exec.
  Qed.

  #[global] Instance pureｰget_size gen tag vs :
    PureExec
      (0 < length vs)
      1
      (GetSize $ Val $ ValBlock gen tag vs)
      (Val $ ValNat (length vs)).
  Proof.
    solve_pure_exec.
  Qed.

  #[global] Instance pureｰload gen tag vs (fld : nat) v :
    PureExec
      (vs !! fld = Some v)
      1
      (Load (Val $ ValBlock gen tag vs) (Val $ ValNat fld))
      (Val v).
  Proof.
    solve_pure_exec.
  Qed.
End pure_exec.
