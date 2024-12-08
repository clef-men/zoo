From zoo Require Import
  prelude.
From zoo.iris.program_logic Require Export
  adequacy.
From zoo.language Require Export
  tactics
  notations.
From zoo Require Import
  options.

Implicit Types i : nat.
Implicit Types n m : Z.
Implicit Types l : location.
Implicit Types lit : literal.
Implicit Types e : expr.
Implicit Types es : list expr.
Implicit Types v w : val.
Implicit Types k : ectxi.
Implicit Types K : ectx.
Implicit Types h : gmap location val.
Implicit Types σ : state.
Implicit Types ρ : config zoo.

Definition erase_literal lit :=
  match lit with
  | LitProph _ =>
      LitPoison
  | _ =>
      lit
  end.

Definition erase_resolve e0 e1 e2 : expr :=
  (e2, e1, e0).<2>.
Fixpoint erase_expr e :=
  match e with
  | Val v =>
      Val
        (erase_val v)
  | Var x =>
      Var
        x
  | Rec f x e =>
      Rec
        f x
        (erase_expr e)
  | App e1 e2 =>
      App
        (erase_expr e1)
        (erase_expr e2)
  | Unop op e =>
      Unop
        op
        (erase_expr e)
  | Binop op e1 e2 =>
      Binop
        op
        (erase_expr e1)
        (erase_expr e2)
  | Equal e1 e2 =>
      Equal
        (erase_expr e1)
        (erase_expr e2)
  | If e0 e1 e2 =>
      If
        (erase_expr e0)
        (erase_expr e1)
        (erase_expr e2)
  | Constr tag es =>
      Constr
        tag
        (erase_expr <$> es)
  | Proj i e =>
      Proj
        i
        (erase_expr e)
  | Match e0 x e1 brs =>
      Match
        (erase_expr e0)
        x
        (erase_expr e1)
        ((λ br, (br.1, erase_expr br.2)) <$> brs)
  | Reveal e =>
      Reveal
        (erase_expr e)
  | For e1 e2 e3 =>
      For
        (erase_expr e1)
        (erase_expr e2)
        (erase_expr e3)
  | Record es =>
      Record
        (erase_expr <$> es)
  | Alloc e1 e2 =>
      Alloc
        (erase_expr e1)
        (erase_expr e2)
  | Load e =>
      Load
        (erase_expr e)
  | Store e1 e2 =>
      Store
        (erase_expr e1)
        (erase_expr e2)
  | Xchg e1 e2 =>
      Xchg
        (erase_expr e1)
        (erase_expr e2)
  | CAS e0 e1 e2 =>
      CAS
        (erase_expr e0)
        (erase_expr e1)
        (erase_expr e2)
  | FAA e1 e2 =>
      FAA
        (erase_expr e1)
        (erase_expr e2)
  | Fork e =>
      Fork
        (erase_expr e)
  | Proph =>
      (fun: <> => #LitPoison)%V ()%V
  | Resolve e0 e1 e2 =>
      erase_resolve
        (erase_expr e0)
        (erase_expr e1)
        (erase_expr e2)
  end
with erase_val v :=
  match v with
  | ValLit lit =>
      ValLit
        (erase_literal lit)
  | ValRec f x e =>
      ValRec
        f x
        (erase_expr e)
  | ValConstr cid tag vs =>
      ValConstr
        cid tag
        (erase_val <$> vs)
  end.
#[global] Arguments erase_expr !_ / : assert.
#[global] Arguments erase_val !_ / : assert.

Definition erase_exprs es :=
  erase_expr <$> es.

Lemma erase_val_subst x v w :
  erase_expr (subst x v w) = subst x (erase_val v) (erase_val w).
Proof.
  done.
Qed.
Lemma erase_expr_subst x v e :
  erase_expr (subst x v e) = subst x (erase_val v) (erase_expr e).
Proof.
  move: e. fix IH 1. destruct e.
  all: simpl; try case_decide; rewrite ?IH ?erase_val_subst; auto.
  all:
    try select (list expr) ltac:(fun es =>
      induction es; [done | naive_solver congruence]
    ).
  select (list branch) ltac:(fun brs =>
    f_equal;
    induction brs;
    [ done
    | simpl; case_decide; rewrite ?IH; f_equal; done
    ]
  ).
Qed.

Lemma erase_expr_subst' x v e :
  erase_expr (subst' x v e) = subst' x (erase_val v) (erase_expr e).
Proof.
  destruct x; eauto using erase_expr_subst.
Qed.
Lemma erase_val_subst' x v w :
  erase_expr (subst x v w) = subst x (erase_val v) (erase_val w).
Proof.
  destruct x; eauto using erase_val_subst.
Qed.

Fixpoint erase_ectxi k : ectx :=
  match k with
  | CtxApp1 v2 =>
      [CtxApp1 (erase_val v2)]
  | CtxApp2 e1 =>
      [CtxApp2 (erase_expr e1)]
  | CtxUnop op =>
      [CtxUnop op]
  | CtxBinop1 op v2 =>
      [CtxBinop1 op (erase_val v2)]
  | CtxBinop2 op e1 =>
      [CtxBinop2 op (erase_expr e1)]
  | CtxEqual1 v2 =>
      [CtxEqual1 (erase_val v2)]
  | CtxEqual2 e1 =>
      [CtxEqual2 (erase_expr e1)]
  | CtxIf e1 e2 =>
      [CtxIf (erase_expr e1) (erase_expr e2)]
  | CtxConstr tag vs es =>
      [CtxConstr tag (erase_val <$> vs) (erase_expr <$> es)]
  | CtxProj proj =>
      [CtxProj proj]
  | CtxMatch x e1 brs =>
      [CtxMatch x (erase_expr e1) ((λ br, (br.1, erase_expr br.2)) <$> brs)]
  | CtxReveal =>
      [CtxReveal]
  | CtxFor1 e2 e3 =>
      [CtxFor1 (erase_expr e2) (erase_expr e3)]
  | CtxFor2 v1 e3 =>
      [CtxFor2 (erase_val v1) (erase_expr e3)]
  | CtxRecord vs es =>
      [CtxRecord (erase_val <$> vs) (erase_expr <$> es)]
  | CtxAlloc1 v2 =>
      [CtxAlloc1 (erase_val v2)]
  | CtxAlloc2 e1 =>
      [CtxAlloc2 (erase_expr e1)]
  | CtxLoad =>
      [CtxLoad]
  | CtxStore1 v2 =>
      [CtxStore1 (erase_val v2)]
  | CtxStore2 e1 =>
      [CtxStore2 (erase_expr e1)]
  | CtxXchg1 v2 =>
      [CtxXchg1 (erase_val v2)]
  | CtxXchg2 e1 =>
      [CtxXchg2 (erase_expr e1)]
  | CtxCAS0 v1 v2 =>
      [CtxCAS0 (erase_val v1) (erase_val v2)]
  | CtxCAS1 e0 v2 =>
      [CtxCAS1 (erase_expr e0) (erase_val v2)]
  | CtxCAS2 e0 e1 =>
      [CtxCAS2 (erase_expr e0) (erase_expr e1)]
  | CtxFAA1 v2 =>
      [CtxFAA1 (erase_val v2)]
  | CtxFAA2 e1 =>
      [CtxFAA2 (erase_expr e1)]
  | CtxResolve0 k v1 v2 =>
      erase_ectxi k ++
      [CtxConstr 0 [erase_val v2; erase_val v1] []; CtxProj 2]
  | CtxResolve1 e0 v2 =>
      [CtxConstr 0 [erase_val v2] [erase_expr e0]; CtxProj 2]
  | CtxResolve2 e0 e1 =>
      [CtxConstr 0 [] [erase_expr e1; erase_expr e0]; CtxProj 2]
  end.

Definition erase_ectx K : ectx :=
  K ≫= erase_ectxi.

Definition erase_heap h :=
  erase_val <$> h.

Definition erase_state σ :=
  {|state_heap := erase_heap (state_heap σ) ;
    state_prophets := ∅ ;
  |}.

Definition erase_cfg ρ : config zoo :=
  (erase_exprs ρ.1, erase_state ρ.2).

Lemma erase_to_val e v :
  to_val (erase_expr e) = Some v →
    ∃ v',
    to_val e = Some v' ∧
    erase_val v' = v.
Proof.
  destruct e; naive_solver.
Qed.

Lemma erase_not_val e :
  to_val e = None →
  to_val (erase_expr e) = None.
Proof.
  destruct e; done.
Qed.

Lemma erase_ectx_app K1 K2 :
  erase_ectx (K1 ++ K2) = erase_ectx K1 ++ erase_ectx K2.
Proof.
  rewrite /erase_ectx bind_app //.
Qed.

Lemma erase_expr_fill K e :
  erase_expr (fill K e) = fill (erase_ectx K) (erase_expr e).
Proof.
  move: e. induction K as [| k K IH] using rev_ind => e //.
  rewrite !erase_ectx_app !fill_app /= -{}IH.
  induction k.
  all: rewrite ?fill_app /= /erase_resolve.
  all: auto 10 with f_equal.
  all: rewrite fmap_app /of_vals -!list_fmap_compose //.
Qed.

(* Lemma val_unboxed_erased v : *)
(*   val_unboxed (erase_val v) ↔ val_unboxed v. *)
(* Proof. *)
(*   destruct v; rewrite /= /literal_unboxed; repeat (done || simpl; case_match). *)
(* Qed. *)
(* Lemma val_comparable_erase v1 v2 : *)
(*   val_comparable (erase_val v1) (erase_val v2) ↔ *)
(*   val_comparable v1 v2. *)
(* Proof. *)
(*   rewrite /val_comparable !val_unboxed_erased. done. *)
(* Qed. *)
(* Lemma erase_val_inj_iff v1 v2 : *)
(*   val_comparable v1 v2 → *)
(*   erase_val v1 = erase_val v2 ↔ v1 = v2. *)
(* Proof. *)
(*   destruct v1, v2; rewrite /= /literal_unboxed; *)
(*     repeat (done || (by intros [[] | []]) || simpl; case_match). *)
(* Qed. *)

Lemma eval_unop_erase op v v' :
  eval_unop op (erase_val v) = Some v' ↔
    ∃ w,
    eval_unop op v = Some w ∧
    erase_val w = v'.
Proof.
  destruct op, v as [[] | |]; naive_solver.
Qed.

Lemma eval_binop_erase op v1 v2 v' :
  eval_binop op (erase_val v1) (erase_val v2) = Some v' ↔
    ∃ w,
    eval_binop op v1 v2 = Some w ∧
    erase_val w = v'.
Proof.
  destruct v1 as [[] | |]; try naive_solver;
  destruct v2 as [[] | |]; try naive_solver;
  destruct op; naive_solver.

  (* rewrite /bin_op_eval /bin_op_eval_int /bin_op_eval_bool /bin_op_eval_loc; *)
  (*   split; [intros ?|intros (?&?&?)]; *)
  (*     repeat (case_match; simplify_eq/=); eauto. *)
  (* - eexists _; split; eauto; simpl. *)
  (*   erewrite bool_decide_ext; first by eauto. *)
  (*   rewrite erase_val_inj_iff; done. *)
  (* - by assert (val_comparable v1 v2) by by apply val_comparable_erase. *)
  (* - by erewrite bool_decide_ext; last apply erase_val_inj_iff. *)
  (* - by assert (val_comparable (erase_val v1) (erase_val v2)) *)
  (*     by by apply val_comparable_erase. *)
Qed.

Lemma lookup_erase_heap_None h l :
  erase_heap h !! l = None ↔ h !! l = None.
Proof.
  rewrite lookup_fmap; destruct (h !! l); done.
Qed.

Lemma lookup_erase_heap h l :
  erase_heap h !! l = erase_val <$> h !! l.
Proof.
  apply lookup_fmap.
Qed.

Lemma erase_heap_insert h l v :
  erase_heap (<[l := v]> h) = <[l := erase_val v]> (erase_heap h).
Proof.
  apply fmap_insert.
Qed.

Lemma fmap_heap_array (f : val → val) l vs :
  f <$> heap_array l vs = heap_array l (f <$> vs).
Proof.
  move: l. induction vs as [| v vs IH] => l.
  - apply fmap_empty.
  - rewrite fmap_insert IH //.
Qed.

Lemma erase_heap_array l vs h :
  erase_heap (heap_array l vs ∪ h) =
  heap_array l (erase_val <$> vs) ∪ erase_heap h.
Proof.
  apply map_eq => l'.
  rewrite lookup_fmap !lookup_union -fmap_heap_array !lookup_fmap.
  destruct (heap_array l vs !! l'), (h !! l'); done.
Qed.

Lemma erase_state_init l vs σ :
  erase_state (state_init_heap l vs σ) =
  state_init_heap l (erase_val <$> vs) (erase_state σ).
Proof.
  rewrite /erase_state erase_heap_array //.
Qed.

Definition base_steps_to_erasure_of e1 σ1 e2 σ2 es :=
  ∃ κ' e2' σ2' es' ϕ,
  base_step e1 σ1 κ' e2' σ2' es' ϕ ∧
  erase_expr e2' = e2 ∧
  erase_state σ2' = σ2 ∧
  erase_exprs es' = es.

Lemma erased_base_step_base_step_rec f x e v σ :
  base_steps_to_erasure_of
    ((rec: f x => e)%V v)
    σ
    (subst' f (rec: f x => erase_expr e) $ subst' x (erase_val v) $ erase_expr e)
    (erase_state σ)
    [].
Proof.
  repeat econstructor. rewrite !erase_expr_subst' //.
Qed.
Lemma erased_base_step_base_step_Proph σ :
  base_steps_to_erasure_of
    Proph
    σ
    #LitPoison
    (erase_state σ)
    [].
Proof.
  repeat eexists _. split; [apply base_step_proph' | done].
Qed.
Lemma erased_base_step_base_step_Alloc n v σ l :
  (0 < n)%Z →
  ( ∀ i : Z,
    (0 ≤ i < n)%Z →
    erase_heap (state_heap σ) !! (l +ₗ i) = None
  ) →
  base_steps_to_erasure_of
    (Alloc #n v)
    σ
    #l
    (state_init_heap l (replicate (Z.to_nat n) (erase_val v)) (erase_state σ))
    [].
Proof.
  repeat eexists _. split_and!.
  - econstructor; first done.
    setoid_rewrite <- lookup_erase_heap_None. done.
  - done.
  - rewrite erase_state_init fmap_replicate //.
  - done.
Qed.
Lemma erased_base_step_base_step_Load l σ v :
  erase_heap (state_heap σ) !! l = Some v →
  base_steps_to_erasure_of
    (!#l)
    σ
    v
    (erase_state σ)
    [].
Proof.
  intros Hl.
  rewrite lookup_erase_heap in Hl.
  destruct (state_heap σ !! l) eqn:?; simplify.
  repeat eexists _; split; first econstructor; done.
Qed.
Lemma erased_base_step_base_step_Xchg l v w σ :
  erase_heap (state_heap σ) !! l = Some v →
  base_steps_to_erasure_of
    (Xchg #l w)
    σ
    v
    {|state_heap := <[l := erase_val w]> (erase_heap (state_heap σ)) ;
      state_prophets := ∅ ;
    |}
    [].
Proof.
  intros Hl.
  rewrite lookup_erase_heap in Hl.
  destruct (state_heap σ !! l) eqn:?; simplify.
  repeat eexists _; split_and!; first econstructor; try done.
  rewrite /erase_state erase_heap_insert //.
Qed.
Lemma erased_base_step_base_step_Store l v w σ :
  erase_heap (state_heap σ) !! l = Some v →
  base_steps_to_erasure_of
    (#l <- w)
    σ
    ()
    {|state_heap := <[l := erase_val w]> (erase_heap (state_heap σ)) ;
      state_prophets := ∅ ;
    |}
    [].
Proof.
  intros Hl.
  rewrite lookup_erase_heap in Hl.
  destruct (state_heap σ !! l) eqn:?; simplify.
  repeat eexists _; split_and!; first econstructor; try done.
  rewrite /erase_state erase_heap_insert //.
Qed.
(* Lemma erased_base_step_base_step_CAS l v w σ vl : *)
(*   erase_heap (heap σ) !! l = Some (Some vl) → *)
(*   val_comparable vl (erase_val v) → *)
(*   base_steps_to_erasure_of *)
(*     (CAS #l v w) σ *)
(*     (vl, #(bool_decide (vl = erase_val v)))%V *)
(*     (if bool_decide (vl = erase_val v) *)
(*      then {| heap := <[l:=Some $ erase_val w]> (erase_heap (heap σ)); *)
(*              used_proph_id := ∅ |} *)
(*      else erase_state σ) []. *)
(* Proof. *)
(*   intros Hl Hvl. *)
(*   rewrite lookup_erase_heap in Hl. *)
(*   destruct (heap σ !! l) as [[u|]|] eqn:?; simplify_eq/=. *)
(*   rewrite -> val_comparable_erase in Hvl. *)
(*   destruct (decide (u = v)) as [->|Hneq]. *)
(*   - eexists _, _, _, _; simpl; split. *)
(*     { econstructor; eauto. } *)
(*     rewrite !bool_decide_eq_true_2; eauto using erase_val_inj_iff; []. *)
(*     rewrite -?erase_heap_insert_Some. *)
(*     split_and!; auto. *)
(*   - eexists _, _, _, _; simpl; split. *)
(*     { econstructor; eauto. } *)
(*     rewrite !bool_decide_eq_false_2; eauto; []. *)
(*     by rewrite erase_val_inj_iff. *)
(* Qed. *)
(*Lemma erased_base_step_base_step_FAA l n m σ :*)
(*  erase_heap (heap σ) !! l = Some (Some #n) →*)
(*  base_steps_to_erasure_of*)
(*    (FAA #l #m) σ #n*)
(*    {| heap := <[l:= Some #(n + m)]> (erase_heap (heap σ));*)
(*       used_proph_id := ∅ |} [].*)
(*Proof.*)
(*  intros Hl.*)
(*  rewrite lookup_erase_heap in Hl.*)
(*  destruct (heap σ !! l) as [[[[]| | | |]|]|] eqn:?; simplify_eq/=.*)
(*  repeat econstructor; first by eauto.*)
(*  by rewrite /state_upd_heap /erase_state /= erase_heap_insert_Some.*)
(*Qed.*)

(*(** When the erased program makes a base step, so does the original program. *)*)
(*Lemma erased_base_step_base_step e1 σ1 κ e2 σ2 efs:*)
(*  base_step (erase_expr e1) (erase_state σ1) κ e2 σ2 efs →*)
(*  base_steps_to_erasure_of e1 σ1 e2 σ2 efs.*)
(*Proof.*)
(*  intros Hhstep.*)
(*  inversion Hhstep; simplify_eq/=;*)
(*    repeat match goal with*)
(*           | H : _ = erase_expr ?e |- _ => destruct e; simplify_eq/=*)
(*           | H : _ = erase_val ?v |- _ => destruct v; simplify_eq/=*)
(*           | H : _ = erase_base_lit ?l |- _ => destruct l; simplify_eq/=*)
(*           | H : context [erased_new_proph] |- _ => unfold erased_new_proph in H*)
(*           | H : un_op_eval _ (erase_val _) = Some _ |- _ =>*)
(*             apply un_op_eval_erase in H as [? [? ?]]*)
(*           | H : bin_op_eval _ (erase_val _) (erase_val _) = Some _ |- _ =>*)
(*             apply bin_op_eval_erase in H as [? [? ?]]*)
(*           | H : val_unboxed (erase_val _) |- _ =>*)
(*             apply -> val_unboxed_erased in H*)
(*           end; simplify_eq/=;*)
(*    try (by repeat econstructor);*)
(*  eauto using erased_base_step_base_step_rec,*)
(*    erased_base_step_base_step_Proph,*)
(*    erased_base_step_base_step_AllocN,*)
(*    erased_base_step_base_step_Free,*)
(*    erased_base_step_base_step_Load,*)
(*    erased_base_step_base_step_Xchg,*)
(*    erased_base_step_base_step_Store,*)
(*    erased_base_step_base_step_CAS,*)
(*    erased_base_step_base_step_FAA.*)
(*Qed.*)

(*Lemma fill_to_resolve e v1 v2 K e' :*)
(*  to_val e' = None →*)
(*  Resolve e v1 v2 = fill K e' →*)
(*  K = [] ∨ ∃ K' Ki, K = K' ++ [ResolveLCtx Ki v1 v2].*)
(*Proof.*)
(*  intros Hnv Hrs; simpl in *.*)
(*  assert (∀ v K, fill K e' ≠ v) as Hcontr.*)
(*  { intros w K' Hw.*)
(*    assert (to_val (of_val w) = to_val (fill K' e')) as He'*)
(*        by (by rewrite Hw).*)
(*    rewrite fill_not_val in He'; by eauto. }*)
(*  destruct K as [|Ki K _] using rev_ind; first by left.*)
(*  rewrite fill_app in Hrs.*)
(*  destruct Ki; simplify_eq/=; eauto;*)
(*    try exfalso; eapply Hcontr; eauto.*)
(*Qed.*)

(*Lemma projs_pure_steps (v0 v1 v2 : val) :*)
(*  rtc pure_step (Fst (Fst (v0, v1, v2))) v0.*)
(*Proof.*)
(*  etrans; first apply (rtc_pure_step_ctx (fill [PairLCtx _; FstCtx; FstCtx])).*)
(*  { apply rtc_once.*)
(*    apply pure_base_step_pure_step.*)
(*    split; first repeat econstructor.*)
(*    intros ????? Hhstep; inversion Hhstep; simplify_eq/=; eauto. }*)
(*  simpl.*)
(*  etrans; first apply (rtc_pure_step_ctx (fill [FstCtx; FstCtx])).*)
(*  { apply rtc_once.*)
(*    apply pure_base_step_pure_step.*)
(*    split; first repeat econstructor.*)
(*    intros ????? Hhstep; inversion Hhstep; simplify_eq/=; eauto. }*)
(*  simpl.*)
(*  etrans; first apply (rtc_pure_step_ctx (fill [FstCtx])).*)
(*  { apply rtc_once.*)
(*    apply pure_base_step_pure_step.*)
(*    split; first repeat econstructor.*)
(*    intros ????? Hhstep; inversion Hhstep; simplify_eq/=; eauto. }*)
(*  simpl.*)
(*  apply rtc_once.*)
(*  apply pure_base_step_pure_step.*)
(*  split; first repeat econstructor.*)
(*  intros ????? Hhstep; inversion Hhstep; simplify_eq/=; eauto.*)
(*Qed.*)

(*Lemma Resolve_3_vals_base_stuck v0 v1 v2 σ κ e σ' efs :*)
(*  ¬ base_step (Resolve v0 v1 v2) σ κ e σ' efs.*)
(*Proof.*)
(*  intros Hhstep.*)
(*  inversion Hhstep; simplify_eq/=.*)
(*  apply (eq_None_not_Some (to_val (Val v0))); last eauto.*)
(*  by eapply val_base_stuck.*)
(*Qed.*)

(*Lemma Resolve_3_vals_unsafe (v0 v1 v2 : val) σ :*)
(*  ¬ not_stuck (Resolve v0 v1 v2) σ.*)
(*Proof.*)
(*  assert(∀ w K e, Val w = fill K e → is_Some (to_val e)) as Hvfill.*)
(*  { intros ? K ? Heq; eapply (fill_val K); rewrite /= -Heq; eauto. }*)
(*  apply not_not_stuck.*)
(*  split; first done.*)
(*  intros ???? [K e1' e2' Hrs Hhstep]; simplify_eq/=.*)
(*  destruct K as [|Ki K _] using rev_ind.*)
(*  { simplify_eq/=.*)
(*    eapply Resolve_3_vals_base_stuck; eauto. }*)
(*  rewrite fill_app in Hrs.*)
(*  destruct Ki; simplify_eq/=.*)
(*  - rename select ectx_item into Ki.*)
(*    pose proof (fill_item_val Ki (fill K e1')) as Hnv.*)
(*    apply fill_val in Hnv as [? Hnv]; last by rewrite -Hrs; eauto.*)
(*    by erewrite val_base_stuck in Hnv.*)
(*  - edestruct Hvfill as [? Heq]; eauto.*)
(*    by erewrite val_base_stuck in Heq.*)
(*  - edestruct Hvfill as [? Heq]; eauto.*)
(*    by erewrite val_base_stuck in Heq.*)
(*Qed.*)

(*(** [(e1, σ1)] takes a [prim_step] to [(e2', σ2')] forking threads [efs']*)
(* such that [σ2] is the erasure of [σ2'] and [efs] is the erasure of*)
(* [efs']. Furthermore, [e2] takes [pure_steps] to match up with [e2].  It is*)
(* crucial for us that [e2] takes [pure_step]s because we need to know*)
(* that [e2] does not get stuck and that the steps are deterministic.*)

(* Essentially, the main part of the erasure proof's argument is that if*)
(* the erased program takes steps, then the original program also takes*)
(* matching steps. This however, does not entirely hold. In cases where*)
(* the erasure of [Resovle] takes a step, the original program*)
(* immediately produces the value while the erased program has to still*)
(* perform projections [Fst] to get the result (see the [Resolve] case*)
(* of [erase_expr]). For this purpose, we prove that in those cases (and*)
(* also in general) the erased program also takes a number of (possibly*)
(* zero) steps so that the original and the erased programs are matched*)
(* up again. *)*)
(*Definition prim_step_matched_by_erased_steps e1 σ1 e2 σ2 efs :=*)
(*  ∃ e2' σ2' κ' efs' e2'',*)
(*    prim_step e1 σ1 κ' e2' σ2' efs' ∧ rtc pure_step e2 e2'' ∧*)
(*    erase_expr e2' = e2'' ∧ erase_state σ2' = σ2 ∧ erase_exprs efs' = efs.*)

(*Lemma prim_step_matched_by_erased_steps_ectx K e1 σ1 e2 σ2 efs :*)
(*  prim_step_matched_by_erased_steps e1 σ1 e2 σ2 efs →*)
(*  prim_step_matched_by_erased_steps (fill K e1) σ1 (fill (erase_ectx K) e2) σ2 efs.*)
(*Proof.*)
(*  intros (?&?&?&?&?&?&?&?&?&?); simplify_eq/=.*)
(*  eexists _, _, _, _, _; repeat split.*)
(*  - by apply fill_prim_step.*)
(*  - rewrite erase_ectx_expr.*)
(*    by eapply (rtc_pure_step_ctx (fill (erase_ectx K))).*)
(*Qed.*)

(*Definition is_Resolve (e : expr) :=*)
(*  match e with Resolve _ _ _ => True | _ => False end.*)

(*#[global] Instance is_Resolve_dec e : Decision (is_Resolve e).*)
(*Proof. destruct e; solve_decision. Qed.*)

(*Lemma non_resolve_prim_step_matched_by_erased_steps_ectx_item*)
(*      Ki e1 e1' σ1 e2 σ2 efs :*)
(*  to_val e1' = None →*)
(*  ¬ is_Resolve e1 →*)
(*  not_stuck e1 σ1 →*)
(*  erase_expr e1 = fill_item Ki e1' →*)
(*  (∀ e1, erase_expr e1 = e1' → not_stuck e1 σ1 →*)
(*         prim_step_matched_by_erased_steps e1 σ1 e2 σ2 efs) →*)
(*  prim_step_matched_by_erased_steps e1 σ1 (fill_item Ki e2) σ2 efs.*)
(*Proof.*)
(*  intros Hnv Hnr Hsf He1 IH.*)
(*  destruct Ki; simplify_eq/=;*)
(*    repeat*)
(*      match goal with*)
(*      | H : erase_expr ?e = _ |- _ => destruct e; simplify_eq/=; try done*)
(*      | H : context [erased_new_proph] |- _ =>*)
(*        rewrite /erased_new_proph in H; simplify_eq/=*)
(*      | |- prim_step_matched_by_erased_steps ?e _ _ _ _ =>*)
(*        let tac K e :=*)
(*            lazymatch K with*)
(*            | [] => fail*)
(*            | _ => apply (prim_step_matched_by_erased_steps_ectx K);*)
(*                    apply IH; [done| by eapply (not_stuck_fill_inv (fill K))]*)
(*            end*)
(*        in*)
(*        reshape_expr e tac*)
(*      end.*)
(*Qed.*)

(*Lemma prim_step_matched_by_erased_steps_ectx_item Ki K e1 e1' σ1 e2 σ2 efs κ :*)
(*  base_step e1' (erase_state σ1) κ e2 σ2 efs →*)
(*  not_stuck e1 σ1 →*)
(*  erase_expr e1 = fill_item Ki (fill K e1') →*)
(*  (∀ K' e1, length K' ≤ length K →*)
(*     erase_expr e1 = (fill K' e1') → not_stuck e1 σ1 →*)
(*     prim_step_matched_by_erased_steps e1 σ1 (fill K' e2) σ2 efs) →*)
(*  prim_step_matched_by_erased_steps e1 σ1 (fill_item Ki (fill K e2)) σ2 efs.*)
(*Proof.*)
(*  intros Hhstp Hsf He1 IH; simpl in *.*)
(*  (** Case split on whether e1 is a [Resolve] expression. *)*)
(*  destruct (decide (is_Resolve e1)); last first.*)
(*  { (** e1 is not a [Resolve] expression. *)*)
(*    eapply non_resolve_prim_step_matched_by_erased_steps_ectx_item; [|by eauto..].*)
(*    by eapply fill_not_val, val_base_stuck. }*)
(*  (** e1 is a [Resolve] expression. *)*)
(*  destruct Ki; simplify_eq/=;*)
(*    repeat*)
(*      match goal with*)
(*      | H : erase_expr ?e = ?e' |- _ =>*)
(*        progress*)
(*          match e' with*)
(*          | fill _ _ => idtac*)
(*          | _ => destruct e; simplify_eq/=*)
(*          end*)
(*      end; try done.*)
(*  destruct K as [|Ki K _] using rev_ind; simplify_eq/=; [|].*)
(*  { (* case where (Fst (erase_expr e1_1, erase_expr e1_2, erase_expr e1_3)) *)*)
(*    (*      takes a base_step; it is impossible! *)*)
(*    by inversion Hhstp; simplify_eq. }*)
(*  rewrite /erase_resolve fill_app /= in He1; simplify_eq/=.*)
(*  destruct Ki; simplify_eq/=; rewrite fill_app /=.*)
(*  destruct K as [|Ki K _] using rev_ind; simplify_eq/=; [|].*)
(*  { (* case where (erase_expr e1_1, erase_expr e1_2, erase_expr e1_3) *)*)
(*    (*      takes a base_step; it is impossible! *)*)
(*    inversion Hhstp. }*)
(*  rewrite fill_app /= in He1.*)
(*  destruct Ki; simplify_eq/=; rewrite fill_app /=.*)
(*  - destruct K as [|Ki K _] using rev_ind; simplify_eq/=; [|].*)
(*    { (** [Resolve v0 v1 v2] is not safe! *)*)
(*      inversion Hhstp; simplify_eq/=.*)
(*      repeat*)
(*        match goal with*)
(*        | H : erase_expr ?e = _ |- _ => destruct e; simplify_eq/=*)
(*        | H : _ = erase_expr ?e |- _ => destruct e; simplify_eq/=*)
(*        end.*)
(*      by exfalso; eapply Resolve_3_vals_unsafe. }*)
(*    rewrite fill_app /= in He1.*)
(*    destruct Ki; simplify_eq/=; rewrite fill_app /=.*)
(*    + (** e1 is of the form ([Resolve] e10 e11 v0) and e11 takes a prim_step. *)*)
(*      destruct Hsf as [[? ?]| (?&?&?&?&Hrpstp)]; first done; simpl in *.*)
(*      inversion Hrpstp as [??? Hrs ? Hhstp']; simplify_eq/=.*)
(*      repeat*)
(*        match goal with*)
(*        | H : erase_expr ?e = ?e' |- _ =>*)
(*          progress*)
(*            match e' with*)
(*            | fill _ _ => idtac*)
(*            | _ => destruct e; simplify_eq/=*)
(*            end*)
(*        end.*)
(*      edestruct fill_to_resolve as [?|[K' [Ki HK]]]; eauto;*)
(*        [by eapply val_base_stuck| |]; simplify_eq/=.*)
(*      * (** e1 is of the form ([Resolve] e10 e11 v0) and e11 takes a base_step. *)*)
(*        inversion Hhstp'; simplify_eq.*)
(*        edestruct (IH K) as (?&?&?&?&?&Hpstp&?&?&?&?);*)
(*          [rewrite !length_app /=; lia|done|by eapply base_step_not_stuck|];*)
(*            simplify_eq/=.*)
(*        apply base_reducible_prim_step in Hpstp; simpl in *;*)
(*          last by rewrite /base_reducible /=; eauto 10.*)
(*        epose (λ H, base_step_to_val _ _ _ (Val _) _ _ _ _ _ _ _ H Hpstp)*)
(*          as Hhstv; edestruct Hhstv as [? ?%of_to_val]; [done|eauto|];*)
(*          simplify_eq.*)
(*        eexists _, _, _, _, _; repeat split;*)
(*          first (by apply base_prim_step; econstructor; eauto); auto.*)
(*        etrans.*)
(*        { by apply (rtc_pure_step_ctx*)
(*                      (fill [PairLCtx _; PairLCtx _; FstCtx; FstCtx])). }*)
(*        apply projs_pure_steps.*)
(*      * (** e1 is of the form ([Resolve] e10 v v0) and e10 takes a*)
(*           (non-base) prim_step. *)*)
(*        rewrite fill_app in Hrs; simplify_eq/=.*)
(*        edestruct (IH K) as (?&?&?&?&?&Hpstp&Hprstps&?&?&?);*)
(*          [rewrite !length_app; lia|done| |].*)
(*        { change (fill_item Ki) with (fill [Ki]).*)
(*          by rewrite -fill_app; eapply prim_step_not_stuck, Ectx_step. }*)
(*        simplify_eq/=.*)
(*        change (fill_item Ki) with (fill [Ki]) in Hpstp.*)
(*        rewrite -fill_app in Hpstp.*)
(*        eapply base_reducible_prim_step_ctx in Hpstp as [e2'' [He2'' Hpstp]];*)
(*          last by eexists _; eauto.*)
(*        simplify_eq/=.*)
(*        eexists _, _, _, _, _; repeat split.*)
(*        -- apply (fill_prim_step [ResolveLCtx _ _ _]); eapply Ectx_step; eauto.*)
(*        -- simpl; rewrite fill_app in Hprstps.*)
(*           by apply (rtc_pure_step_ctx*)
(*                    (fill [PairLCtx _; PairLCtx _; FstCtx; FstCtx])).*)
(*    + (** e1 is of the form ([Resolve] e1_ e1_2 v) and e1_2 takes a prim_step. *)*)
(*      repeat*)
(*        match goal with*)
(*        | H : erase_expr ?e = ?e' |- _ =>*)
(*          progress*)
(*            match e' with*)
(*            | fill _ _ => idtac*)
(*            | _ => destruct e; simplify_eq/=*)
(*            end*)
(*        end.*)
(*      apply (prim_step_matched_by_erased_steps_ectx [ResolveMCtx _ _]).*)
(*      apply IH; [rewrite !length_app /=; lia|done|*)
(*                 by eapply (not_stuck_fill_inv (fill [ResolveMCtx _ _])); simpl].*)
(*  - (** e1 is of the form ([Resolve] e1_ e1_2 e13) and e1_3 takes a prim_step. *)*)
(*    apply (prim_step_matched_by_erased_steps_ectx [ResolveRCtx _ _]).*)
(*    apply IH; [rewrite !length_app /=; lia|done|*)
(*                 by eapply (not_stuck_fill_inv (fill [ResolveRCtx _ _])); simpl].*)
(*Qed.*)

(*Lemma erased_prim_step_prim_step e1 σ1 κ e2 σ2 efs:*)
(*  prim_step (erase_expr e1) (erase_state σ1) κ e2 σ2 efs → not_stuck e1 σ1 →*)
(*  prim_step_matched_by_erased_steps e1 σ1 e2 σ2 efs.*)
(*Proof.*)
(*  intros Hstp He1sf.*)
(*  inversion Hstp as [K e1' e2' He1 ? Hhstp]; clear Hstp; simplify_eq/=.*)
(*  set (len := length K); assert (length K = len) as Hlen by done; clearbody len.*)
(*  revert K Hlen e1 He1 He1sf.*)
(*  induction len as [m IHm]using lt_wf_ind; intros K Hlen e1 He1 He1sf;*)
(*    simplify_eq.*)
(*  destruct K as [|Ki K _] using rev_ind; simplify_eq/=.*)
(*  { apply erased_base_step_base_step in Hhstp as (?&?&?&?&?&<-&?&<-).*)
(*    eexists _, _, _, _, _; repeat split;*)
(*      first (by apply base_prim_step); auto using rtc_refl. }*)
(*  rewrite length_app in IHm; simpl in *.*)
(*  rewrite fill_app /=; rewrite fill_app /= in He1.*)
(*  eapply prim_step_matched_by_erased_steps_ectx_item; eauto; [].*)
(*  { intros K' **; simpl in *. apply (IHm (length K')); auto with lia. }*)
(*Qed.*)

(*Lemma base_step_erased_prim_step_CAS v1 v2 σ l vl:*)
(*  heap σ !! l = Some (Some vl) →*)
(*  val_comparable vl v1 →*)
(*  ∃ e2' σ2' ef', prim_step (CAS #l (erase_val v1)*)
(*                             (erase_val v2)) (erase_state σ) [] e2' σ2' ef'.*)
(*Proof.*)
(*  intros Hl Hv.*)
(*  destruct (bool_decide (vl = v1)) eqn:Heqvls.*)
(*  - do 3 eexists; apply base_prim_step;*)
(*      econstructor; [|by apply val_comparable_erase|by eauto].*)
(*      by rewrite /erase_state /state_upd_heap /= lookup_erase_heap Hl.*)
(*  - do 3 eexists; apply base_prim_step;*)
(*        econstructor; [|by apply val_comparable_erase|by eauto].*)
(*      by rewrite /erase_state /state_upd_heap /= lookup_erase_heap Hl.*)
(*Qed.*)

(*Lemma base_step_erased_prim_step_resolve e w σ :*)
(*  (∃ e2' σ2' ef', prim_step (erase_expr e) (erase_state σ) [] e2' σ2' ef') →*)
(*    ∃ e2' σ2' ef',*)
(*    prim_step (erase_resolve (erase_expr e) #LitPoison (erase_val w)) (erase_state σ) [] e2' σ2' ef'.*)
(*Proof.*)
(*  intros (?&?&?&?).*)
(*  by eexists _, _, _;*)
(*    apply (fill_prim_step [PairLCtx _; PairLCtx _;FstCtx; FstCtx]).*)
(*Qed.*)

(*Lemma base_step_erased_prim_step_un_op σ op v v':*)
(*  un_op_eval op v = Some v' →*)
(*    ∃ e2' σ2' ef',*)
(*    prim_step (Unop op (erase_val v)) (erase_state σ) [] e2' σ2' ef'.*)
(*Proof.*)
(*  do 3 eexists; apply base_prim_step; econstructor.*)
(*  apply un_op_eval_erase; eauto.*)
(*Qed.*)

(*Lemma base_step_erased_prim_step_bin_op σ op v1 v2 v':*)
(*  bin_op_eval op v1 v2 = Some v' →*)
(*    ∃ e2' σ2' ef',*)
(*    prim_step (Binop op (erase_val v1) (erase_val v2)) (erase_state σ) [] e2' σ2' ef'.*)
(*Proof.*)
(*  do 3 eexists; apply base_prim_step; econstructor.*)
(*  apply bin_op_eval_erase; eauto.*)
(*Qed.*)

(*Lemma base_step_erased_prim_step_allocN σ l n v:*)
(*  (0 < n)%Z →*)
(*  (∀ i : Z, (0 ≤ i)%Z → (i < n)%Z → heap σ !! (l +ₗ i) = None) →*)
(*    ∃ e2' σ2' ef',*)
(*    prim_step (AllocN #n (erase_val v)) (erase_state σ) [] e2' σ2' ef'.*)
(*Proof.*)
(*  do 3 eexists; apply base_prim_step; econstructor; eauto.*)
(*  intros; rewrite lookup_erase_heap_None; eauto.*)
(*Qed.*)

(*Lemma base_step_erased_prim_step_free σ l v :*)
(*  heap σ !! l = Some (Some v) →*)
(*    ∃ e2' σ2' ef',*)
(*    prim_step (Free #l) (erase_state σ) [] e2' σ2' ef'.*)
(*Proof.*)
(*  intros Hw. do 3 eexists; apply base_prim_step; econstructor.*)
(*  rewrite /erase_state /state_upd_heap /= lookup_erase_heap Hw; eauto.*)
(*Qed.*)

(*Lemma base_step_erased_prim_step_load σ l v:*)
(*  heap σ !! l = Some (Some v) →*)
(*    ∃ e2' σ2' ef',*)
(*    prim_step (! #l) (erase_state σ) [] e2' σ2' ef'.*)
(*Proof.*)
(*  do 3 eexists; apply base_prim_step; econstructor.*)
(*  rewrite /erase_state /state_upd_heap /= lookup_erase_heap.*)
(*  by destruct lookup; simplify_eq.*)
(*Qed.*)

(*Lemma base_step_erased_prim_step_xchg σ l v w :*)
(*  heap σ !! l = Some (Some v) →*)
(*    ∃ e2' σ2' ef',*)
(*    prim_step (Xchg #l (erase_val w)) (erase_state σ) [] e2' σ2' ef'.*)
(*Proof.*)
(*  intros Hl. do 3 eexists; apply base_prim_step; econstructor.*)
(*  rewrite /erase_state /state_upd_heap /= lookup_erase_heap Hl; eauto.*)
(*Qed.*)

(*Lemma base_step_erased_prim_step_store σ l v w :*)
(*  heap σ !! l = Some (Some v) →*)
(*    ∃ e2' σ2' ef',*)
(*    prim_step (#l <- erase_val w) (erase_state σ) [] e2' σ2' ef'.*)
(*Proof.*)
(*  intros Hw. do 3 eexists; apply base_prim_step; econstructor.*)
(*  rewrite /erase_state /state_upd_heap /= lookup_erase_heap Hw; eauto.*)
(*Qed.*)

(*Lemma base_step_erased_prim_step_FAA σ l n n':*)
(*  heap σ !! l = Some (Some #n) →*)
(*    ∃ e2' σ2' ef',*)
(*    prim_step (FAA #l #n') (erase_state σ) [] e2' σ2' ef'.*)
(*Proof.*)
(*  intros Hl.*)
(*  do 3 eexists; apply base_prim_step. econstructor.*)
(*  by rewrite /erase_state /state_upd_heap /= lookup_erase_heap Hl.*)
(*Qed.*)

(*(***)
(*[Resolve] is translated as a projection out of a triple.*)
(*Therefore, when resolve takes a base step, the erasure of [Resolve] takes a*)
(*prim step inside the triple.*)
(**)*)
(*Lemma base_step_erased_prim_step e1 σ1 κ e2 σ2 ef:*)
(*  base_step e1 σ1 κ e2 σ2 ef →*)
(*    ∃ e2' σ2' ef',*)
(*    prim_step (erase_expr e1) (erase_state σ1) [] e2' σ2' ef'.*)
(*Proof.*)
(*  induction 1; simplify_eq/=;*)
(*    eauto using base_step_erased_prim_step_CAS,*)
(*                base_step_erased_prim_step_resolve,*)
(*                base_step_erased_prim_step_un_op,*)
(*                base_step_erased_prim_step_bin_op,*)
(*                base_step_erased_prim_step_allocN,*)
(*                base_step_erased_prim_step_free,*)
(*                base_step_erased_prim_step_load,*)
(*                base_step_erased_prim_step_store,*)
(*                base_step_erased_prim_step_xchg,*)
(*                base_step_erased_prim_step_FAA;*)
(*    by do 3 eexists; apply base_prim_step; econstructor.*)
(*Qed.*)

(*Lemma reducible_erased_reducible e σ :*)
(*  reducible e σ →*)
(*  reducible (erase_expr e) (erase_state σ).*)
(*Proof.*)
(*  intros (?&?&?&?&Hpstp); simpl in *.*)
(*  inversion Hpstp; simplify_eq/=.*)
(*  rewrite erase_ectx_expr.*)
(*  edestruct base_step_erased_prim_step as (?&?&?&?); first done; simpl in *.*)
(*  eexists _, _, _, _; eapply fill_prim_step; eauto.*)
(*Qed.*)

(*Lemma pure_step_tp_safe t1 t2 e1 σ :*)
(*  (∀ e2, e2 ∈ t2 → not_stuck e2 σ) →*)
(*  pure_steps_tp t1 (erase_exprs t2) →*)
(*  e1 ∈ t1 → not_stuck e1 (erase_state σ).*)
(*Proof.*)
(*  intros Ht2 Hpr [i He1]%elem_of_list_lookup_1.*)
(*  eapply Forall2_lookup_l in Hpr as [e2' [He2' Hpr]]; simpl in *; eauto.*)
(*  rewrite /erase_exprs list_lookup_fmap in He2'.*)
(*  destruct (t2 !! i) eqn:He2; simplify_eq/=.*)
(*  apply elem_of_list_lookup_2, Ht2 in He2.*)
(*  clear -Hpr He2.*)
(*  inversion Hpr as [|??? [? _]]; simplify_eq.*)
(*  - destruct He2 as [[? ?%of_to_val]|]; simplify_eq/=; first by left; eauto.*)
(*    by right; apply reducible_erased_reducible.*)
(*  - right; eauto using reducible_no_obs_reducible.*)
(*Qed.*)

Definition erased_step ρ1 ρ2 :=
  ∃ κ ϕ,
  step ρ1 κ ρ2 ϕ.

Lemma erasure e σ :
  adequate e σ →
  adequate (erase_expr e) (erase_state σ).
Proof.
  intros H.
  cut (
    ∀ t2 σ2,
    rtc erased_step ([erase_expr e], erase_state σ) (t2, σ2) →
      ∃ t2' t2'' σ2',
      rtc erased_step ([e], σ) (t2'', σ2') ∧
      t2' = erase_exprs t2'' ∧
      σ2 = erase_state σ2' ∧
      Forall2 (rtc pure_step) t2 t2'
  ). {
    intros Hreach; split; simpl in *.
    - intros ? ? ? Hrtc; edestruct (Hreach _ _ Hrtc) as
          (t2'&t2''&σ2'&Hos&Ht2'&Hσ2&Hptp); simplify_eq/=.
      apply Forall2_cons_inv_l in Hptp as (oe&t3&Hoe%rtc_pure_step_val&_&?);
        destruct t2''; simplify_eq/=.
      apply erase_to_val in Hoe as (?&?%of_to_val&?); simplify_eq.
      pose proof (adequate_result _ _ _ _ Hade _ _ _ Hos); eauto.
    - intros ? ? ? Hs Hrtc He2; edestruct (Hreach _ _ Hrtc) as
          (t2'&t2''&σ2'&Hos&Ht2'&Hσ2&Hptp); simplify_eq/=.
      eapply pure_step_tp_safe; [|done..].
      intros e2' He2'.
      apply (adequate_not_stuck _ _ _ _ Hade _ _ _ eq_refl Hos He2').
  }
  intros t2 σ2 [n Hstps]%rtc_nsteps; simpl in *; revert t2 σ2 Hstps.
  induction n as [|n IHn].
  { intros t2 σ2 Hstps; inversion Hstps; simplify_eq /=.
    repeat econstructor. }
  intros t2 σ2 Hstps.
  apply nsteps_inv_r in Hstps as [[t3 σ3] [Hstps Hρ]]; simpl in *.
  destruct (IHn _ _ Hstps) as (t2'&t2''&σ2'&Hostps&?&?&Hprstps); simplify_eq.
  edestruct @erased_step_pure_step_tp as [[? Hint]|Hext]; simplify_eq/=;
    eauto 10; [|done..].
  destruct Hext as (i&ei&t2'&efs&e'&κ&Hi1&Ht2&Hpstp);
    simplify_eq/=.
  rewrite /erase_exprs list_lookup_fmap in Hi1.
  destruct (t2'' !! i) as [eio|] eqn:Heq; simplify_eq/=.
  edestruct erased_prim_step_prim_step as
    (eio' & σ3 & κ' & efs' & ee & Heiopstp & Hprstps' & ?&?&?); first done;
    last simplify_eq/=.
  { eapply adequate_not_stuck; eauto using elem_of_list_lookup_2. }
  eexists _, _, _; repeat split.
  { etrans; first done.
    apply rtc_once; eexists.
    eapply step_insert; eauto. }
  rewrite /erase_exprs fmap_app.
  rewrite list_fmap_insert/=.
  apply Forall2_app; last done.
  apply Forall2_same_length_lookup; split.
  { apply Forall2_length in Hprstps; rewrite length_fmap in Hprstps.
    by rewrite !length_insert length_fmap. }
  intros j x y.
  destruct (decide (i = j)); simplify_eq.
  { rewrite !list_lookup_insert ?length_fmap; eauto using lookup_lt_Some; [].
    by intros ? ?; simplify_eq. }
  rewrite !list_lookup_insert_ne // list_lookup_fmap.
  intros ? ?.
  eapply Forall2_lookup_lr; eauto.
  by rewrite /erase_exprs list_lookup_fmap.
Qed.
