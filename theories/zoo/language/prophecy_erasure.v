From stdpp Require Import
  gmap.

From zoo Require Import
  prelude.
From zoo.common Require Import
  list.
From zoo.language Require Export
  tactics.
From zoo Require Import
  options.

Implicit Types i : nat.
Implicit Types n m : Z.
Implicit Types l : location.
Implicit Types lit : literal.
Implicit Types e : expr.
Implicit Types es : list expr.
Implicit Types v w : val.
Implicit Types rec : recursive.
Implicit Types k : ectxi.
Implicit Types K : ectx.
Implicit Types h : gmap location val.
Implicit Types σ : state.
Implicit Types ρ : config zoo.

Definition literal_wf lit :=
  match lit with
  | LitPoison =>
      False
  | _ =>
      True
  end.

Fixpoint expr_wf e :=
  match e with
  | Val v =>
      val_wf v
  | Var _ =>
      True
  | Rec _ _ e =>
      expr_wf e
  | App e1 e2 =>
      expr_wf e1 ∧
      expr_wf e2
  | Let _ e1 e2 =>
      expr_wf e1 ∧
      expr_wf e2
  | Unop _ e =>
      expr_wf e
  | Binop _ e1 e2 =>
      expr_wf e1 ∧
      expr_wf e2
  | Equal e1 e2 =>
      expr_wf e1 ∧
      expr_wf e2
  | If e0 e1 e2 =>
      expr_wf e0 ∧
      expr_wf e1 ∧
      expr_wf e2
  | For e1 e2 e3 =>
      expr_wf e1 ∧
      expr_wf e2 ∧
      expr_wf e3
  | Alloc e1 e2 =>
      expr_wf e1 ∧
      expr_wf e2
  | Block _ _ es =>
      Forall' expr_wf es
  | Reveal e =>
      expr_wf e
  | Match e0 _ e1 brs =>
      expr_wf e0 ∧
      expr_wf e1 ∧
      Forall' (λ br, expr_wf br.2) brs
  | GetTag e =>
      expr_wf e
  | GetSize e =>
      expr_wf e
  | Load e1 e2 =>
      expr_wf e1 ∧
      expr_wf e2
  | Store e1 e2 e3 =>
      expr_wf e1 ∧
      expr_wf e2 ∧
      expr_wf e3
  | Xchg e1 e2 =>
      expr_wf e1 ∧
      expr_wf e2
  | CAS e0 e1 e2 =>
      expr_wf e0 ∧
      expr_wf e1 ∧
      expr_wf e2
  | FAA e1 e2 =>
      expr_wf e1 ∧
      expr_wf e2
  | Fork e =>
      expr_wf e
  | Proph =>
      True
  | Resolve e0 e1 e2 =>
      expr_wf e0 ∧
      expr_wf e1 ∧
      expr_wf e2
  end
with val_wf v :=
  match v with
  | ValLit lit =>
      literal_wf lit
  | ValRecs _ recs =>
      Forall' (λ rec, expr_wf rec.2) recs
  | ValBlock _ _ vs =>
      Forall' val_wf vs
  end.

Definition exprs_wf :=
  Forall expr_wf.

Definition state_wf σ :=
  map_Forall (λ _, val_wf) σ.(state_heap).

Definition config_wf ρ :=
  exprs_wf ρ.1 ∧
  state_wf ρ.2.

Lemma fill_item_wf_inv k e :
  expr_wf (fill_item k e) →
  expr_wf e.
Proof.
  intros H.
  induction k; try naive_solver.
  rewrite /= Forall'_Forall in H.
  list_simplifier. done.
Qed.
Lemma fill_wf_inv K e :
  expr_wf (fill K e) →
  expr_wf e.
Proof.
  induction K as [| k K IH] using rev_ind; first done.
  rewrite fill_app /=.
  intros ?%fill_item_wf_inv%IH. done.
Qed.

Definition erase_literal lit :=
  match lit with
  | LitProph _ =>
      LitPoison
  | _ =>
      lit
  end.

Definition erase_resolve e0 e1 e2 : expr :=
  Load (Block Immutable 0 [e0; e1; e2]) (Val $ ValInt 0).
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
        f
        x
        (erase_expr e)
  | App e1 e2 =>
      App
        (erase_expr e1)
        (erase_expr e2)
  | Let x e1 e2 =>
      Let
        x
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
  | For e1 e2 e3 =>
      For
        (erase_expr e1)
        (erase_expr e2)
        (erase_expr e3)
  | Alloc e1 e2 =>
      Alloc
        (erase_expr e1)
        (erase_expr e2)
  | Block mut tag es =>
      Block
        mut
        tag
        (erase_expr <$> es)
  | Reveal e =>
      Reveal
        (erase_expr e)
  | Match e0 x e1 brs =>
      Match
        (erase_expr e0)
        x
        (erase_expr e1)
        ((λ br, (br.1, erase_expr br.2)) <$> brs)
  | GetTag e =>
      GetTag
        (erase_expr e)
  | GetSize e =>
      GetSize
        (erase_expr e)
  | Load e1 e2 =>
      Load
        (erase_expr e1)
        (erase_expr e2)
  | Store e1 e2 e3 =>
      Store
        (erase_expr e1)
        (erase_expr e2)
        (erase_expr e3)
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
      App (Val $ ValFun BAnon (Val ValPoison)) (Val ValUnit)
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
  | ValRecs i recs =>
      ValRecs
        i
        ((λ rec, (rec.1, erase_expr rec.2)) <$> recs)
  | ValBlock bid tag vs =>
      ValBlock
        bid
        tag
        (erase_val <$> vs)
  end.
#[global] Arguments erase_expr !_ / : assert.
#[global] Arguments erase_val !_ / : assert.

Definition erase_recursive rec :=
  (rec.1, erase_expr rec.2).

Definition erase_exprs es :=
  erase_expr <$> es.

Fixpoint erase_ectxi k : ectx :=
  match k with
  | CtxApp1 v2 =>
      [CtxApp1 (erase_val v2)]
  | CtxApp2 e1 =>
      [CtxApp2 (erase_expr e1)]
  | CtxLet x e2 =>
      [CtxLet x (erase_expr e2)]
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
  | CtxFor1 e2 e3 =>
      [CtxFor1 (erase_expr e2) (erase_expr e3)]
  | CtxFor2 v1 e3 =>
      [CtxFor2 (erase_val v1) (erase_expr e3)]
  | CtxAlloc1 v2 =>
      [CtxAlloc1 (erase_val v2)]
  | CtxAlloc2 e1 =>
      [CtxAlloc2 (erase_expr e1)]
  | CtxBlock mut tag es vs =>
      [CtxBlock mut tag (erase_expr <$> es) (erase_val <$> vs)]
  | CtxReveal =>
      [CtxReveal]
  | CtxMatch x e1 brs =>
      [CtxMatch x (erase_expr e1) ((λ br, (br.1, erase_expr br.2)) <$> brs)]
  | CtxGetTag =>
      [CtxGetTag]
  | CtxGetSize =>
      [CtxGetSize]
  | CtxLoad1 v2 =>
      [CtxLoad1 (erase_val v2)]
  | CtxLoad2 e1 =>
      [CtxLoad2 (erase_expr e1)]
  | CtxStore1 v2 v3 =>
      [CtxStore1 (erase_val v2) (erase_val v3)]
  | CtxStore2 e1 v3 =>
      [CtxStore2 (erase_expr e1) (erase_val v3)]
  | CtxStore3 e1 e2 =>
      [CtxStore3 (erase_expr e1) (erase_expr e2)]
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
      [CtxBlock Immutable 0 [] [erase_val v1; erase_val v2]; CtxLoad1 (ValInt (Z.of_nat 0))]
  | CtxResolve1 e0 v2 =>
      [CtxBlock Immutable 0 [erase_expr e0] [erase_val v2]; CtxLoad1 (ValInt (Z.of_nat 0))]
  | CtxResolve2 e0 e1 =>
      [CtxBlock Immutable 0 [erase_expr e0; erase_expr e1] []; CtxLoad1 (ValInt (Z.of_nat 0))]
  end.

Definition erase_ectx K : ectx :=
  K ≫= erase_ectxi.

Definition erase_heap h :=
  erase_val <$> h.

Definition erase_state σ :=
  {|state_headers := σ.(state_headers) ;
    state_heap := erase_heap σ.(state_heap) ;
    state_prophets := ∅ ;
  |}.

Lemma erase_to_val e 𝑣 :
  to_val (erase_expr e) = Some 𝑣 →
    ∃ v,
    to_val e = Some v ∧
    erase_val v = 𝑣.
Proof.
  destruct e; naive_solver.
Qed.
Lemma erase_expr_val_inv e 𝑣 :
  erase_expr e = Val 𝑣 →
    ∃ v,
    e = Val v ∧
    𝑣 = erase_val v.
Proof.
  destruct e; naive_solver.
Qed.
Lemma erase_not_val e :
  to_val e = None →
  to_val (erase_expr e) = None.
Proof.
  destruct e; done.
Qed.
Lemma erase_exprs_vals es 𝑣s :
  erase_exprs es = of_vals 𝑣s →
    ∃ vs,
    es = of_vals vs ∧
    𝑣s = erase_val <$> vs.
Proof.
  move: 𝑣s. induction es as [| e es IH] => 𝑣s H.
  all: destruct 𝑣s as [| 𝑣 𝑣s]; try done.
  - eauto.
  - injection H as [= (v & -> & ->)%erase_expr_val_inv (vs & -> & ->)%IH].
    exists (v :: vs). done.
Qed.

Lemma erase_ectx_app K1 K2 :
  erase_ectx (K1 ++ K2) = erase_ectx K1 ++ erase_ectx K2.
Proof.
  rewrite /erase_ectx bind_app //.
Qed.

Lemma erase_fill_item k e :
  erase_expr (fill_item k e) = fill (erase_ectxi k) (erase_expr e).
Proof.
  induction k.
  all: rewrite //=.
  - rewrite fmap_app fmap_cons /of_vals -!list_fmap_compose //.
  - rewrite fill_app IHk //.
Qed.
Lemma erase_fill K e :
  erase_expr (fill K e) = fill (erase_ectx K) (erase_expr e).
Proof.
  move: e. induction K as [| k K IH] using rev_ind => e; first done.
  rewrite erase_ectx_app !fill_app /= erase_fill_item IH //.
Qed.

Lemma erase_fill_inv e 𝐾 𝑒 𝜎 :
  (* not_stuck e σ → *)
  base_reducible 𝑒 𝜎 →
  erase_expr e = fill 𝐾 𝑒 →
    ∃ K e',
    𝐾 = erase_ectx K ∧
    𝑒 = erase_expr e' ∧
    e = fill K e'.
Proof.
  intros H𝑒.
  move: e. induction 𝐾 as [| 𝑘 𝐾 IH] using rev_ind => e Heq.
  { eexists [], _. done. }
  rewrite fill_app /= in Heq.
  destruct 𝑘, e.
  all: try done.
  all: simplify.
  all:
    repeat
      match goal with
      | H: erase_expr _ = Val _ |- _ =>
          apply erase_expr_val_inv in H as (? & -> & ->)
      | H: erase_expr _ = fill _ _ |- _ =>
          apply IH in H as (? & ? & -> & -> & ->)
      end.
  all:
    try solve [
      match goal with
      | |- context [_ ++ [?k _ _]] =>
          eexists (_ ++ [k _ _])
      | |- context [_ ++ [?k _]] =>
          eexists (_ ++ [k _])
      | |- context [_ ++ [?k]] =>
          eexists (_ ++ [k])
      end;
      eexists;
      rewrite erase_ectx_app fill_app //
    ].
  - destruct (rev_elim 𝐾) as [-> | (𝐾' & 𝑘 & ->)].
    + apply base_reducible_not_val in H𝑒. naive_solver.
    + rewrite fill_app /= in Heq. destruct 𝑘; done.
  - destruct (rev_elim 𝐾) as [-> | (𝐾' & 𝑘 & ->)].
    + apply base_reducible_not_val in H𝑒. naive_solver.
    + rewrite fill_app /= in H. destruct 𝑘; done.
  - select (erase_expr <$> _ = _) (fun Heq =>
      apply fmap_app_cons_inv in Heq as (es1 & e & es2 & -> & -> & (K & e' & -> & -> & ->)%symmetry%IH & (? & -> & ->)%symmetry%erase_exprs_vals)
    ).
    eexists (_ ++ [CtxBlock _ _ _ _]), _.
    rewrite erase_ectx_app fill_app //.
  - rewrite /erase_resolve /= in Heq.
    simplify.
    destruct (rev_elim 𝐾) as [-> | (𝐾' & 𝑘 & ->)].
    + assert (∃ σ, reducible (Resolve e1 e2 e3) σ) as (σ & He) by admit.
      simplify.
      destruct H𝑒 as (𝜅 & 𝑒' & 𝜎' & 𝑒s & H𝑠𝑡𝑒𝑝).
      invert H𝑠𝑡𝑒𝑝.
      apply (erase_exprs_vals [e1; e2; e3]) in H as (? & ? & ->).
      do 3 (destruct x as [| ? x]; first done).
      simplify.
      destruct He as (κ & e' & σ' & es & [? ? ? ? ? Hstep]).
      simplify.
      admit.
    + rewrite fill_app /= in Heq.
      destruct 𝑘; try done.
      simplify.
      (* destruct es. *)
      admit.
  - injection Heq as [= _ Heq].
    edestruct (fill_val 𝐾 𝑒). { rewrite /= -Heq //. }
    apply base_reducible_not_val in H𝑒. naive_solver.
Admitted.
Lemma erase_base_step_inv e1 σ1 𝜅 𝑒2 𝜎2 𝑒s :
  expr_wf e1 →
  state_wf σ1 →
  base_step (erase_expr e1) (erase_state σ1) 𝜅 𝑒2 𝜎2 𝑒s →
    ∃ κ e2 σ2 es,
    expr_wf e2 ∧
    state_wf σ2 ∧
    exprs_wf es ∧
    base_step e1 σ1 κ e2 σ2 es ∧
    rtc pure_step 𝑒2 (erase_expr e2) ∧
    𝜎2 = erase_state σ2 ∧
    𝑒s = erase_exprs es.
Proof.
Admitted.
Lemma erase_prim_step_inv e1 σ1 𝜅 𝑒2 𝜎2 𝑒s :
  expr_wf e1 →
  state_wf σ1 →
  prim_step (erase_expr e1) (erase_state σ1) 𝜅 𝑒2 𝜎2 𝑒s →
    ∃ κ e2 σ2 es,
    expr_wf e2 ∧
    state_wf σ2 ∧
    exprs_wf es ∧
    prim_step e1 σ1 κ e2 σ2 es ∧
    rtc pure_step 𝑒2 (erase_expr e2) ∧
    𝜎2 = erase_state σ2 ∧
    𝑒s = erase_exprs es.
Proof.
  intros He1 Hσ1 [𝐾 𝑒1' 𝑒2' Heq -> H𝑠𝑡𝑒𝑝].
  eapply erase_fill_inv in Heq as (K & e1' & -> & -> & ->).
  2: eauto with zoo.
  apply erase_base_step_inv in H𝑠𝑡𝑒𝑝 as (κ & e2' & σ2 & es & He2' & Hσ2 & Hes & Hstep & Hrel & -> & ->); first last.
  { done. }
  { eapply fill_wf_inv. done. }
  exists κ, (fill K e2'), σ2, es. split_and!; try done.
  - admit.
  - apply base_step_fill_prim_step. done.
  - admit.
Admitted.

Definition erase_relation ρ 𝜌 :=
  config_wf ρ ∧
  Forall2 (λ e 𝑒, rtc pure_step 𝑒 (erase_expr e)) ρ.1 𝜌.1 ∧
  𝜌.2 = erase_state ρ.2.
Lemma erase_relation_step ρ1 𝜌1 𝜌2 :
  erase_relation ρ1 𝜌1 →
  silent_step 𝜌1 𝜌2 →
    ∃ ρ2,
    erase_relation ρ2 𝜌2 ∧
    rtc silent_step ρ1 ρ2.
Proof.
  destruct ρ1 as (es1, σ1), 𝜌1 as (𝑒s1, 𝜎1).
  intros ((Hes1 & Hσ1) & Hrel & ?) (𝜅 & (i & 𝑒1 & 𝑒2 & 𝜎2 & 𝑒s & H𝑠𝑡𝑒𝑝 & H𝑒s1_lookup & ->)).
  simplify.
  opose proof* Forall2_lookup_r as (e1 & Hes1_lookup & H𝑠𝑡𝑒𝑝s); [done.. |].
  apply rtc_inv in H𝑠𝑡𝑒𝑝s as [-> | (𝑒1' & H𝑠𝑡𝑒𝑝_ & H𝑠𝑡𝑒𝑝s)].
  - opose proof* Forall_lookup_1 as He1; [done.. |].
    opose proof* erase_prim_step_inv as (κ & e2 & σ2 & es & He2 & Hσ2 & Hes & Hstep & H𝑠𝑡𝑒𝑝s & -> & Heq); [done.. |]. subst 𝑒s.
    exists (<[i := e2]> es1 ++ es, σ2). split.
    + split_and!; first split; try done.
      * apply Forall_app_2; last done. apply Forall_insert; done.
      * apply Forall2_app.
        -- apply Forall2_insert; done.
        -- apply Forall2_fmap_r, Forall_Forall2_diag, Forall_true.
           eauto using rtc.
    + apply rtc_once. exists κ, i, e1, e2, σ2, es. done.
  - eapply pure_step_det in H𝑠𝑡𝑒𝑝 as (-> & -> & -> & ->); last done.
    rewrite right_id.
    exists (es1, σ1). split; last done. split_and!; try done.
    eapply Forall2_insert_r; done.
Qed.
Lemma erase_relation_steps ρ1 𝜌1 𝜌2 :
  erase_relation ρ1 𝜌1 →
  rtc silent_step 𝜌1 𝜌2 →
    ∃ ρ2,
    erase_relation ρ2 𝜌2 ∧
    rtc silent_step ρ1 ρ2.
Proof.
  intros Hrel1 H𝑠𝑡𝑒𝑝s.
  move: ρ1 Hrel1. induction H𝑠𝑡𝑒𝑝s as [| 𝜌1 𝜌2 𝜌3 H𝑠𝑡𝑒𝑝 H𝑠𝑡𝑒𝑝s IH] => ρ1 Hrel1.
  - naive_solver.
  - eapply erase_relation_step in H𝑠𝑡𝑒𝑝 as (ρ2 & (ρ3 & Hrel3 & Hsteps2)%IH & Hsteps1); last done.
    eexists. split; first done. etrans; done.
Qed.

Lemma erase_base_reducible e σ :
  base_reducible e σ →
  reducible (erase_expr e) (erase_state σ).
Proof.
  intros (κ & e2 & σ2 & es & Hstep).
  invert Hstep.
  all:
    try solve [
      eexists _, _, _, _, [] _ _;
      constructor
    ].
Admitted.
Lemma erase_reducible e σ :
  reducible e σ →
  reducible (erase_expr e) (erase_state σ).
Proof.
  intros (κ & e2 & σ2 & es & [K e1' e2' -> -> Hstep]).
  rewrite erase_fill.
  apply reducible_fill, erase_base_reducible.
  eauto with zoo.
Qed.
Lemma erase_not_stuck e σ :
  not_stuck e σ →
  not_stuck (erase_expr e) (erase_state σ).
Proof.
  intros [(v & <-%of_to_val) | Hstep].
  - apply val_not_stuck. done.
  - apply reducible_not_stuck, erase_reducible. done.
Qed.

Lemma erase_safe e σ :
  expr_wf e →
  state_wf σ →
  safe ([e], σ) →
  safe ([erase_expr e], erase_state σ).
Proof.
  intros He Hσ Hadequate (𝑒s, 𝜎) H𝑠𝑡𝑒𝑝s.
  eapply (erase_relation_steps ([e], σ)) in H𝑠𝑡𝑒𝑝s as ((es, σ') & (Hes & Hrel & ?) & Hsafe%Hadequate); last first.
  { split_and!; first split; try done.
    - apply Forall_singleton. done.
    - apply Forall2_cons. done.
  }
  simplify.
  rewrite Forall_lookup => i 𝑒 H𝑒s_lookup.
  eapply Forall2_lookup_r in Hrel as (e' & Hes_lookup & H𝑠𝑡𝑒𝑝s); last done.
  eapply Forall_lookup in Hsafe; last done.
  apply rtc_inv in H𝑠𝑡𝑒𝑝s as [-> | (𝑒' & H𝑠𝑡𝑒𝑝 & _)].
  - apply erase_not_stuck. done.
  - eapply pure_step_not_stuck. done.
Qed.
