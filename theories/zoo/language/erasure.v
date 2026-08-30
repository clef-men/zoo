Require Import stdpp.gmap.

Require Import zoo.prelude.
Require Import zoo.common.fin_maps.
Require Import zoo.language.tactics.
Require Import zoo.language.typeclasses.
Require Export zoo.language.wf.
Require Import zoo.options.

Implicit Type i : nat.
Implicit Type n m : Z.
Implicit Type tag : tag.
Implicit Type l : location.
Implicit Type pid : prophet_id.
Implicit Type gen : generativity.
Implicit Type mut : mutability.
Implicit Type lit 𝑙𝑖𝑡 : literal.
Implicit Type e eᵣ 𝑒 𝑒ᵣ : expr.
Implicit Type es 𝑒s : list expr.
Implicit Type v 𝑣 w 𝑤 : val.
Implicit Type vs : list val.
Implicit Type br : branch.
Implicit Type brs : list branch.
Implicit Type subj 𝑠𝑢𝑏𝑗 : subject.
Implicit Type rec : recursive.
Implicit Type recs : list recursive.
Implicit Type tid : thread_id.
Implicit Type hdr : header.
Implicit Type κ κs 𝜅 𝜅s : list observation.
Implicit Type k 𝑘 : ectxi.
Implicit Type K 𝐾 : ectx.
Implicit Type h : gmap location val.
Implicit Type σ 𝜎 : state.
Implicit Type ρ 𝜌 : config.

Fixpoint erase۰expr e :=
  match e with
  | Val v =>
      Val
        (erase۰val v)
  | Var x =>
      Var
        x
  | Rec f x e =>
      Rec
        f
        x
        (erase۰expr e)
  | App e1 e2 =>
      App
        (erase۰expr e1)
        (erase۰expr e2)
  | Let x e1 e2 =>
      Let
        x
        (erase۰expr e1)
        (erase۰expr e2)
  | Unop op e =>
      Unop
        op
        (erase۰expr e)
  | Binop op e1 e2 =>
      Binop
        op
        (erase۰expr e1)
        (erase۰expr e2)
  | Equal e1 e2 =>
      Equal
        (erase۰expr e1)
        (erase۰expr e2)
  | If e0 e1 e2 =>
      If
        (erase۰expr e0)
        (erase۰expr e1)
        (erase۰expr e2)
  | For e1 e2 e3 =>
      For
        (erase۰expr e1)
        (erase۰expr e2)
        (erase۰expr e3)
  | Alloc e1 e2 =>
      Alloc
        (erase۰expr e1)
        (erase۰expr e2)
  | Block mut tag es =>
      Block
        mut
        tag
        (erase۰expr <$> es)
  | Match e0 x e1 brs =>
      Match
        (erase۰expr e0)
        x
        (erase۰expr e1)
        ((λ br, (br.1, erase۰expr br.2)) <$> brs)
  | GetTag e =>
      GetTag
        (erase۰expr e)
  | GetSize e =>
      GetSize
        (erase۰expr e)
  | Load e1 e2 =>
      Load
        (erase۰expr e1)
        (erase۰expr e2)
  | Store e1 e2 e3 =>
      Store
        (erase۰expr e1)
        (erase۰expr e2)
        (erase۰expr e3)
  | Xchg e1 e2 =>
      Xchg
        (erase۰expr e1)
        (erase۰expr e2)
  | CAS e0 e1 e2 =>
      CAS
        (erase۰expr e0)
        (erase۰expr e1)
        (erase۰expr e2)
  | FAA e1 e2 =>
      FAA
        (erase۰expr e1)
        (erase۰expr e2)
  | Fork e =>
      Fork
        (erase۰expr e)
  | LocalGet =>
      LocalGet
  | LocalSet e =>
      LocalSet
        (erase۰expr e)
  | Proph =>
      Proph
  | Resolve e0 e1 e2 =>
      ResolveErasure
        (erase۰expr e0)
        (erase۰expr e1)
        (erase۰expr e2)
  | ResolveErasure e0 e1 e2 =>
      ResolveErasure
        (erase۰expr e0)
        (erase۰expr e1)
        (erase۰expr e2)
  end
with erase۰val v :=
  match v with
  | ValLit _ =>
      v
  | ValRecs i recs =>
      ValRecs
        i
        ((λ rec, (rec.1, erase۰expr rec.2)) <$> recs)
  | ValBlock bid tag vs =>
      ValBlock
        bid
        tag
        (erase۰val <$> vs)
  end.
#[global] Arguments erase۰expr !_ / : assert.
#[global] Arguments erase۰val !_ / : assert.

Definition erase۰branch br :=
  (br.1, erase۰expr br.2).

Definition erase۰recursive rec :=
  (rec.1, erase۰expr rec.2).

Definition erase۰subject subj :=
  match subj with
  | SubjectLoc _ =>
      subj
  | SubjectBlock gen vs =>
      SubjectBlock gen (erase۰val <$> vs)
  end.

Definition erase۰state σ :=
  {|state۰headers := σ.(state۰headers) ;
    state۰heap := erase۰val <$> σ.(state۰heap) ;
    state۰locals := erase۰val <$> σ.(state۰locals) ;
    state۰prophets := σ.(state۰prophets) ;
  |}.

Fixpoint erase۰ectxi k : ectx :=
  match k with
  | CtxApp1 v2 =>
      [CtxApp1 (erase۰val v2)]
  | CtxApp2 e1 =>
      [CtxApp2 (erase۰expr e1)]
  | CtxLet x e2 =>
      [CtxLet x (erase۰expr e2)]
  | CtxUnop op =>
      [CtxUnop op]
  | CtxBinop1 op v2 =>
      [CtxBinop1 op (erase۰val v2)]
  | CtxBinop2 op e1 =>
      [CtxBinop2 op (erase۰expr e1)]
  | CtxEqual1 v2 =>
      [CtxEqual1 (erase۰val v2)]
  | CtxEqual2 e1 =>
      [CtxEqual2 (erase۰expr e1)]
  | CtxIf e1 e2 =>
      [CtxIf (erase۰expr e1) (erase۰expr e2)]
  | CtxFor1 e2 e3 =>
      [CtxFor1 (erase۰expr e2) (erase۰expr e3)]
  | CtxFor2 v1 e3 =>
      [CtxFor2 (erase۰val v1) (erase۰expr e3)]
  | CtxAlloc1 v2 =>
      [CtxAlloc1 (erase۰val v2)]
  | CtxAlloc2 e1 =>
      [CtxAlloc2 (erase۰expr e1)]
  | CtxBlock mut tag es vs =>
      [CtxBlock mut tag (erase۰expr <$> es) (erase۰val <$> vs)]
  | CtxMatch x e1 brs =>
      [CtxMatch x (erase۰expr e1) ((λ br, (br.1, erase۰expr br.2)) <$> brs)]
  | CtxGetTag =>
      [CtxGetTag]
  | CtxGetSize =>
      [CtxGetSize]
  | CtxLoad1 v2 =>
      [CtxLoad1 (erase۰val v2)]
  | CtxLoad2 e1 =>
      [CtxLoad2 (erase۰expr e1)]
  | CtxStore1 v2 v3 =>
      [CtxStore1 (erase۰val v2) (erase۰val v3)]
  | CtxStore2 e1 v3 =>
      [CtxStore2 (erase۰expr e1) (erase۰val v3)]
  | CtxStore3 e1 e2 =>
      [CtxStore3 (erase۰expr e1) (erase۰expr e2)]
  | CtxXchg1 v2 =>
      [CtxXchg1 (erase۰val v2)]
  | CtxXchg2 e1 =>
      [CtxXchg2 (erase۰expr e1)]
  | CtxCAS0 v1 v2 =>
      [CtxCAS0 (erase۰val v1) (erase۰val v2)]
  | CtxCAS1 e0 v2 =>
      [CtxCAS1 (erase۰expr e0) (erase۰val v2)]
  | CtxCAS2 e0 e1 =>
      [CtxCAS2 (erase۰expr e0) (erase۰expr e1)]
  | CtxFAA1 v2 =>
      [CtxFAA1 (erase۰val v2)]
  | CtxFAA2 e1 =>
      [CtxFAA2 (erase۰expr e1)]
  | CtxLocalSet =>
      [CtxLocalSet]
  | CtxResolve0 k v1 v2 =>
      erase۰ectxi k ++
      [CtxResolveErasure0 (erase۰val v1) (erase۰val v2)]
  | CtxResolve1 e0 v2 =>
      [CtxResolveErasure1 (erase۰expr e0) (erase۰val v2)]
  | CtxResolve2 e0 e1 =>
      [CtxResolveErasure2 (erase۰expr e0) (erase۰expr e1)]
  | CtxResolveErasure0 v1 v2 =>
      [CtxResolveErasure0 (erase۰val v1) (erase۰val v2)]
  | CtxResolveErasure1 e0 v2 =>
      [CtxResolveErasure1 (erase۰expr e0) (erase۰val v2)]
  | CtxResolveErasure2 e0 e1 =>
      [CtxResolveErasure2 (erase۰expr e0) (erase۰expr e1)]
  end.
#[global] Arguments erase۰ectxi !_ / : assert.

Definition erase۰ectx K : ectx :=
  K ≫= erase۰ectxi.

Lemma erase۰valｰimmediate v :
  val۰immediate v →
  erase۰val v = v.
Proof.
  destruct v as [| | tag gen []] => //.
Qed.

Lemma erase۰exprｰvalｰinv e 𝑣 :
  erase۰expr e = Val 𝑣 →
    ∃ v,
    e = Val v ∧
    𝑣 = erase۰val v.
Proof.
  destruct e; naive.
Qed.
Lemma erase۰exprsｰvals {es 𝑣s} vs :
  es = of_vals vs →
  𝑣s = erase۰val <$> vs →
  erase۰expr <$> es = of_vals 𝑣s.
Proof.
  intros -> ->.
  induction vs as [| v vs IH].
  - done.
  - simpl. f_equal => //.
Qed.
Lemma erase۰exprsｰvalsｰinv es 𝑣s :
  erase۰expr <$> es = of_vals 𝑣s →
    ∃ vs,
    es = of_vals vs ∧
    𝑣s = erase۰val <$> vs.
Proof.
  move: 𝑣s. induction es as [| e es IH] => 𝑣s H.
  all: destruct 𝑣s as [| 𝑣 𝑣s] => //.
  - eauto.
  - injection H as [= (v & -> & ->)%erase۰exprｰvalｰinv (vs & -> & ->)%IH].
    exists (v :: vs) => //.
Qed.

Lemma erase۰ectxｰapp K1 K2 :
  erase۰ectx (K1 ++ K2) = erase۰ectx K1 ++ erase۰ectx K2.
Proof.
  rewrite /erase۰ectx bind_app //.
Qed.

Lemma eraseｰfilli k e :
  erase۰expr (filli k e) = fill (erase۰ectxi k) (erase۰expr e).
Proof.
  induction k.
  all: rewrite //=.
  - rewrite fmap_app fmap_cons /of_vals -!list_fmap_compose //.
  - rewrite fillｰapp IHk //.
Qed.
Lemma eraseｰfill K e :
  erase۰expr (fill K e) = fill (erase۰ectx K) (erase۰expr e).
Proof.
  move: e. induction K as [| k K IH] using rev_ind => e. 1: done.
  rewrite erase۰ectxｰapp !fillｰapp /= eraseｰfilli IH //.
Qed.

Lemma eraseｰsubst x v e :
  erase۰expr (subst x v e) = subst x (erase۰val v) (erase۰expr e).
Proof.
  move: e. fix IH 1. destruct e.
  all: simpl.
  all: repeat destruct (_ ≟ _).
  all: rewrite ?IH; auto.
  all:
    try select (list expr) ltac:(fun es =>
      induction es; first done;
      naive congruence
    ).
  all:
    try select (list branch) ltac:(fun brs =>
      f_equal;
      induction brs; first done;
      simpl;
      repeat destruct (existsb _ _);
      repeat destruct (_ ≟ _);
      rewrite ?IH; f_equal => //
    ).
Qed.
Lemma eraseｰsubst' x v e :
  erase۰expr (subst' x v e) = subst' x (erase۰val v) (erase۰expr e).
Proof.
  destruct x; eauto using eraseｰsubst.
Qed.
Lemma eraseｰsubst_list xs vs e :
  erase۰expr (subst_list xs vs e) = subst_list xs (erase۰val <$> vs) (erase۰expr e).
Proof.
  all: move: vs; induction xs as [| x xs IH] => vs.
  all: destruct vs as [| v vs].
  all: try done.
  rewrite eraseｰsubst' IH //.
Qed.

Lemma eraseｰeval_unop op v lit :
  eval_unop op v = Some lit →
  eval_unop op (erase۰val v) = Some lit.
Proof.
  all: destruct op.
  all: destruct v as [[] | | gen tag [| v vs]].
  all: naive.
Qed.
Lemma eraseｰeval_unopｰinv op v 𝑙𝑖𝑡 :
  eval_unop op (erase۰val v) = Some 𝑙𝑖𝑡 →
  eval_unop op v = Some 𝑙𝑖𝑡.
Proof.
  all: destruct op.
  all: destruct v as [[] | | gen tag [| v vs]].
  all: naive.
Qed.

Lemma eraseｰeval_binop op v1 v2 lit :
  eval_binop op v1 v2 = Some lit →
  eval_binop op (erase۰val v1) (erase۰val v2) = Some lit.
Proof.
  all: destruct op.
  all: destruct v1 as [[] | |].
  all: try done.
  all: destruct v2 as [[] | |].
  all: naive.
Qed.
Lemma eraseｰeval_binopｰinv op v1 v2 𝑙𝑖𝑡 :
  eval_binop op (erase۰val v1) (erase۰val v2) = Some 𝑙𝑖𝑡 →
  eval_binop op v1 v2 = Some 𝑙𝑖𝑡.
Proof.
  all: destruct op.
  all: destruct v1 as [[] | |].
  all: try done.
  all: destruct v2 as [[] | |].
  all: naive.
Qed.

Lemma eraseｰeval_app recs x v e :
  erase۰expr (eval_app recs x v e) = eval_app (erase۰recursive <$> recs) x (erase۰val v) (erase۰expr e).
Proof.
  enough (
    ∀ recs' i,
    erase۰expr $ eval_app' foldri' recs x v e recs' i = eval_app' foldri' (erase۰recursive <$> recs) x (erase۰val v) (erase۰expr e) (erase۰recursive <$> recs') i
  ) by eauto.
  induction recs' as [| rec recs' IH] => i.
  - apply eraseｰsubst'.
  - rewrite eraseｰsubst' IH //.
Qed.

Lemma eraseｰeval_match tag sz subj x_fb e_fb brs e 𝑠𝑢𝑏𝑗 :
  𝑠𝑢𝑏𝑗 = erase۰subject subj →
  eval_match tag sz subj x_fb e_fb brs = Some e →
  eval_match tag sz 𝑠𝑢𝑏𝑗 x_fb (erase۰expr e_fb) (erase۰branch <$> brs) = Some $ erase۰expr e.
Proof.
  intros -> H.
  all: induction brs as [| br brs].
  all: destruct subj.
  all: simp.
  all: rewrite ?erase_subst' //.
  all: repeat destruct (_ ≟ _); auto.
  all: simp.
  all: repeat case_match => //.
  all: simp.
  all: rewrite ?eraseｰsubst_list ?eraseｰsubst' //.
Qed.
Lemma eraseｰeval_matchｰinv tag sz subj x_fb e_fb brs 𝑒 :
  eval_match tag sz (erase۰subject subj) x_fb (erase۰expr e_fb) (erase۰branch <$> brs) = Some 𝑒 →
    ∃ e,
    eval_match tag sz subj x_fb e_fb brs = Some e ∧
    𝑒 = erase۰expr e.
Proof.
  intros H.
  all: induction brs as [| br brs].
  all: destruct subj.
  all: simp.
  all: repeat destruct (_ ≟ _); auto.
  all: simp.
  all: repeat case_match => //.
  all: simp.
  all: rewrite -?(eraseｰsubst' _ (ValLoc _)).
  all: rewrite -?(eraseｰsubst' _ (ValBlock _ _ _)).
  all: rewrite -?eraseｰsubst_list.
  all: eauto.
Qed.

Lemma eraseｰstate۰update_heapｰinsert l v σ :
  erase۰state (state۰update_heap <[l := v]> σ) = state۰update_heap <[l := erase۰val v]> (erase۰state σ).
Proof.
  rewrite /erase۰state fmap_insert //.
Qed.
Lemma eraseｰstate۰update_localsｰsnoc v σ :
  erase۰state (state۰update_locals (.++ [v]) σ) = state۰update_locals (.++ [erase۰val v]) (erase۰state σ).
Proof.
  rewrite /erase۰state fmap_snoc //.
Qed.
Lemma eraseｰstate۰update_localsｰinsert tid v σ :
  erase۰state (state۰update_locals (insert tid v) σ) = state۰update_locals (insert tid $ erase۰val v) (erase۰state σ).
Proof.
  rewrite /erase۰state list_fmap_insert //.
Qed.
Lemma eraseｰchunk l vs :
  erase۰val <$> chunk l vs = chunk l (erase۰val <$> vs).
Proof.
  move: l. induction vs as [| v vs IH] => l //.
  rewrite fmap_insert IH //.
Qed.
Lemma eraseｰstate۰alloc l hdr vs σ :
  erase۰state (state۰alloc l hdr vs σ) = state۰alloc l hdr (erase۰val <$> vs) (erase۰state σ).
Proof.
  rewrite /erase۰state map_fmap_union eraseｰchunk //.
Qed.
Lemma eraseｰstate۰alloc_condition l sz σ :
  state۰alloc_condition l sz (erase۰state σ) ↔ state۰alloc_condition l sz σ.
Proof.
  rewrite /state۰alloc_condition /=.
  setoid_rewrite lookupｰfmapｰNone => //.
Qed.

#[local] Lemma eraseｰexprｰvalｰinj :
  ( ∀ e1 e2,
    erase۰expr e1 = erase۰expr e2 →
    expr۰wf e1 →
    expr۰wf e2 →
    e1 = e2
  ) ∧ (
    ∀ v1 v2,
    erase۰val v1 = erase۰val v2 →
    val۰wf v1 →
    val۰wf v2 →
    v1 = v2
  ).
Proof.
  apply exprｰvalｰmutind.
  1-11,14-16,17-24,26:
    intros;
    select expr (fun e2 => destruct e2);
    naive.
  - intros mut tag es1 IH [] [= <- <-] Hwf1 Hwf2.
    f_equal.
    simp_Forall+/= in *; naive.
  - intros e10 IH0 bdr e11 IH1 brs1 IHbrs [] [=] Hwf1 Hwf2.
    f_equal. 1-3: naive.
    simp_Forall+/= in *. split. 1: naive.
    naive eauto using injective_projections.
  - intros e10 IH0 e11 IH1 e12 IH2 [] [=] Hwf1 Hwf2.
    + naive.
    + done.
  - intros lit [] [= <-] => //.
  - intros i recs1 IH [] [= <- H] Hwf1 Hwf2.
    f_equal.
    simp_Forall+/= in *. split. 1: naive.
    naive eauto using injective_projections.
  - intros gen tag vs1 IH [] [= <- <-] Hwf1 Hwf2.
    f_equal.
    simp_Forall+/= in *; naive.
Qed.
Lemma erase۰valｰinj v1 v2 :
  erase۰val v1 = erase۰val v2 →
  val۰wf v1 →
  val۰wf v2 →
  v1 = v2.
Proof.
  apply eraseｰexprｰvalｰinj.
Qed.
Lemma erase۰valｰinjｰnonsimilar v1 v2 :
  erase۰val v1 ≉ erase۰val v2 →
  v1 ≉ v2.
Proof.
  all: destruct v1 as [[] | | [[] |] tag1 [| v1 vs1]].
  all: try done.
  all: destruct v2 as [[] | | [[] |] tag2 [| v2 vs2]].
  all: cbn; naive.
Qed.
Lemma erase۰valｰinjｰsimilar v1 v2 :
  erase۰val v1 ≈ erase۰val v2 →
  val۰wf v1 →
  val۰wf v2 →
  v1 ≈ v2.
Proof.
  all: move: v2; induction v1 as [[] | | [[] |] tag1 [| v1 vs1'] IH] => v2.
  all: destruct v2 as [[] | | [[] |] tag2 [| v2 vs2']].
  all: cbn; try naive.
  - rewrite -!fmap_cons -!Forall'ｰcons.
    set vs1 := v1 :: vs1' in IH |- *. clearbody vs1.
    set vs2 := v2 :: vs2'. clearbody vs2.
    intros ([= <-] & <- & [=]) Hwf1 Hwf2.
    simp_Forall+ in *. split_and! => //.
    + naive.
    + intros.
      apply erase۰valｰinj; naive.
  - rewrite -!fmap_cons -!Forall'ｰcons.
    set vs1 := v1 :: vs1' in IH |- *. clearbody vs1.
    set vs2 := v2 :: vs2'. clearbody vs2.
    intros (_ & <- & ?) Hwf1 Hwf2.
    simp_Forall+ in *. split_and! => //.
    + naive.
    + intros.
      apply erase۰valｰinj; naive.
  - intros (<- & ?) Hwf1 Hwf2.
    simp_Forall+ in *. naive.
Qed.

Lemma eraseｰbase_reducibleｰnoｰresolve tid e σ :
  base_reducible tid e σ →
  ¬ expr۰is_resolve e →
  base_reducible tid (erase۰expr e) (erase۰state σ).
Proof.
  intros (κ & e2 & σ2 & es & Hstep) He.
  inv Hstep => //.
  all:
    try solve [
      do 4 eexists => //=;
      eauto
        using
          eraseｰeval_unop,
          eraseｰeval_binop,
          erase۰exprsｰvals
        with
          zoo
    ].
  - do 5 econstructor.
    eapply list_lookup_fmap_Some. naive.
  - apply base_reducibleｰequal.
  - apply base_reducibleｰequal.
  - do 5 econstructor.
    all: rewrite 1?length_fmap.
    + done.
    + eapply erase۰exprsｰvals => //.
    + rewrite eraseｰstate۰alloc_condition //.
  - do 5 econstructor => //.
    eapply eraseｰeval_match => // //.
  - do 5 econstructor.
    rewrite length_fmap.
    eapply eraseｰeval_match => // //.
  - do 5 econstructor.
    simp_length.
  - do 5 econstructor.
    simp_length.
  - do 5 econstructor.
    rewrite lookup_fmap H //.
  - do 5 econstructor.
    rewrite list_lookup_fmap H //.
  - do 5 econstructor.
    rewrite lookup_fmap fmap_is_Some //.
  - do 5 econstructor.
    rewrite lookup_fmap H //.
  - eapply base_reducibleｰcas.
    rewrite lookup_fmap H //.
  - eapply base_reducibleｰcas.
    rewrite lookup_fmap H //.
  - do 5 econstructor.
    rewrite lookup_fmap H //.
  - do 5 econstructor.
    rewrite list_lookup_fmap H //.
  - do 5 econstructor.
    rewrite list_lookup_fmap fmap_is_Some //.
Qed.
Lemma eraseｰbase_reducibleｰresolve tid e σ :
  base_reducible tid e σ →
  expr۰is_resolve e →
  reducible tid (erase۰expr e) (erase۰state σ).
Proof.
  intros (κ & e' & σ2 & es & Hstep) He.
  induction Hstep => //=.
  apply (fillｰreducible _ [CtxResolveErasure0 _ _]).
  destruct_decide (expr۰is_resolve e).
  - naive.
  - apply base_reducibleｰreducible, eraseｰbase_reducibleｰnoｰresolve. 2: done.
    eauto with zoo.
Qed.
Lemma eraseｰbase_reducible tid e σ :
  base_reducible tid e σ →
  reducible tid (erase۰expr e) (erase۰state σ).
Proof.
  intros Hreducible.
  destruct_decide (expr۰is_resolve e) as (e0 & e1 & e2 & ->)%expr۰is_resolveｰalt | He.
  - apply eraseｰbase_reducibleｰresolve => //.
  - apply base_reducibleｰreducible, eraseｰbase_reducibleｰnoｰresolve => //.
Qed.
Lemma eraseｰreducible tid e σ :
  reducible tid e σ →
  reducible tid (erase۰expr e) (erase۰state σ).
Proof.
  intros (κ & e2 & σ2 & es & [K e1ᵣ e2ᵣ -> -> Hstep]).
  rewrite eraseｰfill.
  apply fillｰreducible, eraseｰbase_reducible.
  eauto with zoo.
Qed.
Lemma eraseｰnot_stuck tid e σ 𝑒 𝜎 :
  not_stuck tid e σ →
  𝑒 = erase۰expr e →
  𝜎 = erase۰state σ →
  not_stuck tid 𝑒 𝜎.
Proof.
  intros [(v & <-%of_valｰto_val) | Hstep] -> ->.
  - apply valｰnot_stuck => //.
  - apply reducibleｰnot_stuck, eraseｰreducible => //.
Qed.

#[local] Ltac inv_erase :=
  repeat (
    match goal with
    | H: context [(fmap (M := gmap _) _ _) !! _ = None] |- _ =>
        setoid_rewrite lookupｰfmapｰNone in H
    | H: context [(fmap (M := list) _ _) !! _ = Some _] |- _ =>
        setoid_rewrite list_lookup_fmap_Some in H
    | H: context [(fmap (M := gmap _) _ _) !! _ = Some _] |- _ =>
        setoid_rewrite lookup_fmap_Some in H
    | H: context [is_Some ((fmap (M := list) _ _) !! _)] |- _ =>
        rewrite /is_Some in H;
        setoid_rewrite list_lookup_fmap_Some in H
    | H: context [is_Some ((fmap (M := gmap _) _ _) !! _)] |- _ =>
        rewrite /is_Some in H;
        setoid_rewrite lookup_fmap_Some in H
    | _: _ = erase۰expr ?e |- _ =>
        destruct e => //
    | _: _ = erase۰val ?v |- _ =>
        destruct v => //
    | _: erase۰val ?v = ValLit (LitInt _) |- _ =>
        destruct v as [[] | |] => //
    | H: of_vals _ = erase۰expr <$> _ |- _ =>
        apply symmetry, erase۰exprsｰvalsｰinv in H
    | _: _ :: _ = erase۰val <$> ?vs |- _ =>
        destruct vs; first done
    | _: [] = erase۰val <$> ?vs |- _ =>
        destruct vs; last done
    | H: eval_unop _ (erase۰val _) = _ |- _ =>
        apply eraseｰeval_unopｰinv in H
    | H: eval_binop _ (erase۰val _) (erase۰val _) = _ |- _ =>
        apply eraseｰeval_binopｰinv in H
    | H: eval_match _ _ (SubjectLoc _) _ (erase۰expr _) _ = Some _ |- _ =>
        apply (eraseｰeval_matchｰinv _ _ (SubjectLoc _)) in H
    | H: eval_match _ _ (SubjectBlock _ _) _ (erase۰expr _) _ = Some _ |- _ =>
        apply (eraseｰeval_matchｰinv _ _ (SubjectBlock _ _)) in H
    end;
    simp
  ).
Lemma eraseｰbase_stepｰinv tid e σ 𝑒 𝜎 𝜅 𝑒' 𝜎' 𝑒s :
  base_step tid 𝑒 𝜎 𝜅 𝑒' 𝜎' 𝑒s →
  𝑒 = erase۰expr e →
  𝜎 = erase۰state σ →
  ¬ expr۰is_resolve e →
  expr۰wf e →
  state۰wf σ →
    ∃ κ e' σ' es,
    base_step tid e σ κ e' σ' es ∧
    rtc pure_step 𝑒' (erase۰expr e') ∧
    𝜎' = erase۰state σ' ∧
    𝑒s = erase۰expr <$> es.
Proof.
  intros Hstep -> -> He Hwf_e Hwf_σ.
  inv Hstep.
  all: inv_erase.
  all:
    try solve [
      simp_length in *;
      repeat eexists; eauto with zoo;
      try case_match;
      rewrite
        ?eraseｰeval_app
        ?eraseｰsubst'
        ?eraseｰstate۰update_heapｰinsert
        //
    ].
  - repeat eexists.
    + apply base_stepｰequalｰfail.
      apply erase۰valｰinjｰnonsimilar => //.
    + done.
    + done.
  - repeat eexists.
    + apply base_stepｰequalｰsuccess.
      apply erase۰valｰinjｰsimilar => //.
    + done.
    + done.
  - repeat eexists.
    + constructor => //.
      rewrite -eraseｰstate۰alloc_condition //.
    + done.
    + rewrite eraseｰstate۰alloc fmap_replicate //.
    + done.
  - repeat eexists.
    + simp_length in *.
      constructor; simp_length.
      rewrite -eraseｰstate۰alloc_condition //.
    + done.
    + simp_length.
      rewrite eraseｰstate۰alloc //.
    + done.
  - repeat eexists.
    + eapply (base_stepｰblockｰimmutableｰgenerativeｰstrong _ _ _ _ _ bid) => //.
    + done.
    + done.
  - repeat eexists.
    + eapply base_stepｰcasｰfail => //.
      apply erase۰valｰinjｰnonsimilar => //.
    + done.
    + done.
  - repeat eexists.
    + eapply base_stepｰcasｰsuccess => //.
      apply erase۰valｰinjｰsimilar => //.
      eapply Hwf_σ => //.
    + done.
    + rewrite eraseｰstate۰update_heapｰinsert //.
    + done.
  - repeat eexists.
    + constructor => //.
    + done.
    + rewrite eraseｰstate۰update_localsｰsnoc //.
      rewrite erase۰valｰimmediate //.
    + done.
  - repeat eexists; eauto with zoo.
    + done.
    + rewrite eraseｰstate۰update_localsｰinsert //.
  - eexists [], (Val $ ValProph pid), _, []. split_and! => //.
    + constructor => //.
    + done.
Qed.

Lemma eraseｰfillｰinvｰnoｰresolve tid K e σ 𝐾 𝑒 :
  fill (erase۰ectx K) (erase۰expr e) = fill 𝐾 𝑒 →
  base_reducible tid e σ →
  base_reducible tid 𝑒 (erase۰state σ) →
  ¬ expr۰is_resolve e →
    𝐾 = erase۰ectx K ∧
    𝑒 = erase۰expr e.
Proof.
  intros Heq Hreducible H𝑟𝑒𝑑𝑢𝑐𝑖𝑏𝑙𝑒 He.
  eapply baseｰredexｰunique in Heq as (<- & <-) => //.
  apply eraseｰbase_reducibleｰnoｰresolve => //.
Qed.
#[local] Lemma eraseｰfillｰinvｰresolveｰauxｰ1 tid e pid v σ κ e' σ' es 𝐾 𝑒ᵣ 𝜎 𝜅 𝑒ᵣ' 𝜎' 𝑒s:
  ResolveErasure (erase۰expr e) (Val $ ValProph pid) (Val $ erase۰val v) = fill 𝐾 𝑒ᵣ →
  base_step tid e σ κ e' σ' es →
  base_step tid 𝑒ᵣ 𝜎 𝜅 𝑒ᵣ' 𝜎' 𝑒s →
    ∃ 𝐾',
    𝐾 = 𝐾' ++ [CtxResolveErasure0 (ValProph pid) (erase۰val v)].
Proof.
  intros Heq Hstep H𝑠𝑡𝑒𝑝.

  destruct 𝐾 as [| 𝑘 𝐾 _] using rev_ind.
  { simpl in Heq. inv H𝑠𝑡𝑒𝑝.
    destruct (erase۰exprｰvalｰinv e v0) as (? & -> & _). 1: done.
    apply base_stepｰnotｰval in Hstep => //.
  }
  rewrite fillｰapp in Heq.

  destruct 𝑘 => //; first last.
  { injection Heq as _ _ Heq.
    apply base_stepｰnotｰval, (fillｰnotｰval 𝐾) in H𝑠𝑡𝑒𝑝.
    rewrite -Heq // in H𝑠𝑡𝑒𝑝.
  } {
    injection Heq as _ Heq _.
    apply base_stepｰnotｰval, (fillｰnotｰval 𝐾) in H𝑠𝑡𝑒𝑝.
    rewrite -Heq // in H𝑠𝑡𝑒𝑝.
  }
  injection Heq as Heq <- <-.

  eauto.
Qed.
#[local] Lemma eraseｰfillｰinvｰresolveｰauxｰ2 e v1 pid v2 :
  rtc pure_step e (Val v1) →
  rtc pure_step
    (fill [CtxResolveErasure0 (ValProph pid) v2] e)
    (Val v1).
Proof.
  intros He.
  trans (fill [CtxResolveErasure0 (ValProph pid) v2] (Val v1)).
  { apply pure_stepsｰfill => //. }
  apply (rtc_nsteps_2 1), pure_exec => //.
Qed.
Lemma eraseｰfillｰinvｰresolve tid e σ 𝐾 𝑒ᵣ 𝜎 𝜅 𝑒ᵣ' 𝜎' 𝑒s :
  erase۰expr e = fill 𝐾 𝑒ᵣ →
  base_reducible tid e σ →
  base_step tid 𝑒ᵣ 𝜎 𝜅 𝑒ᵣ' 𝜎' 𝑒s →
  expr۰is_resolve e →
  expr۰wf e →
  state۰wf σ →
  𝜎 = erase۰state σ →
    ∃ κ v σ' es,
    base_step tid e σ κ (Val v) σ' es ∧
    rtc pure_step (fill 𝐾 𝑒ᵣ') (Val $ erase۰val v) ∧
    𝜎' = erase۰state σ' ∧
    𝑒s = erase۰expr <$> es.
Proof.
  intros Heq Hreducible H𝑠𝑡𝑒𝑝 He Hwf_e Hwf_σ ->.
  move: 𝐾 Heq. induction e => // 𝐾 Heq {IHe2 IHe3}.
  destruct Hreducible as (κ & eᵣ' & σ' & es & Hstep).
  inv Hstep => {He}.
  destruct (eraseｰfillｰinvｰresolveｰauxｰ1 tid e1 pid v σ κ0 (Val w) σ' es 𝐾 𝑒ᵣ (erase۰state σ) 𝜅 𝑒ᵣ' 𝜎' 𝑒s) as (𝐾' & ->) => //.
  rewrite fillｰapp in Heq.
  injection Heq as Heq.
  destruct_decide (expr۰is_resolve e1).
  - edestruct IHe1 as (κ & v1 & σ'' & es' & Hstep & Hpures & H𝜎' & H𝑒s) => //.
    { eauto with zoo. }
    { naive. }
    exists (κ ++ [(pid, (v1, v))]), v1, σ'', es'. split_and! => //.
    + constructor => //.
    + rewrite fillｰapp.
      apply eraseｰfillｰinvｰresolveｰauxｰ2 => //.
  - destruct (baseｰredexｰunique tid [] (erase۰expr e1) (erase۰state σ) 𝐾' 𝑒ᵣ (erase۰state σ)) as (<- & <-).
    { done. }
    { eauto using eraseｰbase_reducibleｰnoｰresolve with zoo. }
    { eauto with zoo. }
    simpl.
    eapply eraseｰbase_stepｰinv in H𝑠𝑡𝑒𝑝 as (κ & e' & σ'_ & es_ & Hstep & Hpures & -> & ->) => //.
    destruct (base_stepｰtoｰval tid e1 σ κ0 (Val w) σ' es κ e' σ'_ es_) as (w_ & <-%of_valｰto_val) => //.
    exists (κ ++ [(pid, (w_, v))]), w_, σ'_, es_. split_and! => //.
    + constructor => //.
    + apply eraseｰfillｰinvｰresolveｰauxｰ2 => //.
    + naive.
Qed.

Lemma eraseｰprim_stepｰinv tid e σ 𝑒 𝜎 𝜅 𝑒' 𝜎' 𝑒s :
  prim_step tid 𝑒 𝜎 𝜅 𝑒' 𝜎' 𝑒s →
  𝑒 = erase۰expr e →
  𝜎 = erase۰state σ →
  expr۰wf e →
  state۰wf σ →
  not_stuck tid e σ →
    ∃ κ e' σ' es,
    prim_step tid e σ κ e' σ' es ∧
    rtc pure_step 𝑒' (erase۰expr e') ∧
    𝜎' = erase۰state σ' ∧
    𝑒s = erase۰expr <$> es.
Proof.
  intros [𝐾 𝑒ᵣ 𝑒ᵣ' Heq -> H𝑠𝑡𝑒𝑝] -> -> Hwf_e Hwf_σ [(v & <-%of_valｰto_val) | (K & eᵣ & -> & Hreducible)%reducibleｰfillｰbase_reducible].
  - destruct (to_valｰfillｰSome 𝐾 𝑒ᵣ (erase۰val v)) as (-> & ->).
    { rewrite -Heq //. }
    apply base_stepｰnotｰval in H𝑠𝑡𝑒𝑝 => //.
  - rewrite eraseｰfill in Heq.
    apply fillｰwf in Hwf_e as (Hwf_K & Hwf_eᵣ).
    destruct_decide (expr۰is_resolve eᵣ) as Heᵣ.
    + destruct (stepｰbyｰval tid (erase۰ectx K) 𝐾 (erase۰expr eᵣ) 𝑒ᵣ (erase۰state σ) 𝜅 𝑒ᵣ' 𝜎' 𝑒s) as (𝐾' & ->) => //.
      { apply eq_None_ne_Some. intros 𝑣 (v & -> & ->)%of_valｰto_val%symmetry%erase۰exprｰvalｰinv => //.
      }
      rewrite fillｰapp in Heq. apply (inj _) in Heq.
      destruct (eraseｰfillｰinvｰresolve tid eᵣ σ 𝐾' 𝑒ᵣ (erase۰state σ) 𝜅 𝑒ᵣ' 𝜎' 𝑒s) as (κ & v & σ' & es & Hstep & Hpures & -> & ->) => //.
      exists κ, (fill K (Val v)), σ', es. split_and!.
      * econstructor => //.
      * rewrite fillｰapp eraseｰfill.
        apply pure_stepsｰfill => //.
      * done.
      * done.
    + eapply eraseｰfillｰinvｰnoｰresolve in Heq as (-> & ->) => //; first last.
      { eauto with zoo. }
      eapply eraseｰbase_stepｰinv in H𝑠𝑡𝑒𝑝 as (κ & eᵣ' & σ' & es & Hstep & Hpures & -> & ->) => //.
      exists κ, (fill K eᵣ'), σ', es. split_and! => //.
      * apply base_stepｰfillｰprim_step => //.
      * rewrite eraseｰfill.
        apply pure_stepsｰfill => //.
Qed.

Record erase۰relation ρ 𝜌 :=
  { erase۰relationｰwf :
      config۰wf ρ
  ; erase۰relationｰsafe :
      safe ρ
  ; erase۰relationｰexprs :
      Forall2 (λ e 𝑒, rtc pure_step 𝑒 (erase۰expr e)) ρ.1 𝜌.1
  ; erase۰relationｰstate :
      𝜌.2 = erase۰state ρ.2
  }.

Lemma erase۰relationｰexprsｰwf ρ 𝜌 es :
  erase۰relation ρ 𝜌 →
  es = ρ.1 →
  Forall expr۰wf es.
Proof.
  intros Hrelation%erase۰relationｰwf%config۰wfｰexprs -> => //.
Qed.
Lemma erase۰relationｰexprｰwf ρ 𝜌 tid e :
  erase۰relation ρ 𝜌 →
  ρ.1 !! tid = Some e →
  expr۰wf e.
Proof.
  intros Hrelation%erase۰relationｰwf%config۰wfｰexprs Hlookup.
  eapply Forall_lookup => //.
Qed.
Lemma erase۰relationｰstateｰwf ρ 𝜌 σ :
  erase۰relation ρ 𝜌 →
  σ = ρ.2 →
  state۰wf σ.
Proof.
  intros Hrelation%erase۰relationｰwf%config۰wfｰstate -> => //.
Qed.
Lemma erase۰relationｰexprｰnot_stuck ρ 𝜌 tid e σ :
  erase۰relation ρ 𝜌 →
  ρ.1 !! tid = Some e →
  σ = ρ.2 →
  not_stuck tid e σ.
Proof.
  intros Hrelation%erase۰relationｰsafe Hlookup ->.
  apply safeｰnot_stuck => //.
Qed.
Lemma erase۰relationｰstate' ρ 𝜌 σ 𝜎 :
  erase۰relation ρ 𝜌 →
  σ = ρ.2 →
  𝜎 = 𝜌.2 →
  𝜎 = erase۰state σ.
Proof.
  intros Hrelation%erase۰relationｰstate -> -> => //.
Qed.
#[local] Hint Resolve
  erase۰relationｰwf
  erase۰relationｰsafe
  erase۰relationｰexprsｰwf
  erase۰relationｰexprｰwf
  erase۰relationｰstateｰwf
  erase۰relationｰexprｰnot_stuck
  erase۰relationｰstate'
: core.

Lemma erase۰relationｰstep ρ1 𝜌1 𝜌2 :
  erase۰relation ρ1 𝜌1 →
  silent_step 𝜌1 𝜌2 →
    ∃ ρ2,
    erase۰relation ρ2 𝜌2 ∧
    rtc silent_step ρ1 ρ2.
Proof.
  destruct ρ1 as (es1, σ1), 𝜌1 as (𝑒s1, 𝜎1).
  intros Hrelation (𝜅 & (tid & 𝑒1 & 𝑒2 & 𝜎2 & 𝑒s & H𝑠𝑡𝑒𝑝 & H𝑒s1_lookup & ->)).
  simp.
  opose proof* Forall2_lookup_r as (e1 & Hes1_lookup & H𝑠𝑡𝑒𝑝s).
  { apply Hrelation. }
  { done. }
  apply rtc_inv in H𝑠𝑡𝑒𝑝s as [-> | (𝑒1' & H𝑠𝑡𝑒𝑝_ & H𝑠𝑡𝑒𝑝s)].
  - eapply eraseｰprim_stepｰinv in H𝑠𝑡𝑒𝑝 as (κ & e2 & σ2 & es & Hstep & H𝑠𝑡𝑒𝑝s & -> & ->). 2-6: eauto.
    pose proof Hstep as (Hwf_e2 & Hwf_σ2 & Hwf_es)%prim_stepｰwf. 2,3: eauto.
    exists (<[tid := e2]> es1 ++ es, σ2). split. 1: split. 1: split.
    + apply Forall_app. split => //.
      eauto using Forall_insert.
    + done.
    + eapply safeｰstep.
      { eauto. }
      { repeat eexists => //. }
    + apply Forall2_app.
      * apply Forall2_insert. 2: done.
        apply Hrelation.
      * apply Forall2_fmap_r, Forall_Forall2_diag, Forall_true.
        eauto using rtc.
    + done.
    + apply rtc_once.
      repeat eexists => //.
  - eapply pure_stepｰdet in H𝑠𝑡𝑒𝑝 as (-> & -> & -> & ->). 2: done.
    rewrite right_id.
    exists (es1, σ1). split => //. 1: split.
    + eauto.
    + eauto.
    + eapply Forall2ｰinsertｰr => //.
      apply Hrelation.
    + eauto.
Qed.
Lemma erase۰relationｰsteps ρ1 𝜌1 𝜌2 :
  erase۰relation ρ1 𝜌1 →
  rtc silent_step 𝜌1 𝜌2 →
    ∃ ρ2,
    erase۰relation ρ2 𝜌2 ∧
    rtc silent_step ρ1 ρ2.
Proof.
  intros Hrelation1 H𝑠𝑡𝑒𝑝s.
  move: ρ1 Hrelation1. induction H𝑠𝑡𝑒𝑝s as [| 𝜌1 𝜌2 𝜌3 H𝑠𝑡𝑒𝑝 H𝑠𝑡𝑒𝑝s IH] => ρ1 Hrelation1.
  - naive.
  - eapply erase۰relationｰstep in H𝑠𝑡𝑒𝑝 as (ρ2 & (ρ3 & Hrelation3 & Hsteps2)%IH & Hsteps1). 2: done.
    eexists. split. 1: done. etrans => //.
Qed.

Lemma eraseｰsafe e σ :
  safe ([e], σ) →
  expr۰wf e →
  state۰wf σ →
  safe ([erase۰expr e], erase۰state σ).
Proof.
  intros Hsafe Hwf_e Hwf_σ (𝑒s, 𝜎) H𝑠𝑡𝑒𝑝s.
  eapply (erase۰relationｰsteps ([e], σ)) in H𝑠𝑡𝑒𝑝s as ((es, σ') & Hrelation & Hnot_stuck%Hsafe); last first.
  { split => //.
    - split => //. simp_Forall+/=.
    - simp_Forall+/=.
  }
  rewrite Foralliｰlookup => tid 𝑒 H𝑒s_lookup.
  odestruct Forall2_lookup_r as (e' & Hes_lookup & H𝑠𝑡𝑒𝑝s).
  { apply Hrelation. }
  { done. }
  eapply Foralliｰlookup in Hnot_stuck. 2: done.
  apply rtc_inv in H𝑠𝑡𝑒𝑝s as [-> | (𝑒' & H𝑠𝑡𝑒𝑝 & _)].
  - eauto using eraseｰnot_stuck.
  - eapply pure_stepｰnot_stuck => //.
Qed.
