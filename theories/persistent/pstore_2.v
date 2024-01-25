From zebre Require Import
  prelude.
From iris.algebra Require Import gmap.
From zebre.language Require Import
  notations
  diaframe.
From zebre.persistent Require Export
  base.
From zebre Require Import
  options.

From zebre.persistent Require Import
  map_agree.

Implicit Types l r : loc.
Implicit Types v t s : val.
Implicit Types σ : gmap loc val.

#[local] Notation "'snap_store'" :=
  0
( in custom zebre_proj
).
#[local] Notation "'snap_root'" :=
  1
( in custom zebre_proj
).

#[local] Definition descr_match : val :=
  λ: "descr" "Root" "Diff",
    match: "descr" with
    | Injl <> =>
        "Root" ()
    | Injr "x" =>
        "Diff" "x".<0> "x".<1> "x".<2>
    end.
#[local] Notation "'match:' e0 'with' | 'Root' => e1 | 'Diff' x1 x2 x3 => e2 'end'" := (
  (Val descr_match) e0 (Lam BAnon e1) (Lam x1 (Lam x2 (Lam x3 e2)))
)(x1, x2, x3 at level 1,
  e0, e1, e2 at level 200,
  format "'[hv' match:  e0  with  '/' '[' |  Root  =>  '/    ' e1 ']'  '/' '[' |  Diff  x1  x2  x3  =>  '/    ' e2  ']' '/' end ']'"
) : expr_scope.
#[local] Notation "'match:' e0 'with' 'Root' => e1 | 'Diff' x1 x2 x3 => e2 'end'" := (
  (Val descr_match) e0 (Lam BAnon e1) (Lam x1 (Lam x2 (Lam x3 e2)))
)(x1, x2, x3 at level 1,
  e0, e1, e2 at level 200,
  only parsing
) : expr_scope.
#[local] Notation "'match::' e0 'with' | 'Root' => e1 | 'Diff' x1 x2 x3 => e2 'end'" := (
  (Val descr_match) e0 (Val (ValLam BAnon e1)) (Val (ValLam x1 (Lam x2 (Lam x3 e2))))
)(x1, x2, x3 at level 1,
  e0, e1, e2 at level 200,
  format "'[hv' match::  e0  with  '/' '[' |  Root  =>  '/    ' e1 ']'  '/' '[' |  Diff  x1  x2  x3  =>  '/    ' e2  ']' '/' end ']'"
) : expr_scope.
#[local] Notation "'match::' e0 'with' 'Root' => e1 | 'Diff' x1 x2 x3 => e2 'end'" := (
  (Val descr_match) e0 (Val (ValLam BAnon e1)) (Val (ValLam x1 (Lam x2 (Lam x3 e2))))
)(x1, x2, x3 at level 1,
  e0, e1, e2 at level 200,
  only parsing
) : expr_scope.

#[local] Definition ValRoot :=
  ValInjl ().
#[local] Notation "'&&Root'" :=
  ValRoot.
#[local] Instance pure_descr_match_Root e1 x1 x2 x3 e2 :
  PureExec True 11
    (match:: &&Root with Root => e1 | Diff x1 x2 x3 => e2 end)
    e1.
Proof.
  solve_pure_exec.
Qed.

#[local] Definition descr_Diff : val :=
  λ: "v1" "v2" "v3", Injr ("v1", "v2", "v3").
#[local] Definition ValDiff v1 v2 v3 :=
  ValInjr (v1, v2, v3).
#[local] Notation "'&Diff'" :=
  descr_Diff.
#[local] Notation "'&&Diff'" :=
  ValDiff.
#[local] Lemma descr_Diff_inj v1 v2 v3 w1 w2 w3 :
  &&Diff v1 v2 v3 = &&Diff w1 w2 w3 →
  v1 = w1 ∧ v2 = w2 ∧ v3 = w3.
Proof.
  naive_solver.
Qed.
#[local] Instance pure_descr_Diff v1 v2 v3 :
  PureExec True 7
    (&Diff v1 v2 v3)
    (&&Diff v1 v2 v3).
Proof.
  solve_pure_exec.
Qed.
#[local] Instance pure_descr_match_Diff v1 v2 v3 e1 x1 x2 x3 e2 :
  PureExec True 18
    (match:: &&Diff v1 v2 v3 with Root => e1 | Diff x1 x2 x3 => e2 end)
    (subst' x1 v1 (subst' x2 v2 (subst' x3 v3 e2))).
Proof.
  solve_pure_exec.
Qed.

#[global] Opaque descr_match.
#[global] Opaque ValRoot.
#[global] Opaque descr_Diff.
#[global] Opaque ValDiff.

Definition pstore_create : val :=
  λ: <>,
    ref (ref &&Root).

Definition pstore_ref : val :=
  λ: "v",
    ref "v".

Definition pstore_get : val :=
  λ: "t" "r",
    !"r".

Definition pstore_set : val :=
  λ: "t" "r" "v",
    let: "root" := ref &&Root in
    !"t" <- &Diff "r" !"r" "root" ;;
    "r" <- "v" ;;
    "t" <- "root".

Definition pstore_capture : val :=
  λ: "t",
    ("t", !"t").

#[local] Definition pstore_reroot : val :=
  rec: "pstore_reroot" "node" :=
    match: !"node" with
    | Root =>
        ()
    | Diff "r" "v" "node'" =>
        "pstore_reroot" "node'" ;;
        "node'" <- &Diff "r" !"r" "node" ;;
        "r" <- "v" ;;
        "node" <- &&Root
    end.

Definition pstore_restore : val :=
  λ: "t" "s",
    if: "t" ≠ "s".<snap_store> then (
      Fail
    ) else (
      let: "root" := "s".<snap_root> in
      match: !"root" with
      | Root =>
          ()
      | Diff <> <> <> =>
          pstore_reroot "root" ;;
          "t" <- "root"
      end
    ).

Class PstoreG Σ `{zebre_G : !ZebreG Σ} := {
  pstore_G_map_G : map_agreeG Σ loc (gmap loc val) ;
}.

Definition pstore_Σ := #[
  map_agreeΣ loc (gmap loc val)
].
#[global] Instance subG_pstore_Σ Σ `{zebre_G : !ZebreG Σ} :
  subG pstore_Σ Σ →
  PstoreG Σ.
Proof.
  solve_inG.
Qed.

Section rtc_lab.
Context {A B:Type}.
Context (R:A -> B -> A -> Prop).

Inductive rtcl : A -> list B -> A -> Prop :=
| rtcl_refl : forall a, rtcl a [] a
| rtcl_l : forall a1 b a2 bs a3,
    R a1 b a2 ->
    rtcl a2 bs a3 ->
    rtcl a1 (b::bs) a3.

Lemma rtcl_r a1 b a2 bs a3 :
  rtcl a1 bs a2 ->
  R a2 b a3 ->
  rtcl a1 (bs++[b]) a3.
Proof.
  induction 1.
  { eauto using rtcl_refl,rtcl_l. }
  { intros. rewrite -app_comm_cons. eauto using rtcl_l. }
Qed.

End rtc_lab.

Section Graph.
Definition graph (A B:Type) `{Countable A} `{Countable B} := gset (A*B*A).

Context `{Countable A} `{Countable B}.
Definition vertices (g:graph A B) : gset A :=
  set_fold (fun '(x,_,y) acc => {[x;y]} ∪ acc) ∅ g.

Lemma vertices_empty :
  vertices ∅ = ∅.
Proof. compute_done. Qed.

Definition vin {A B C:Type} (x:(A*B*C)) := match x with (a,_,_) => a end.
Definition vout {A B C:Type} (x:(A*B*C)) := match x with (_,_,c) => c end.

Lemma elem_of_vertices x (g:graph A B) :
  x ∈ vertices g <-> exists b y, ((x,b,y) ∈ g \/ (y,b,x) ∈ g).
Proof.
  apply set_fold_ind_L with (P := fun f g => x ∈ f  <-> exists b y, ((x,b,y) ∈ g \/ (y,b,x) ∈ g)).
  set_solver.
  intros ((?,?),?). set_solver.
Qed.

Lemma vertices_singleton (x:(A*B*A)) :
  vertices {[x]} = {[vin x; vout x]}.
Proof.
  rewrite /vertices set_fold_singleton. destruct x as ((?&?)&?); set_solver.
Qed.

Lemma vertices_union (g1 g2:graph A B) :
  vertices (g1 ∪ g2) = vertices g1 ∪ vertices g2.
Proof.
  revert g2. induction g1 using set_ind_L; intros g2.
  { rewrite /vertices set_fold_empty !left_id_L //. }
  replace ({[x]} ∪ X ∪ g2) with (X ∪ ({[x]} ∪ g2)) by set_solver.
  rewrite (union_comm_L _  X).
  rewrite !IHg1. rewrite -union_assoc_L. f_equal.
  destruct_decide (decide (x ∈ g2)).
  { replace ({[x]} ∪ g2) with g2 by set_solver.
    rewrite vertices_singleton.
    assert ({[vin x; vout x]} ⊆ vertices g2); last by set_solver.
    intros l Hl. apply elem_of_vertices.
    rewrite elem_of_union !elem_of_singleton in Hl. destruct x as ((?,?),?). set_solver. }
  rewrite {1}/vertices /set_fold. simpl.
  rewrite (foldr_permutation _ _ _ _ (x::elements g2)).
  { intros. destruct a1 as ((?,?),?),a2 as ((?,?),?); set_solver. }
  { by apply elements_union_singleton. }
  { simpl. rewrite vertices_singleton. destruct x as ((?,?),?). set_solver. }
Qed.


Definition edge (g:graph A B) x c y := (x,c,y) ∈ g.
Definition reachable (g:graph A B) x bs y := rtcl (edge g) x bs y.

Lemma reachable_weak g1 g2 x bs y :
  reachable g1 x bs y ->
  g1 ⊆ g2 ->
  reachable g2 x bs y.
Proof.
  induction 1; intros Hi. apply rtcl_refl. eapply rtcl_l.
  by apply Hi. by apply IHrtcl.
Qed.

End Graph.

Section pstore_G.
  Context `{pstore_G : PstoreG Σ}.

#[local] Definition pstore_map_auth γ map :=
    @map_agree_auth _ _ _ _ _ pstore_G_map_G γ map.
  #[local] Definition pstore_map_elem γ l σ :=
    @map_agree_elem _ _ _ _ _ pstore_G_map_G γ l σ.

  Definition pstore_store σ0 σ :=
    union_with (λ _, Some) σ0 σ.

  Notation diff := (loc*val)%type. (* the loc and its old value. *)
  Notation graph_store := (graph loc diff).
  Notation map_model := (gmap loc (gmap loc val)).

  Definition apply_diffs (ds:list diff) (σ:gmap loc val) : gmap loc val :=
    foldr (fun '(l,v) σ => <[l:=v]> σ) σ ds.

  Record store_inv (M:map_model) (g:graph_store) (r:loc) (σ:gmap loc val) :=
    { si1 : dom M = vertices g ∪ {[r]};
      si2 : M !! r = Some σ;
      si3 : forall r', r' ∈ vertices g -> exists ds, reachable g r' ds r;
      si4 : forall r' ds σ',
        reachable g r' ds r -> M !! r' = Some σ' -> σ' ⊆ (apply_diffs ds σ)
    }.

  Definition locs_of_edges_in g (X:gset loc) :=
    forall r l v r', edge g r (l,v) r' -> l ∈ X.

  Record coherent (σ0 σ:gmap loc val) (g:graph_store) :=
    { coh1 : σ ⊆ σ0;
      coh2 : locs_of_edges_in g (dom σ0);
      coh3 : forall r ds, reachable g r ds r -> ds = nil (* acyclicity. *)
    }.

  Lemma gmap_included_insert `{Countable K} {V} (σ1 σ2:gmap K V) (l:K) (v:V) :
    σ1 ⊆ σ2 ->
    <[l:=v]>σ1 ⊆ <[l:=v]>σ2.
  Proof.
    intros ? l'. destruct_decide (decide (l=l')).
    { subst. rewrite !lookup_insert //. }
    { rewrite !lookup_insert_ne //. }
  Qed.

  Lemma gmap_included_insert_notin `{Countable K} {V} (σ1 σ2:gmap K V) (l:K) (v:V) :
    l ∉ dom σ1 ->
    σ1 ⊆ σ2 ->
    σ1 ⊆ <[l:=v]>σ2.
  Proof.
    intros ?? l'. destruct_decide (decide (l=l')).
    { subst. rewrite lookup_insert // not_elem_of_dom_1 //. }
    { rewrite !lookup_insert_ne //. }
  Qed.

  Lemma incl_dom_incl σ0 σ  :
    σ ⊆ σ0 ->
    dom σ ⊆ dom σ0.
  Proof.
    intros X1.
    intros l Hl. apply elem_of_dom in Hl. destruct Hl as (?&Hl).
    eapply map_subseteq_spec in X1; last done. by eapply elem_of_dom.
  Qed.

  #[local] Definition pstore (t:val) (σ:gmap loc val) : iProp Σ :=
    ∃ (t0 r:loc) (σ0:gmap loc val) (* the global map, with all the points-to ever allocated *)
      (g:graph_store)
      (M:map_model),
    ⌜t=#t0 /\ store_inv M g r σ /\ coherent σ0 σ g⌝ ∗
    t0 ↦ #(LiteralLoc r) ∗
    r ↦ &&Root ∗
    ([∗ map] l ↦ v ∈ σ0, l ↦ v) ∗
    ([∗ set] x ∈ g, let '(r,(l,v),r') := x in r ↦ &&Diff #(LiteralLoc l) v #(LiteralLoc r')).

  Definition open_inv : string :=
    "[%t0 [%r [%σ0 [%g [%M ((->&%Hinv&%Hcoh)&Ht0&Hr&Hσ0&Hg)]]]]]".

  Definition pstore_snapshot γ l σ : iProp Σ :=
    pstore_map_elem γ l σ.

  #[global] Instance pstore_snapshot_persistent γ l σ :
    Persistent (pstore_snapshot γ l σ).
  Proof.
    apply _.
  Qed.

  Lemma pstore_create_spec :
    {{{ True }}}
      pstore_create ()
    {{{ t,
      RET t;
        pstore t ∅
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    wp_alloc r as "Hroot".
    wp_alloc t0 as "Ht0".
    iApply "HΦ". iModIntro.
    iExists t0,r,∅,∅,{[r := ∅]}. iFrame.
    rewrite big_sepM_empty big_sepS_empty !right_id.
    iPureIntro. split_and!; first done.
    { constructor.
      { rewrite dom_singleton_L vertices_empty //. set_solver. }
      { rewrite lookup_singleton //. }
      { intros ?. rewrite vertices_empty. set_solver. }
      { intros ??? Hr.
        inversion Hr.
        { subst. rewrite lookup_singleton //. set_solver. }
        { exfalso. subst. set_solver. } } }
    { constructor. set_solver.
      { intros ????. set_solver. }
      { intros ??. inversion 1; subst. done. set_solver. } }
  Qed.

  Lemma use_locs_of_edges_in  g r ds r' X :
    locs_of_edges_in g X ->
    reachable g r ds r' ->
    (list_to_set ds.*1) ⊆ X.
  Proof.
    intros He.
    induction 1. set_solver.
    apply He in H. set_solver.
  Qed.

  Lemma dom_apply_diffs ds σ :
    dom (apply_diffs ds σ) = dom σ ∪ (list_to_set ds.*1).
  Proof.
    induction ds as [|(?&?)]; set_solver.
  Qed.

  Lemma apply_diff_insert_ne ds l v σ :
    l ∉ ds.*1 ->
    apply_diffs ds (<[l:=v]> σ) = <[l:=v]> (apply_diffs ds σ).
  Proof.
    induction ds as [|(?&?)].
    { intros ?. reflexivity. }
    { intros. simpl. rewrite IHds. set_solver.
      rewrite insert_commute //. set_solver. }
  Qed.

  Lemma pstore_ref_spec t σ v :
    {{{
      pstore t σ
    }}}
      pstore_ref v
    {{{ l,
      RET #l;
      ⌜σ !! l = None⌝ ∗
      pstore t (<[l := v]> σ)
    }}}.
  Proof.
    iIntros (ϕ) open_inv. iIntros "HΦ".

    wp_rec. wp_alloc l as "Hl".
    iApply "HΦ".

    iAssert ⌜σ0 !! l = None⌝%I as %Hl0.
    { rewrite -not_elem_of_dom. iIntros (Hl).
      apply elem_of_dom in Hl. destruct Hl.
      iDestruct (big_sepM_lookup with "[$]") as "Hl_"; first done.
      iDestruct (mapsto_ne with "Hl Hl_") as %?. done. }
    assert (σ !! l = None) as Hl.
    { eapply not_elem_of_dom. apply not_elem_of_dom in Hl0.
      intros ?. apply Hl0. destruct Hcoh. eapply incl_dom_incl; eauto. }
    iDestruct (mapsto_ne with "Hl Hr") as %Hlr.


    iModIntro. iStep.
    iExists t0,r, (<[l:=v]>σ0),g,(<[r:=<[l:=v]>σ]>M).

    rewrite big_sepM_insert //. iFrame.
    iPureIntro. split_and !; first done.
    { destruct Hinv as [X1 X2 X3 X4].
      constructor.
      { rewrite dom_insert_L; set_solver. }
      { rewrite lookup_insert //. }
      { eauto. }
      { intros r' ds σ' Hr. destruct_decide (decide (r=r')).
        { subst. rewrite lookup_insert. eapply coh3 in Hr; eauto. set_solver. }
        { rewrite lookup_insert_ne //.
          intros Hreach. eapply X4 in Hreach; eauto.
          destruct Hcoh as [Z1 Z2].
          eapply use_locs_of_edges_in in Z2. 2:done.
          rewrite apply_diff_insert_ne.
          { apply not_elem_of_dom in Hl0. set_solver. }
          apply gmap_included_insert_notin; last done.
          apply incl_dom_incl in Z1. apply incl_dom_incl in Hreach.
          rewrite dom_apply_diffs in Hreach.
          apply not_elem_of_dom in Hl0,Hl. set_solver. } } }
    { destruct Hcoh as [X1 X2].
      constructor.
      { eauto using gmap_included_insert. }
      { intros. rewrite dom_insert_L. intros ??. set_solver. }
      { eauto. } }
  Qed.


  Lemma pstore_get_spec {t σ l} v :
    σ !! l = Some v →
    {{{
      pstore t σ
    }}}
      pstore_get t #l
    {{{
      RET v;
      pstore t σ
    }}}.
  Proof.
    iIntros (Hl ϕ) open_inv. iIntros "HΦ".
    wp_rec. iStep 4. iModIntro.

    iDestruct (big_sepM_lookup_acc _ _ l v with "[$]") as "(?&Hσ0)".
    { destruct Hcoh as [X1 X2].
      specialize (X1 l). rewrite Hl in X1. destruct (σ0!!l); naive_solver. }

    iSteps.
  Qed.

  Lemma pstore_set_spec t σ l v :
    l ∈ dom σ →
    {{{
      pstore t σ
    }}}
      pstore_set t #l v
    {{{
      RET ();
      pstore t (<[l := v]> σ)
    }}}.
  Proof.
    iIntros (Hl Φ) open_inv. iIntros "HΦ".
    wp_rec. iStep 8. iModIntro.
    wp_alloc r' as "Hr'".

    assert (l ∈ dom σ0) as Hl0.
    { destruct Hcoh as [Z1 _ _]. apply incl_dom_incl in Z1. eauto. }
    apply elem_of_dom in Hl0. destruct Hl0 as (w&Hl0).

    iDestruct (big_sepM_insert_acc with "[$]") as "(?&Hσ0)". done.
    wp_load. wp_load. wp_store. iStep 4. iModIntro.
    wp_store. wp_store. iApply "HΦ".

    iSpecialize ("Hσ0" with "[$]").

    iAssert ⌜r' ∉ vertices g⌝%I as %Hr'.
    { admit. (* only one root? *) }

    iModIntro. iExists t0,r',(<[l:=v]> σ0), ({[(r,(l,w),r')]} ∪ g), (<[r':=<[l:=v]> σ]>M).
    rewrite big_sepS_union.
    { apply disjoint_singleton_l. intros ?. apply Hr'.
      apply elem_of_vertices. eauto. }
    rewrite big_sepS_singleton. iFrame.
    iPureIntro.
    { split_and!; first done.
      { destruct Hinv as [X1 X2 X3 X4].
        constructor.
        { rewrite dom_insert_L vertices_union vertices_singleton //. set_solver. }
        { rewrite lookup_insert //. }
        { rewrite vertices_union vertices_singleton. intros x.
          rewrite !elem_of_union !elem_of_singleton.
          intros [[-> | ->] | Hx].
          { exists [(l,w)]. simpl. eapply rtcl_l. 2:apply rtcl_refl. set_solver. }
          { exists nil. apply rtcl_refl. }
          { apply X3 in Hx. destruct Hx as (ds,Hx). exists (ds++[(l,w)]).
            eapply rtcl_r.
            { eapply reachable_weak; eauto. set_solver. }
            { set_solver. } } }
        { intros x ds. admit. } }
      { destruct Hcoh as [X1 X2].
        constructor.
        { eauto using gmap_included_insert. }
        { set_solver. }
        { admit. } } }
  Abort.

  Lemma pstore_catpure_spec t σ0 σ :
    {{{
      pstore_model t σ0 σ
    }}}
      pstore_capture t
    {{{ s,
      RET s;
      pstore_model t σ0 σ ∗
      pstore_snapshot_model s t σ
    }}}.
  Proof.
  Abort.

  Lemma pstore_repstore_spec t σ0 σ s σ' :
    {{{
      pstore_model t σ0 σ ∗
      pstore_snapshot_model s t σ'
    }}}
      pstore_restore t s
    {{{
      RET ();
      pstore_model t σ0 σ'
    }}}.
  Proof.
  Abort.
End pstore_G.

#[global] Opaque pstore_create.
#[global] Opaque pstore_ref.
#[global] Opaque pstore_get.
#[global] Opaque pstore_set.
#[global] Opaque pstore_capture.
#[global] Opaque pstore_restore.

#[global] Opaque pstore_model.
#[global] Opaque pstore_snapshot_model.
