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

End rtc_lab.

Section Graph.
Definition graph (A B:Type) `{Countable A} `{Countable B} := gset (A*B*A).

Context `{Countable A} `{Countable B}.
Definition vertices (g:graph A B) : gset A :=
  set_fold (fun '(x,_,y) acc => {[x;y]} ∪ acc) ∅ g.

Lemma vertices_empty :
  vertices ∅ = ∅.
Proof. compute_done. Qed.

Definition edge (g:graph A B) x c y := (x,c,y) ∈ g.
Definition reachable (g:graph A B) x bs y := rtcl (edge g) x bs y.

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
      si4 : forall r' ds,
        reachable g r' ds r -> M !! r' = Some (apply_diffs ds σ)
    }.

  Record coherent (σ0 σ:gmap loc val) (g:graph_store) :=
    { coh1 : σ ⊆ σ0;
      coh2 : forall r l v r', edge g r (l,v) r' -> l ∈ dom σ
    }.

  Lemma coherent_dom_incl σ0 σ g  :
    coherent σ0 σ g ->
    dom σ ⊆ dom σ0.
  Proof.
    intros [X1 X2].
    intros l Hl. apply elem_of_dom in Hl. destruct Hl as (?&Hl).
    eapply map_subseteq_spec in X1; last done. by eapply elem_of_dom.
  Qed.

  #[local] Definition pstore γ (t:val) (σ:gmap loc val) : iProp Σ :=
    ∃ (t0 r:loc) (σ0:gmap loc val) (* the global map, with all the points-to ever allocated *)
      (g:graph_store)
      (M:map_model),
    ⌜t=#t0 /\ store_inv M g r σ /\ coherent σ0 σ g⌝ ∗
    t0 ↦ #(LiteralLoc r) ∗
    r ↦ &&Root ∗
    pstore_map_auth γ (delete r M) ∗
    ([∗ map] l ↦ v ∈ σ0, l ↦ v) ∗
    ([∗ set] x ∈ g, let '(r,(l,v),r') := x in r ↦ &&Diff #(LiteralLoc l) v #(LiteralLoc r')).

  Definition open_inv : string :=
    "[%t0 [%r [%σ0 [%g [%M ((->&%Hinv&%Hcoh)&Ht0&Hr&Hauth&Hσ0&Hg)]]]]]".

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
    {{{ t γ,
      RET t;
        pstore γ t ∅
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    wp_alloc r as "Hroot".
    wp_alloc t0 as "Ht0".
    iMod (map_agree_alloc {[r:=∅]}) as "[%γ ?]".
    iApply "HΦ". iModIntro.
    iExists t0,r,∅,∅,{[r := ∅]}. iFrame.
    rewrite big_sepM_empty big_sepS_empty !right_id.
    iPureIntro. split_and!; first done.
    { constructor.
      { rewrite dom_singleton_L vertices_empty //. set_solver. }
      { rewrite lookup_singleton //. }
      { intros ?. rewrite vertices_empty. set_solver. }
      { intros ?? Hr.
        inversion Hr.
        { subst. rewrite lookup_singleton //. }
        { exfalso. subst. set_solver. } } }
    { constructor. set_solver. set_solver. }
  Qed.

  Lemma pstore_ref_spec γ t σ v :
    {{{
      pstore γ t σ
    }}}
      pstore_ref v
    {{{ l,
      RET #l;
      ⌜σ !! l = None⌝ ∗
      pstore γ t (<[l := v]> σ)
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
      intros ?. apply Hl0. eapply coherent_dom_incl; eauto. }
    iDestruct (mapsto_ne with "Hl Hr") as %Hlr.


    iModIntro. iStep.
    iExists t0,r, (<[l:=v]>σ0),g,(<[r:=<[l:=v]>σ]>M).

    rewrite delete_insert_delete big_sepM_insert //. iFrame.
    iPureIntro. split_and !; first done.
    { destruct Hinv as [X1 X2 X3 X4].
      constructor.
      { rewrite dom_insert_L; set_solver. }
      { rewrite lookup_insert //. }
      { eauto. }
      { intros r' ds Hr. destruct_decide (decide (r=r')).
        { subst. rewrite lookup_insert. admit. (* acyclic *) }
        { rewrite lookup_insert_ne //. erewrite X4; eauto. admit. (* have to switch to inclusion. *) } } }
    { destruct Hcoh as [X1 X2].
      constructor.
      { admit. }
      { intros. rewrite dom_insert_L. set_solver. } }
  Abort.


  Lemma pstore_get_spec {γ t σ l} v :
    σ !! l = Some v →
    {{{
      pstore γ t σ
    }}}
      pstore_get t #l
    {{{
      RET v;
      pstore γ t σ
    }}}.
  Proof.
    iIntros (? ϕ) open_inv. iIntros "HΦ".
    wp_rec. iStep 4. iModIntro.
    admit. (* wp_load. *)
  Abort.

  Lemma pstore_set_spec γ t σ l v :
    l ∈ dom σ →
    {{{
      pstore γ t σ
    }}}
      pstore_set t #l v
    {{{
      RET ();
      pstore γ t (<[l := v]> σ)
    }}}.
  Proof.
    iIntros (Hl Φ) open_inv. iIntros "HΦ".
    wp_rec. iStep 8. iModIntro.
    wp_alloc r' as "Hr'".

    assert (l ∈ dom σ0) as Hl0.
    { eapply coherent_dom_incl in Hl; eauto. }
    apply elem_of_dom in Hl0. destruct Hl0 as (w&Hl0).

    iDestruct (big_sepM_insert_acc with "[$]") as "(?&Hσ0)". done.
    wp_load. wp_load. wp_store. iStep 4. iModIntro.
    wp_store. wp_store. iApply "HΦ".

    iSpecialize ("Hσ0" with "[$]").
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