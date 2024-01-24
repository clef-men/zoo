From iris.base_logic Require Import
  lib.ghost_map.

From zebre Require Import
  prelude.
From zebre.language Require Import
  notations
  diaframe.
From zebre.persistent Require Export
  base.
From zebre Require Import
  options.

Implicit Types l r root : loc.
Implicit Types v t : val.
Implicit Types σ : gmap loc val.
Implicit Types map : gmap loc (gmap loc val).

#[local] Definition descr_match : val :=
  λ: "descr" "Root" "Diff",
    match: "descr" with
    | Injl <> =>
        "Root" #()
    | Injr "x" =>
        "Diff" "x".𝟙.𝟙 "x".𝟙.𝟚 "x".𝟚
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
  ValInjl #().
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
  PureExec True 8
    (&Diff v1 v2 v3)
    (&&Diff v1 v2 v3).
Proof.
  solve_pure_exec.
Qed.
#[local] Instance pure_descr_match_Diff v1 v2 v3 e1 x1 x2 x3 e2 :
  PureExec True 20
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
    ref &&Root.

Definition pstore_ref : val :=
  λ: "v",
    ref "v".

#[local] Definition pstore_reroot : val :=
  rec: "pstore_reroot" "t" :=
    match: !"t" with
    | Root =>
        #()
    | Diff "r" "v" "t'" =>
        "pstore_reroot" "t'" ;;
        "t'" <- &Diff "r" !"r" "t" ;;
        "r" <- "v" ;;
        "t" <- &&Root
    end.

Definition pstore_get : val :=
  λ: "t" "r",
    pstore_reroot "t" ;;
    !"r".

Definition pstore_set : val :=
  λ: "t" "r" "v",
    pstore_reroot "t" ;;
    let: "t'" := ref &&Root in
    "t" <- &Diff "r" !"r" "t'" ;;
    "r" <- "v" ;;
    "t'".

Class PstoreG Σ `{zebre_G : !ZebreG Σ} := {
  pstore_G_map_G : ghost_mapG Σ loc (gmap loc val) ;
}.

Definition pstore_Σ := #[
  ghost_mapΣ loc (gmap loc val)
].
#[global] Instance subG_pstore_Σ Σ `{zebre_G : !ZebreG Σ} :
  subG pstore_Σ Σ →
  PstoreG Σ.
Proof.
  solve_inG.
Qed.

Section pstore_G.
  Context `{pstore_G : PstoreG Σ}.

  Definition pstore_name :=
    gname.
  Implicit Types γ : pstore_name.

  #[local] Definition pstore_map_auth γ map :=
    @ghost_map_auth _ _ _ _ _ pstore_G_map_G γ 1 map.
  #[local] Definition pstore_map_elem γ l σ :=
    @ghost_map_elem _ _ _ _ _ pstore_G_map_G γ l DfracDiscarded σ.

  Definition pstore_store σ0 σ :=
    union_with (λ _, Some) σ0 σ.

  #[local] Definition pstore_inv_inner γ σ0 map root : iProp Σ :=
    ∃ σ_root,
    ⌜map !! root = Some σ_root⌝ ∗
    ⌜map_Forall (λ _ σ, dom σ ⊆ dom σ0) map⌝ ∗
    pstore_map_auth γ map ∗
    root ↦ &&Root ∗
    ( [∗ map] r ↦ v ∈ pstore_store σ0 σ_root,
      r ↦ v
    ) ∗
    ( [∗ map] l ↦ σ ∈ delete root map,
      ∃ r v l' σ',
      ⌜map !! l' = Some σ'⌝ ∗
      ⌜pstore_store σ0 σ = <[r := v]> (pstore_store σ0 σ')⌝ ∗
      l ↦ &&Diff #r v #l'
    ).
  Definition pstore_inv γ σ0 : iProp Σ :=
    ∃ map root,
    pstore_inv_inner γ σ0 map root.

  Definition pstore_model t γ σ : iProp Σ :=
    ∃ l,
    ⌜t = #l⌝ ∗
    pstore_map_elem γ l σ.

  #[local] Instance pstore_inv_inner_timeless γ σ0 map root :
    Timeless (pstore_inv_inner γ σ0 map root).
  Proof.
    apply _.
  Qed.
  #[global] Instance pstore_inv_timeless γ σ0 :
    Timeless (pstore_inv γ σ0).
  Proof.
    apply _.
  Qed.
  #[global] Instance pstore_model_persistent t γ σ :
    Persistent (pstore_model t γ σ).
  Proof.
    apply _.
  Qed.

  #[local] Lemma pstore_map_alloc root :
    ⊢ |==>
      ∃ γ,
      pstore_map_auth γ {[root := ∅]} ∗
      pstore_map_elem γ root ∅.
  Proof.
    iMod (@ghost_map_alloc _ _ _ _ _ pstore_G_map_G {[root := ∅]}) as "(%γ_map & Hmap_auth & Hmap_elem)".
    setoid_rewrite big_sepM_singleton.
    iMod (ghost_map_elem_persist with "Hmap_elem") as "Hmap_elem".
    iSteps.
  Qed.
  #[local] Lemma pstore_map_lookup γ map l σ :
    pstore_map_auth γ map -∗
    pstore_map_elem γ l σ -∗
    ⌜map !! l = Some σ⌝.
  Proof.
    apply ghost_map_lookup.
  Qed.
  #[local] Lemma pstore_map_insert {γ map} l σ :
    map !! l = None →
    pstore_map_auth γ map ⊢ |==>
      pstore_map_auth γ (<[l := σ]> map) ∗
      pstore_map_elem γ l σ.
  Proof.
    iIntros "%Hlookup Hmap_auth".
    iMod (ghost_map_insert with "Hmap_auth") as "(Hmap_auth & Hmap_elem)"; first done.
    iMod (ghost_map_elem_persist with "Hmap_elem") as "Hmap_elem".
    iSteps.
  Qed.

  #[local] Lemma pstore_store_dom σ0 σ :
    dom σ ⊆ dom σ0 →
    dom (pstore_store σ0 σ) ≡ dom σ0.
  Proof.
    rewrite set_equiv => Hσ_dom r. rewrite !elem_of_dom lookup_union_with.
    destruct (σ0 !! r) eqn:Hσ0_lookup, (σ !! r) eqn:Hσ_lookup; try done.
    apply not_elem_of_dom_2 in Hσ0_lookup. apply elem_of_dom_2 in Hσ_lookup. set_solver.
  Qed.
  #[local] Lemma pstore_store_insert r v σ0 σ :
    dom σ ⊆ dom σ0 →
    σ0 !! r = None →
    pstore_store (<[r := v]> σ0) σ = <[r := v]> (pstore_store σ0 σ).
  Proof.
    intros Hσ_dom Hσ0_lookup.
    rewrite insert_union_with_l // -not_elem_of_dom.
    rewrite -not_elem_of_dom in Hσ0_lookup.
    set_solver.
  Qed.

  Lemma pstore_create_spec :
    {{{ True }}}
      pstore_create #()
    {{{ t γ,
      RET t;
      pstore_inv γ ∅ ∗
      pstore_model t γ ∅
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    wp_alloc root as "Hroot".
    iMod (pstore_map_alloc root) as "(%γ & Hmap_auth & Hmap_elem)".
    iApply "HΦ".
    iSplitR "Hmap_elem"; last iSteps.
    iExists {[root := ∅]}, root. iFrame. iExists ∅.
    iSplitR. { rewrite lookup_singleton //. }
    iSplitR. { rewrite map_Forall_singleton //. }
    iSplitR. { rewrite /pstore_store left_id big_sepM_empty //. }
    rewrite delete_singleton big_sepM_empty //.
  Qed.

  Lemma pstore_ref_spec γ σ0 v :
    {{{
      pstore_inv γ σ0
    }}}
      pstore_ref v
    {{{ r,
      RET #r;
      ⌜σ0 !! r = None⌝ ∗
      pstore_inv γ (<[r := v]> σ0)
    }}}.
  Proof.
    iIntros "%Φ (%map & %root & %σ_root & %Hmap_lookup_root & %Hmap & Hmap_auth & Hroot & Hσ_root & Hmap) HΦ".
    assert (dom σ_root ⊆ dom σ0) as Hσ_root_dom.
    { rewrite map_Forall_lookup in Hmap. naive_solver. }
    wp_rec. wp_alloc r as "Hr".
    iApply "HΦ".
    iAssert ⌜σ0 !! r = None⌝%I as %Hσ0_lookup.
    { rewrite -not_elem_of_dom. iIntros "%Hr".
      assert (∃ w, pstore_store σ0 σ_root !! r = Some w) as (w & Hunion_lookup).
      { eexists. apply lookup_lookup_total_dom. rewrite pstore_store_dom //. }
      iDestruct (big_sepM_lookup with "Hσ_root") as "Hr_"; first done.
      iDestruct (mapsto_ne with "Hr Hr_") as %[]. done.
    }
    assert (σ_root !! r = None).
    { rewrite -!not_elem_of_dom in Hσ0_lookup |- *. set_solver. }
    iModIntro. iStep. iExists map, root. iFrame. iExists σ_root.
    iSplit. { iPureIntro. set_solver. }
    iSplit. { iPureIntro. eapply map_Forall_impl; first done. set_solver. }
    iSplitR "Hmap".
    { setoid_rewrite <- insert_union_with_l; last done.
      iApply (big_sepM_insert_2 with "[Hr] Hσ_root").
      iSteps.
    }
    iApply (big_sepM_impl with "Hmap"). iIntros "!> %l %σ %Hdelete_map_lookup (%r' & %v' & %l' & %σ' & %Hmap_lookup' & %Hdiff & Hl & Hmap_elem)".
    iExists r', v', l', σ'. iSteps.
    assert (dom σ ⊆ dom σ0) as Hσ_dom.
    { rewrite map_Forall_lookup in Hmap. rewrite lookup_delete_Some in Hdelete_map_lookup. naive_solver. }
    assert (σ !! r = None).
    { rewrite -!not_elem_of_dom in Hσ0_lookup |- *. set_solver. }
    assert (dom σ' ⊆ dom σ0) as Hσ'_dom.
    { rewrite map_Forall_lookup in Hmap. naive_solver. }
    rewrite pstore_store_insert // Hdiff pstore_store_insert // insert_commute //.
  Abort.

  #[local] Lemma pstore_reroot_spec γ σ0 map root l σ :
    {{{
      pstore_inv_inner γ σ0 map root ∗
      pstore_map_elem γ l σ
    }}}
      pstore_reroot #l
    {{{
      RET #();
      pstore_inv_inner γ σ0 map l
    }}}.
  Proof.
  Abort.

  Lemma pstore_get_spec {γ σ0 t σ r} v :
    pstore_store σ0 σ !! r = Some v →
    {{{
      pstore_inv γ σ0 ∗
      pstore_model t γ σ
    }}}
      pstore_get t #r
    {{{
      RET v;
      pstore_inv γ σ0
    }}}.
  Proof.
  Abort.

  Lemma pstore_set_spec γ σ0 t σ r v :
    r ∈ dom σ0 →
    {{{
      pstore_inv γ σ0 ∗
      pstore_model t γ σ
    }}}
      pstore_set t #r v
    {{{ t',
      RET t';
      pstore_inv γ σ0 ∗
      pstore_model t' γ (<[r := v]> (pstore_store σ0 σ))
    }}}.
  Proof.
  Abort.
End pstore_G.

#[global] Opaque pstore_create.
#[global] Opaque pstore_ref.
#[global] Opaque pstore_get.
#[global] Opaque pstore_set.

#[global] Opaque pstore_inv.
#[global] Opaque pstore_model.
