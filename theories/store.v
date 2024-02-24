(* Based on:
   https://gitlab.com/basile.clement/store/-/blob/main/src/store.ml?ref_type=heads
*)

From iris.base_logic Require Import
  lib.ghost_map.

From zebre Require Import
  prelude.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Import
  assert
  lst.
From zebre Require Import
  options.

#[local] Notation "'gen'" := (
  in_type "t" 0
)(in custom zebre_field
).
#[local] Notation "'root'" := (
  in_type "t" 1
)(in custom zebre_field
).

#[local] Notation "'ref_gen'" := (
  in_type "ref" 0
)(in custom zebre_field
).
#[local] Notation "'ref_value'" := (
  in_type "ref" 1
)(in custom zebre_field
).

#[local] Notation "'snap_store'" :=
  ("snap", 0)
( in custom zebre_proj
).
#[local] Notation "'snap_gen'" :=
  ("snap", 1)
( in custom zebre_proj
).
#[local] Notation "'snap_root'" :=
  ("snap", 2)
( in custom zebre_proj
).

#[local] Notation "'Root'" :=
  ("descr", 0)
( in custom zebre_tag
).
#[local] Notation "'Diff'" :=
  ("descr", 1)
( in custom zebre_tag
).

Definition store_create : val :=
  λ: <>,
    { #0; ref §Root }.

Definition store_ref : val :=
  λ: "t" "v",
    { #0; "v" }.

Definition store_get : val :=
  λ: "t" "r",
    "r".{ref_value}.

Definition store_set : val :=
  λ: "t" "r" "v",
    let: "g_t" := "t".{gen} in
    let: "g_r" := "r".{ref_gen} in
    if: "g_t" = "g_r" then (
      "r" <-{ref_value} "v"
    ) else (
      let: "root" := ref §Root in
      "t".{root} <- ‘Diff{ "r", "g_r", "r".{ref_value}, "root" } ;;
      "r" <-{ref_gen} "g_t" ;;
      "r" <-{ref_value} "v" ;;
      "t" <-{root} "root"
    ).

Definition store_capture : val :=
  λ: "t",
    let: "g" := "t".{gen} in
    "t" <-{gen} #1 + "g" ;;
    ("t", "g", "t".{root}).

#[local] Definition store_collect : val :=
  rec: "store_collect" "node" "acc" :=
    match: !"node" with
    | Root =>
        ("node", "acc")
    | Diff <> <> <> "node'" =>
        "store_collect" "node'" ‘Cons{ "node", "acc" }
    end.
#[local] Definition store_revert : val :=
  rec: "store_revert" "node" "seg" :=
    match: "seg" with
    | Nil =>
        "node" <- §Root
    | Cons "node'" "seg" =>
        match: !"node'" with
        | Root =>
            Fail
        | Diff "r" "g" "v" "node_" =>
            assert ("node_" = "node") ;;
            "node" <- ‘Diff{ "r", "r".{ref_gen}, "r".{ref_value}, "node'" } ;;
            "r" <-{ref_gen} "g" ;;
            "r" <-{ref_value} "v" ;;
            "store_revert" "node'" "seg"
        end
    end.
#[local] Definition store_reroot : val :=
  λ: "node",
    let: "root", "nodes" := store_collect "node" §Nil in
    store_revert "root" "nodes".

Definition store_restore : val :=
  λ: "t" "s",
    if: "t" ≠ "s".<snap_store> then (
      Fail
    ) else (
      let: "root" := "s".<snap_root> in
      match: !"root" with
      | Root =>
          ()
      | Diff <> <> <> <> =>
          store_reroot "root" ;;
          "t" <-{gen} #1 + "s".<snap_gen> ;;
          "t" <-{root} "root"
      end
    ).

Implicit Types l r node cnode base root dst : loc.
Implicit Types nodes : list loc.
Implicit Types v t s : val.
Implicit Types σ : gmap loc val.

#[local] Definition generation :=
  nat.
Implicit Types g : generation.

#[local] Definition store :=
  gmap loc (generation * val).
Implicit Types ς : store.
Implicit Types data : generation * val.

#[local] Definition descriptor : Set :=
  generation * store.
Implicit Types descr base_descr : descriptor.

Class StoreG Σ `{zebre_G : !ZebreG Σ} := {
  #[local] store_G_nodes_G :: ghost_mapG Σ loc descriptor ;
}.

Definition store_Σ := #[
  ghost_mapΣ loc descriptor
].
Lemma subG_store_Σ Σ `{zebre_G : !ZebreG Σ} :
  subG store_Σ Σ →
  StoreG Σ.
Proof.
  solve_inG.
Qed.

Section store_G.
  Context `{store_G : StoreG Σ}.

  #[local] Definition store_on σ0 ς :=
    ς ∪ (pair 0 <$> σ0).
  #[local] Definition store_generation g ς :=
    map_Forall (λ r data, data.1 ≤ g) ς.

  #[local] Definition delta : Set :=
    loc * (generation * val).
  Implicit Types δ : delta.
  Implicit Types δs : list delta.

  #[local] Definition delta_apply δs ς :=
    list_to_map δs ∪ ς.
  #[local] Fixpoint delta_chain node nodes δs dst : iProp Σ :=
    match nodes, δs with
    | [], [] =>
        ⌜node = dst⌝
    | node' :: nodes, δ :: δs =>
        node ↦ ’Diff{ #δ.1, #δ.2.1, δ.2.2, #node' } ∗
        delta_chain node' nodes δs dst
    | _, _ =>
        False
    end.

  #[local] Definition cnodes_auth γ cnodes :=
    ghost_map_auth γ 1 cnodes.
  #[local] Definition cnodes_pointsto γ cnode descr :=
    ghost_map_elem γ cnode (DfracOwn 1) descr.
  #[local] Definition cnodes_elem γ cnode descr :=
    ghost_map_elem γ cnode DfracDiscarded descr.

  #[local] Definition cnode_model γ σ0 cnode descr node ς : iProp Σ :=
    ⌜dom descr.2 ⊆ dom σ0⌝ ∗
    ⌜store_generation descr.1 descr.2⌝ ∗
    cnodes_elem γ cnode descr ∗
    ( ∃ nodes δs,
      ⌜store_on σ0 descr.2 = store_on σ0 $ delta_apply δs ς⌝ ∗
      delta_chain cnode nodes δs node
    ).
  Definition store_model t σ0 σ : iProp Σ :=
    ∃ l γ g root ς,
    ⌜t = #l⌝ ∗
    ⌜σ = snd <$> ς⌝ ∗
    meta l nroot γ ∗
    l.[gen] ↦ #g ∗
    l.[root] ↦ #root ∗
    root ↦ §Root ∗
    ( [∗ map] r ↦ data ∈ store_on σ0 ς,
      r.[ref_gen] ↦ #data.1 ∗
      r.[ref_value] ↦ data.2
    ) ∗
    ⌜store_generation g ς⌝ ∗
    if g is 0 then
      cnodes_pointsto γ root (0, ς)
    else
      ∃ cnodes base base_descr,
      cnodes_auth γ cnodes ∗
      (* base cnode *)
      ⌜cnodes !! base = Some base_descr⌝ ∗
      ⌜base_descr.1 < g⌝ ∗
      cnode_model γ σ0 base base_descr root ς ∗
      (* other cnodes *)
      ( [∗ map] cnode ↦ descr ∈ delete base cnodes,
        ∃ cnode' descr',
        ⌜cnodes !! cnode' = Some descr'⌝ ∗
        cnode_model γ σ0 cnode descr cnode' descr'.2
      ).

  Definition store_snapshot_model s t σ : iProp Σ :=
    ∃ l γ g node descr,
    ⌜t = #l ∧ s = (t, #g, #node)%V⌝ ∗
    meta l nroot γ ∗
    cnodes_elem γ node descr ∗
    ⌜descr.1 ≤ g⌝.

  #[global] Instance store_model_timeless t σ0 σ :
    Timeless (store_model t σ0 σ).
  Proof.
  Abort.
  #[global] Instance store_snapshot_persistent s t σ :
    Persistent (store_snapshot_model s t σ).
  Proof.
    apply _.
  Qed.

  #[local] Definition cnodes_alloc root :
    ⊢ |==>
      ∃ γ,
      cnodes_auth γ {[root := (0, ∅)]} ∗
      cnodes_pointsto γ root (0, ∅).
  Proof.
    iMod ghost_map_alloc as "(%γ & Hcnodes_auth & Hcnodes_pointsto)".
    iSteps. rewrite big_sepM_singleton. iSteps.
  Qed.

  Lemma store_create_spec :
    {{{ True }}}
      store_create ()
    {{{ t,
      RET t;
      store_model t ∅ ∅
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    wp_alloc root as "Hroot".
    wp_record l as "Hmeta" "(Hl_gen & Hl_root & _)".
    iMod (cnodes_alloc root) as "(%γ & Hcnodes_auth & Hcnodes_pointsto)".
    iMod (meta_set with "Hmeta") as "Hmeta"; first done.
    iApply "HΦ".
    iExists l, γ, 0, root, ∅. iFrame. rewrite big_sepM_empty. iSteps.
  Qed.

  Lemma store_ref_spec t σ0 σ v :
    {{{
      store_model t σ0 σ
    }}}
      store_ref t v
    {{{ r,
      RET #r;
      ⌜σ0 !! r = None⌝ ∗
      store_model t (<[r := v]> σ0) σ
    }}}.
  Proof.
  Abort.

  Lemma store_get_spec {t σ0 σ r} v :
    (σ ∪ σ0) !! r = Some v →
    {{{
      store_model t σ0 σ
    }}}
      store_get t #r
    {{{
      RET v;
      store_model t σ0 σ
    }}}.
  Proof.
  Abort.

  Lemma store_set_spec t σ0 σ r v :
    r ∈ dom σ0 →
    {{{
      store_model t σ0 σ
    }}}
      store_set t #r v
    {{{
      RET ();
      store_model t σ0 (<[r := v]> σ)
    }}}.
  Proof.
  Abort.

  Lemma store_capture_spec t σ0 σ :
    {{{
      store_model t σ0 σ
    }}}
      store_capture t
    {{{ s,
      RET s;
      store_model t σ0 σ ∗
      store_snapshot_model s t σ
    }}}.
  Proof.
  Abort.

  Lemma store_restore_spec t σ0 σ s σ' :
    {{{
      store_model t σ0 σ ∗
      store_snapshot_model s t σ'
    }}}
      store_restore t s
    {{{
      RET ();
      store_model t σ0 σ'
    }}}.
  Proof.
  Abort.
End store_G.

#[global] Opaque store_create.
#[global] Opaque store_ref.
#[global] Opaque store_get.
#[global] Opaque store_set.
#[global] Opaque store_capture.
#[global] Opaque store_restore.

#[global] Opaque store_model.
#[global] Opaque store_snapshot_model.
