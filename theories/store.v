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

Implicit Types r : loc.
Implicit Types v t s : val.
Implicit Types σ : gmap loc val.

#[local] Notation "'root'" :=
  0
( in custom zebre_field
).
#[local] Notation "'gen'" :=
  1
( in custom zebre_field
).

#[local] Notation "'ref_value'" :=
  0
( in custom zebre_field
).
#[local] Notation "'ref_gen'" :=
  1
( in custom zebre_field
).

#[local] Notation "'snap_store'" :=
  0
( in custom zebre_proj
).
#[local] Notation "'snap_root'" :=
  1
( in custom zebre_proj
).
#[local] Notation "'snap_gen'" :=
  2
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
    { ref §Root; #0 }.

Definition store_ref : val :=
  λ: "t" "v",
    { "v"; #0 }.

Definition store_get : val :=
  λ: "t" "r",
    "r".{ref_value}.

Definition store_set : val :=
  λ: "t" "r" "v",
    let: "t_gen" := "t".{gen} in
    let: "r_gen" := "r".{ref_gen} in
    if: "t_gen" = "r_gen" then (
      "r" <-{ref_value} "v"
    ) else (
      let: "root" := ref §Root in
      "t".{root} <- ‘Diff{ "r", "r".{ref_value}, "r_gen", "root" } ;;
      "r" <-{ref_value} "v" ;;
      "r" <-{ref_gen} "t_gen" ;;
      "t" <-{root} "root"
    ).

Definition store_capture : val :=
  λ: "t",
    let: "gen" := "t".{gen} in
    "t" <-{gen} #1 + "gen" ;;
    ("t", "t".{root}, "gen").

#[local] Definition store_reroot : val :=
  rec: "store_reroot" "node" :=
    match: !"node" with
    | Root =>
        ()
    | Diff "r" "v" "gen" "node'" =>
        "store_reroot" "node'" ;;
        "node'" <- ‘Diff{ "r", "r".{ref_value}, "r".{ref_gen}, "node" } ;;
        "r" <-{ref_value} "v" ;;
        "r" <-{ref_gen} "gen" ;;
        "node" <- §Root
    end.

#[local] Definition store_reroot_opt_aux : val :=
  rec: "store_reroot_opt_aux" "node" :=
    match: !"node" with
    | Root =>
        ()
    | Diff "r" "v" "gen" "node'" =>
        "store_reroot_opt_aux" "node'" ;;
        "node'" <- ‘Diff{ "r", "r".{ref_value}, "r".{ref_gen}, "node" } ;;
        "r" <-{ref_value} "v" ;;
        "r" <-{ref_gen} "gen"
    end.
#[local] Definition store_reroot_opt : val :=
  λ: "node",
    match: !"node" with
    | Root =>
        ()
    | Diff <> <> <> <> =>
        store_reroot_opt_aux "node" ;;
        "node" <- §Root
    end.

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
        | Diff "r" "v" "gen" "node_" =>
            assert ("node_" = "node") ;;
            "node" <- ‘Diff{ "r", "r".{ref_value}, "r".{ref_gen}, "node'" } ;;
            "r" <-{ref_value} "v" ;;
            "r" <-{ref_gen} "gen" ;;
            "store_revert" "node'" "seg"
        end
    end.
#[local] Definition store_reroot_opt2 : val :=
  λ: "node",
    let: "collect" := store_collect "node" §Nil in
    store_revert "collect".<0> "collect".<1>.

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
          "t" <-{root} "root" ;;
          "t" <-{gen} #1 + "s".<snap_gen>
      end
    ).

Class StoreG Σ `{zebre_G : !ZebreG Σ} := {
}.

Definition store_Σ := #[
].
Lemma subG_store_Σ Σ `{zebre_G : !ZebreG Σ} :
  subG store_Σ Σ →
  StoreG Σ.
Proof.
  solve_inG.
Qed.

Section store_G.
  Context `{store_G : StoreG Σ}.

  Definition store_store σ0 σ :=
    union_with (λ _, Some) σ0 σ.

  Definition store_model t σ0 σ : iProp Σ.
  Proof. Admitted.

  Definition store_snapshot_model s t σ : iProp Σ.
  Proof. Admitted.

  #[global] Instance store_model_timeless t σ0 σ :
    Timeless (store_model t σ0 σ).
  Proof.
  Abort.
  #[global] Instance store_snapshot_persistent s t σ :
    Persistent (store_snapshot_model s t σ).
  Proof.
  Abort.

  Lemma store_create_spec :
    {{{ True }}}
      store_create ()
    {{{ t,
      RET t;
      store_model t ∅ ∅
    }}}.
  Proof.
  Abort.

  Lemma store_ref_spec t σ0 σ v :
    {{{
      store_model t σ0 σ
    }}}
      store_ref t v
    {{{ r,
      RET #r;
      store_model t (<[r := v]> σ0) σ
    }}}.
  Proof.
  Abort.

  Lemma store_get_spec {t σ0 σ r} v :
    store_store σ0 σ !! r = Some v →
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

  Lemma store_catpure_spec t σ0 σ :
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
