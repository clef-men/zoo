From zebre Require Import
  prelude.
From zebre.language Require Import
  notations
  diaframe.
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

#[local] Definition descr_match : val :=
  λ: "descr" "Root" "Diff",
    match: "descr" with
      Injl <> =>
        "Root" ()
    | Injr "x" =>
        "Diff" "x".<0> "x".<1> "x".<2> "x".<3>
    end.
#[local] Notation "'match:' e0 'with' | 'Root' => e1 | 'Diff' x1 x2 x3 x4 => e2 'end'" := (
  (Val descr_match) e0 (Lam BAnon e1) (Lam x1 (Lam x2 (Lam x3 (Lam x4 e2))))
)(x1, x2, x3, x4 at level 1,
  e0, e1, e2 at level 200,
  format "'[hv' match:  e0  with  '/' '[' |  Root  =>  '/    ' e1 ']'  '/' '[' |  Diff  x1  x2  x3  x4  =>  '/    ' e2  ']' '/' end ']'"
) : expr_scope.
#[local] Notation "'match:' e0 'with' 'Root' => e1 | 'Diff' x1 x2 x3 x4 => e2 'end'" := (
  (Val descr_match) e0 (Lam BAnon e1) (Lam x1 (Lam x2 (Lam x3 (Lam x4 e2))))
)(x1, x2, x3, x4 at level 1,
  e0, e1, e2 at level 200,
  only parsing
) : expr_scope.
#[local] Notation "'match::' e0 'with' | 'Root' => e1 | 'Diff' x1 x2 x3 x4 => e2 'end'" := (
  (Val descr_match) e0 (Val (ValLam BAnon e1)) (Val (ValLam x1 (Lam x2 (Lam x3 (Lam x4 e2)))))
)(x1, x2, x3, x4 at level 1,
  e0, e1, e2 at level 200,
  format "'[hv' match::  e0  with  '/' '[' |  Root  =>  '/    ' e1 ']'  '/' '[' |  Diff  x1  x2  x3  x4  =>  '/    ' e2  ']' '/' end ']'"
) : expr_scope.
#[local] Notation "'match::' e0 'with' 'Root' => e1 | 'Diff' x1 x2 x3 x4 => e2 'end'" := (
  (Val descr_match) e0 (Val (ValLam BAnon e1)) (Val (ValLam x1 (Lam x2 (Lam x3 (Lam x4 e2)))))
)(x1, x2, x3, x4 at level 1,
  e0, e1, e2 at level 200,
  only parsing
) : expr_scope.

#[local] Definition ValRoot :=
  ValInjl ().
#[local] Notation "'&&Root'" :=
  ValRoot.
#[local] Instance pure_descr_match_Root e1 x1 x2 x3 x4 e2 :
  PureExec True 11
    (match:: &&Root with Root => e1 | Diff x1 x2 x3 x4 => e2 end)
    e1.
Proof.
  solve_pure_exec.
Qed.

#[local] Definition descr_Diff : val :=
  λ: "v1" "v2" "v3" "v4", Injr ("v1", "v2", "v3", "v4").
#[local] Definition ValDiff v1 v2 v3 v4 :=
  ValInjr (v1, v2, v3, v4).
#[local] Notation "'&Diff'" :=
  descr_Diff.
#[local] Notation "'&&Diff'" :=
  ValDiff.
#[local] Lemma descr_Diff_inj v1 v2 v3 v4 w1 w2 w3 w4 :
  &&Diff v1 v2 v3 v4 = &&Diff w1 w2 w3 w4 →
  v1 = w1 ∧ v2 = w2 ∧ v3 = w3 ∧ v4 = w4.
Proof.
  naive_solver.
Qed.
#[local] Instance pure_descr_Diff v1 v2 v3 v4 :
  PureExec True 9
    (&Diff v1 v2 v3 v4)
    (&&Diff v1 v2 v3 v4).
Proof.
  solve_pure_exec.
Qed.
#[local] Instance pure_descr_match_Diff v1 v2 v3 v4 e1 x1 x2 x3 x4 e2 :
  PureExec True 21
    (match:: &&Diff v1 v2 v3 v4 with Root => e1 | Diff x1 x2 x3 x4 => e2 end)
    (subst' x1 v1 (subst' x2 v2 (subst' x3 v3 (subst' x4 v4 e2)))).
Proof.
  solve_pure_exec.
Qed.

#[global] Opaque descr_match.
#[global] Opaque ValRoot.
#[global] Opaque descr_Diff.
#[global] Opaque ValDiff.

Definition store_create : val :=
  λ: <>,
    { ref &&Root; #0 }.

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
      "r" <-{ref_value}- "v"
    ) else (
      let: "root" := ref &&Root in
      "t".{root} <- &Diff "r" "r".{ref_value} "r_gen" "root" ;;
      "r" <-{ref_value}- "v" ;;
      "r" <-{ref_gen}- "t_gen" ;;
      "t" <-{root}- "root"
    ).

Definition store_capture : val :=
  λ: "t",
    let: "gen" := "t".{gen} in
    "t" <-{gen}- #1 + "gen" ;;
    ("t", "t".{root}, "gen").

#[local] Definition store_reroot : val :=
  rec: "store_reroot" "node" :=
    match: !"node" with
    | Root =>
        ()
    | Diff "r" "v" "gen" "node'" =>
        "store_reroot" "node'" ;;
        "node'" <- &Diff "r" "r".{ref_value} "r".{ref_gen} "node" ;;
        "r" <-{ref_value}- "v" ;;
        "r" <-{ref_gen}- "gen" ;;
        "node" <- &&Root
    end.

#[local] Definition store_reroot_opt_aux : val :=
  rec: "store_reroot_opt_aux" "node" :=
    match: !"node" with
    | Root =>
        ()
    | Diff "r" "v" "gen" "node'" =>
        "store_reroot_opt_aux" "node'" ;;
        "node'" <- &Diff "r" "r".{ref_value} "r".{ref_gen} "node" ;;
        "r" <-{ref_value}- "v" ;;
        "r" <-{ref_gen}- "gen"
    end.
#[local] Definition store_reroot_opt : val :=
  λ: "node",
    match: !"node" with
    | Root =>
        ()
    | Diff <> <> <> <> =>
        store_reroot_opt_aux "node" ;;
        "node" <- &&Root
    end.

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
          "t" <-{root}- "root" ;;
          "t" <-{gen}- #1 + "s".<snap_gen>
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
