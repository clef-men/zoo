From zebre Require Import
  prelude.
From zebre.language Require Import
  notations
  diaframe.
From zebre.persistent Require Export
  base.
From zebre Require Import
  options.

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
}.

Definition pstore_Σ := #[
].
#[global] Instance subG_pstore_Σ Σ `{zebre_G : !ZebreG Σ} :
  subG pstore_Σ Σ →
  PstoreG Σ.
Proof.
Qed.

Section pstore_G.
  Context `{pstore_G : PstoreG Σ}.

  Definition pstore_store σ0 σ :=
    union_with (λ _, Some) σ0 σ.

  Definition pstore_model t σ0 σ : iProp Σ.
  Proof. Admitted.

  Definition pstore_snapshot_model s t σ : iProp Σ.
  Proof. Admitted.

  #[global] Instance pstore_model_timeless t σ0 σ :
    Timeless (pstore_model t σ0 σ).
  Proof.
  Abort.
  #[global] Instance pstore_snapshot_persistent s t σ :
    Persistent (pstore_snapshot_model s t σ).
  Proof.
  Abort.

  Lemma pstore_create_spec :
    {{{ True }}}
      pstore_create ()
    {{{ t,
      RET t;
      pstore_model t ∅ ∅
    }}}.
  Proof.
  Abort.

  Lemma pstore_ref_spec t σ0 σ v :
    {{{
      pstore_model t σ0 σ
    }}}
      pstore_ref t v
    {{{ r,
      RET #r;
      pstore_model t (<[r := v]> σ0) σ
    }}}.
  Proof.
  Abort.

  Lemma pstore_get_spec {t σ0 σ r} v :
    pstore_store σ0 σ !! r = Some v →
    {{{
      pstore_model t σ0 σ
    }}}
      pstore_get t #r
    {{{
      RET v;
      pstore_model t σ0 σ
    }}}.
  Proof.
  Abort.

  Lemma pstore_set_spec t σ0 σ r v :
    r ∈ dom σ0 →
    {{{
      pstore_model t σ0 σ
    }}}
      pstore_set t #r v
    {{{
      RET ();
      pstore_model t σ0 (<[r := v]> σ)
    }}}.
  Proof.
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
