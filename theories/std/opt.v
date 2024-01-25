From zebre Require Import
  prelude.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Export
  base.
From zebre Require Import
  options.

Implicit Types v : val.

Definition opt_match : val :=
  λ: "t" "None" "Some",
    match: "t" with
      Injl <> as "x" =>
        "None" "x"
    | Injr "x1" as "x2" =>
        "Some" "x1" "x2"
    end.
Notation "'match:' e0 'with' | 'None' 'as' x1 => e1 | 'Some' x21 'as' x22 => e2 'end'" := (
  (Val opt_match) e0 (Lam x1 e1) (Lam x21 (Lam x22 e2))
)(x1, x21, x22 at level 1,
  e0, e1, e2 at level 200,
  format "'[hv' match:  e0  with  '/' '[' |  None  as  x1  =>  '/    ' e1 ']'  '/' '[' |  Some  x21  as  x22  =>  '/    ' e2  ']' '/' end ']'"
) : expr_scope.
Notation "'match:' e0 'with' 'None' 'as' x1 => e1 | 'Some' x21 'as' x22 => e2 'end'" := (
  (Val opt_match) e0 (Lam x1 e1) (Lam x21 (Lam x22 e2))
)(x1, x21, x22 at level 1,
  e0, e1, e2 at level 200,
  only parsing
) : expr_scope.
Notation "'match::' e0 'with' | 'None' 'as' x1 => e1 | 'Some' x21 'as' x22 => e2 'end'" := (
  (Val opt_match) e0 (Val (ValLam x1 e1)) (Val (ValLam x21 (Lam x22 e2)))
)(x1, x21, x22 at level 1,
  e0, e1, e2 at level 200,
  format "'[hv' match::  e0  with  '/' '[' |  None  as  x1  =>  '/    ' e1 ']'  '/' '[' |  Some  x21  as  x22  =>  '/    ' e2  ']' '/' end ']'"
) : expr_scope.
Notation "'match::' e0 'with' 'None' 'as' x1 => e1 | 'Some' x21 'as' x22 => e2 'end'" := (
  (Val opt_match) e0 (Val (ValLam x1 e1)) (Val (ValLam x21 (Lam x22 e2)))
)(x1, x21, x22 at level 1,
  e0, e1, e2 at level 200,
  only parsing
) : expr_scope.
Notation "'match:' e0 'with' | 'None' => e1 | 'Some' x => e2 'end'" := (
  (Val opt_match) e0 (Lam BAnon e1) (Lam x (Lam BAnon e2))
)(x at level 1,
  e0, e1, e2 at level 200,
  format "'[hv' match:  e0  with  '/' '[' |  None  =>  '/    ' e1 ']'  '/' '[' |  Some  x  =>  '/    ' e2  ']' '/' end ']'"
) : expr_scope.
Notation "'match:' e0 'with' 'None' => e1 | 'Some' x => e2 'end'" := (
  (Val opt_match) e0 (Lam BAnon e1) (Lam x (Lam BAnon e2))
)(x at level 1,
  e0, e1, e2 at level 200,
  only parsing
) : expr_scope.
Notation "'match::' e0 'with' | 'None' => e1 | 'Some' x => e2 'end'" := (
  (Val opt_match) e0 (Val (ValLam BAnon e1)) (Val (ValLam x (Lam BAnon e2)))
)(x at level 1,
  e0, e1, e2 at level 200,
  format "'[hv' match::  e0  with  '/' '[' |  None  =>  '/    ' e1 ']'  '/' '[' |  Some  x  =>  '/    ' e2  ']' '/' end ']'"
) : expr_scope.
Notation "'match::' e0 'with' 'None' => e1 | 'Some' x => e2 'end'" := (
  (Val opt_match) e0 (Val (ValLam BAnon e1)) (Val (ValLam x (Lam BAnon e2)))
)(x at level 1,
  e0, e1, e2 at level 200,
  only parsing
) : expr_scope.

Definition ValNone :=
  ValInjl ().
Notation "'&&None'" :=
  ValNone.
#[global] Instance pure_opt_match_None x1 e1 x21 x22 e2 :
  PureExec True 11
    (match:: &&None with None as x1 => e1 | Some x21 as x22 => e2 end)
    (subst' x1 &&None e1).
Proof.
  solve_pure_exec.
Qed.

Definition opt_Some : val :=
  λ: "v", Injr "v".
Definition ValSome :=
  ValInjr.
Notation "'&Some'" :=
  opt_Some.
Notation "'&&Some'" :=
  ValSome.
#[global] Instance opt_Some_inj :
  Inj (=) (=) &&Some.
Proof.
  rewrite /Inj. naive_solver.
Qed.
#[global] Instance pure_opt_Some v :
  PureExec True 2
    (&Some v)
    (&&Some v).
Proof.
  solve_pure_exec.
Qed.
#[global] Instance pure_opt_match_Some v x1 e1 x21 x22 e2 :
  PureExec True 13
    (match:: &&Some v with None as x1 => e1 | Some x21 as x22 => e2 end)
    (subst' x21 v (subst' x22 (&&Some v) e2)).
Proof.
  solve_pure_exec.
Qed.

#[global] Opaque opt_match.
#[global] Opaque ValNone.
#[global] Opaque opt_Some.
#[global] Opaque ValSome.

Coercion opt_to_val o :=
  match o with
  | None =>
      &&None
  | Some v =>
      &&Some v
  end.
#[global] Arguments opt_to_val !_ / : assert.

#[global] Instance opt_to_val_inj :
  Inj (=) (=) opt_to_val.
Proof.
  intros [] []; naive_solver.
Qed.
#[global] Instance lst_to_val_physical o :
  ValPhysical (opt_to_val o).
Proof.
  destruct o; done.
Qed.

Section zebre_G.
  Context `{zebre_G : !ZebreG Σ}.
  Context τ `{!iType (iPropI Σ) τ}.

  Definition opt_type t : iProp Σ :=
      ⌜t = &&None⌝
    ∨ ∃ v, ⌜t = &&Some v⌝ ∗ τ v.
  #[global] Instance opt_type_itype :
    iType _ opt_type.
  Proof.
    split. apply _.
  Qed.

  Lemma opt_type_match t e1 x e2 Φ :
    opt_type t -∗
    ( WP e1 {{ Φ }} ∧
      ∀ v, τ v -∗ WP subst' x v e2 {{ Φ }}
    ) -∗
    WP match:: t with None => e1 | Some x => e2 end {{ Φ }}.
  Proof.
    iIntros "[-> | (%v & -> & #Hv)] H";
      [rewrite bi.and_elim_l | rewrite bi.and_elim_r];
      iSteps.
  Qed.
End zebre_G.
