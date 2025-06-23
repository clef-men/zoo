From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  option.
From zoo_saturn Require Export
  base
  ws_queue_1__code.
From zoo_saturn Require Import
  ws_queue_1__types.
From zoo Require Import
  options.

Implicit Types v t : val.
Implicit Types vs : list val.

Class WsQueue1G Σ `{zoo_G : !ZooG Σ} := {
}.

Definition ws_queue_1_Σ := #[
].
#[global] Instance subG_ws_queue_1_Σ Σ `{zoo_G : !ZooG Σ} :
  subG ws_queue_1_Σ Σ →
  WsQueue1G Σ .
Proof.
  (* solve_inG. *)
Qed.

Section ws_queue_1_G.
  Context `{ws_queue_1_G : WsQueue1G Σ}.

  Definition ws_queue_1_inv t (ι : namespace) : iProp Σ.
  Proof. Admitted.

  Definition ws_queue_1_model t vs : iProp Σ.
  Proof. Admitted.

  Definition ws_queue_1_owner t : iProp Σ.
  Proof. Admitted.

  #[global] Instance ws_queue_1_model_timeless t model :
    Timeless (ws_queue_1_model t model).
  Proof.
  Admitted.
  #[global] Instance ws_queue_1_owner_timeless t :
    Timeless (ws_queue_1_owner t).
  Proof.
  Admitted.
  #[global] Instance ws_queue_1_inv_persistent t ι :
    Persistent (ws_queue_1_inv t ι).
  Proof.
  Admitted.

  Lemma ws_queue_1_model_exclusive t vs1 vs2 :
    ws_queue_1_model t vs1 -∗
    ws_queue_1_model t vs2 -∗
    False.
  Proof.
  Admitted.

  Lemma ws_queue_1_owner_exclusive t :
    ws_queue_1_owner t -∗
    ws_queue_1_owner t -∗
    False.
  Proof.
  Admitted.

  Lemma ws_queue_1_create_spec ι :
    {{{
      True
    }}}
      ws_queue_1_create ()
    {{{ t,
      RET t;
      ws_queue_1_inv t ι ∗
      ws_queue_1_model t [] ∗
      ws_queue_1_owner t
    }}}.
  Proof.
  Admitted.

  Lemma ws_queue_1_push_spec t ι v :
    <<<
      ws_queue_1_inv t ι ∗
      ws_queue_1_owner t
    | ∀∀ vs,
      ws_queue_1_model t vs
    >>>
      ws_queue_1_push t v @ ↑ι
    <<<
      ws_queue_1_model t (vs ++ [v])
    | RET ();
      ws_queue_1_owner t
    >>>.
  Proof.
  Admitted.

  Lemma ws_queue_1_steal_spec t ι :
    <<<
      ws_queue_1_inv t ι
    | ∀∀ vs,
      ws_queue_1_model t vs
    >>>
      ws_queue_1_steal t @ ↑ι
    <<<
      ws_queue_1_model t (tail vs)
    | RET head vs;
      True
    >>>.
  Proof.
  Admitted.

  Lemma ws_queue_1_pop_spec t ι :
    <<<
      ws_queue_1_inv t ι ∗
      ws_queue_1_owner t
    | ∀∀ vs,
      ws_queue_1_model t vs
    >>>
      ws_queue_1_pop t @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ⌜vs = []⌝ ∗
          ws_queue_1_model t []
      | Some v =>
          ∃ vs',
          ⌜vs = vs' ++ [v]⌝ ∗
          ws_queue_1_model t vs'
      end
    | RET o;
      ws_queue_1_owner t
    >>>.
  Proof.
  Admitted.
End ws_queue_1_G.

From zoo_saturn Require
  ws_queue_1__opaque.

#[global] Opaque ws_queue_1_inv.
#[global] Opaque ws_queue_1_model.
#[global] Opaque ws_queue_1_owner.
