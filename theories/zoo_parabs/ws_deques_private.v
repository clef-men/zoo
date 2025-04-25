From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  option
  array
  deque
  random_round.
From zoo_parabs Require Export
  base
  ws_deques_private__code.
From zoo Require Import
  options.

Implicit Types v t round : val.
Implicit Types vs : list val.
Implicit Types vss : list (list val).
Implicit Types status : status.

Class WsDequesPrivateG Σ `{zoo_G : !ZooG Σ} := {
}.

Definition ws_deques_private_Σ := #[
].
#[global] Instance subG_ws_deques_private_Σ Σ `{zoo_G : !ZooG Σ} :
  subG ws_deques_private_Σ Σ →
  WsDequesPrivateG Σ.
Proof.
  (* solve_inG. *)
Qed.

Section ws_deques_private_G.
  Context `{ws_deques_private_G : WsDequesPrivateG Σ}.

  (* #[local] Definition ws_deques_private_inv_inner deques v_flags v_requests v_responses sz : iProp Σ := *)
  (*   ∃ flags requests responses vss, *)
  (*   array_model v_flags (DfracOwn 1) flags ∗ *)
  (*   array_model v_requests (DfracOwn 1) requests ∗ *)
  (*   array_model v_reponses (DfracOwn 1) responses ∗ *)
  (*   ( [∗ list] deque; vs ∈ deques; vss, *)
  (*     deque_model deque vs *)
  (*   ) ∗ *)
  (*   ( [∗ list] flag; vs ∈ flags; vss, *)
  (*     ⌜flag = #(bool_decide (vs ≠ []))⌝ *)
  (*     ⌜flag = #true ∨ flag = #false ∧ vs = []⌝ *)
  (*   ) *)
  (* . *)
  (* Definition ws_deques_private_inv t ι sz : iProp Σ := *)
  (*   ∃ deques flags requests responses, *)
  (*   ⌜t = (v_deques, v_flags, v_requests, v_responses)%V⌝ ∗ *)
  (*   array_model v_deques DfracDiscarded deques ∗ *)
  (*   inv ι (ws_deques_private_inv_inner deques v_flags v_requests v_responses sz). *)

  Definition ws_deques_private_inv t (ι : namespace) (sz : nat) : iProp Σ.
  Proof. Admitted.

  Definition ws_deques_private_model t vss : iProp Σ.
  Proof. Admitted.

  Definition ws_deques_private_owner t (i : nat) status : iProp Σ.
  Proof. Admitted.

  #[global] Instance ws_deques_private_model_timeless t vss :
    Timeless (ws_deques_private_model t vss).
  Proof.
  Admitted.
  #[global] Instance ws_deques_private_inv_persistent t ι sz :
    Persistent (ws_deques_private_inv t ι sz).
  Proof.
  Admitted.

  Lemma ws_deques_private_inv_agree t ι sz1 sz2 :
    ws_deques_private_inv t ι sz1 -∗
    ws_deques_private_inv t ι sz2 -∗
    ⌜sz1 = sz2⌝.
  Proof.
  Admitted.

  Lemma ws_deques_private_inv_owner t ι sz i status :
    ws_deques_private_inv t ι sz -∗
    ws_deques_private_owner t i status -∗
    ⌜i < sz⌝.
  Proof.
  Admitted.
  Lemma ws_deques_private_owner_exclusive t i status1 status2 :
    ws_deques_private_owner t i status1 -∗
    ws_deques_private_owner t i status2 -∗
    False.
  Proof.
  Admitted.

  Lemma ws_deques_private_create_spec ι sz :
    (0 ≤ sz)%Z →
    {{{
      True
    }}}
      ws_deques_private_create #sz
    {{{ t,
      RET t;
      ws_deques_private_inv t ι ₊sz ∗
      ws_deques_private_model t (replicate ₊sz []) ∗
      [∗ list] i ∈ seq 0 ₊sz,
        ws_deques_private_owner t i Nonblocked
    }}}.
  Proof.
  Admitted.

  Lemma ws_deques_private_size_spec t ι sz :
    {{{
      ws_deques_private_inv t ι sz
    }}}
      ws_deques_private_size t
    {{{
      RET #sz;
      True
    }}}.
  Proof.
  Admitted.

  Lemma ws_deques_private_block_spec t ι sz i i_ :
    i = ⁺i_ →
    {{{
      ws_deques_private_inv t ι sz ∗
      ws_deques_private_owner t i_ Nonblocked
    }}}
      ws_deques_private_block t #i
    {{{
      RET ();
      ws_deques_private_owner t i_ Blocked
    }}}.
  Proof.
  Admitted.

  Lemma ws_deques_private_unblock_spec t ι sz i i_ :
    i = ⁺i_ →
    {{{
      ws_deques_private_inv t ι sz ∗
      ws_deques_private_owner t i_ Blocked
    }}}
      ws_deques_private_unblock t #i
    {{{
      RET ();
      ws_deques_private_owner t i_ Nonblocked
    }}}.
  Proof.
  Admitted.

  Lemma ws_deques_private_push_spec t ι sz i i_ v :
    i = ⁺i_ →
    <<<
      ws_deques_private_inv t ι sz ∗
      ws_deques_private_owner t i_ Nonblocked
    | ∀∀ vss,
      ws_deques_private_model t vss
    >>>
      ws_deques_private_push t #i v @ ↑ι
    <<<
      ∃∃ vs,
      ⌜vss !! i_ = Some vs⌝ ∗
      ws_deques_private_model t (<[i_ := vs ++ [v]]> vss)
    | RET ();
      ws_deques_private_owner t i_ Nonblocked
    >>>.
  Proof.
  Admitted.

  Lemma ws_deques_private_pop_spec t ι sz i i_ :
    i = ⁺i_ →
    <<<
      ws_deques_private_inv t ι sz ∗
      ws_deques_private_owner t i_ Nonblocked
    | ∀∀ vss,
      ws_deques_private_model t vss
    >>>
      ws_deques_private_pop t #i @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ⌜vss !! i_ = Some []⌝ ∗
          ws_deques_private_model t vss
      | Some v =>
          ∃ vs,
          ⌜vss !! i_ = Some (vs ++ [v])⌝ ∗
          ws_deques_private_model t (<[i_ := vs]> vss)
      end
    | RET o;
      ws_deques_private_owner t i_ Nonblocked
    >>>.
  Proof.
  Admitted.

  Lemma ws_deques_private_steal_to_spec t ι (sz : nat) i i_ j :
    i = ⁺i_ →
    (0 ≤ j < sz)%Z →
    <<<
      ws_deques_private_inv t ι sz ∗
      ws_deques_private_owner t i_ Blocked
    | ∀∀ vss,
      ws_deques_private_model t vss
    >>>
      ws_deques_private_steal_to t #i #j @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_deques_private_model t vss
      | Some v =>
          ∃ vs,
          ⌜vss !! ₊j = Some (v :: vs)⌝ ∗
          ws_deques_private_model t (<[₊j := vs]> vss)
      end
    | RET o;
      ws_deques_private_owner t i_ Blocked
    >>>.
  Proof.
  Admitted.

  Lemma ws_deques_private_steal_as_spec t ι sz i i_ round :
    i = ⁺i_ →
    0 < sz →
    <<<
      ws_deques_private_inv t ι sz ∗
      ws_deques_private_owner t i_ Blocked ∗
      random_round_model' round (sz - 1) (sz - 1)
    | ∀∀ vss,
      ws_deques_private_model t vss
    >>>
      ws_deques_private_steal_as t #i round @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_deques_private_model t vss
      | Some v =>
          ∃ j vs,
          ⌜₊i ≠ j⌝ ∗
          ⌜vss !! j = Some (v :: vs)⌝ ∗
          ws_deques_private_model t (<[j := vs]> vss)
      end
    | RET o;
      ∃ n,
      ws_deques_private_owner t i_ Blocked ∗
      random_round_model' round (sz - 1) n
    >>>.
  Proof.
  Admitted.
End ws_deques_private_G.

#[global] Opaque ws_deques_private_create.
#[global] Opaque ws_deques_private_size.
#[global] Opaque ws_deques_private_block.
#[global] Opaque ws_deques_private_unblock.
#[global] Opaque ws_deques_private_push.
#[global] Opaque ws_deques_private_pop.
#[global] Opaque ws_deques_private_steal_to.
#[global] Opaque ws_deques_private_steal_as.

#[global] Opaque ws_deques_private_inv.
#[global] Opaque ws_deques_private_model.
#[global] Opaque ws_deques_private_owner.
