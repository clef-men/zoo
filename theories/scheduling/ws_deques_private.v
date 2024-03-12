(* Based on:
   https://inria.hal.science/hal-00863028
*)

From zebre Require Import
  prelude.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Import
  array
  deque.
From zebre.scheduling Require Export
  ws_deques.
From zebre Require Import
  options.

Implicit Types v t : val.
Implicit Types vs : list val.
Implicit Types vss : list (list val).

Parameter array_cas : val.

#[local] Notation "'Blocked'" := (
  in_type "request" 0
)(in custom zebre_tag
).
#[local] Notation "'NoRequest'" := (
  in_type "request" 1
)(in custom zebre_tag
).
#[local] Notation "'Request'" := (
  in_type "request" 2
)(in custom zebre_tag
).

#[local] Notation "'NoResponse'" := (
  in_type "response" 0
)(in custom zebre_tag
).
#[local] Notation "'No'" := (
  in_type "response" 1
)(in custom zebre_tag
).
#[local] Notation "'Yes'" := (
  in_type "response" 2
)(in custom zebre_tag
).

#[local] Notation "'deques'" := (
  in_type "t" 0
)(in custom zebre_field
).
#[local] Notation "'flags'" := (
  in_type "t" 1
)(in custom zebre_field
).
#[local] Notation "'requests'" := (
  in_type "t" 2
)(in custom zebre_field
).
#[local] Notation "'responses'" := (
  in_type "t" 3
)(in custom zebre_field
).

Definition ws_deques_private_create : val :=
  λ: "sz",
    { array_init "sz" deque_create;
      array_make "sz" #false;
      array_make "sz" §Blocked;
      array_make "sz" §NoResponse
    }.

Definition ws_deques_private_size : val :=
  λ: "t",
    array_size "t".{deques}.

#[local] Definition ws_deques_private_block_aux : val :=
  λ: "t" "i" "j",
    array_unsafe_set "t".{responses} "j" §No ;;
    array_unsafe_set "t".{requests} "i" §Blocked.
#[local] Definition ws_deques_private_block : val :=
  λ: "t" "i",
    array_unsafe_set "t".{flags} "i" #false ;;
    let: "requests" := "t".{requests} in
    match: array_unsafe_get "requests" "i" with
    | Blocked =>
        ()
    | NoRequest =>
        ifnot: array_cas "requests" "i" §NoRequest §Blocked then
          match: array_unsafe_get "requests" "i" with
          | Request "j" =>
              ws_deques_private_block_aux "t" "i" "j"
          | _ =>
              () (* unreachable *)
          end
    | Request "j" =>
        ws_deques_private_block_aux "t" "i" "j"
    end.

#[local] Definition ws_deques_private_unblock : val :=
  λ: "t" "i",
    array_unsafe_set "t".{requests} "i" §NoRequest ;;
    array_unsafe_set "t".{flags} "i" "true".

#[local] Definition ws_deques_private_respond : val :=
  λ: "t" "i",
    let: "deque" := array_unsafe_get "t".{deques} "i" in
    let: "requests" := "t".{requests} in
    match: array_unsafe_get "requests" "i" with
    | Request "j" =>
        let: ‘Some "v" := deque_pop_front "deque" in
        array_unsafe_set "t".{responses} "j" ‘Yes{ "v" } ;;
        array_unsafe_set "requests" "i" (if: deque_is_empty "deque" then §Blocked else §NoRequest)
    | _ =>
        ()
    end.

Definition ws_deques_private_push : val :=
  λ: "t" "i" "v",
    deque_push_back (array_unsafe_get "t".{deques} "i") "v" ;;
    if: array_unsafe_get "t".{flags} "i" then (
      ws_deques_private_respond "t" "i"
    ) else (
      ws_deques_private_unblock "t" "i"
    ).

Definition ws_deques_private_pop : val :=
  λ: "t" "i",
    let: "deque" := array_unsafe_get "t".{deques} "i" in
    let: "res" := deque_pop_back "deque" in
    match: "res" with
    | None =>
        ()
    | Some <> =>
        if: deque_is_empty "deque" then (
          ws_deques_private_block "t" "i"
        ) else (
          ws_deques_private_respond "t" "i"
        )
    end ;;
    "res".

#[local] Definition ws_deques_private_steal_to_aux : val :=
  rec: "ws_deques_private_steal_to_aux" "t" "i" :=
    let: "responses" := "t".{responses} in
    match: array_unsafe_get "responses" "i" with
    | NoResponse =>
        "ws_deques_private_steal_to_aux" "t" "i"
    | No =>
        §None
    | Yes "v" =>
        array_unsafe_set "responses" "i" §NoResponse ;;
        ‘Some{ "v" }
    end.
Definition ws_deques_private_steal_to : val :=
  λ: "t" "i" "j",
    if: array_unsafe_get "t".{flags} "j" && array_cas "t".{requests} "j" §NoRequest ‘Request{ "i" } then (
      ws_deques_private_steal_to_aux "t" "i"
    ) else (
      §None
    ).

Class WsDequesPrivateG Σ `{zebre_G : !ZebreG Σ} := {
}.

Definition ws_deques_private_Σ := #[
].
#[global] Instance subG_ws_deques_private_Σ Σ `{zebre_G : !ZebreG Σ} :
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

  Definition ws_deques_private_owner t (i : nat) : iProp Σ.
  Proof. Admitted.

  #[global] Instance ws_deques_private_model_timeless t vss :
    Timeless (ws_deques_private_model t vss).
  Proof.
  Admitted.
  #[global] Instance ws_deques_private_owner_timeless t i :
    Timeless (ws_deques_private_owner t i).
  Proof.
  Admitted.
  #[global] Instance ws_deques_private_inv_persistent t ι sz :
    Persistent (ws_deques_private_inv t ι sz).
  Proof.
  Admitted.

  Lemma ws_deques_private_owner_exclusive t i :
    ws_deques_private_owner t i -∗
    ws_deques_private_owner t i -∗
    False.
  Proof.
  Admitted.

  Lemma ws_deques_private_create_spec ι sz :
    let sz' := Z.to_nat sz in
    (0 ≤ sz)%Z →
    {{{ True }}}
      ws_deques_private_create #sz
    {{{ t,
      RET t;
      ws_deques_private_inv t ι sz' ∗
      ws_deques_private_model t (replicate sz' []) ∗
      [∗ list] i ∈ seq 0 sz',
        ws_deques_private_owner t i
    }}}.
  Proof.
  Admitted.

  Lemma ws_deques_private_size_spec t ι sz :
    {{{
      ws_deques_private_inv t ι sz
    }}}
      ws_deques_private_size t
    {{{
      RET #sz; True
    }}}.
  Proof.
  Admitted.

  Lemma ws_deques_private_push_spec t ι sz i v :
    let i' := Z.to_nat i in
    (0 ≤ i)%Z →
    <<<
      ws_deques_private_inv t ι sz ∗
      ws_deques_private_owner t i'
    | ∀∀ vss,
      ws_deques_private_model t vss
    >>>
      ws_deques_private_push t #i v @ ↑ι
    <<<
      ∃∃ vs,
      ⌜vss !! i' = Some vs⌝ ∗
      ws_deques_private_model t (<[i' := vs ++ [v]]> vss)
    | RET ();
      ws_deques_private_owner t i'
    >>>.
  Proof.
  Admitted.

  Lemma ws_deques_private_pop_spec t ι sz i :
    let i' := Z.to_nat i in
    (0 ≤ i)%Z →
    <<<
      ws_deques_private_inv t ι sz ∗
      ws_deques_private_owner t i'
    | ∀∀ vss,
      ws_deques_private_model t vss
    >>>
      ws_deques_private_pop t #i @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ⌜vss !! i' = Some []⌝ ∗
          ws_deques_private_model t vss
      | Some v =>
          ∃ vs,
          ⌜vss !! i' = Some (vs ++ [v])⌝ ∗
          ws_deques_private_model t (<[i' := vs]> vss)
      end
    | RET o;
      ws_deques_private_owner t i'
    >>>.
  Proof.
  Admitted.

  Lemma ws_deques_private_steal_to_spec t ι (sz : nat) i :
    let i' := Z.to_nat i in
    (0 ≤ i < sz)%Z →
    <<<
      ws_deques_private_inv t ι sz
    | ∀∀ vss,
      ws_deques_private_model t vss
    >>>
      ws_deques_private_steal_to t #i @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ⌜vss !! i' = Some []⌝ ∗
          ws_deques_private_model t vss
      | Some v =>
          ∃ vs,
          ⌜vss !! i' = Some (v :: vs)⌝ ∗
          ws_deques_private_model t (<[i' := vs]> vss)
      end
    | RET o; True
    >>>.
  Proof.
  Admitted.

  Definition ws_deques_private :=
    Build_ws_deques
      ws_deques_private_owner_exclusive
      ws_deques_private_create_spec
      ws_deques_private_size_spec
      ws_deques_private_push_spec
      ws_deques_private_pop_spec
      ws_deques_private_steal_to_spec.
End ws_deques_private_G.

#[global] Opaque ws_deques_private_create.
#[global] Opaque ws_deques_private_size.
#[global] Opaque ws_deques_private_push.
#[global] Opaque ws_deques_private_pop.
#[global] Opaque ws_deques_private_steal_to.

#[global] Opaque ws_deques_private_inv.
#[global] Opaque ws_deques_private_model.
#[global] Opaque ws_deques_private_owner.
