(* Based on:
   https://github.com/ocaml-multicore/saturn/blob/306bea620cc0cfcc33639c45a56da59add9bdd92/src/htbl/htbl.body.ml
*)

[@@@zoo.ignore]

module Bucket = struct
  type ('k, 'v) t =
    | Init
    | Nil
    | Cons of 'k * 'v * ('k, 'v) t
    | Resize of ('k, 'v) t

  let rec assoc ~equal key = function
    | Init ->
        assert false
    | Nil ->
        Nil
    | Cons (key', _, t') as t ->
        if equal key key' then
          t
        else
          assoc ~equal key t'
    | Resize t ->
        assoc ~equal key t

  let[@zoo.ignore] rec dissoc ~equal key = function
    | Nil ->
        raise_notrace Not_found
    | Cons (key', v, t) ->
        if equal key key' then
          t
        else
          Cons (key', v, dissoc ~equal key t)
    | _ ->
        assert false
  let[@zoo.opaque] dissoc ~equal key t =
    try
      Some (dissoc ~equal key t)
    with Not_found ->
      None

  let rec filter pred = function
    | Nil ->
        Nil
    | Cons (key, v, t) ->
        if pred key then
          Cons (key, v, filter pred t)
        else
          filter pred t
    | _ ->
        assert false
  [@@tail_mod_cons]

  let rec merge t1 = function
    | Nil ->
        t1
    | Cons (key, v, t2) ->
        Cons (key, v, merge t1 t2)
    | _ ->
        assert false
  [@@tail_mod_cons]
end

module Buckets : sig
  type ('k, 'v) t

  val make :
    int -> ('k, 'v) Bucket.t -> ('k, 'v) t

  val size :
    ('k, 'v) t -> int

  val get :
    ('k, 'v) t -> int -> ('k, 'v) Bucket.t

  val cas :
    ('k, 'v) t -> int -> ('k, 'v) Bucket.t -> ('k, 'v) Bucket.t -> bool
  val cas_init :
    ('k, 'v) t -> int -> ('k, 'v) Bucket.t -> unit

  val take :
    ('k, 'v) t -> int -> ('k, 'v) Bucket.t
end = struct
  open Bucket

  type ('k, 'v) t =
    ('k, 'v) Bucket.t Atomic_array.t

  let make : int -> ('k, 'v) Bucket.t -> ('k, 'v) t =
    Atomic_array.make

  let size : ('k, 'v) t -> int =
    Atomic_array.size

  let get : ('k, 'v) t -> int -> ('k, 'v) Bucket.t =
    Atomic_array.unsafe_get

  let cas : ('k, 'v) t -> int -> ('k, 'v) Bucket.t -> ('k, 'v) Bucket.t -> bool =
    Atomic_array.unsafe_cas
  let cas_init t i bucket =
    if get t i == Init then
      cas t i Init bucket |> ignore

  let rec take t i backoff =
    match get t i with
    | Init ->
        assert false
    | Resize bucket ->
        bucket
    | bucket ->
        if cas t i bucket (Resize bucket) then
          bucket
        else
          take t i (Backoff.once backoff)
  let take t i =
    take t i Backoff.default
end

type ('k, 'v) status =
  | Normal
  | Resizing of
    { resizing_buckets: ('k, 'v) Buckets.t
    ; resizing_mask: int
    }

type ('k, 'v) state =
  { buckets: ('k, 'v) Buckets.t
  ; mask: int
  ; status: ('k, 'v) status
  }

type ('k, 'v) t =
  { hash: 'k -> int
  ; equal: 'k -> 'k -> bool
  ; sizes: int Atomic_array.t
  ; mutable state: ('k, 'v) state [@atomic]
  }

let[@zoo.opaque] min_buckets =
  1 lsl 4
let[@zoo.opaque] max_buckets =
  Sys.max_array_length

let create ~hash ~equal =
  let sizes = Atomic_array.make (Domain.recommended_domain_count ()) 0 in
  let state =
    { buckets= Buckets.make min_buckets Nil
    ; mask= min_buckets - 1
    ; status= Normal
    }
  in
  { hash; equal; sizes; state }

let[@inline] index t state key =
  t.hash key land state.mask

let find_node t key =
  let state = t.state in
  let i = index t state key in
  let bucket = Buckets.get state.buckets i in
  Bucket.assoc ~equal:t.equal key bucket

let find t key =
  match find_node t key with
  | Nil ->
      None
  | Cons (_, v, _) ->
      Some v
  | _ ->
      assert false

let mem t key =
  find_node t key != Nil

let rec split_buckets t state buckets mask i step =
  let i = (i + step) land mask in
  let bucket = Buckets.take state.buckets i in
  let cap = Buckets.size state.buckets in
  let new_bucket_1 = Bucket.filter (fun key -> t.hash key land cap == 0) bucket in
  let new_bucket_2 = Bucket.filter (fun key -> t.hash key land cap == cap) bucket in
  if t.state != state then (
    false
  ) else (
    Buckets.cas_init buckets i new_bucket_1 ;
    Buckets.cas_init buckets (i + cap) new_bucket_2 ;
    i == 0 || split_buckets t state buckets mask i step
  )

let rec merge_buckets t state buckets mask i step =
  let i = (i + step) land mask in
  let bucket_1 = Buckets.take state.buckets i in
  let bucket_2 = Buckets.take state.buckets (i + Buckets.size buckets) in
  let new_bucket = Bucket.merge bucket_1 bucket_2 in
  if t.state != state then (
    false
  ) else (
    Buckets.cas_init buckets i new_bucket ;
    i == 0 || merge_buckets t state buckets mask i step
  )

let rec finish_as t state =
  match state.status with
  | Normal ->
      ()
  | Resizing { resizing_buckets= buckets; resizing_mask= mask } ->
      if
        let cap = Buckets.size state.buckets in
        let new_cap = Buckets.size buckets in
        let step = Random.bits () lor 1 in
        if cap < new_cap then
          split_buckets t state buckets mask 0 step
        else
          merge_buckets t state buckets mask 0 step
      then
        let new_state = { buckets; mask; status= Normal } in
        if not @@ Atomic.Loc.compare_and_set [%atomic.loc t.state] state new_state then
          finish t
      else
        finish t
and finish t =
  finish_as t t.state

let resize t state new_cap =
  let new_buckets = Buckets.make new_cap Init in
  let new_status =
    Resizing
    { resizing_buckets= new_buckets
    ; resizing_mask= new_cap - 1
    }
  in
  let new_state = { state with status= new_status } in
  if Atomic.Loc.compare_and_set [%atomic.loc t.state] state new_state then
    finish_as t new_state
let resize t state delta =
  let i = Domain.self_index () mod Atomic_array.size t.sizes in
  Atomic_array.unsafe_faa t.sizes i delta |> ignore ;
  if state.status == Normal
  && Random.bits () land state.mask == 0
  && t.state == state
  then
    let sz = Atomic_array.sum t.sizes in
    let cap = Buckets.size state.buckets in
    if cap < sz && cap < max_buckets then
      resize t state (cap lsl 1)
    else if min_buckets < cap && 3 * sz < cap then
      resize t state (cap lsr 1)

let rec add_aux t key v backoff =
  let state = t.state in
  let i = index t state key in
  match Buckets.get state.buckets i with
  | Init ->
      assert false
  | Resize _ ->
      finish t ;
      add t key v
  | bucket ->
      if Bucket.assoc ~equal:t.equal key bucket != Nil then (
        false
      ) else if Buckets.cas state.buckets i bucket (Cons (key, v, bucket)) then (
        resize t state 1 ;
        true
      ) else (
        add_aux t key v (Backoff.once backoff)
      )
and add t key v =
  add_aux t key v Backoff.default

let rec remove_aux t key backoff =
  let state = t.state in
  let i = index t state key in
  match Buckets.get state.buckets i with
  | Init ->
      assert false
  | Resize _ ->
      finish t ;
      remove t key
  | bucket ->
      match Bucket.dissoc ~equal:t.equal key bucket with
      | None ->
          false
      | Some new_bucket ->
          if Buckets.cas state.buckets i bucket new_bucket then (
            resize t state (-1) ;
            true
          ) else (
            remove_aux t key (Backoff.once backoff)
          )
and remove t key =
  remove_aux t key Backoff.default
