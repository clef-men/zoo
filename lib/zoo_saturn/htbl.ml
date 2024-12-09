(* Based on:
   https://github.com/ocaml-multicore/picos/blob/fa1da88bf3643fa18af2357a426e74ea2ac31072/lib/picos_aux.htbl/picos_aux_htbl.ml
*)

type ('k, 'v) bucket =
  | Nil :
    ('k, 'v) bucket
  | Cons :
    'k * 'v * ('k, 'v) bucket ->
    ('k, 'v) bucket
  | Resize :
    { (* actually never mutated but we must prevent sharing *)
      mutable bucket: ('k, 'v) bucket;
    } ->
    ('k, 'v) bucket

type ('k, 'v) buckets =
  ('k, 'v) bucket Atomic_array.t

type ('k, 'v) status =
  | Normal
  | Resizing of
    { resizing_buckets: ('k, 'v) buckets;
      resizing_mask: int;
    }

type ('k, 'v) state =
  { buckets: ('k, 'v) buckets;
    mask: int;
    status: ('k, 'v) status;
  }

type ('k, 'v) t =
  { hash: 'k -> int;
    equal: 'k -> 'k -> bool;
    random: Random.t;
    sizes: int Atomic_array.t;
    mutable state: ('k, 'v) state [@atomic];
  }

let[@zoo.opaque] min_buckets =
  1 lsl 4
let[@zoo.opaque] max_buckets =
  Sys.max_array_length

let rec bucket_assoc equal key = function
  | Nil ->
      Nil
  | Cons (key', _, bucket') as bucket ->
      if equal key key' then
        bucket
      else
        bucket_assoc equal key bucket'
  | Resize bucket_r ->
      bucket_assoc equal key bucket_r.bucket

let[@zoo.exclude] rec bucket_dissoc equal key = function
  | Nil ->
      raise_notrace Not_found
  | Cons (key', v, bucket) ->
      if equal key key' then
        bucket
      else
        Cons (key', v, bucket_dissoc equal key bucket)
  | Resize _ ->
      assert false
let[@zoo.opaque] bucket_dissoc equal key bucket =
  try Some (bucket_dissoc equal key bucket) with Not_found -> None

let[@tail_mod_cons] rec bucket_filter pred = function
  | Nil ->
      Nil
  | Cons (key, v, bucket) ->
      if pred key then
        Cons (key, v, bucket_filter pred bucket)
      else
        bucket_filter pred bucket
  | Resize _ ->
      assert false

let[@tail_mod_cons] rec bucket_merge bucket = function
  | Nil ->
      bucket
  | Cons (key, v, bucket) ->
      Cons (key, v, bucket_merge bucket bucket)
  | Resize _ ->
      assert false

let create hash equal =
  let random = Random.create () in
  let sizes = Atomic_array.make (Domain.recommended_domain_count ()) 0 in
  let state =
    { buckets= Atomic_array.make min_buckets Nil;
      mask= min_buckets - 1;
      status= Normal;
    }
  in
  { hash; equal; random; sizes; state }

let[@inline] index t state key =
  t.hash key land state.mask

let find_node t key =
  let state = t.state in
  let i = index t state key in
  let bucket = Atomic_array.unsafe_get state.buckets i in
  bucket_assoc t.equal key bucket

let find t key =
  match find_node t key with
  | Nil ->
      None
  | Cons (_, v, _) ->
      Some v
  | Resize _ ->
      assert false

let mem t key =
  find_node t key != Nil

let rec take buckets i =
  match Atomic_array.unsafe_get buckets i with
  | Resize bucket_r ->
      bucket_r.bucket
  | bucket ->
      if Atomic_array.unsafe_cas buckets i bucket (Resize { bucket }) then (
        bucket
      ) else (
        Domain.yield () ;
        take buckets i
      )

let rec split_buckets t state buckets mask i step =
  let i = (i + step) land mask in
  let bucket = take state.buckets i in
  let cap = Atomic_array.size state.buckets in
  let new_bucket_1 = bucket_filter (fun key -> t.hash key land cap == 0) bucket in
  let new_bucket_2 = bucket_filter (fun key -> t.hash key land cap == cap) bucket in
  let bucket_1 = Atomic_array.unsafe_get buckets i in
  let bucket_2 = Atomic_array.unsafe_get buckets (i + cap) in
  if t.state != state then (
    false
  ) else (
    begin match bucket_1 with
    | Resize _ ->
        Atomic_array.unsafe_cas buckets i bucket_1 new_bucket_1 |> ignore
    | _ ->
        ()
    end ;
    begin match bucket_2 with
    | Resize _ ->
        Atomic_array.unsafe_cas buckets (i + cap) bucket_2 new_bucket_2 |> ignore
    | _ ->
        ()
    end ;
    i = 0 || split_buckets t state buckets mask i step
  )

let rec merge_buckets t state buckets mask i step =
  let i = (i + step) land mask in
  let buckets_1 = take state.buckets i in
  let buckets_2 = take state.buckets (i + Atomic_array.size buckets) in
  let new_bucket = bucket_merge buckets_1 buckets_2 in
  let bucket = Atomic_array.unsafe_get buckets i in
  if t.state != state then (
    false
  ) else (
    begin match bucket with
    | Resize _ ->
        Atomic_array.unsafe_cas buckets i bucket new_bucket |> ignore
    | _ ->
        ()
    end ;
    i = 0 || merge_buckets t state buckets mask i step
  )

let rec finish_as t state =
  match state.status with
  | Normal ->
      ()
  | Resizing resizing_r ->
      if
        let cap = Atomic_array.size state.buckets in
        let new_cap = Atomic_array.size resizing_r.resizing_buckets in
        let step = Random.bits t.random lor 1 in
        if cap < new_cap then
          split_buckets t state resizing_r.resizing_buckets resizing_r.resizing_mask 0 step
        else
          merge_buckets t state resizing_r.resizing_buckets resizing_r.resizing_mask 0 step
      then
        let new_state =
          { buckets= resizing_r.resizing_buckets;
            mask= resizing_r.resizing_mask;
            status= Normal;
          }
        in
        if not @@ Atomic.Loc.compare_and_set [%atomic.loc t.state] state new_state then
          finish t
      else
        finish t
and finish t =
  finish_as t t.state

let resize t state new_cap =
  let new_buckets = Atomic_array.make new_cap (Resize { bucket= Nil }) in
  let new_status =
    Resizing {
      resizing_buckets= new_buckets;
      resizing_mask= new_cap - 1;
    }
  in
  let new_state = { state with status= new_status } in
  if Atomic.Loc.compare_and_set [%atomic.loc t.state] state new_state then
    finish_as t new_state
let resize t state delta =
  let i = Domain.self_index () mod Atomic_array.size t.sizes in
  Atomic_array.unsafe_faa t.sizes i delta |> ignore ;
  if state.status == Normal
  && Random.bits t.random land state.mask = 0
  && t.state == state
  then
    let sz = Atomic_array.sum t.sizes in
    let cap = Atomic_array.size state.buckets in
    if cap < sz && cap < max_buckets then
      resize t state (cap lsl 1)
    else if min_buckets < cap && 3 * sz < cap then
      resize t state (cap lsr 1)

let rec add t key v =
  let state = t.state in
  let i = index t state key in
  match Atomic_array.unsafe_get state.buckets i with
  | Resize _ ->
      finish t ;
      add t key v
  | bucket ->
      if bucket_assoc t.equal key bucket != Nil then (
        false
      ) else if Atomic_array.unsafe_cas state.buckets i bucket (Cons (key, v, bucket)) then (
        resize t state 1 ;
        true
      ) else (
        Domain.yield () ;
        add t key v
      )

let rec remove t key =
  let state = t.state in
  let i = index t state key in
  match Atomic_array.unsafe_get state.buckets i with
  | Resize _ ->
      finish t ;
      remove t key
  | bucket ->
      match bucket_dissoc t.equal key bucket with
      | None ->
          false
      | Some new_bucket ->
          if Atomic_array.unsafe_cas state.buckets i bucket new_bucket then (
            resize t state (-1) ;
            true
          ) else (
            Domain.yield () ;
            remove t key
          )
