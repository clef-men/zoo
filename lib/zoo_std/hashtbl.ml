(* Based on:
   https://github.com/ocaml-multicore/picos/blob/fa1da88bf3643fa18af2357a426e74ea2ac31072/lib/picos_aux.htbl/picos_aux_htbl.ml
*)

type ('k, 'v) bucket =
  | Nil
  | Cons of 'k * 'v * ('k, 'v) bucket

type ('k, 'v) t =
  { hash: 'k -> int;
    equal: 'k -> 'k -> bool;
    mutable buckets: ('k, 'v) bucket array;
    mutable mask: int;
    mutable size: int;
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

let[@zoo.ignore] rec bucket_dissoc equal key = function
  | Nil ->
      raise_notrace Not_found
  | Cons (key', v, bucket) ->
      if equal key key' then
        bucket
      else
        Cons (key', v, bucket_dissoc equal key bucket)
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

let[@tail_mod_cons] rec bucket_merge bucket = function
  | Nil ->
      bucket
  | Cons (key, v, bucket) ->
      Cons (key, v, bucket_merge bucket bucket)

let create hash equal =
  let buckets = Array.make min_buckets Nil in
  let mask = min_buckets - 1 in
  { hash; equal; buckets; mask; size= 0 }

let[@inline] index t key =
  t.hash key land t.mask

let find_node t key =
  let i = index t key in
  let bucket = Array.unsafe_get t.buckets i in
  bucket_assoc t.equal key bucket

let find t key =
  match find_node t key with
  | Nil ->
      None
  | Cons (_, v, _) ->
      Some v

let mem t key =
  find_node t key != Nil

let resize t cap new_cap =
  let new_buckets = Array.make new_cap Nil in
  if cap < new_cap then
    for i = 0 to cap - 1 do
      let bucket = Array.unsafe_get t.buckets i in
      let new_bucket_1 = bucket_filter (fun key -> t.hash key land cap == 0) bucket in
      let new_bucket_2 = bucket_filter (fun key -> t.hash key land cap == cap) bucket in
      Array.unsafe_set new_buckets i new_bucket_1 ;
      Array.unsafe_set new_buckets (i + cap) new_bucket_2
    done
  else
    for i = 0 to new_cap - 1 do
      let bucket_1 = Array.unsafe_get t.buckets i in
      let bucket_2 = Array.unsafe_get t.buckets (i + new_cap) in
      let new_bucket = bucket_merge bucket_1 bucket_2 in
      Array.unsafe_set new_buckets i new_bucket
    done ;
  t.buckets <- new_buckets ;
  t.mask <- new_cap - 1
let resize t delta =
  let sz = t.size in
  t.size <- sz + delta ;
  if Random.bits () land t.mask == 0 then
    let cap = Array.size t.buckets in
    if cap < sz && cap < max_buckets then
      resize t cap (cap lsl 1)
    else if min_buckets < cap && 3 * sz < cap then
      resize t cap (cap lsr 1)

let add t key v =
  let i = index t key in
  let bucket = Array.unsafe_get t.buckets i in
  if bucket_assoc t.equal key bucket != Nil then (
    false
  ) else (
    Array.unsafe_set t.buckets i (Cons (key, v, bucket)) ;
    resize t 1 ;
    true
  )

let remove t key =
  let i = index t key in
  let bucket = Array.unsafe_get t.buckets i in
  match bucket_dissoc t.equal key bucket with
  | None ->
      false
  | Some new_bucket ->
      Array.unsafe_set t.buckets i new_bucket ;
      resize t (-1) ;
      true
