module Bucket = struct
  type ('k, 'v, _) t_tagged =
    | Nil :
      ('k, 'v, [> `Nil]) t_tagged
    | Cons :
      { key: 'k
      ; mutable data: 'v
      ; mutable next: ('k, 'v) t
      } ->
      ('k, 'v, [> `Cons]) t_tagged

  and ('k, 'v) t =
    ('k, 'v, [`Nil | `Cons]) t_tagged

  let rec assoc ~equal key = function
    | Nil ->
        None
    | Cons cons_r ->
        if equal key cons_r.key then
          Some cons_r.data
        else
          assoc ~equal key cons_r.next

  let mem ~equal key t =
    assoc ~equal key t != None

  let add key v t =
    Cons { key; data= v; next= t }

  let rec remove ~equal key (prev : (_, _, [`Cons]) t_tagged) = function
    | Nil ->
        None
    | Cons cons_r as t ->
        if equal key cons_r.key then (
          let Cons prev_r = prev in
          prev_r.next <- cons_r.next ;
          Some cons_r.data
        ) else (
          remove ~equal key t cons_r.next
        )
  let remove ~equal ts i key = function
    | Nil ->
        None
    | Cons cons_r as t ->
        if equal key cons_r.key then (
          Array.unsafe_set ts i cons_r.next ;
          Some cons_r.data
        ) else (
          remove ~equal key t cons_r.next
        )

  let rec replace ~equal key v = function
    | Nil ->
        None
    | Cons cons_r ->
        if equal key cons_r.key then (
          let v' = cons_r.data in
          cons_r.data <- v ;
          Some v'
        ) else (
          replace ~equal key v cons_r.next
        )

  let rec filter pred = function
    | Nil ->
        Nil
    | Cons cons_r ->
        if pred cons_r.key then
          Cons { cons_r with next= filter pred cons_r.next }
        else
          filter pred cons_r.next
  [@@tail_mod_cons]
end

type ('k, 'v) t =
  { hash: 'k -> int
  ; equal: 'k -> 'k -> bool
  ; mutable buckets: ('k, 'v) Bucket.t array
  ; mutable mask: int
  ; mutable size: int
  }

let min_capacity =
  16
let max_capacity =
  Sys.max_array_length

let create ~hash ~equal =
  { hash
  ; equal
  ; buckets= Array.make min_capacity Bucket.Nil
  ; mask= min_capacity - 1
  ; size= 0
  }

let[@inline] size t =
  t.size

let[@inline] index t key =
  t.hash key land t.mask

let find t key =
  let i = index t key in
  let bucket = Array.unsafe_get t.buckets i in
  Bucket.assoc ~equal:t.equal key bucket

let mem t key =
  find t key != None

let resize t =
  let cap = Array.size t.buckets in
  let new_cap = cap lsl 1 in
  if new_cap < t.size && new_cap <= max_capacity then
    let new_buckets = Array.make new_cap Bucket.Nil in
    for i = 0 to cap - 1 do
      let bucket = Array.unsafe_get t.buckets i in
      let new_bucket_1 = Bucket.filter (fun key -> t.hash key land cap == 0) bucket in
      let new_bucket_2 = Bucket.filter (fun key -> t.hash key land cap == cap) bucket in
      Array.unsafe_set new_buckets i new_bucket_1 ;
      Array.unsafe_set new_buckets (i + cap) new_bucket_2
    done ;
    t.buckets <- new_buckets ;
    t.mask <- new_cap - 1

let add t key v =
  let i = index t key in
  let bucket = Array.unsafe_get t.buckets i in
  if Bucket.mem ~equal:t.equal key bucket then (
    false
  ) else (
    Array.unsafe_set t.buckets i (Bucket.add key v bucket) ;
    t.size <- t.size + 1 ;
    resize t ;
    true
  )

let find_and_remove t key =
  let i = index t key in
  let bucket = Array.unsafe_get t.buckets i in
  match Bucket.remove ~equal:t.equal t.buckets i key bucket with
  | None ->
      None
  | Some _ as res ->
      t.size <- t.size - 1 ;
      res

let remove t key =
  find_and_remove t key |> ignore

let find_and_replace t key v =
  let i = index t key in
  let bucket = Array.unsafe_get t.buckets i in
  match Bucket.replace ~equal:t.equal key v bucket with
  | Some _ as res ->
      res
  | None ->
      Array.unsafe_set t.buckets i (Bucket.add key v bucket) ;
      t.size <- t.size + 1 ;
      resize t ;
      None

let replace t key v =
  find_and_replace t key v |> ignore
