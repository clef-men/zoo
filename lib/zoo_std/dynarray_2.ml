(* Based on:
   https://github.com/ocaml/ocaml/blob/50ce58a33aac9d067ee88af2e84dba02f8f49033/stdlib/dynarray.ml
*)

type 'a slot =
  'a ref option

type 'a t =
  { mutable size: int;
    mutable data: 'a slot array;
  }

let create () =
  { size= 0; data= Array.create () }

let make sz v =
  { size= sz; data= Array.init sz (fun () -> Some (ref v)) }

let initi sz fn =
  { size= sz; data= Array.initi sz (fun i -> Some (ref (fn i))) }

let size t =
  t.size
let data t =
  t.data
let capacity t =
  Array.size (data t)

let set_size t sz =
  t.size <- sz
let set_data t data =
  t.data <- data

let is_empty t =
  size t == 0

let get t i =
  match Array.get (data t) i with
  | None ->
      invalid_arg "index out of bounds"
  | Some ref ->
      !ref

let set t i v =
  match Array.get (data t) i with
  | None ->
      invalid_arg "index out of bounds"
  | Some ref ->
      ref := v

let next_capacity n =
  Int.max 8 (if n <= 512 then 2 * n else n + n / 2)
let reserve t n =
  if not (0 <= n) then
    invalid_arg "negative capacity" ;
  let data = data t in
  let cap = Array.size data in
  if cap < n then (
    let cap = Int.max n (next_capacity cap) in
    let data = Array.unsafe_grow data cap None in
    set_data t data
  )
let reserve_extra t n =
  if not (0 <= n) then
    invalid_arg "negative extra capacity" ;
  reserve t (size t + n)

let try_push t slot =
  let sz = size t in
  let data = data t in
  if Array.size data <= sz then (
    false
  ) else (
    set_size t (sz + 1) ;
    Array.unsafe_set data sz slot ;
    true
  )
let rec push_aux t slot =
  reserve_extra t 1 ;
  if not (try_push t slot) then
    push_aux t slot
let push t v =
  let slot = Some (ref v) in
  if not (try_push t slot) then
    push_aux t slot

let pop t =
  let sz = size t in
  let data = data t in
  if not (sz <= Array.size data) then
    failwith "inconsistency" ;
  if not (0 < sz) then
    invalid_arg "empty dynarray" ;
  let sz = sz - 1 in
  match Array.unsafe_get data sz with
  | None ->
      failwith "inconsistency"
  | Some ref ->
      Array.unsafe_set data sz None ;
      set_size t sz ;
      !ref

let fit_capacity t =
  let sz = size t in
  let data = data t in
  if Array.size data != sz then
    set_data t (Array.shrink data sz)

let reset t =
  set_size t 0 ;
  set_data t (Array.create ())
