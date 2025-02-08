(* Based on:
   https://github.com/ocaml-multicore/saturn/blob/306bea620cc0cfcc33639c45a56da59add9bdd92/src/spsc_queue/spsc_queue.ml
*)

type 'a t =
  { data: 'a option array;
    mutable front: int [@atomic];
    mutable front_cache: int;
    mutable back: int [@atomic];
    mutable back_cache: int;
  }

let create cap =
  { data= Array.unsafe_make cap None;
    front= 0;
    front_cache= 0;
    back= 0;
    back_cache= 0;
  }

let push t data back =
  let cap = Array.size data in
  let front_cache = t.front_cache in
  if back < front_cache + cap then
    true
  else
    let front = t.front in
    t.front_cache <- front ;
    back < front + cap
let push t v =
  let data = t.data in
  let back = t.back in
  if push t data back then (
    Array.unsafe_cset data back (Some v) ;
    t.back <- back + 1 ;
    false
  ) else (
    true
  )

let pop t front =
  let back_cache = t.back_cache in
  if front < back_cache then
    true
  else
    let back = t.back in
    t.back_cache <- back ;
    front < back
let pop t =
  let front = t.front in
  if pop t front then
    let data = t.data in
    let res = Array.unsafe_cget data front in
    Array.unsafe_cset data front None ;
    t.front <- front + 1 ;
    res
  else
    None
