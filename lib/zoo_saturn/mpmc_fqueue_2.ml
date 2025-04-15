[@@@zoo.ignore]

type 'a t =
  { data: 'a Optional.t Atomic_array.t;
    mutable front: int [@atomic];
    mutable back: int [@atomic];
  }

let create sz =
  { data= Atomic_array.make sz Optional.Nothing;
    front= 0;
    back= 0;
  }

let make sz v =
  let data = Atomic_array.make sz Optional.Nothing in
  Atomic_array.unsafe_set data 0 (Something v) ;
  { data;
    front= 0;
    back= 1;
  }

let is_empty t =
  t.back <= t.front

let rec push t v =
  let i = Atomic.Loc.fetch_and_add [%atomic.loc t.back] 1 in
  let data = t.data in
  if Atomic_array.size data <= i then
    false
  else if Atomic_array.unsafe_cas data i Nothing (Something v) then
    true
  else
    push t v

let rec pop t =
  let i = Atomic.Loc.fetch_and_add [%atomic.loc t.front] 1 in
  let data = t.data in
  if Atomic_array.size data <= i then
    None
  else
    match Atomic_array.unsafe_xchg data i Anything with
    | Nothing ->
        Domain.yield () ;
        pop t
    | Anything ->
        assert false
    | Something v ->
        Some v
