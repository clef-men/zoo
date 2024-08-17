type ('a, _) node =
  | Nil :
    ('a, [> `Nil]) node
  | Node :
    { mutable next: ('a, [`Nil | `Node]) node [@atomic];
      mutable data: 'a;
    } ->
    ('a, [> `Node]) node

type 'a t =
  { mutable front: ('a, [`Next]) node [@atomic];
    mutable back: ('a, [`Next]) node [@atomic];
  }

let create () =
  let front = { next= Nil; back= Nil } in
  { front; back= front }

let is_empty t =
  let Node node_ = t.front in
  node_.next == Nil

let rec do_push (node : (_, [`Next]) node) new_back =
  let Node node_ = node in
  let next = node_.next in
  if next == Nil then (
    if not @@ Atomic.Loc.compare_and_set [%atomic.loc node_.next] Nil new_back then (
      Domain.cpu_relax () ;
      do_push node new_back
    )
  ) else (
    do_push next new_back
  )
let rec fix_back t back (new_back : (_, [`Next]) node) =
  let Node new_back_ = new_back in
  if new_back_.next == Nil
  && Atomic.Loc.compare_and_set [%atomic.loc t.back] back new_back
  then (
    Domain.cpu_relax () ;
    fix_back t t.back new_back
  )
let push t v =
  let new_back = Node { next= Nil; data= v } in
  let back = t.back in
  do_push back new_back ;
  fix_back t back new_back

let rec pop t =
  let Node old_front_ as old_front = t.front in
  match old.front_.next with
  | Nil ->
      None
  | Node front_ as front ->
      if Atomic.Loc.compare_and_set [%atomic.loc t.front] old_front front then (
        let v = front_.data in
        front_.data <- Obj.magic () ;
        Some v
      ) else (
        Domain.cpu_relax () ;
        pop t
      )
