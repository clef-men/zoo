type 'a t =
  { front: 'a list;
    back: 'a list;
  }

let empty =
  { front= []; back= [] }

let is_empty t =
  Lst.is_empty t.front && Lst.is_empty t.back

let push t v =
  { front= t.front; back= v :: t.back }

let pop t =
  match t.front with
  | v :: front ->
      Some (v, { front; back= t.back })
  | [] ->
      match Lst.rev t.back with
      | [] ->
          None
      | v :: front ->
          Some (v, { front; back= [] })
