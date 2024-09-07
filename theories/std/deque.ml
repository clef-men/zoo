type 'a t =
  'a Xdeque.t

let create =
  Xdeque.create

let is_empty =
  Xdeque.is_empty

let push_front t v =
  Xdeque.push_front t { xdeque_prev= t; xdeque_next= t; xdeque_data= v }

let push_back t v =
  Xdeque.push_back t { xdeque_prev= t; xdeque_next= t; xdeque_data= v }

let pop_front t =
  match Xdeque.pop_front t with
  | None ->
      None
  | Some node ->
      Some node.xdeque_data

let pop_back t =
  match Xdeque.pop_back t with
  | None ->
      None
  | Some node ->
      Some node.xdeque_data

let iter t fn =
  Xdeque.iter t (fun node -> fn node.Xdeque.xdeque_data)
