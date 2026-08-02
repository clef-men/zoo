type 'a t =
  'a Xdeque.t

let create =
  Xdeque.create

let is_empty =
  Xdeque.is_empty

let push_front t v =
  Xdeque.push_front t { prev= t; next= t; data= v }

let push_back t v =
  Xdeque.push_back t { prev= t; next= t; data= v }

let pop_front t =
  match Xdeque.pop_front t with
  | None ->
      None
  | Some node ->
      Some node.data

let pop_back t =
  match Xdeque.pop_back t with
  | None ->
      None
  | Some node ->
      Some node.data

let iter fn =
  Xdeque.iter (fun node -> fn node.Xdeque.data)
