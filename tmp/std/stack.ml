type 'a t =
  'a Dynarray.t

let create =
  Dynarray.create

let is_empty =
  Dynarray.is_empty

let push =
  Dynarray.push

let pop =
  Dynarray.pop
