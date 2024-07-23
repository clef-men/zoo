type t =
  | A
  | B of int
  | C of int * int

let test1 t =
  match t with
  | A ->
      0
  | B i ->
      i
  | C (i1, i2) ->
      i1 + i2

let test2 t =
  match t with
  | A ->
      ()
  | B _ ->
      ()
  | C _ ->
      ()

let test3 t =
  match t with
  | A ->
      A
  | B _ as t ->
      t
  | C _ as t ->
      t

let test4 t =
  match t with
  | A ->
      ()
  | _ ->
      ()

let test5 t =
  match t with
  | t ->
      t

let test6 t =
  match t with
  | t' as t ->
      let _ = t in
      t'
