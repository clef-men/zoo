type t =
  | A
  | B of { mutable f1: int; f2: int }

let test1 t =
  match t with
  | A ->
      0
  | B r ->
      r.f1

let test2 t =
  match t with
  | A ->
      0
  | B r as t ->
      let _ = t in
      r.f1

let test3 t =
  match t with
  | A ->
      A
  | B r ->
      B r

let test4 t =
  match t with
  | A ->
      A
  | B r as t ->
      let _ = t in
      B r
