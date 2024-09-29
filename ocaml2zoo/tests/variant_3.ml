type t =
  | A
  | B of { f1: int; f2: int }

let test1 () =
  B { f1= 0; f2= 0 }

let test2 t =
  match t with
  | A ->
      0
  | B { f1; f2 } ->
      f1 + f2

let test3 t =
  match t with
  | A ->
      0
  | B { f1; f2 } as t ->
      let _ = t in
      f1 + f2

let test4 t =
  match t with
  | A ->
      0
  | B { f1= x1; f2= x2 } ->
      x1 + x2

let test5 t =
  match t with
  | A ->
      0
  | B { f1= x1; f2= x2 } as t ->
      let _ = t in
      x1 + x2

let test6 t =
  match t with
  | A ->
      0
  | B r ->
      r.f1 + r.f2

let test7 t =
  match t with
  | A ->
      0
  | B r as t ->
      let _ = t in
      r.f1 + r.f2
