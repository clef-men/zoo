type 'a t =
  | Gnil
  | Gcons of 'a * 'a t [@generative]

let rec rev_app t1 t2 =
  match t1 with
  | Gnil ->
      t2
  | Gcons (v, t1) ->
      rev_app t1 (Gcons (v, t2))

let rev t =
  rev_app t Gnil
