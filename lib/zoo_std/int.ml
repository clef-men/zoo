type t =
  int

let min =
  Stdlib.Int.min
[@@zoo.overwrite
  fun (n1 : int) (n2 : int) ->
    if n1 < n2 then n1 else n2
]

let max =
  Stdlib.Int.max
[@@zoo.overwrite
  fun (n1 : int) (n2 : int) ->
    if n1 < n2 then n2 else n1
]

let positive_part t =
  max 0 t
