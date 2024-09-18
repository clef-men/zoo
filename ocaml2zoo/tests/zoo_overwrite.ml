let test1 =
  ()
[@@zoo.overwrite
  fun () -> ()
]

let rec test2 =
  ()
[@@zoo.overwrite
  fun () -> test2 ()
]
