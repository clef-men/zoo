let test1 =
  ()
[@@zoo.override
  fun () -> ()
]

let rec test2 =
  ()
[@@zoo.override
  fun () -> test2 ()
]
