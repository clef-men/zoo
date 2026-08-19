let[@zoo.opaque] init =
  Stdlib.Random.self_init

let[@zoo.opaque] bits () =
  Stdlib.Random.nativebits ()
  |> Nativeint.to_int

let[@zoo.opaque] int =
  Stdlib.Random.int

let int_in_range lb ub =
  lb + int (ub - lb)

module State = struct
  type t =
    Stdlib.Random.State.t

  let[@zoo.opaque] create =
    Stdlib.Random.State.make_self_init

  let[@zoo.opaque] bits t =
    t
    |> Stdlib.Random.State.nativebits
    |> Nativeint.to_int

  let[@zoo.opaque] int =
    Stdlib.Random.State.int

  let int_in_range t lb ub =
    lb + int t (ub - lb)
end

module Round = struct
  type t =
    { random: State.t
    ; array: int array
    ; mutable index: int
    }

  let create sz =
    { random= State.create ()
    ; array= Array.unsafe_initi sz (fun i -> i)
    ; index= sz
    }

  let reset t =
    t.index <- Array.size t.array

  let next t =
    let arr = t.array in
    let i = t.index in
    let j = State.int t.random i in
    let res = Array.unsafe_get arr j in
    let i = i - 1 in
    Array.unsafe_set arr j (Array.unsafe_get arr i) ;
    Array.unsafe_set arr i res ;
    t.index <- i ;
    res
end
