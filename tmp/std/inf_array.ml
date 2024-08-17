type 'a t =
  { data: 'a array;
    default: 'a;
    mutex: Mutex.t;
  }

let create default =
  let data = Array.create () in
  let proph = Zoo.proph () in
  let t = { data; default; mutex= Mutex.create () } in
  Zoo.resolve () proph t ;
  t

let get t i =
  Mutex.protect t.mutex (fun () ->
    let data = t.data in
    if i < Array.size data then (
      Array.unsafe_get data i
    ) else (
      t.default
    )
  )

let set t i v =
  Mutex.protect t.mutex (fun () ->
    let data = t.data in
    let sz = Array.size data in
    if i < sz then (
      Array.unsafe_set data i v
    ) else (
      let data = Array.grow data (1 + i) t.default in
      t.data <- data ;
      Array.unsafe_set data i v
    )
  )
