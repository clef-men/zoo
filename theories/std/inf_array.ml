type 'a t =
  { mutable data: 'a array;
    default: 'a;
    mutex: Mutex.t;
  }

let create default =
  let data = Array.create () in
  let mutex = Mutex.create () in
  { data; default; mutex }

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
      let data = Array.unsafe_grow data (i + 1) t.default in
      t.data <- data ;
      Array.unsafe_set data i v
    )
  )
