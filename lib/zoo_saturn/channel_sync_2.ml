type 'a t =
  { channels: 'a Channel_sync_1.t array
  ; capacity_log: int
  }

let create ~cap_log =
  { channels= Array.unsafe_init (1 lsl cap_log) Channel_sync_1.create
  ; capacity_log= cap_log
  }

let rec send t v log =
  if t.capacity_log < log then
    false
  else
    let i = Random.int (1 lsl log) in
    let chan = Array.unsafe_get t.channels i in
    Channel_sync_1.send chan v || send t v (log + 1)
let send t v =
  send t v 0

let rec recv t log =
  if t.capacity_log < log then
    None
  else
    let i = Random.int (1 lsl log) in
    let chan = Array.unsafe_get t.channels i in
    match Channel_sync_1.recv chan with
    | None ->
        recv t (log + 1)
    | Some _ as res ->
        res
let recv t =
  recv t 0
