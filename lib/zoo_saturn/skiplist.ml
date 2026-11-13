type ('k, 'v, _) node =
  | Null :
    ('k, 'v, [> `Null]) node
  | Node :
    'k * 'v * ('k, 'v, [`Null | `Node | `Mark]) node Atomic_array.t ->
    ('k, 'v, [> `Node]) node
  | Mark :
    ('k, 'v, [`Null | `Node | `Mark]) node ->
    ('k, 'v, [> `Mark]) node

type ('k, 'v) t =
  { compare: 'k -> 'k -> int
  ; root: ('k, 'v, [`Null | `Node | `Mark]) node Atomic_array.t
  }

let rec random_height max_height =
  let m = 1 lsl max_height - 1 in
  let x = Random.bits () land m in
  if x = 1 then
    random_height max_height
  else
    let n = 0 in
    let n, x = if 0xFFFF < x then n + 0x10, x lsr 0x10 else n, x in
    let n, x = if 0x00FF < x then n + 0x08, x lsr 0x08 else n, x in
    let n, x = if 0x000F < x then n + 0x04, x lsr 0x04 else n, x in
    let n, x = if 0x0003 < x then n + 0x02, x lsr 0x02 else n, x in
    let n, _ = if 0x0001 < x then n + 0x01, x lsr 0x01 else n, x in
    max_height - n

let create ~max_height ~compare =
  { compare
  ; root= Atomic_array.make max_height Null
  }

let rec find_node_1 t key prevs lvl : _ -> (_, _, [< `Null | `Node]) node = function
  | Mark _ ->
      find_node t key
  | Null ->
      if 0 < lvl then
        find_node_2 t key prevs (lvl - 1)
      else
        Null
  | Node (key', _, nexts) as curr ->
      match Atomic_array.unsafe_get nexts lvl with
      | Mark node ->
          if Atomic_array.unsafe_cas prevs lvl curr node then
            find_node_1 t key prevs lvl node
          else
            find_node_2 t key prevs lvl
      | next ->
          let cmp = t.compare key key' in
          if 0 < cmp then
            find_node_1 t key nexts lvl next
          else if 0 == cmp then
            curr
          else if 0 < lvl then
            find_node_2 t key prevs (lvl - 1)
          else
            Null
and find_node_2 t key prevs lvl =
  find_node_1 t key prevs lvl (Atomic_array.unsafe_get prevs lvl)
and find_node t key =
  let prevs = t.root in
  let lvl = Atomic_array.size prevs - 1 in
  find_node_2 t key prevs lvl

let find_node_resolved t key =
  let proph = Zoo.proph () in
  Zoo.resolve proph (find_node t key)

let find t key =
  match find_node_resolved t key with
  | Null ->
      None
  | Node (_, value, _) ->
      Some value

let mem t key =
  match find_node_resolved t key with
  | Null ->
      false
  | Node _ ->
      true

let rec find_path_1 t key prevs preds succs lvl low = function
  | Mark _ ->
      find_path t key preds succs low
  | Null ->
      if lvl < Array.size preds then (
        Array.unsafe_set preds lvl prevs ;
        Array.unsafe_set succs lvl Null
      ) ;
      low < lvl && find_path_2 t key prevs preds succs (lvl - 1) low
  | Node (key', _, nexts) as curr ->
      match Atomic_array.unsafe_get nexts lvl with
      | Mark node ->
          if Atomic_array.unsafe_cas prevs lvl curr node then
            find_path_1 t key prevs preds succs lvl low node
          else
            find_path_2 t key prevs preds succs lvl low
      | next ->
          let cmp = t.compare key key' in
          if 0 < cmp then
            find_path_1 t key nexts preds succs lvl low next
          else (
            if lvl < Array.size preds then (
              Array.unsafe_set preds lvl prevs ;
              Array.unsafe_set succs lvl curr
            ) ;
            if low < lvl then
              find_path_2 t key prevs preds succs (lvl - 1) low
            else
              0 == cmp
          )
and find_path_2 t key prevs preds succs lvl low =
  find_path_1 t key prevs preds succs lvl low (Atomic_array.unsafe_get prevs lvl)
and find_path t key preds succs low =
  let prevs = t.root in
  let lvl = Atomic_array.size prevs - 1 in
  find_path_2 t key prevs preds succs lvl low

let is_marked = function
  | Mark _ ->
      true
  | _ ->
      false

let rec update_lvls t key preds succs nexts node lvl =
  if lvl == Atomic_array.size nexts then (
    if is_marked (Atomic_array.unsafe_get nexts (lvl - 1)) then
      find_node t key |> ignore ;
    true
  ) else if
    let succ = Array.unsafe_get succs lvl in
    Atomic_array.unsafe_cas (Array.unsafe_get preds lvl) lvl succ node
  then (
    update_lvls t key preds succs nexts node (lvl + 1)
  ) else (
    find_path t key preds succs lvl |> ignore ;
    update_nexts t key preds succs nexts node lvl (Atomic_array.size nexts - 1)
  )
and update_nexts t key preds succs nexts node lvl lvl' =
  if lvl' < lvl then
    update_lvls t key preds succs nexts node lvl
  else
    match Atomic_array.unsafe_get nexts lvl' with
    | Mark _ ->
        find_node t key |> ignore ;
        true
    | before ->
        let succ = Array.unsafe_get succs lvl' in
        if before == succ || Atomic_array.unsafe_cas nexts lvl' before succ then
          update_nexts t key preds succs nexts node lvl (lvl' - 1)
        else
          update_lvls t key preds succs nexts node lvl
let rec add t key value preds succs =
  not (find_path t key preds succs 0)
  &&
  let nexts = Atomic_array.initi (Array.size succs) (fun i -> Array.unsafe_get succs i) in
  let node = Node (key, value, nexts) in
  if
    let succ = Array.unsafe_get succs 0 in
    Atomic_array.unsafe_cas (Array.unsafe_get preds 0) 0 succ node
  then
    update_lvls t key preds succs nexts node 1
  else
    add t key value preds succs
let add t key value =
  let height = random_height (Atomic_array.size t.root) in
  let preds = Array.make height t.root in
  let succs = Array.make height Null in
  add t key value preds succs

let rec remove_1 t key nexts lvl = function
  | Mark _ ->
      if lvl == 0 then
        false
      else
        remove_2 t key nexts (lvl - 1)
  | succ ->
      if Atomic_array.unsafe_cas nexts lvl succ (Mark succ) then
        if lvl == 0 then (
          find_node t key |> ignore ;
          true
        ) else (
          remove_2 t key nexts (lvl - 1)
        )
      else
        remove_2 t key nexts lvl
and remove_2 t key nexts lvl =
  remove_1 t key nexts lvl (Atomic_array.unsafe_get nexts lvl)
let remove t key =
  let proph = Zoo.proph () in
  match Zoo.resolve proph (find_node t key) with
  | Null ->
      false
  | Node (_, _, nexts) ->
      let lvl = Atomic_array.size nexts - 1 in
      remove_2 t key nexts lvl
