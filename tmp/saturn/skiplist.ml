type ('k, 'v, _) node =
  | Null :
    ('k, 'v, [> `Null]) node
  | Node :
    'k * 'v * ('k, 'v) links ->
    ('k, 'v, [> `Node]) node
  | Mark :
    ('k, 'v, [< `Null | `Node]) ->
    ('k, 'v, [> `Mark]) node

and ('k, 'v) link =
  | Link :
    ('k, 'v, [< `Null | `Node | `Mark]) node ->
    ('k, 'v) link
[@@unboxed]

and ('k, 'v) links =
  ('k, 'v) link array

type ('k, 'v) t =
  { compare: 'k -> 'k -> int;
    root: ('k, 'v) links;
  }

let[zoo.assume] random_height max_height =
  let m = (1 lsl max_height) - 1 in
  let x = Random.bits () land m in
  if x = 1 then
    get_random_height max_height
  else
    let n = 0 in
    let n, x = if 0xFFFF < x then n + 0x10, x lsr 0x10 else n, x in
    let n, x = if 0x00FF < x then n + 0x08, x lsr 0x08 else n, x in
    let n, x = if 0x000F < x then n + 0x04, x lsr 0x04 else n, x in
    let n, x = if 0x0003 < x then n + 0x02, x lsr 0x02 else n, x in
    let n, _ = if 0x0001 < x then n + 0x01, x lsr 0x01 else n, x in
    max_height - n

let create max_height compare =
  { compare;
    root= Array.make max_height (Link Null);
  }

let rec find_node_1 t key prev lvl : _ -> (_, _, [< `Null | `Node]) node = function
  | Link (Mark _) ->
      find_node t key
  | Link Null ->
      if 0 < lvl then
        find_node_2 t key prev (lvl - 1)
      else
        Null
  | Link (Node (key', _, next) as curr) ->
      match Array.unsafe_get next lvl with
      | Link (Mark node) ->
          if Array.unsafe_cas prev lvl (Link curr) (Link node) then
            find_node_1 t key prev lvl (Link node)
          else
            find_node_2 t key prev lvl
      | next ->
          let cmp = t.compare key key' in
          if 0 < cmp then
            find_node_1 t key next lvl next
          else if 0 == cmp then
            curr
          else if 0 < lvl then
            find_node_2 t key prev (lvl - 1)
          else
            Null
and find_node_2 t key prev lvl =
  find_node_1 t key prev lvl (Array.unsafe_get prev lvl)
and find_node t key =
  let prev = t.root in
  let lvl = Array.size prev - 1 in
  find_node_2 t key prev lvl

let find t key =
  match find_node t key with
  | Null ->
      None
  | Node (_, value, _) ->
      Some value

let mem t key =
  match find_node t key with
  | Null ->
      false
  | Node _ ->
      true

let rec find_path_1 t key prev preds succs lvl low = function
  | Link (Mark _) ->
      find_path t key preds succs low
  | Link Null ->
      if lvl < Array.size preds then (
        Array.unsafe_set preds lvl prev ;
        Array.unsafe_set succs lvl (Link Null)
      ) ;
      low < lvl && find_path_2 t key prev preds succs (lvl - 1) low
  | Link (Node (key', _, next) as curr) ->
      match Array.unsafe_get next lvl with
      | Link (Mark node) ->
          if Array.unsafe_cas prev lvl (Link curr) (Link node) then
            find_path_1 t key prev preds succs lvl low (Link node)
          else
            find_path_2 t key prev preds succs lvl low
      | next ->
          let cmp = t.compare key key' in
          if 0 < cmp then
            find_path_1 t key next preds succs lvl low next
          else (
            if lvl < Array.size preds then (
              Array.unsafe_set preds lvl prev ;
              Array.unsafe_set succs lvl (Link curr)
            ) ;
            if low < lvl then (
              find_path_2 t key prev preds succs (lvl - 1) low
            ) else (
              0 = cmp
            )
          )
and find_path_2 t key prev preds succs lvl low =
  find_path_1 t key prev preds succs lvl low (Array.unsafe_get prev lvl)
and find_path t key preds succs low =
  let prev = t.root in
  let lvl = Array.size prev - 1 in
  find_path_2 t key prev preds succs lvl low

let[@inline] is_marked = function
  | Link (Mark _) ->
      true
  | _ ->
      false

let rec update_lvls t key preds succs next node lvl =
  if lvl == Array.size next then (
    if is_marked @@ Array.unsafe_get next (lvl - 1) then
      find_node t key |> ignore ;
    true
  ) else if
    let succ = Array.unsafe_get succs lvl in
    Array.unsafe_cas (Array.unsafe_get preds lvl) lvl succ (Link node)
  then (
    update_lvls t key preds succs next node (1 + lvl)
  ) else (
    find_path t key preds succs lvl |> ignore ;
    update_nexts t key preds succs next node lvl (Array.size next - 1)
  )
and update_nexts t key preds succs next node lvl lvl' =
  if lvl' < lvl then
    update_lvls t key preds succs next node lvl lvl
  else
    match Array.unsafe_get next lvl' with
    | Link (Mark _) ->
        find_node t key |> ignore ;
        true
    | before ->
        let succ = Array.unsafe_get succs lvl' in
        if before == succ || Array.unsafe_cas next lvl' before succ then
          update_nexts t key preds succs next node lvl (lvl' - 1)
        else
          update_lvls t key preds succs next node lvl
let rec add t key value preds succs =
  not (find_path t key preds succs 0)
  &&
  let next = Array.clone succs in
  let node = Node (key, value, next) in
  if
    let succ = Array.unsafe_get succs 0 in
    Array.unsafe_cas (Array.unsafe_get preds 0) 0 succ (Link node)
  then
    update_lvls t key preds succs next node 1
  else
    add t key value preds succs
let add t key value =
  let height = random_height (Array.size t.root) in
  let preds = Array.unsafe_alloc height in
  let succs = Array.make height (Link Null) in
  add t key value preds succs

let rec remove_1 t key next lvl = function
  | Link (Mark _) ->
      if lvl = 0 then
        false
      else
        remove_2 t key next (lvl - 1)
  | Link (_ as succ) ->
      if Array.unsafe_cas next lvl (Link succ) (Link (Mark succ)) then
        if lvl = 0 then (
          find_node t key |> ignore ;
          true
        ) else (
          remove_2 t key next (lvl - 1)
        )
      else
        remove_2 t key next lvl
and remove_2 t key next lvl =
  remove_1 t key next lvl (Array.unsafe_get next lvl)
let remove t key =
  match find_node t key with
  | Null ->
      false
  | Node (_, _, next) ->
      let lvl = Array.size next - 1 in
      remove_2 t key next lvl
