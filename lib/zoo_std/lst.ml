type 'a t =
  'a list

let singleton v =
  [v]

let head = function
  | [] ->
      assert false
  | v :: _ ->
      v

let tail = function
  | [] ->
      assert false
  | _ :: t ->
      t

let is_empty = function
  | [] ->
      true
  | _ :: _ ->
      false

let rec get t i =
  if i <= 0 then
    head t
  else
    get (tail t) (i - 1)

let[@tail_mod_cons] rec initi sz fn i =
  if sz <= i then
    []
  else
    let v = fn i in
    v :: initi sz fn (i + 1)
let initi sz fn =
  initi sz fn 0
let init sz fn =
  initi sz (fun _i -> fn ())

let rec foldli fn i acc t =
  match t with
  | [] ->
      acc
  | v :: t ->
      foldli fn (i + 1) (fn i acc v) t
let foldli fn =
  foldli fn 0
let foldl fn =
  foldli (fun _i -> fn)

let rec foldri fn i t acc =
  match t with
  | [] ->
      acc
  | v :: t ->
      fn i v (foldri fn (i + 1) t acc)
let foldri fn =
  foldri fn 0
let foldr fn =
  foldri (fun _i -> fn)

let size t =
  foldl (fun acc _ -> acc + 1) 0 t

let rev_app t1 t2 =
  foldl (fun acc v -> v :: acc) t2 t1
let rev t =
  rev_app t []

let app t1 t2 =
  foldr (fun v acc -> v :: acc) t1 t2
let snoc t v =
  app t (singleton v)

let iteri fn =
  foldli (fun i () -> fn i) ()
let iter fn =
  iteri (fun _i -> fn)

let[@tail_mod_cons] rec mapi fn i t =
  match t with
  | [] ->
      []
  | v :: t ->
      let v = fn i v in
      v :: mapi fn (i + 1) t
let mapi fn =
  mapi fn 0
let map fn =
  mapi (fun _i -> fn)

let rec forall pred = function
  | [] ->
      true
  | v :: t ->
      pred v && forall pred t

let rec exists pred = function
  | [] ->
      false
  | v :: t ->
      pred v || exists pred t
