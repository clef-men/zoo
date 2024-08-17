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
  if i <= 0 then (
    head t
  ) else (
    get (tail t) (i - 1)
  )

let rec initi_aux sz fn i =
  if sz <= i then (
    []
  ) else (
    let v = fn i in
    v :: initi_aux sz fn (1 + i)
  )
let initi sz fn =
  initi_aux sz fn 0
let init sz fn =
  initi sz (fun _ -> fn ())

let rec foldli_aux t acc fn i
  match t with
  | [] ->
      acc
  | v :: t ->
      foldli_aux t (fn acc i v) fn (1 + i)
let foldli t acc fn =
  foldli_aux t acc fn 0
let foldl t acc fn =
  foldli t acc (fun acc _ -> fn acc)

let rec foldri_aux t fn acc i =
  match t with
  | [] ->
      acc
  | v :: t ->
      fn i v (foldri_aux t fn acc (1 + i))
let foldri t fn acc =
  foldri_aux t fn acc 0
let foldr t fn acc =
  foldri t (fun _ -> fn) acc

let size t =
  foldl t 0 (fun acc _ -> 1 + acc)

let rev_app t1 t2 =
  foldl t1 t2 (fun acc v -> v :: acc)
let rev t =
  rev_app t []

let app t1 t2 =
  foldr t1 (fun v acc -> v :: acc) t2
let snoc t v =
  app t (singleton v)

let iteri t fn =
  foldli t () (fun () -> fn)
let iter t fn =
  iteri t (fun _ -> fn)

let rec mapi_aux t fn i =
  match t with
  | [] ->
      []
  | v :: t ->
      let v = fn i v in
      let t = mapi_aux t fn (1 + i) in
      v :: t
let mapi t fn =
  mapi_aux t fn 0
let map t fn =
  mapi t (fun _ -> fn)
