open Bench

let dls =
  Domain.DLS.new_key Random.State.make_self_init

module Make
  (Pool : Pool.S)
= struct
  let[@inline] row sz i =
    i / sz
  let[@inline] col sz i =
    i mod sz

  let[@inline] index sz x y =
    x * sz + y

  let create ctx sz fn =
    let len = sz * sz in
    let mat = Array.create_float len in
    Pool.for_ ctx ~beg:0 ~end_:len (fun _ctx i ->
      fn (row sz i) (col sz i)
      |> Array.unsafe_set mat i
    ) ;
    mat

  let get sz mat x y =
    Array.unsafe_get mat (index sz x y)
  let set sz mat x y v =
    Array.unsafe_set mat (index sz x y) v

  let copy ctx mat =
    let len = Array.length mat in
    let mat' = Array.create_float len in
    Pool.divide ctx ~beg:0 ~end_:len (fun _ctx i sz ->
      Array.blit mat i mat' i sz
    ) ;
    mat'

  let lu ctx sz mat0 =
    let mat = copy ctx mat0 in
    for k = 0 to sz - 2 do
      Pool.for_ ctx ~beg:(k + 1) ~end_:sz @@ fun _ctx x ->
        let factor = get sz mat x k /. get sz mat k k in
        for y = k + 1 to sz - 1 do
          (get sz mat x y -. factor *. get sz mat k y)
          |> set sz mat x y
        done ;
        set sz mat x k factor
    done ;
    mat

  let main sz ctx =
    let mat =
      create ctx sz @@ fun _ _ ->
        (Random.State.float (Domain.DLS.get dls) 100.0) +. 1.0
    in
    let lu = lu ctx sz mat in
    let _ =
      create ctx sz @@ fun x y ->
        if y < x then
          get sz lu x y
        else if x = y then
          1.0
        else
          0.0
    in
    let _ =
      create ctx sz @@ fun x y ->
        if x <= y then
          get sz lu x y
        else
          0.0
    in
    ()
end

let pool : (module Pool.S) =
  let open Pool in
  match Sys.argv.(1) with
  | "parabs" ->
      (module Parabs)
  | "domainslib" ->
      (module Domainslib)
  | "moonpool-fifo" ->
      (module Moonpool_fifo)
  | "moonpool-ws" ->
      (module Moonpool_ws)
  | _ ->
      failwith "illegal method"

let size =
  int_of_string Sys.argv.(2)

let num_domains =
  match Sys.argv.(3) with
  | num_domains ->
      int_of_string num_domains
  | exception Invalid_argument _ ->
      Domain.recommended_domain_count () - 1

let () =
  let (module Pool) = pool in
  let module M = Make(Pool) in
  let pool = Pool.create ~num_domains () in
  let _ = Pool.run pool (M.main size) in
  Pool.kill pool
