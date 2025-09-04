open Bench

let dls =
  Domain.DLS.new_key Random.State.make_self_init

module Make
  (Pool : Pool.S)
= struct
  module Matrix_parallel =
    Matrix.Parallel(Pool)

  let create ctx sz fn =
    let mat = Matrix.create sz in
    Matrix_parallel.apply ctx mat fn ;
    mat

  let lu ctx sz mat0 =
    let mat = Matrix_parallel.copy ctx mat0 in
    for k = 0 to sz - 2 do
      Pool.for_ ctx ~beg:(k + 1) ~end_:sz @@ fun _ctx i ->
        let factor = Matrix.get mat i k /. Matrix.get mat k k in
        for j = k + 1 to sz - 1 do
          (Matrix.get mat i j -. factor *. Matrix.get mat k j)
          |> Matrix.set mat i j
        done ;
        Matrix.set mat i k factor
    done ;
    mat

  let main sz ctx =
    let mat =
      create ctx sz @@ fun _ _ ->
        (Random.State.float (Domain.DLS.get dls) 100.0) +. 1.0
    in
    let lu = lu ctx sz mat in
    let _ =
      create ctx sz @@ fun i j ->
        if j < i then
          Matrix.get lu i j
        else if i = j then
          1.0
        else
          0.0
    in
    let _ =
      create ctx sz @@ fun i j ->
        if i <= j then
          Matrix.get lu i j
        else
          0.0
    in
    ()
end

let pool =
  Pool.impl_of_string Sys.argv.(1)

let size =
  int_of_string Sys.argv.(2)

let num_domains =
  let default = Domain.recommended_domain_count () - 1 in
  Utils.get_int_param "EXTRA_DOMAINS" ~default

let () =
  let (module Pool) = pool in
  let module M = Make(Pool) in
  let pool = Pool.create ~num_domains () in
  let _ = Pool.run pool (M.main size) in
  Pool.kill pool
