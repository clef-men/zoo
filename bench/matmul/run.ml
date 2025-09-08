open Bench

module Make
  (Pool : Pool.S)
= struct
  module Matrix_parallel =
    Matrix.Parallel(Pool)

  let main sz ctx =
    let mat1 = Matrix.create sz in
    let mat2 = Matrix.create sz in
    let mat3 = Matrix.create sz in
    Matrix_parallel.apply ctx mat1 (fun i j -> Float.of_int (i + j));
    Matrix_parallel.apply ctx mat2 (fun i j -> Float.of_int (i * j));
    Matrix_parallel.fill ctx mat3 0.0 ;
    Pool.for_ ctx ~beg:0 ~end_:sz (fun _ctx i ->
      for j = 0 to sz - 1 do
        for k = 0 to sz - 1 do
          let v = Matrix.get mat3 i j in
          let v = v +. Matrix.get mat1 i k *. Matrix.get mat2 k j in
          Matrix.set mat3 i j v
        done
      done
    )
end

let pool =
  Pool.impl_of_string Sys.argv.(1)

let size =
  int_of_string Sys.argv.(2)

let num_domains =
  let default = Domain.recommended_domain_count () - 1 in
  Option.value ~default (Utils.get_int_param "EXTRA_DOMAINS")

let () =
  let (module Pool) = pool in
  let module M = Make(Pool) in
  let pool = Pool.create ~num_domains () in
  let _ = Pool.run pool (M.main size) in
  Pool.kill pool
