open Bench

module Make
  (Pool : Pool.S)
= struct
  let main sz ctx =
    let arr = Array.make sz 0 in
    Pool.for_ ctx ~beg:0 ~end_:sz @@ fun _ctx i ->
      Array.unsafe_set arr i i
end

let pool =
  Pool.impl_of_string Sys.argv.(1)

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
