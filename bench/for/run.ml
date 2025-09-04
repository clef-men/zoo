open Bench

let work _ctx _i =
  for _ = 1 to 1024 do
    Sys.opaque_identity ()
  done

module Make
  (Pool : Pool.S)
= struct
  let main ~cutoff n ctx =
    Pool.for_ ctx work ~beg:0 ~end_:n ~chunk:cutoff
end

let pool =
  Pool.impl_of_string Sys.argv.(1)

let cutoff =
  int_of_string Sys.argv.(2)

let input =
  int_of_string Sys.argv.(3)

let num_domains =
  let default = Domain.recommended_domain_count () - 1 in
  Utils.get_int_param "EXTRA_DOMAINS" ~default

let () =
  let (module Pool) = pool in
  let module M = Make(Pool) in
  let pool = Pool.create ~num_domains () in
  let _ = Pool.run pool (M.main ~cutoff input) in
  Pool.kill pool
