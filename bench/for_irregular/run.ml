open Bench

(* This benchmarks runs a non-parallel version of 'fibonacci'
   on small inputs on a cyclic extension of the input array
     10, 11, 12, 13, ..., limit - 1, limit

   Because 'fibo n' takes exponential time in 'n', most tasks are
   almost immediate, but a few tasks (those close to 'limit') dominate
   the runtime. Furthermore, short/easy tasks are close together in
   the array, and long/hard tasks are also close together, so the
   typical chunking strategiy work poorly -- if the chunk size is too
   large, most domains will have only easy tasks, and one domain will
   have all the hard tasks.

   This benchmark should thus be difficult for implementations with
   larger task-creation or task-switching overhead: small
   cutoffs/chunk sizes are costly, but increasing the chunk/cutoff
   size is bad due to the irregularity of the cost of the tasks.
*)

let rec fibo n =
  if n <= 1 then n
  else fibo (n - 1) + fibo (n - 2)

let work ~data _ctx i =
  ignore (Sys.opaque_identity (fibo data.(i)))

let cycle_between ~base ~limit i =
  base + i mod (limit - base)

module Make
  (Pool : Pool.S)
= struct
  let main ~limit ~cutoff n ctx =
    let base = 10 in
    let data = Array.init n (cycle_between ~base ~limit) in
    Pool.for_ ctx (work ~data) ~beg:0 ~end_:n ?chunk:cutoff
end

let pool =
  Pool.impl_of_string Sys.argv.(1)

let limit =
  Option.value ~default:30
    (Utils.get_int_param "LIMIT")

let cutoff =
  Utils.get_int_param "CUTOFF"

let input =
  int_of_string Sys.argv.(2)

let num_domains =
  let default = Domain.recommended_domain_count () - 1 in
  Option.value ~default (Utils.get_int_param "EXTRA_DOMAINS")

let () =
  let (module Pool) = pool in
  let module M = Make(Pool) in
  let pool = Pool.create ~num_domains () in
  let _ = Pool.run pool (M.main ~cutoff ~limit input) in
  Pool.kill pool
