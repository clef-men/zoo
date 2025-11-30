(* Based on:
   https://github.com/ocaml/ocaml/pull/14393
*)

type 'a state =
  | Unset of (unit -> 'a)
  | Setting of Mutex.t
  | Set of 'a

type 'a t =
  'a state Atomic.t

let make fn =
  Atomic.make (Unset fn)

let return res =
  Atomic.make (Set res)

let is_set t =
  match Atomic.get t with
  | Set _ ->
      true
  | _ ->
      false
let is_unset t =
  not @@ is_set t

let rec get t =
  match Atomic.get t with
  | Set res ->
      res
  | Setting mtx ->
      Mutex.synchronize mtx ;
      get t
  | Unset fn as state ->
      let mtx = Mutex.create_lock () in
      if Atomic.compare_and_set t state (Setting mtx) then
        let res = fn () in
        Atomic.set t (Set res) ;
        Mutex.unlock mtx ;
        res
      else
        get t
