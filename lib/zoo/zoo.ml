type dummy =
  Obj.t

let dummy =
  Obj.repr (ref ())

type _ proph =
  dummy

let proph () =
  dummy
let resolve x _ _ =
  x
let resolve' proph v_proph =
  resolve ((fun () -> ()) ()) proph v_proph

type id =
  dummy

let id () =
  dummy
