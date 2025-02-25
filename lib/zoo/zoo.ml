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

type id =
  dummy

let id () =
  dummy
