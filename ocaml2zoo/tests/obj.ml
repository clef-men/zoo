let test () =
  let x = Obj.repr () in
  let _ = Obj.obj x in
  let _ = Obj.magic x in
  let _ = Obj.tag x in
  let _ = Obj.size x in
  let _ = Obj.field x 0 in
  let _ = Obj.set_field x 0 x in
  let _ = Obj.new_block 0 0 in
  ()
