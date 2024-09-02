let test () =
  let _ = Obj.tag (Obj.repr 0) in
  let _ = Obj.size (Obj.repr 0) in
  let _ = Obj.field (Obj.repr 0) 0 in
  let _ = Obj.set_field (Obj.repr 0) 0 (Obj.repr 0) in
  let _ = Obj.new_block 0 0 in
  ()
