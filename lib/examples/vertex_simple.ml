let main ~num_worker a b c d =
  let ivar = Ivar_3.create () in

  let vtx_a = Vertex.create' @@ fun _ctx -> a () in
  let vtx_b = Vertex.create' @@ fun _ctx -> b () in
  let vtx_c = Vertex.create' @@ fun _ctx -> c () in
  let vtx_d = Vertex.create' @@ fun ctx -> d () ; Ivar_3.notify ivar ctx in

  Vertex.precede vtx_a vtx_b ;
  Vertex.precede vtx_a vtx_c ;
  Vertex.precede vtx_b vtx_d ;
  Vertex.precede vtx_c vtx_d ;

  Pool.run ~num_worker (fun ctx ->
    Vertex.release ctx vtx_d ;
    Vertex.release ctx vtx_c ;
    Vertex.release ctx vtx_b ;
    Vertex.release ctx vtx_a ;
    Pool.wait_ivar ctx ivar
  )
