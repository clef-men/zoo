let main num_dom a b c d =
  let flag = Mpsc_flag.create () in

  let vtx_a = Vertex.create' @@ fun _ctx -> a () in
  let vtx_b = Vertex.create' @@ fun _ctx -> b () in
  let vtx_c = Vertex.create' @@ fun _ctx -> c () in
  let vtx_d = Vertex.create' @@ fun _ctx -> d () ; Mpsc_flag.set flag in

  Vertex.precede vtx_a vtx_b ;
  Vertex.precede vtx_a vtx_c ;
  Vertex.precede vtx_b vtx_d ;
  Vertex.precede vtx_c vtx_d ;

  let pool = Pool.create num_dom in
  Pool.run pool (fun ctx ->
    Vertex.release ctx vtx_d ;
    Vertex.release ctx vtx_c ;
    Vertex.release ctx vtx_b ;
    Vertex.release ctx vtx_a ;
    Pool.wait_until ctx (fun () -> Mpsc_flag.get flag)
  ) ;
  Pool.kill pool
