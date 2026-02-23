let rec main ctx vtx r n =
  if n <= 1 then (
    r := n ;
    true
  ) else (
    let r1 = ref 0 in
    let vtx1 = Vertex.create None in
    let n1 = n - 1 in
    Vertex.set_task vtx1 (fun ctx -> main ctx vtx1 r1 n1) ;
    Vertex.release ctx vtx1 ;

    let r2 = ref 0 in
    let vtx2 = Vertex.create None in
    let n2 = n - 2 in
    Vertex.set_task vtx2 (fun ctx -> main ctx vtx2 r2 n2) ;
    Vertex.release ctx vtx2 ;

    Vertex.precede vtx1 vtx ;
    Vertex.precede vtx2 vtx ;
    Vertex.yield vtx @@ fun _ctx ->
    r := !r1 + !r2 ;
    true
  )

let main num_dom n =
  let pool = Pool.create num_dom in
  let res =
    Pool.run pool @@ fun ctx ->
      let r = ref 0 in
      let vtx1 = Vertex.create None in
      Vertex.set_task vtx1 (fun ctx -> main ctx vtx1 r n) ;
      Vertex.release ctx vtx1 ;

      let flag = Mpsc_flag.create () in
      let vtx2 = Vertex.create' (fun _ctx -> Mpsc_flag.set flag) in
      Vertex.precede vtx1 vtx2 ;
      Vertex.release ctx vtx2 ;

      Pool.wait_until ctx (fun () -> Mpsc_flag.get flag) ;
      !r
  in
  Pool.kill pool ;
  res
