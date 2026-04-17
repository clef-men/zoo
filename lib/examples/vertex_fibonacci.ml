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

let main ~num_worker n =
  Pool.run ~num_worker (fun ctx ->
    let r = ref 0 in
    let vtx1 = Vertex.create None in
    Vertex.set_task vtx1 (fun ctx -> main ctx vtx1 r n) ;
    Vertex.release ctx vtx1 ;

    let ivar = Ivar_4.create () in
    let vtx2 = Vertex.create' (fun ctx -> Ivar_4.notify ivar ctx ()) in
    Vertex.precede vtx1 vtx2 ;
    Vertex.release ctx vtx2 ;

    Pool.wait_ivar ctx ivar ;
    !r
  )
