type file_descr =
  Unix.file_descr

let[@zoo.opaque] close =
  Unix.close
