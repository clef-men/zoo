type t

val make :
  Unix.file_descr -> t

val close :
  t -> bool

val remove :
  t -> Unix.file_descr option

val use :
  t -> (unit -> 'a) -> (Unix.file_descr -> 'a) -> 'a

val is_open :
  t -> bool

val peek :
  t -> Unix.file_descr option
