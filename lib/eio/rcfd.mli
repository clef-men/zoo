type t

val make :
  Unics.file_descr -> t

val close :
  t -> bool

val remove :
  t -> Unics.file_descr option

val use :
  t -> (unit -> 'a) -> (Unics.file_descr -> 'a) -> 'a

val is_open :
  t -> bool

val peek :
  t -> Unics.file_descr option
