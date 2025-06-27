type t

[@@@zoo{|
predicate inv
  (t : val)
  (fd : val)
  (Ψ : fraction → Prop)
persistent inv

predicate token
  (t : val)
  (f : fraction)

predicate closing
  (t : val)
persistent closing
|}]

val make :
  Unix.file_descr -> t
[@@zoo{|
  arguments
    fd
  requires
    Ψ 1
  returns
    ?t
  ensures
    inv ?t fd Ψ
|}]

val close :
  t -> bool
[@@zoo{|
  arguments
    t
  requires
    inv t fd Ψ
  , Ψ 1 -∗
      ∃ chars.
      Unix.fd_model fd 1 chars
  returns
    ?b
  ensures
    closing t
|}]
[@@zoo{|
  specification
    closing
  arguments
    t
  requires
    inv t fd Ψ
  , closing t
  returns
    false
|}]

val remove :
  t -> Unix.file_descr option
[@@zoo{|
  arguments
    t
  requires
    inv t fd Ψ
  returns
    ?o
  ensures
    closing t
  , match ?o with
    | None ->
        True
    | Some fd_ ->
        fd_ = fd ∗
        Ψ 1
    end
|}]
[@@zoo{|
  specification
    closing
  arguments
    t
  requires
    inv t fd Ψ
  , closing t
  returns
    None
|}]

val use :
  t -> (unit -> 'a) -> (Unix.file_descr -> 'a) -> 'a
[@@zoo{|
  arguments
    t
  , closed
  , open
  requires
    inv t fd Ψ
  , spec_once closed {
      returns
        ?res
      ensures
        Χ false ?res
    }
  , spec_once open {
      arguments
        fd_
      requires
        fd_ = fd
      , token t f
      , Ψ f
      returns
        ?res
      ensures
        token t f
      , Ψ f
      , Χ true ?res
    }
  returns
    ?res
  ensures
    Χ ?b ?res
|}]

val is_open :
  t -> bool
[@@zoo{|
  arguments
    t
  requires
    inv t fd Ψ
  returns
    ?b
  ensures
    if ?b then
      True
    else
      closing t
|}]
[@@zoo{|
  specification
    closing
  arguments
    t
  requires
    inv t fd Ψ
  , closing t
  returns
    false
|}]

val peek :
  t -> Unix.file_descr option
[@@zoo{|
  arguments
    t
  requires
    inv t fd Ψ
  returns
    ?o
  ensures
    match ?o with
    | None ->
        closing t
    | Some fd_ ->
        fd_ = fd
    end
|}]
[@@zoo{|
  specification
    closing
  arguments
    t
  requires
    inv t fd Ψ
  , closing t
  returns
    None
|}]
