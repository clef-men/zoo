type t

[@@@zoo{|
predicate inv
  (t : val)
  (owned : bool)
  (fd : val)
  (Ψ : fraction → Prop)
persistent inv

predicate owner
  (t : val)

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
    inv ?t owned fd Ψ
  , if owned then
      owner ?t
    else
      True
|}]

val use :
  t -> (unit -> 'a) -> (Unix.file_descr -> 'a) -> 'a
[@@zoo{|
  arguments
    t
  , closed
  , open
  requires
    inv t owned fd Ψ
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
      , Ψ f
      returns
        ?res
      ensures
        Ψ f
      , Χ true ?res
    }
  returns
    ?res
  ensures
    Χ ?b ?res
|}]
[@@zoo{|
  specification
    owner
  arguments
    t
  , closed
  , open
  requires
    inv t owned fd Ψ
  , owner t
  , spec_once open {
      arguments
        fd_
      requires
        fd_ = fd
      , Ψ f
      returns
        ?res
      ensures
        Ψ f
      , Χ ?res
    }
  returns
    ?res
  ensures
    Χ ?res
|}]
[@@zoo{|
  arguments
    t
  , closed
  , open
  requires
    inv t owned fd Ψ
  , closing t
  , spec_once closed {
      returns
        ?res
      ensures
        Χ ?res
    }
  returns
    ?res
  ensures
    Χ ?res
|}]

val close :
  t -> bool
[@@zoo{|
  arguments
    t
  requires
    inv t owned fd Ψ
  , if owned then
      owner t
    else
      True
  , Ψ 1 -∗
      ∃ chars.
      Unix.fd_model fd 1 chars
  returns
    ?b
  ensures
    closing t
  , if owned then
      ?b = true
    else
      True
|}]
[@@zoo{|
  specification
    closing
  arguments
    t
  requires
    inv t false fd Ψ
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
    inv t owned fd Ψ
  , if owned then
      owner t
    else
      True
  returns
    ?o
  ensures
    closing t
  , if owned then
      ?o = Some fd ∗
      Ψ 1
    else
      match ?o with
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
    inv t false fd Ψ
  , closing t
  returns
    None
|}]

val is_open :
  t -> bool
[@@zoo{|
  arguments
    t
  requires
    inv t owned fd Ψ
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
    owner
  arguments
    t
  requires
    inv t owned fd Ψ
  , owner t
  returns
    true
  ensures
    owner t
|}]
[@@zoo{|
  specification
    closing
  arguments
    t
  requires
    inv t false fd Ψ
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
    inv t owned fd Ψ
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
    owner
  arguments
    t
  requires
    inv t owned fd Ψ
  , owner t
  returns
    Some fd
  ensures
    owner t
|}]
[@@zoo{|
  specification
    closing
  arguments
    t
  requires
    inv t owned fd Ψ
  , closing t
  returns
    None
|}]
