type mutability =
  | Immutable
  | Mutable

type declaration =
  | Record of mutability * string list
  | Variant of string list

module Kind = struct
  type t =
    | Record of mutability
    | Variant

  let entry = function
    | Record Immutable ->
        Zoo.Custom_entry.proj
    | Record Mutable ->
        Zoo.Custom_entry.field
    | Variant ->
        Zoo.Custom_entry.constructor
end

let library_name =
  Utils.current_directory

let module_name () =
  Utils.current_unit ()
  |> String.split_all ~sep:"__"
  |> List.hd

let type_name id =
  Printf.sprintf "%s%s%s%s%s"
    (library_name ())
    Separator.dot
    (module_name ())
    Separator.dot
    (id |> Libnames.string_of_qualid)

let item_name ~qualified ~id ~kind name =
  Printf.sprintf "%s%s%s"
    ( if qualified then
        Printf.sprintf "%s%s"
          (module_name ())
          Separator.cdot2
      else
        ""
    )
    ( let path, id = id |> Libnames.repr_qualid in
      let path =
        if id |> Names.Id.to_string |> String.starts_with_uppercase then
          Names_.DirPath.case path ~empty:path ~snoc:(fun _id path -> path)
        else
          path
      in
      if Names.DirPath.is_empty path then
        ""
      else
        Printf.sprintf "%s%s"
          (path |> Names.DirPath.to_string)
          Separator.cdot2
    )
    name

let notation_interp ~id ~(kind : Kind.t) i =
  let open Constrexpr in
  let open Constrexpr_ in
  mk_app
    Zoo.in_type_ref
    [ id |> type_name |> mk_string
    ; match kind with
      | Record _mut ->
          mk_int i
      | Variant ->
          Zoo._Tag_ref i
    ]
let notation ~qualified ~id ~kind i name =
  let open Vernacexpr in
  { ntn_decl_string=
      name
      |> item_name ~qualified ~id ~kind
      |> Printf.sprintf "'%s'"
      |> CAst.make
  ; ntn_decl_interp=
      notation_interp ~id ~kind i
  ; ntn_decl_scope=
      None
  ; ntn_decl_modifiers=
      [ SetCustomEntry
        ( kind |> Kind.entry |> Libnames.qualid_of_string
        , None
        ) |> CAst.make
      ]
  }
let notation ~(locality : Hints.hint_locality) ~qualified ~id ~kind i name =
  Metasyntax.add_notation_syntax
    ~local:(locality = Local)
    ~infix:false
    None
    (notation ~qualified ~id ~kind i name)

let synterp ~locality ~qualified id decl =
  match decl with
  | Record (mut, flds) ->
      flds |> List.mapi (notation ~locality ~qualified ~id ~kind:(Record mut))
  | Variant ctors ->
      ctors |> List.mapi (notation ~locality ~qualified ~id ~kind:Variant)

let interp ~(locality : Hints.hint_locality) decls =
  decls |> List.iter @@ fun decl ->
    Metasyntax.add_notation_interpretation
      ~local:(locality = Local)
      (Global.env ())
      decl
