type mutability =
  | Immutable
  | Mutable

type constancy =
  | Constant
  | Nonconstant

type constructor =
  { constructor_tag: string
  ; constructor_constancy: constancy
  }

type declaration =
  | Record of mutability * string list
  | Variant of constructor list

type t =
  | Record of mutability
  | Variant

module Kind = struct
  type t =
    | Record of mutability
    | Variant

  let entry = function
    | Record Immutable ->
        Zoo.Custom_entry.projection
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

let item_name ~qualified ~id name =
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

let notation_interp ~id ~(kind : Kind.t) i name =
  let open Constrexpr in
  let open Constrexpr_ in
  mk_app
    Zoo.in_type_constr
    [ id |> type_name |> mk_string
    ; name |> mk_string
    ; match kind with
      | Record _mut ->
          mk_int i
      | Variant ->
          Zoo._Tag_constr i
    ]
let notation ~qualified ~id ~kind i name =
  let open Vernacexpr in
  { ntn_decl_string=
      name
      |> item_name ~qualified ~id
      |> Printf.sprintf "'%s'"
      |> CAst.make
  ; ntn_decl_interp=
      notation_interp ~id ~kind i name
  ; ntn_decl_scope=
      None
  ; ntn_decl_modifiers=
      [ SetCustomEntry
        ( kind |> Kind.entry |> Libnames.qualid_of_string
        , None
        ) |> CAst.make
      ]
  }
let notation ~locality ~qualified ~id ~kind i name =
  Metasyntax.add_notation_syntax
    ~local:(locality = Hints.Local)
    ~infix:false
    None
    (notation ~qualified ~id ~kind i name)

let rec record ~locality ~qualified ~id mut flds =
  flds |> List.mapi (notation ~locality ~qualified ~id ~kind:(Record mut))

let rec variant ~locality ~qualified ~id ctors =
  let cnt_const = ref 0 in
  let cnt_nonconst = ref 0 in
  ctors |> List.map @@ fun ctor ->
    let cnt =
      match ctor.constructor_constancy with
      | Constant ->
          cnt_const
      | Nonconstant ->
          cnt_nonconst
    in
    let i = !cnt in
    incr cnt ;
    notation ~locality ~qualified ~id ~kind:Variant i ctor.constructor_tag

let synterp ~locality ~qualified id (decl : declaration) =
  match decl with
  | Record (mut, flds) ->
      record ~locality ~qualified ~id mut flds
  | Variant ctors ->
      variant ~locality ~qualified ~id ctors

let interp ~locality decls =
  decls |> List.iter @@ fun decl ->
    Metasyntax.add_notation_interpretation
      ~local:(locality = Hints.Local)
      (Global.env ())
      decl
