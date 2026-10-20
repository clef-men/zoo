let record_basename =
  "name"
let record_name () : string =
  Printf.sprintf "%s%s%s"
    (Utils.current_unit ())
    Separator.cdot
    record_basename
let record_ident () : Names.lident =
  record_name ()
  |> Names_.lident_of_string
let record_qualid () : Libnames.qualid =
  record_name ()
  |> Libnames.qualid_of_string
let record_ref () : Constrexpr.constr_expr =
  record_qualid ()
  |> Constrexpr_.mk_ref

let field_name (name : string) : string =
  Printf.sprintf "%s%s%s"
    (record_name ())
    Separator.cdot
    name
let field_ident (id : Names.Id.t) : Names.Id.t =
  id |> Names_.Id.map field_name
let field_qualid (id : Names.Id.t) : Libnames.qualid =
  id
  |> field_ident
  |> Libnames.qualid_of_ident

let coercion_name () : string =
  Printf.sprintf "%s%s%s"
    (record_name ())
    Separator.cdot
    "to_val"
let coercion_lname () : Names.lname =
  coercion_name ()
  |> Names_.lname_of_string
let coercion_qualid () : Libnames.qualid =
  coercion_name ()
  |> Libnames.qualid_of_string
let coercion_ref () : Constrexpr.constr_expr =
  coercion_qualid ()
  |> Constrexpr_.mk_ref

let instance_name () : string =
  Printf.sprintf "%s%s%s"
    (record_name ())
    Separator.hyphen
    "to_val"
let instance_lname () : Names.lname =
  instance_name ()
  |> Names_.lname_of_string
let instance_qualid () : Libnames.qualid =
  instance_name ()
  |> Libnames.qualid_of_string

let field (name : Names.Name.t) : Names.Name.t =
  match name with
  | Anonymous ->
      Anonymous
  | Name id ->
      Name (id |> field_ident)
let field (name : Names.lname) =
  name |> CAst.map field
let field (decl : Vernacexpr.local_decl_expr) : Vernacexpr.local_decl_expr =
  match decl with
  | AssumExpr (name, bdrs, ty) ->
      AssumExpr (name |> field, bdrs, ty)
  | DefExpr (name, bdrs, body, ty) ->
      DefExpr (name |> field, bdrs, body, ty)
let field (decl, attrs : Vernacexpr.local_decl_expr * Vernacexpr.record_field_attr_unparsed) =
  decl |> field, attrs

let fields =
  List.map field

let record flds =
  let open Vernacexpr in
  [ None
  , VernacInductive
    ( Record
    , [ ( ( (NoCoercion, (record_ident (), None))
          , ([], None)
          , None
          , RecordDecl (None, flds |> fields, None)
          )
        , []
        )
      ]
    )
  ; ( None
    , VernacReserve [[Iris.gamma_lident], record_ref ()]
    )
  ]

let instance ~locality =
  let open Vernacexpr in
  let open Constrexpr_ in
  [ ( Some locality
    , VernacInstance
      ( (instance_lname (), None)
      , []
      , mk_app Zoo._ToVal_ref [record_ref ()]
      , Some (false, coercion_ref ())
      , Hints.empty_hint_info
      )
    )
  ]

type coercion_kind =
  | Location
  | Prophet
  | Other
let coercion fld =
  let open Constrexpr in
  let open Constrexpr_ in
  CProj
  ( false
  , (fld |> field_qualid, None)
  , []
  , Iris.gamma_ref
  ) |> CAst.make
let coercion ~kind fld =
  let open Constrexpr_ in
  match kind with
  | Location ->
      mk_app Zoo._ValLoc_ref [coercion fld]
  | Prophet ->
      mk_app Zoo._ValProph_ref [coercion fld]
  | Other ->
      coercion fld
let coercion ~locality ~kind fld =
  let open Vernacexpr in
  let open Constrexpr in
  let open Constrexpr_ in
  [ ( Some locality
    , VernacDefinition
      ( (NoDischarge, Definition)
      , (coercion_lname (), None)
      , DefineBody
        ( [ CLocalAssum
            ( [Iris.gamma_lname]
            , None
            , Default Explicit
            , record_ref ()
            )
          ]
        , None
        , coercion ~kind fld
        , Some Zoo.val_ref
        )
      )
    )
  ; ( None
    , VernacCoercion
      ( AN (coercion_qualid ()) |> CAst.make
      , Some
        ( RefClass (AN (record_qualid ()) |> CAst.make)
        , RefClass (AN Zoo.val_qualid |> CAst.make)
        )
      )
    )
  ]
let coercion ~locality fld ty =
  let ty = Nametab.locate ty in
  if Names.GlobRef.UserOrd.equal ty (Zoo.location_globref ()) then
    coercion ~locality ~kind:Location fld
  else if Names.GlobRef.UserOrd.equal ty (Zoo.prophet_identifier_globref ()) then
    coercion ~locality ~kind:Prophet fld
  else
    coercion ~locality ~kind:Other fld
let coercion ~locality (flds : (Vernacexpr.local_decl_expr * Vernacexpr.record_field_attr_unparsed) list) =
  match flds with
  | (AssumExpr ({ v= Name fld; _}, _bdrs, { v= CRef (ty, _inst); _ }), _attrs) :: _ ->
      coercion ~locality fld ty @
      instance ~locality
  | _ ->
      []

let main ~locality ~state flds =
  let state =
    Vernacinterp_.interp ~state @@ List.flatten @@
      [ record flds
      ; coercion ~locality flds
      ]
  in
  Vernacstate_.unfreeze_full_state state ;
  Please_derive.derive ~locality ~kind:Inhabited ~ty:(record_qualid ()) ;
  Please_derive.derive ~locality ~kind:Eq_decision ~ty:(record_qualid ()) ;
  Please_derive.derive ~locality ~kind:Countable ~ty:(record_qualid ())
let main ~locality flds =
  Vernacstate_.freeze_full_state_and_try @@ fun state ->
    main ~locality ~state flds
