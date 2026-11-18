type field_kind =
  | Normal
  | Sharp

type field =
  { kind: field_kind
  ; name: string
  ; typ: Constrexpr.constr_expr
  }

let record_basename =
  "name"
let record_name () : string =
  Printf.sprintf "%s%s%s"
    (Utils.current_unit ())
    Separator.cdot1
    record_basename
let record_ident () : Names.lident =
  record_name ()
  |> Names_.lident_of_string
let record_qualid () : Libnames.qualid =
  record_name ()
  |> Libnames.qualid_of_string
let record_constr () : Constrexpr.constr_expr =
  record_qualid ()
  |> Constrexpr_.mk_ref

let field_name (name : string) : string =
  Printf.sprintf "%s%s%s"
    (record_name ())
    Separator.cdot1
    name

let coercion_name () : string =
  Printf.sprintf "%s%s%s"
    (record_name ())
    Separator.cdot1
    "to_val"
let coercion_lname () : Names.lname =
  coercion_name ()
  |> Names_.lname_of_string
let coercion_qualid () : Libnames.qualid =
  coercion_name ()
  |> Libnames.qualid_of_string
let coercion_constr () : Constrexpr.constr_expr =
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

let field fld =
  Vernacexpr.AssumExpr
  ( fld.name |> field_name |> Names_.lname_of_string
  , []
  , fld.typ
  )

let fields =
  let attrs =
    Vernacexpr.
    { rfu_attrs= []
    ; rfu_coercion= NoCoercion
    ; rfu_instance= NoInstance
    ; rfu_priority= None
    ; rfu_notation= []
    }
  in
  List.map (fun fld -> fld |> field, attrs)

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
    , VernacReserve [[Iris.gamma_lident], record_constr ()]
    )
  ]

let instance ~locality =
  let open Vernacexpr in
  let open Constrexpr_ in
  [ ( Some locality
    , VernacInstance
      ( (instance_lname (), None)
      , []
      , mk_app Zoo._ToVal_constr [record_constr ()]
      , Some (false, coercion_constr ())
      , Hints.empty_hint_info
      )
    )
  ]

module Category = struct
  type t =
    | Nat
    | Int
    | Location
    | Prophet
    | Other

  let of_type (ty : Constrexpr.constr_expr) =
    match ty.v with
    | CRef (ty, _inst) ->
        let ty = Nametab.locate ty in
        if Names.GlobRef.UserOrd.equal ty (Std.nat_gref ()) then
          Nat
        else if Names.GlobRef.UserOrd.equal ty (Std._Z_gref ()) then
          Int
        else if Names.GlobRef.UserOrd.equal ty (Zoo.location_gref ()) then
          Location
        else if Names.GlobRef.UserOrd.equal ty (Zoo.prophet_identifier_gref ()) then
          Prophet
        else
          Other
    | _ ->
        Other

  let coercion t constr =
    let open Constrexpr_ in
    match t with
    | Nat ->
        mk_app Zoo._ValNat_constr [constr]
    | Int ->
        mk_app Zoo._ValInt_constr [constr]
    | Location ->
        mk_app Zoo._ValLoc_constr [constr]
    | Prophet ->
        mk_app Zoo._ValProph_constr [constr]
    | Other ->
        constr
end

type coercion_kind =
  | Single of field
  | Tuple of field list
let coercion fld =
  let open Constrexpr in
  let open Constrexpr_ in
  CProj
  ( false
  , (fld.name |> field_name |> Libnames.qualid_of_string, None)
  , []
  , Iris.gamma_constr
  ) |> CAst.make
let coercion ~kind =
  match kind with
  | Single fld ->
      Category.(coercion (of_type fld.typ)) (coercion fld)
  | Tuple flds ->
      let open Constrexpr_ in
      mk_app
        Zoo._ValTuple_constr
        [ flds
          |> List.map (fun fld ->
            Category.(coercion (of_type fld.typ)) (coercion fld)
          )
          |> mk_list
        ]
let coercion ~locality ~kind =
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
            , record_constr ()
            )
          ]
        , None
        , coercion ~kind
        , Some Zoo.val_constr
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
  ] @
  instance ~locality
let coercion ~locality flds =
  let flds_sharp = flds |> List.filter (fun fld -> fld.kind = Sharp) in
  if flds_sharp <> [] then
    coercion ~locality ~kind:(Tuple flds_sharp)
  else
    match flds with
    | [] ->
        []
    | fld :: _ ->
        coercion ~locality ~kind:(Single fld)

let interp ~locality ~state flds =
  let state =
    Vernacinterp_.interp_synpure ~state @@ List.flatten @@
      [ record flds
      ; coercion ~locality flds
      ]
  in
  Vernacstate_.unfreeze_full_state state ;
  Please_derive.interp ~locality ~kind:Inhabited ~ty:(record_qualid ()) ;
  Please_derive.interp ~locality ~kind:Eq_decision ~ty:(record_qualid ()) ;
  Please_derive.interp ~locality ~kind:Countable ~ty:(record_qualid ())
let interp ~locality flds =
  Vernacstate_.freeze_full_state_and_try @@ fun state ->
    interp ~locality ~state flds
