open Ltac_plugin

type kind =
  | Iris
  | Zoo

type field =
  { name: string
  ; theory: Libnames.qualid
  ; arguments: Constrexpr.constr_expr list
  ; kind: kind
  }

type spec =
  { parameters: Constrexpr.local_binder_expr list
  ; fields: field list
  }

module Error = struct
  module Illegal_parameter = struct
    type t =
      | Pattern
      | Anonymous_explicit

    let to_string = function
      | Pattern ->
          "pattern parameter"
      | Anonymous_explicit ->
          "anonymous explicit parameter"
  end

  type t =
    | Illegal_parameter of Illegal_parameter.t

  let to_string = function
    | Illegal_parameter kind ->
        "illegal parameter: " ^ Illegal_parameter.to_string kind

  let pp t =
    t |> to_string |> Pp.str
end

let error err =
  CErrors.user_err @@ Error.pp err
let illegal_parameter kind =
  error @@ Illegal_parameter kind

let snake_to_camel str =
  str
  |> String.split_on_char '_'
  |> List.map String.capitalize_ascii
  |> String.concat ""

let class_name ?(kind = Zoo) (theory : string) : string =
  let name =
    match kind with
    | Iris ->
        theory
    | Zoo ->
        theory |> snake_to_camel
  in
  name ^ "G"
let class_id ?kind (theory : Names.Id.t) : Names.Id.t =
  theory
  |> Names.Id.to_string
  |> class_name ?kind
  |> Names.Id.of_string
let class_qualid ?kind (theory : Libnames.qualid) : Libnames.qualid =
  let path, id = theory |> Libnames.repr_qualid in
  let id = id |> class_id ?kind in
  Libnames.make_qualid path id

let field_name ~theory (fld : string) : string =
  Printf.sprintf "%s۰G۰%s۰G"
    theory
    fld

let functors_name ?(kind = Zoo) (theory : string) : string =
  let theory =
    match kind with
    | Iris ->
        theory
    | Zoo ->
        theory ^ "۰"
  in
  theory ^ "Σ"
let functors_id ?kind (theory : Names.Id.t) : Names.Id.t =
  theory
  |> Names.Id.to_string
  |> functors_name ?kind
  |> Names.Id.of_string
let functors_qualid ?kind (theory : Libnames.qualid) : Libnames.qualid =
  let path, id = theory |> Libnames.repr_qualid in
  let id = id |> functors_id ?kind in
  Libnames.make_qualid path id

let instance_name (theory : string) : string =
  Printf.sprintf "subGｰ%s۰Σ"
    theory

let fields ~theory spec =
  spec.fields |> List.map @@ fun (fld : field) ->
    let open Vernacexpr in
    let open Constrexpr_ in
    ( AssumExpr
      ( fld.name |> field_name ~theory |> Names_.lname_of_string
      , []
      , mk_app
          (fld.theory |> class_qualid ~kind:fld.kind |> mk_ref)
          (Iris.sigma_ref :: fld.arguments)
      )
    , { rfu_attrs= [("local", Attributes.VernacFlagEmpty) |> CAst.make]
      ; rfu_coercion= NoCoercion
      ; rfu_instance= BackInstance
      ; rfu_priority= None
      ; rfu_notation= []
      }
    )

let class_ ~theory spec =
  let name = theory |> class_name |> Names.Id.of_string |> CAst.make in
  let open Vernacexpr in
  VernacInductive
  ( Class false
  , [ ( ( (NoCoercion, (name, None))
        , (Iris.sigma_binder :: Zoo.zoo_G_binder:: spec.parameters, None)
        , None
        , RecordDecl (None, fields ~theory spec, None)
        )
      , []
      )
    ]
  )

let functors spec =
  List.fold_right (fun fld acc ->
    let open Constrexpr_ in
    mk_app
      Iris.gFunctors_app_ref
      [ mk_app
          (fld.theory |> functors_qualid ~kind:fld.kind |> mk_ref)
          fld.arguments
      ; acc
      ]
  ) spec.fields Iris.gFunctors_nil_ref
let functors ~theory spec =
  let open Vernacexpr in
  VernacDefinition
  ( (NoDischarge, Definition)
  , (theory |> functors_name |> Names_.lname_of_string, None)
  , DefineBody
    ( spec.parameters
    , None
    , functors spec
    , None
    )
  )

let instance ~theory spec =
  let params =
    let open Constrexpr_ in
    spec.parameters |> List.concat_map @@ fun (param : Constrexpr.local_binder_expr) ->
      match param with
      | CLocalDef _ ->
          []
      | CLocalPattern _ ->
          illegal_parameter Pattern
      | CLocalAssum (names, _relevance, kind, _ty) ->
          names |> List.filter_map @@ fun name ->
            let kind =
              match kind with
              | Default kind ->
                  kind
              | Generalized (kind, _) ->
                  kind
            in
            if kind <> Explicit then
              None
            else
              match name.CAst.v with
              | Names.Name.Anonymous ->
                  illegal_parameter Anonymous_explicit
              | Name id ->
                  Some (id |> mk_ref_ident)
  in
  let _id, proof =
    let open Constrexpr_ in
    Classes.new_instance_interactive
      ~locality:SuperGlobal
      ~poly:PolyFlags.default
      (theory |> instance_name |> Names_.lname_of_string, None)
      (Iris.sigma_binder :: Zoo.zoo_G_binder :: spec.parameters)
      ( mk_arrow
          ( mk_app
              Iris.subG_ref
              [ mk_app
                  (theory |> functors_name |> mk_ref_string)
                  params
              ; Iris.sigma_ref
              ]
          )
          ( mk_app
              (theory |> class_name |> mk_ref_string)
              (Iris.sigma_ref :: params)
          )
      )
      Hints.empty_hint_info
      None
  in
  let _ctx, proof =
    Declare.Proof.set_proof_using
      proof
      (Proof_using.using_from_string "Type*")
  in
  let proof, _safe =
    Declare.Proof.by
      (Global.env ())
      ( Zoo.solve_inG_tactic ()
        |> Loc.tag
        |> Tacexpr.(fun id -> TacArg (Reference (Locus.ArgArg id)))
        |> CAst.make
        |> Tacinterp.eval_tactic
      )
      proof
  in
  let _refs =
    Declare.Proof.save_regular
      ~proof
      ~opaque:Opaque
      ~idopt:None
  in
  ()

let interp ~state vernac =
  let vernac = Vernacexpr.VernacSynPure vernac in
  let vernac = Vernacexpr.{ control= []; attrs= []; expr= vernac } in
  let vernac = vernac |> CAst.make in
  Vernacinterp_.interp ~state vernac
let main ~state spec =
  let theory = Utils.current_unit () in
  let state = interp ~state @@ class_ ~theory spec in
  let state = interp ~state @@ functors ~theory spec in
  Vernacstate.unfreeze_full_state state ;
  instance ~theory spec
let main spec =
  let state = Vernacstate.freeze_full_state () in
  try
    main ~state spec
  with exn ->
    Vernacstate.unfreeze_full_state state ;
    raise exn
