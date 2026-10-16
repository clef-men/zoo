open Ltac_plugin

module Kind = struct
  type t =
    | Timeless
    | Persistent

  let to_string = function
    | Timeless ->
        "timeless"
    | Persistent ->
        "persistent"

  let to_ref = function
    | Timeless ->
        Iris._Timeless_ref
    | Persistent ->
        Iris._Persistent_ref
end

module Modifier = struct
  type t =
    | None
    | Discarded
end

module Error = struct
  type t =
    | Anonymous_parameter

  let to_string = function
    | Anonymous_parameter ->
        "anonymous parameter"

  let pp t =
    t |> to_string |> Pp.str
end

let error err =
  CErrors.user_err @@ Error.pp err

let parameters (const : Declarations.constant_body) =
  const.const_type
  |> Constr_.parameters
  |> List.map @@ fun (name, ty) ->
    let id =
      match name with
      | Names.Name.Anonymous ->
          error Anonymous_parameter
      | Name id ->
          id
    in
    id, ty

let instance_name ~kind id =
  Printf.sprintf "%s%s%s"
    (id |> Libnames.qualid_basename |> Names.Id.to_string)
    Separator.hyphen
    (kind |> Kind.to_string)
  |> Names_.lname_of_string

let instance_parameter id =
  let open Constrexpr in
  let open Constrexpr_ in
  CLocalAssum
  ( [id |> Names_.lname_of_ident]
  , None
  , Default Explicit
  , hole
  )
let instance_parameter ~(modifier : Modifier.t) (id, ty) =
  match modifier with
  | None ->
      Some (instance_parameter id)
  | Discarded ->
      if Constr.equal ty (Iris.dfrac_constr ()) then
        None
      else if Constr.equal ty (Zoo.ownership_constr ()) then
        None
      else
        Some (instance_parameter id)
let instance_parameters ~modifier params =
  params |> List.filter_map (instance_parameter ~modifier)

let instance_argument id =
  id |> Constrexpr_.mk_ref_ident
let instance_argument ~(modifier : Modifier.t) (id, ty) =
  match modifier with
  | None ->
      instance_argument id
  | Discarded ->
      if Constr.equal ty (Iris.dfrac_constr ()) then
        Iris._DfracDiscarded_ref
      else if Constr.equal ty (Zoo.ownership_constr ()) then
        Zoo._Discard_ref
      else
        instance_argument id
let instance_arguments ~modifier params =
  params |> List.map (instance_argument ~modifier)

let derive ~locality ~kind ~modifier id =
  let const = Nametab.locate_constant id in
  let const = Environ.lookup_constant const (Global.env ()) in
  let params = parameters const in
  let _id, proof =
    let open Constrexpr_ in
    Classes.new_instance_interactive
      ~locality
      ~poly:PolyFlags.default
      (instance_name ~kind id, None)
      (instance_parameters ~modifier params)
      ( mk_app
          (kind |> Kind.to_ref)
          [mk_app (id |> mk_ref) (instance_arguments ~modifier params)]
      )
      Hints.empty_hint_info
      None
  in
  let _ctx, proof =
    Declare.Proof.set_proof_using
      proof
      (Proof_using.using_from_string "Type*")
  in
  let proof =
    if Declare.Proof.get_open_goals proof = 0 then
      proof
    else
      let proof, _safe =
        Declare.Proof.by
          (Global.env ())
          ( Zoo.solve_iris_typeclass_tactic ()
            |> Loc.tag
            |> Tacexpr.(fun id -> TacArg (Reference (Locus.ArgArg id)))
            |> CAst.make
            |> Tacinterp.eval_tactic
          )
          proof
      in
      proof
  in
  let _refs =
    Declare.Proof.save_regular
      ~proof
      ~opaque:Opaque
      ~idopt:None
  in
  ()
