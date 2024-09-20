open Syntax

module Builtin = struct
  let raising =
    [|[|"Stdlib";"raise"|] ;
      [|"Stdlib";"invalid_arg"|] ;
      [|"Stdlib";"failwith"|] ;
    |]
  let raising =
    Array.fold_left (fun acc path ->
      Path.Set.add (Path.of_array path) acc
    ) Path.Set.empty raising

  let paths =
    [|[|"Stdlib";"ignore"|], Fun ([Some "1"], Local "1"), None ;
      [|"Stdlib";"not"|], Fun ([Some "1"], Unop (Unop_neg, Local "1")), None ;
      [|"Stdlib";"~-"|], Fun ([Some "1"], Unop (Unop_minus, Local "1")), None ;
      [|"Stdlib";"+"|], Fun ([Some "1"; Some "2"], Binop (Binop_plus, Local "1", Local "2")), None ;
      [|"Stdlib";"-"|], Fun ([Some "1"; Some "2"], Binop (Binop_minus, Local "1", Local "2")), None ;
      [|"Stdlib";"*"|], Fun ([Some "1"; Some "2"], Binop (Binop_mult, Local "1", Local "2")), None ;
      [|"Stdlib";"/"|], Fun ([Some "1"; Some "2"], Binop (Binop_quot, Local "1", Local "2")), None ;
      [|"Stdlib";"mod"|], Fun ([Some "1"; Some "2"], Binop (Binop_rem, Local "1", Local "2")), None ;
      [|"Stdlib";"=="|], Fun ([Some "1"; Some "2"], Binop (Binop_eq, Local "1", Local "2")), None ;
      [|"Stdlib";"!="|], Fun ([Some "1"; Some "2"], Binop (Binop_ne, Local "1", Local "2")), None ;
      [|"Stdlib";"<="|], Fun ([Some "1"; Some "2"], Binop (Binop_le, Local "1", Local "2")), None ;
      [|"Stdlib";"<"|], Fun ([Some "1"; Some "2"], Binop (Binop_lt, Local "1", Local "2")), None ;
      [|"Stdlib";">="|], Fun ([Some "1"; Some "2"], Binop (Binop_ge, Local "1", Local "2")), None ;
      [|"Stdlib";">"|], Fun ([Some "1"; Some "2"], Binop (Binop_gt, Local "1", Local "2")), None ;
      [|"Stdlib";"ref"|], Fun ([Some "1"], Ref (Local "1")), None ;
      [|"Stdlib";"!"|], Fun ([Some "1"], Ref_get (Local "1")), None ;
      [|"Stdlib";":="|], Fun ([Some "1"; Some "2"], Ref_set (Local "1", Local "2")), None ;
      [|"Stdlib";"Obj";"repr"|], Fun ([Some "1"], Local "1"), None ;
      [|"Stdlib";"Obj";"obj"|], Fun ([Some "1"], Local "1"), None ;
      [|"Stdlib";"Obj";"magic"|], Fun ([Some "1"], Local "1"), None ;
      [|"Stdlib";"Obj";"tag"|], Fun ([Some "1"], Get_tag (Local "1")), None ;
      [|"Stdlib";"Obj";"size"|], Fun ([Some "1"], Get_size (Local "1")), None ;
      [|"Stdlib";"Obj";"field"|], Fun ([Some "1"; Some "2"], Load (Local "1", Local "2")), None ;
      [|"Stdlib";"Obj";"set_field"|], Fun ([Some "1"; Some "2"; Some "3"], Store (Local "1", Local "2", Local "3")), None ;
      [|"Stdlib";"Obj";"new_block"|], Fun ([Some "1"; Some "2"], Alloc (Local "1", Local "2")), None ;
      [|"Stdlib";"Int";"min"|], Fun ([Some "1"; Some "2"], Apply (Global "minimum", [Local "1"; Local "2"])), Some "int" ;
      [|"Stdlib";"Int";"max"|], Fun ([Some "1"; Some "2"], Apply (Global "maximum", [Local "1"; Local "2"])), Some "int" ;
      [|"Stdlib";"Domain";"cpu_relax"|], Fun ([None], Yield), None ;
      [|"Stdlib";"Atomic";"Loc";"get"|], Fun ([Some "1"], Load (Proj (Local "1", "0"), Proj (Local "1", "1"))), None ;
      [|"Stdlib";"Atomic";"Loc";"set"|], Fun ([Some "1"; Some "2"], Store (Proj (Local "1", "0"), Proj (Local "1", "1"), Local "2")), None ;
      [|"Stdlib";"Atomic";"Loc";"exchange"|], Fun ([Some "1"; Some "2"], Xchg (Local "1", Local "2")), None ;
      [|"Stdlib";"Atomic";"Loc";"compare_and_set"|], Fun ([Some "1"; Some "2"; Some "3"], Cas (Local "1", Local "2", Local "3")), None ;
      [|"Stdlib";"Atomic";"Loc";"fetch_and_add"|], Fun ([Some "1"; Some "2"], Faa (Local "1", Local "2")), None ;
      [|"Stdlib";"Atomic";"Loc";"decr"|], Fun ([Some "1"], Faa (Local "1", Int (-1))), None ;
      [|"Stdlib";"Atomic";"Loc";"incr"|], Fun ([Some "1"], Faa (Local "1", Int 1)), None ;
      [|"Stdlib";"Atomic";"make"|], Fun ([Some "1"], Ref (Local "1")), None ;
      [|"Stdlib";"Atomic";"get"|], Fun ([Some "1"], Ref_get (Local "1")), None ;
      [|"Stdlib";"Atomic";"set"|], Fun ([Some "1"; Some "2"], Ref_set (Local "1", Local "2")), None ;
      [|"Stdlib";"Atomic";"exchange"|], Fun ([Some "1"; Some "2"], Xchg (Atomic_loc (Local "1", "contents"), Local "2")), None ;
      [|"Stdlib";"Atomic";"compare_and_set"|], Fun ([Some "1"; Some "2"; Some "3"], Cas (Atomic_loc (Local "1", "contents"), Local "2", Local "3")), None ;
      [|"Stdlib";"Atomic";"fetch_and_add"|], Fun ([Some "1"; Some "2"], Faa (Atomic_loc (Local "1", "contents"), Local "2")), None ;
      [|"Stdlib";"Atomic";"decr"|], Fun ([Some "1"], Faa (Atomic_loc (Local "1", "contents"), Int (-1))), None ;
      [|"Stdlib";"Atomic";"incr"|], Fun ([Some "1"], Faa (Atomic_loc (Local "1", "contents"), Int 1)), None ;
      [|"Zoo";"proph"|], Proph, None ;
      [|"Zoo";"resolve"|], Fun ([Some "1"; Some "2"; Some "3"], Resolve (Local "1", Local "2", Local "3")), None ;
      [|"Zoo";"id"|], Id, Some "identifier" ;
    |]
  let paths =
    Array.fold_left (fun acc (path, expr, dep) ->
      Path.Map.add (Path.of_array path) (expr, dep) acc
    ) Path.Map.empty paths
  let paths =
    Path.Set.fold (fun path acc ->
      let expr = Fun ([None], Apply (Global "diverge", [Tuple []])) in
      let dep = Some "diverge" in
      Path.Map.add path (expr, dep) acc
    ) raising paths

  type app =
    | Opaque of expression
    | Transparent of (expression list -> expression option)
  let apps =
    [|[|"Stdlib";"ignore"|], (function [expr] -> Some expr | _ -> None), None ;
      [|"Stdlib";"not"|], (function [expr] -> Some (Unop (Unop_neg, expr)) | _ -> None), None ;
      [|"Stdlib";"~-"|], (function [expr] -> Some (Unop (Unop_minus, expr)) | _ -> None), None ;
      [|"Stdlib";"+"|], (function [expr1; expr2] -> Some (Binop (Binop_plus, expr1, expr2)) | _ -> None), None ;
      [|"Stdlib";"-"|], (function [expr1; expr2] -> Some (Binop (Binop_minus, expr1, expr2)) | _ -> None), None ;
      [|"Stdlib";"*"|], (function [expr1; expr2] -> Some (Binop (Binop_mult, expr1, expr2)) | _ -> None), None ;
      [|"Stdlib";"/"|], (function [expr1; expr2] -> Some (Binop (Binop_quot, expr1, expr2)) | _ -> None), None ;
      [|"Stdlib";"mod"|], (function [expr1; expr2] -> Some (Binop (Binop_rem, expr1, expr2)) | _ -> None), None ;
      [|"Stdlib";"=="|], (function [expr1; expr2] -> Some (Binop (Binop_eq, expr1, expr2)) | _ -> None), None ;
      [|"Stdlib";"!="|], (function [expr1; expr2] -> Some (Binop (Binop_ne, expr1, expr2)) | _ -> None), None ;
      [|"Stdlib";"<="|], (function [expr1; expr2] -> Some (Binop (Binop_le, expr1, expr2)) | _ -> None), None ;
      [|"Stdlib";"<"|], (function [expr1; expr2] -> Some (Binop (Binop_lt, expr1, expr2)) | _ -> None), None ;
      [|"Stdlib";">="|], (function [expr1; expr2] -> Some (Binop (Binop_ge, expr1, expr2)) | _ -> None), None ;
      [|"Stdlib";">"|], (function [expr1; expr2] -> Some (Binop (Binop_gt, expr1, expr2)) | _ -> None), None ;
      [|"Stdlib";"&&"|], (function [expr1; expr2] -> Some (Binop (Binop_and, expr1, expr2)) | _ -> None), None ;
      [|"Stdlib";"||"|], (function [expr1; expr2] -> Some (Binop (Binop_or, expr1, expr2)) | _ -> None), None ;
      [|"Stdlib";"ref"|], (function [expr] -> Some (Ref expr) | _ -> None), None ;
      [|"Stdlib";"!"|], (function [expr] -> Some (Ref_get expr) | _ -> None), None ;
      [|"Stdlib";":="|], (function [expr1; expr2] -> Some (Ref_set (expr1, expr2)) | _ -> None), None ;
      [|"Stdlib";"Obj";"repr"|], (function [expr] -> Some expr | _ -> None), None ;
      [|"Stdlib";"Obj";"obj"|], (function [expr] -> Some expr | _ -> None), None ;
      [|"Stdlib";"Obj";"magic"|], (function [expr] -> Some expr | _ -> None), None ;
      [|"Stdlib";"Obj";"tag"|], (function [expr] -> Some (Get_tag expr) | _ -> None), None ;
      [|"Stdlib";"Obj";"size"|], (function [expr] -> Some (Get_size expr) | _ -> None), None ;
      [|"Stdlib";"Obj";"field"|], (function [expr1; expr2] -> Some (Load (expr1, expr2)) | _ -> None), None ;
      [|"Stdlib";"Obj";"set_field"|], (function [expr1; expr2; expr3] -> Some (Store (expr1, expr2, expr3)) | _ -> None), None ;
      [|"Stdlib";"Obj";"new_block"|], (function [expr1; expr2] -> Some (Alloc (expr1, expr2)) | _ -> None), None ;
      [|"Stdlib";"Int";"min"|], (function [expr1; expr2] -> Some (Apply (Global "minimum", [expr1; expr2])) | _ -> None), Some "int" ;
      [|"Stdlib";"Int";"max"|], (function [expr1; expr2] -> Some (Apply (Global "maximum", [expr1; expr2])) | _ -> None), Some "int" ;
      [|"Stdlib";"Domain";"cpu_relax"|], (function [_expr] -> Some Yield | _ -> None), None ;
      [|"Stdlib";"Atomic";"Loc";"get"|], (function [expr] -> Some (Load (Proj (expr, "0"), Proj (expr, "1"))) | _ -> None), None ;
      [|"Stdlib";"Atomic";"Loc";"set"|], (function [expr1; expr2] -> Some (Store (Proj (expr1, "0"), Proj (expr1, "1"), expr2)) | _ -> None), None ;
      [|"Stdlib";"Atomic";"Loc";"exchange"|], (function [expr1; expr2] -> Some (Xchg (expr1, expr2)) | _ -> None), None ;
      [|"Stdlib";"Atomic";"Loc";"compare_and_set"|], (function [expr1; expr2; expr3] -> Some (Cas (expr1, expr2, expr3)) | _ -> None), None ;
      [|"Stdlib";"Atomic";"Loc";"fetch_and_add"|], (function [expr1; expr2] -> Some (Faa (expr1, expr2)) | _ -> None), None ;
      [|"Stdlib";"Atomic";"Loc";"decr"|], (function [expr] -> Some (Faa (expr, Int (-1))) | _ -> None), None ;
      [|"Stdlib";"Atomic";"Loc";"incr"|], (function [expr] -> Some (Faa (expr, Int 1)) | _ -> None), None ;
      [|"Stdlib";"Atomic";"make"|], (function [expr] -> Some (Ref expr) | _ -> None), None ;
      [|"Stdlib";"Atomic";"get"|], (function [expr] -> Some (Ref_get expr) | _ -> None), None ;
      [|"Stdlib";"Atomic";"set"|], (function [expr1; expr2] -> Some (Ref_set (expr1, expr2)) | _ -> None), None ;
      [|"Stdlib";"Atomic";"exchange"|], (function [expr1; expr2] -> Some (Xchg (Atomic_loc (expr1, "contents"), expr2)) | _ -> None), None ;
      [|"Stdlib";"Atomic";"compare_and_set"|], (function [expr1; expr2; expr3] -> Some (Cas (Atomic_loc (expr1, "contents"), expr2, expr3)) | _ -> None), None ;
      [|"Stdlib";"Atomic";"fetch_and_add"|], (function [expr1; expr2] -> Some (Faa (Atomic_loc (expr1, "contents"), expr2)) | _ -> None), None ;
      [|"Stdlib";"Atomic";"decr"|], (function [expr] -> Some (Faa (Atomic_loc (expr, "contents"), Int (-1))) | _ -> None), None ;
      [|"Stdlib";"Atomic";"incr"|], (function [expr] -> Some (Faa (Atomic_loc (expr, "contents"), Int 1)) | _ -> None), None ;
      [|"Zoo";"resolve"|], (function [expr1; expr2; expr3] -> Some (Resolve (expr1, expr2, expr3)) | _ -> None), None ;
    |]
  let apps =
    Array.fold_left (fun acc (path, mk_expr, dep) ->
      Path.Map.add (Path.of_array path) (Transparent mk_expr, dep) acc
    ) Path.Map.empty apps
  let apps =
    Path.Set.fold (fun path acc ->
      let expr = Apply (Global "diverge", [Tuple []]) in
      let dep = Some "diverge" in
      Path.Map.add path (Opaque expr, dep) acc
    ) raising apps

  let constrs =
    let open Either in
    [|[|"()"|], Left (Tuple []), None ;
      [|"true"|], Left (Bool true), None ;
      [|"false"|], Left (Bool false), None ;
      [|"[]"|], Right "Nil", None ;
      [|"::"|], Right "Cons", None ;
      [|"None"|], Right "None", None ;
      [|"Some"|], Right "Some", None ;
    |]
  let constrs =
    Array.fold_left (fun acc (lid, tag, dep) ->
      Longident.Map.add (Longident.of_array lid) (tag, dep) acc
    ) Longident.Map.empty constrs
end

module Attribute = struct
  let has attr =
    List.exists (fun attr' -> attr'.Parsetree.attr_name.txt = attr)

  let prefix =
    "zoo.prefix"
  let has_prefix =
    has prefix

  let force_record =
    "zoo.force_record"
  let has_force_record =
    has force_record

  let reveal =
    "zoo.reveal"
  let has_reveal =
    has reveal

  let opaque =
    "zoo.opaque"
  let has_opaque =
    has opaque

  let overwrite =
    "zoo.overwrite"
  let rec has_overwrite = function
    | [] ->
        None
    | attr :: attrs ->
        let attr_name = attr.Parsetree.attr_name.txt in
        if String.starts_with ~prefix:overwrite attr_name then
          let overwrite_len = String.length overwrite in
          let attr_len = String.length attr_name in
          match String.sub attr_name overwrite_len (attr_len - overwrite_len) with
          | "" ->
              Some (Asttypes.Nonrecursive, attr)
          | "_rec" ->
              Some (Recursive, attr)
          | _ ->
              has_overwrite attrs
        else
          has_overwrite attrs
end

module Unsupported = struct
  type t =
    | Literal_non_integer
    | Pattern_alias
    | Pattern_constant
    | Pattern_variant
    | Pattern_record
    | Pattern_array
    | Pattern_or
    | Pattern_lazy
    | Pattern_guard
    | Pattern_constr
    | Pattern_nested
    | Pattern_invalid
    | Pattern_non_trivial
    | Handler_exception
    | Expr_let_rec_non_function
    | Expr_let_mutual
    | Expr_record_update
    | Expr_for_downward
    | Expr_open
    | Expr_array
    | Expr_try
    | Expr_variant
    | Expr_while
    | Expr_send
    | Expr_new
    | Expr_inst_var
    | Expr_set_inst_var
    | Expr_overwrite
    | Expr_let_module
    | Expr_let_exception
    | Expr_lazy
    | Expr_object
    | Expr_pack
    | Expr_let_op
    | Expr_unreachable
    | Expr_extension
    | Label
    | Functor
    | Type_inlined_record
    | Type_extensible
    | Def_invalid
    | Def_pattern
    | Def_mutual
    | Def_eval
    | Def_primitive
    | Def_exception
    | Def_module
    | Def_module_type
    | Def_open
    | Def_class
    | Def_class_type
    | Def_include

  let to_string = function
    | Literal_non_integer ->
        "non-integer literal"
    | Pattern_alias ->
        {|"as" pattern|}
    | Pattern_constant ->
        "constant pattern"
    | Pattern_variant ->
        "variant pattern"
    | Pattern_record ->
        "record pattern"
    | Pattern_array ->
        "array pattern"
    | Pattern_or ->
        "disjunction pattern"
    | Pattern_lazy ->
        {|"lazy" pattern|}
    | Pattern_guard ->
        "guard expression"
    | Pattern_constr ->
        "invalid constructor pattern"
    | Pattern_nested ->
        "nested pattern"
    | Pattern_invalid ->
        "invalid pattern"
    | Pattern_non_trivial ->
        "non-trivial pattern in function parameter"
    | Handler_exception ->
        "exception handler"
    | Expr_let_rec_non_function ->
        "recursive binding must bind a function"
    | Expr_let_mutual ->
        "mutually recursive let-bindings"
    | Expr_record_update ->
        "record update"
    | Expr_for_downward ->
        {|downward "for" loop|}
    | Expr_open ->
        "opened module must be an identifier"
    | Expr_array ->
        "array expression"
    | Expr_try ->
        {|"try" expression|}
    | Expr_variant ->
        "variant expression"
    | Expr_while ->
        {|"while" expression|}
    | Expr_send ->
        "method call"
    | Expr_new ->
        {|"new" expression|}
    | Expr_inst_var ->
        "instance variable"
    | Expr_set_inst_var ->
        "instance variable assignment"
    | Expr_overwrite ->
        "overwrite expression"
    | Expr_let_module ->
        "module binding"
    | Expr_let_exception ->
        "exception binding"
    | Expr_lazy ->
        {|"lazy" expression|}
    | Expr_object ->
        "object expression"
    | Expr_pack ->
        "module expression"
    | Expr_let_op ->
        "binding operator"
    | Expr_unreachable ->
        "unreachable branch"
    | Expr_extension ->
        "extension"
    | Label ->
        "labeled parameter"
    | Functor ->
        "module functor"
    | Type_inlined_record ->
        "inlined record"
    | Type_extensible ->
        "extensible variant"
    | Def_invalid ->
        "toplevel definition must be a constant or a function"
    | Def_pattern ->
        "toplevel definition pattern must be a variable"
    | Def_mutual ->
        "mutually recursive toplevel definitions"
    | Def_eval ->
        "evaluated expression"
    | Def_primitive ->
        "primitive definition"
    | Def_exception ->
        "exception definition"
    | Def_module ->
        "module definition"
    | Def_module_type ->
        "module type definition"
    | Def_open ->
        {|"open" declaration|}
    | Def_class ->
        "class definition"
    | Def_class_type ->
        "class type definition"
    | Def_include ->
        {|"include" declaration|}

  let pp ppf t =
    Format.pp_print_string ppf (to_string t)
end

module Error = struct
  type t =
    | Unsupported of Unsupported.t
    | Attribute_prefix_invalid_payload
    | Attribute_overwrite_invalid_payload

  let pp ppf = function
    | Unsupported unsupported ->
        Format.fprintf ppf "unsupported feature: %a"
          Unsupported.pp unsupported
    | Attribute_prefix_invalid_payload ->
        Format.fprintf ppf {|payload of attribute "%s" must be a string|}
          Attribute.prefix
    | Attribute_overwrite_invalid_payload ->
        Format.fprintf ppf {|payload of attribute "%s" must be a expression|}
          Attribute.overwrite
end

exception Error of Location.t * Error.t

let error loc err =
  raise @@ Error (loc, err)
let unsupported loc err =
  error loc (Unsupported err)

let record_is_mutable ty =
  let[@warning "-8"] Types.Type_record (lbls, _) = ty.Types.type_kind in
  List.exists (fun lbl -> lbl.Types.ld_mutable = Mutable) lbls ||
  Attribute.has_force_record ty.type_attributes

module Context = struct
  type t =
    { mutable prefix: string;
      env: Env.t;
      global_names: (string, int) Hashtbl.t;
      global_ids: variable Ident.Tbl.t;
      mutable locals: Ident.Set.t;
      deps: (string, unit) Hashtbl.t;
    }

  let create modname env =
    { prefix= modname ^ "_";
      env;
      global_names= Hashtbl.create 17;
      global_ids= Ident.Tbl.create 17;
      locals= Ident.Set.empty;
      deps= Hashtbl.create 17;
    }

  let set_prefix t pref =
    t.prefix <- if pref = "" then "" else pref ^ "_"

  let env t =
    t.env

  let add_global t name =
    match Hashtbl.find_opt t.global_names name with
    | None ->
        Hashtbl.add t.global_names name 0 ;
        0
    | Some cnt ->
        let cnt = cnt + 1 in
        Hashtbl.replace t.global_names name cnt ;
        cnt
  let add_global t id =
    let name = Ident.name id in
    let idx = add_global t name in
    let global = t.prefix ^ name in
    let global =
      let[@warning "-8"] Some cnt = Env.find_value_index id t.env in
      if cnt = 0 then
        global
      else
        global ^ "_" ^ Int.to_string idx
    in
    Ident.Tbl.add t.global_ids id global ;
    global
  let find_global t id =
    Ident.Tbl.find t.global_ids id

  let add_local t id =
    t.locals <- Ident.Set.add id t.locals
  let save_locals t =
    let locals = t.locals in
    fun () -> t.locals <- locals
  let mem_local t id =
    Ident.Set.mem id t.locals

  let add_dependency t dep =
    Hashtbl.replace t.deps dep ()
  let add_dependency_from_path t loc path =
    match Path.head path with
    | None ->
        unsupported loc Functor
    | Some id ->
        let dep = Ident.name id in
        match dep.[0] with
        | 'A'..'Z' ->
            let dep = String.lowercase_ascii dep in
            add_dependency t dep
        | _ ->
            ()
  let dependencies t =
    Hashtbl.fold (fun dep () acc -> dep :: acc) t.deps []
end

let rec pattern_is_neutral (pat : Typedtree.pattern) =
  match pat.pat_desc with
  | Tpat_any ->
      true
  | Tpat_tuple pats ->
      List.for_all pattern_is_neutral pats
  | Tpat_construct (_, constr, pats, _) ->
      constr.cstr_consts + constr.cstr_nonconsts = 1 &&
      List.for_all pattern_is_neutral pats
  | _ ->
      false
let pattern_to_binder ~err ctx (pat : Typedtree.pattern) =
  match pat.pat_desc with
  | Tpat_any ->
      None
  | Tpat_var (id, _, _) ->
      Context.add_local ctx id ;
      Some (Ident.name id)
  | Tpat_alias (pat, id, _, _) ->
      if pattern_is_neutral pat then (
        Context.add_local ctx id ;
        Some (Ident.name id)
      ) else (
        unsupported pat.pat_loc err
      )
  | Tpat_tuple pats ->
      if List.for_all pattern_is_neutral pats then
        None
      else
        unsupported pat.pat_loc err
  | Tpat_construct (_, constr, pats, _) ->
      if constr.cstr_consts + constr.cstr_nonconsts = 1
      && List.for_all pattern_is_neutral pats
      then
        None
      else
        unsupported pat.pat_loc err
  | _ ->
      unsupported pat.pat_loc err

let pattern ctx (pat : Typedtree.pattern) =
  match pat.pat_desc with
  | Tpat_any ->
      None
  | Tpat_var (id, _, _) ->
      Context.add_local ctx id ;
      Some (Pat_var (Ident.name id))
  | Tpat_tuple pats ->
      let bdrs = List.map (pattern_to_binder ~err:Pattern_nested ctx) pats in
      Some (Pat_tuple bdrs)
  | Tpat_construct (lid, constr, pats, _) ->
      let bdrs = List.map (pattern_to_binder ~err:Pattern_nested ctx) pats in
      begin match Longident.Map.find_opt lid.txt Builtin.constrs with
      | Some (tag, dep) ->
          Option.iter (Context.add_dependency ctx) dep ;
          let tag = Either.get_right (fun _ -> unsupported lid.loc Pattern_constr) tag in
          Some (Pat_constr (tag, bdrs))
      | None ->
          let tag = Longident.last lid.txt in
          let tag = Option.get_lazy (fun () -> unsupported lid.loc Functor) tag in
          let[@warning "-8"] Types.Tconstr (variant, _, _) = Types.get_desc constr.cstr_res in
          Context.add_dependency_from_path ctx lid.loc variant ;
          Some (Pat_constr (tag, bdrs))
      end
  | Tpat_alias _ ->
      unsupported pat.pat_loc Pattern_alias
  | Tpat_constant _ ->
      unsupported pat.pat_loc Pattern_constant
  | Tpat_variant _ ->
      unsupported pat.pat_loc Pattern_variant
  | Tpat_record _ ->
      unsupported pat.pat_loc Pattern_record
  | Tpat_array _ ->
      unsupported pat.pat_loc Pattern_array
  | Tpat_or _ ->
      unsupported pat.pat_loc Pattern_or
  | Tpat_lazy _ ->
      unsupported pat.pat_loc Pattern_lazy

let rec expression ctx (expr : Typedtree.expression) =
  match expr.exp_desc with
  | Texp_ident (path, lid, _) ->
      begin match path with
      | Pident id ->
          if Context.mem_local ctx id then
            Local (Ident.name id)
          else
            Global (Context.find_global ctx id)
      | Pdot (path', global) ->
          begin match Path.Map.find_opt path Builtin.paths with
          | Some (expr, dep) ->
              Option.iter (Context.add_dependency ctx) dep ;
              expr
          | None ->
              Context.add_dependency_from_path ctx lid.loc path' ;
              let[@warning "-8"] Some path' = Path.to_string "_" path' in
              let path' = String.lowercase_ascii path' in
              Global (path' ^ "_" ^ global)
          end
      | Papply _ ->
          unsupported expr.exp_loc Functor
      | _ ->
          assert false
      end
  | Texp_constant (Const_int int) ->
      Int int
  | Texp_constant _ ->
      unsupported expr.exp_loc Literal_non_integer
  | Texp_let (rec_flag, [bdg], expr2) ->
      let expr1 = expression ctx bdg.vb_expr in
      let restore_locals = Context.save_locals ctx in
      begin match pattern ctx bdg.vb_pat with
      | None ->
          let expr2 = expression ctx expr2 in
          Seq (expr1, expr2)
      | Some pat ->
          match expr1 with
          | Fun (bdrs, expr1) ->
              let[@warning "-8"] Pat_var local = pat in
              let expr2 = expression ctx expr2 in
              restore_locals () ;
              Letrec (rec_flag, local, bdrs, expr1, expr2)
          | _ ->
              if rec_flag = Recursive then
                unsupported bdg.vb_loc Expr_let_rec_non_function ;
              let expr2 = expression ctx expr2 in
              restore_locals () ;
              Let (pat, expr1, expr2)
      end
  | Texp_let (_, _, _) ->
      unsupported expr.exp_loc Expr_let_mutual
  | Texp_function (params, body) ->
      let restore_locals = Context.save_locals ctx in
      let bdrs =
        List.map (fun (param : Typedtree.function_param) ->
          if param.fp_arg_label <> Nolabel then
            unsupported param.fp_loc Label;
          let[@warning "-8"] Typedtree.Tparam_pat pat = param.fp_kind in
          pattern_to_binder ~err:Pattern_non_trivial ctx pat
        ) params
      in
      begin match body with
      | Tfunction_body expr ->
          let expr = expression ctx expr in
          restore_locals () ;
          Fun (bdrs, expr)
      | Tfunction_cases { cases= brs; param= id; _ } ->
          Context.add_local ctx id ;
          let brs, fb = branches ctx brs in
          restore_locals () ;
          let local = Ident.name id in
          Fun (bdrs @ [Some local], Match (Local local, brs, fb))
      end
  | Texp_apply (expr', exprs) ->
      let arguments () =
        List.map (fun (lbl, expr') ->
          if lbl <> Asttypes.Nolabel then
            unsupported expr.exp_loc Label ;
          expression ctx (Option.get expr')
        ) exprs
      in
      let default exprs =
        let expr' = expression ctx expr' in
        Apply (expr', exprs)
      in
      begin match expr'.exp_desc with
      | Texp_ident (path', _, _) ->
          begin match Path.Map.find_opt path' Builtin.apps with
          | None ->
              default (arguments ())
          | Some (mk_expr, dep) ->
              Option.iter (Context.add_dependency ctx) dep ;
              match mk_expr with
              | Opaque expr ->
                  expr
              | Transparent mk_expr ->
                  let exprs = arguments () in
                  match mk_expr exprs with
                  | Some expr ->
                      expr
                  | None ->
                      default exprs
          end
      | _ ->
          default (arguments ())
      end
  | Texp_ifthenelse (expr1, expr2, expr3) ->
      let expr1 = expression ctx expr1 in
      begin match expr1, expr2.exp_desc, expr3 with
      | Unop (Unop_neg, expr1), Texp_apply ({ exp_desc= Texp_ident (path, _, _); _ }, _), None
        when Path.Set.mem path Builtin.raising ->
          Context.add_dependency ctx "assume" ;
          Apply (Global "assume", [expr1])
      | _ ->
          let expr2 = expression ctx expr2 in
          let expr3 = Option.map (expression ctx) expr3 in
          If (expr1, expr2, expr3)
      end
  | Texp_sequence (expr1, expr2) ->
      let expr1 = expression ctx expr1 in
      let expr2 = expression ctx expr2 in
      Seq (expr1, expr2)
  | Texp_for (id, pat, expr1, expr2, Upto, expr3) ->
      let bdr =
        match pat.ppat_desc with
        | Ppat_any ->
            None
        | Ppat_var { txt= local; _ } ->
            Some local
        | _ ->
            assert false
      in
      let expr1 = expression ctx expr1 in
      let expr2 = expression ctx expr2 in
      let expr2 =
        match expr2 with
        | Binop (Binop_minus, expr2, Int 1) ->
            expr2
        | _ ->
            Binop (Binop_plus, expr2, Int 1)
      in
      let restore_locals = Context.save_locals ctx in
      Context.add_local ctx id ;
      let expr3 = expression ctx expr3 in
      restore_locals () ;
      For (bdr, expr1, expr2, expr3)
  | Texp_for (_, _, _, _, Downto, _) ->
      unsupported expr.exp_loc Expr_for_downward
  | Texp_tuple exprs ->
      let exprs = List.map (expression ctx) exprs in
      Tuple exprs
  | Texp_record rcd ->
      if rcd.extended_expression <> None then
        unsupported expr.exp_loc Expr_record_update ;
      let exprs =
        Array.map (fun (_, lbl) ->
          let[@warning "-8"] Typedtree.Overridden (_, expr) = lbl in
          expression ctx expr
        ) rcd.fields
      in
      if
        let[@warning "-8"] Types.Tconstr (rcd, _, _) = Types.get_desc expr.exp_type in
        record_is_mutable (Env.find_type rcd (Context.env ctx))
      then
        Record exprs
      else
        Tuple (Array.to_list exprs)
  | Texp_construct (lid, constr, exprs) ->
      let exprs = List.map (expression ctx) exprs in
      if constr.cstr_tag = Cstr_unboxed then
        let[@warning "-8"] [expr] = exprs in
        expr
      else
        begin match Longident.Map.find_opt lid.txt Builtin.constrs with
        | Some (tag, dep) ->
            Option.iter (Context.add_dependency ctx) dep ;
            Either.get_left (fun tag -> Constr (Abstract, tag, exprs)) tag
        | None ->
            let tag = Longident.last lid.txt in
            let tag = Option.get_lazy (fun () -> unsupported lid.loc Functor) tag in
            let[@warning "-8"] Types.Tconstr (variant, _, _) = Types.get_desc constr.cstr_res in
            Context.add_dependency_from_path ctx lid.loc variant ;
            let concrete =
              if Attribute.has_reveal constr.cstr_attributes then
                Concrete
              else
                Abstract
            in
            Constr (concrete, tag, exprs)
        end
  | Texp_match (expr, brs, _, _) ->
      let expr = expression ctx expr in
      let brs, fb = branches ctx brs in
      Match (expr, brs, fb)
  | Texp_atomic_loc (expr, lid, lbl) ->
      let expr = expression ctx expr in
      let fld = lbl.lbl_name in
      let[@warning "-8"] Types.Tconstr (rcd, _, _) = Types.get_desc lbl.lbl_res in
      Context.add_dependency_from_path ctx lid.loc rcd ;
      Atomic_loc (expr, fld)
  | Texp_field (expr, lid, lbl) ->
      let expr = expression ctx expr in
      let fld = lbl.lbl_name in
      let[@warning "-8"] Types.Tconstr (rcd, _, _) = Types.get_desc lbl.lbl_res in
      Context.add_dependency_from_path ctx lid.loc rcd ;
      if record_is_mutable (Env.find_type rcd (Context.env ctx)) then
        Record_get (expr, fld)
      else
        Proj (expr, fld)
  | Texp_setfield (expr1, lid, lbl, expr2) ->
      let expr1 = expression ctx expr1 in
      let fld = lbl.lbl_name in
      let[@warning "-8"] Types.Tconstr (rcd, _, _) = Types.get_desc lbl.lbl_res in
      Context.add_dependency_from_path ctx lid.loc rcd ;
      let expr2 = expression ctx expr2 in
      Record_set (expr1, fld, expr2)
  | Texp_assert ({ exp_desc= Texp_construct (_, constr, _); _ }, _) when constr.cstr_name = "false" ->
      Fail
  | Texp_assert (expr, _) ->
      Context.add_dependency ctx "assert" ;
      let expr = expression ctx expr in
      Apply (Global "assert", [expr])
  | Texp_open (open_decl, expr) ->
      begin match open_decl.open_expr.mod_desc with
      | Tmod_ident _ ->
          expression ctx expr
      | _ ->
          unsupported expr.exp_loc Expr_open
      end
  | Texp_array _ ->
      unsupported expr.exp_loc Expr_array
  | Texp_try _ ->
      unsupported expr.exp_loc Expr_try
  | Texp_variant _ ->
      unsupported expr.exp_loc Expr_variant
  | Texp_while _ ->
      unsupported expr.exp_loc Expr_while
  | Texp_send _ ->
      unsupported expr.exp_loc Expr_send
  | Texp_new _ ->
      unsupported expr.exp_loc Expr_new
  | Texp_instvar _ ->
      unsupported expr.exp_loc Expr_inst_var
  | Texp_setinstvar _ ->
      unsupported expr.exp_loc Expr_set_inst_var
  | Texp_override _ ->
      unsupported expr.exp_loc Expr_overwrite
  | Texp_letmodule _ ->
      unsupported expr.exp_loc Expr_let_module
  | Texp_letexception _ ->
      unsupported expr.exp_loc Expr_let_exception
  | Texp_lazy _ ->
      unsupported expr.exp_loc Expr_lazy
  | Texp_object _ ->
      unsupported expr.exp_loc Expr_object
  | Texp_pack _ ->
      unsupported expr.exp_loc Expr_pack
  | Texp_letop _ ->
      unsupported expr.exp_loc Expr_let_op
  | Texp_unreachable ->
      unsupported expr.exp_loc Expr_unreachable
  | Texp_extension_constructor _ ->
      unsupported expr.exp_loc Expr_extension
and branches : type a. Context.t -> a Typedtree.case list -> branch list * fallback option = fun ctx brs ->
  let rec aux1 acc = function
    | [] ->
        acc, None
    | br :: brs ->
        Option.iter (fun expr -> unsupported expr.Typedtree.exp_loc Pattern_guard) br.Typedtree.c_guard ;
        let restore_locals = Context.save_locals ctx in
        let pat = br.c_lhs in
        let pat =
          match (pat.pat_desc : a Typedtree.pattern_desc) with
          | Tpat_value pat ->
              (pat :> Typedtree.(value general_pattern))
          | Tpat_exception _ ->
              unsupported pat.pat_loc Handler_exception
          | Tpat_or _ ->
              unsupported pat.pat_loc Pattern_or
          | Tpat_any ->
              pat
          | Tpat_var _ ->
              pat
          | Tpat_alias _ ->
              pat
          | Tpat_constant _ ->
              pat
          | Tpat_tuple _ ->
              pat
          | Tpat_construct _ ->
              pat
          | Tpat_variant _ ->
              pat
          | Tpat_record _ ->
              pat
          | Tpat_array _ ->
              pat
          | Tpat_lazy _ ->
              pat
        in
        let pat, bdr =
          match pat.pat_desc with
          | Tpat_alias (pat, local, _, _) ->
              Context.add_local ctx local ;
              pat, Some (Ident.name local)
          | _ ->
              pat, None
        in
        let rec aux2 (pat : Typedtree.pattern) bdr =
          match pat.pat_desc with
          | Tpat_any ->
              let expr = expression ctx br.c_rhs in
              restore_locals () ;
              acc, Some { fallback_as= bdr; fallback_expr= expr }
          | Tpat_var (id, _, _) ->
              Context.add_local ctx id ;
              let expr = expression ctx br.c_rhs in
              restore_locals () ;
              let local = Ident.name id in
              begin match bdr with
              | None ->
                  acc, Some { fallback_as= Some local; fallback_expr= expr }
              | Some local' ->
                  acc, Some { fallback_as= bdr; fallback_expr= Let (Pat_var local, Local local', expr) }
              end
          | Tpat_construct (_, constr, pats, _) when constr.cstr_tag = Cstr_unboxed ->
              let[@warning "-8"] [pat] = pats in
              aux2 pat bdr
          | Tpat_construct (lid, constr, pats, _) ->
              let bdrs = List.map (pattern_to_binder ~err:Pattern_invalid ctx) pats in
              let bdrs =
                match bdrs with
                | [None] ->
                    List.make constr.cstr_arity None
                | _ ->
                    bdrs
              in
              let tag, bdrs =
                match Longident.Map.find_opt lid.txt Builtin.constrs with
                | Some (tag, dep) ->
                    Option.iter (Context.add_dependency ctx) dep ;
                    let tag = Either.get_right (fun _ -> unsupported lid.loc Pattern_constr) tag in
                    tag, bdrs
                | None ->
                    let tag = Longident.last lid.txt in
                    let tag = Option.get_lazy (fun () -> unsupported lid.loc Functor) tag in
                    let[@warning "-8"] Types.Tconstr (variant, _, _) = Types.get_desc constr.cstr_res in
                    Context.add_dependency_from_path ctx lid.loc variant ;
                    tag, bdrs
              in
              let expr = expression ctx br.c_rhs in
              restore_locals () ;
              aux1 ({ branch_tag= tag; branch_binders= bdrs; branch_as= bdr; branch_expr= expr } :: acc) brs
          | _ ->
              unsupported pat.pat_loc Pattern_invalid
        in
        aux2 pat bdr
  in
  let brs, fb = aux1 [] brs in
  List.rev brs, fb

let structure_item modname ctx (str_item : Typedtree.structure_item) =
  match str_item.str_desc with
  | Tstr_value (rec_flag, [bdg]) ->
      begin match bdg.vb_pat.pat_desc with
      | Tpat_var (id, { loc; _ }, _) ->
          let global = Context.add_global ctx id in
          let val_ =
            if Attribute.has_opaque bdg.vb_attributes then
              Val_opaque
            else
              let restore_locals = Context.save_locals ctx in
              let rec_, expr =
                match Attribute.has_overwrite bdg.vb_attributes with
                | None ->
                    rec_flag = Recursive, bdg.vb_expr
                | Some (rec_flag', attr) ->
                    match attr.attr_payload with
                    | PStr [{ pstr_desc= Pstr_eval (expr, _); _ }] ->
                        let rec_ = rec_flag = Recursive || rec_flag' = Recursive in
                        let env = Envaux.env_of_only_summary str_item.str_env in
                        let env =
                          if rec_ then
                            let val_descr : Types.value_description =
                              { val_type= Ctype.newvar ();
                                val_attributes= [];
                                val_kind= Val_reg;
                                val_loc= loc;
                                val_uid= Types.Uid.mk ~current_unit:modname;
                              }
                            in
                            Env.add_value id val_descr env
                          else
                            env
                        in
                        rec_, Typecore.type_expression env expr
                    | _ ->
                        error attr.attr_loc Attribute_overwrite_invalid_payload
              in
              if rec_ then
                Context.add_local ctx id ;
              let expr = expression ctx expr in
              restore_locals () ;
              match expr with
              | Fun (bdrs, expr) ->
                  let bdr = if rec_ then Some (Ident.name id) else None in
                  Val_rec (bdr, bdrs, expr)
              | _ ->
                  if expression_is_value expr then
                    Val_expr expr
                  else
                    unsupported bdg.vb_loc Def_invalid
          in
          [global, Val val_]
      | _ ->
          unsupported bdg.vb_pat.pat_loc Def_pattern
      end
  | Tstr_value _ ->
      unsupported str_item.str_loc Def_mutual
  | Tstr_type (_, tys) ->
      List.filter_map (fun (ty : Typedtree.type_declaration) ->
        let var = ty.typ_name.txt in
        let ty = ty.typ_type in
        match ty.type_kind with
        | Type_abstract _ ->
            None
        | Type_record (lbls, _) ->
            let lbls = List.map (fun lbl -> Ident.name lbl.Types.ld_id) lbls in
            let ty = if record_is_mutable ty then Type_record lbls else Type_product lbls in
            Some (var, Type ty)
        | Type_variant (_, Variant_unboxed) ->
            None
        | Type_variant (constrs, _) ->
            let tags =
              List.map (fun (constr : Types.constructor_declaration) ->
                begin match constr.cd_args with
                | Cstr_record _ ->
                    unsupported constr.cd_loc Type_inlined_record
                | _ ->
                    ()
                end ;
                Ident.name constr.cd_id
              ) constrs
            in
            Some (var, Type (Type_variant tags))
        | Type_open ->
            unsupported str_item.str_loc Type_extensible
      ) tys
  | Tstr_attribute attr ->
      if Attribute.has_prefix [attr] then (
        match attr.attr_payload with
        | PStr [{ pstr_desc= Pstr_eval ({ pexp_desc= Pexp_constant { pconst_desc= Pconst_string (pref, _, _); _ }; _ }, _); _ }] ->
            Context.set_prefix ctx pref
        | _ ->
            error attr.attr_loc Attribute_prefix_invalid_payload
      ) ;
      []
  | Tstr_eval _ ->
      unsupported str_item.str_loc Def_eval
  | Tstr_primitive _ ->
      unsupported str_item.str_loc Def_primitive
  | Tstr_typext _ ->
      unsupported str_item.str_loc Type_extensible
  | Tstr_exception _ ->
      unsupported str_item.str_loc Def_exception
  | Tstr_module _
  | Tstr_recmodule _ ->
      unsupported str_item.str_loc Def_module
  | Tstr_modtype _ ->
      unsupported str_item.str_loc Def_module_type
  | Tstr_open _ ->
      unsupported str_item.str_loc Def_open
  | Tstr_class _ ->
      unsupported str_item.str_loc Def_class
  | Tstr_class_type _ ->
      unsupported str_item.str_loc Def_class_type
  | Tstr_include _ ->
      unsupported str_item.str_loc Def_include

let structure modname (str : Typedtree.structure) =
  let env = Envaux.env_of_only_summary str.str_final_env in
  let ctx = Context.create modname env in
  let definitions = List.concat_map (structure_item modname ctx) str.str_items in
  let dependencies = Context.dependencies ctx in
  { modname; dependencies; definitions }
