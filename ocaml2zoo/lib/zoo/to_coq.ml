open Syntax

module Fmt = struct
  include Fmt

  let rec list_index ~sep item ppf i = function
    | [] ->
        ()
    | x :: xs ->
        sep ppf () ;
        item ppf i x ;
        list_index ~sep item ppf (i + 1) xs
  let list_index ?(sep = cut) item ppf = function
    | [] ->
        ()
    | x :: xs ->
        item ppf 0 x ;
        list_index ~sep item ppf 1 xs
end

let boolean ppf =
  Fmt.pf ppf "#%B"
let integer ppf =
  Fmt.pf ppf "#%i"

let global_variable ppf global =
  Fmt.pf ppf "%s" global
let local_variable ppf local =
  Fmt.pf ppf {|"%s"|} local

let binder ppf = function
  | None ->
      Fmt.pf ppf "<>"
  | Some local ->
      local_variable ppf local

let typ ppf (var, ty) =
  match ty with
  | Type_product flds ->
      Fmt.list_index (fun ppf i fld ->
        Fmt.pf ppf {|Notation "'%s'" := (@,  in_type "%s" %i@,)(in custom zoo_proj@,).|}
          fld var i
      ) ppf flds
  | Type_record flds ->
      Fmt.list_index (fun ppf i fld ->
        Fmt.pf ppf {|Notation "'%s'" := (@,  in_type "%s" %i@,)(in custom zoo_field@,).|}
          fld var i
      ) ppf flds
  | Type_variant tags ->
      Fmt.list_index (fun ppf i tag ->
        Fmt.pf ppf {|Notation "'%s'" := (@,  in_type "%s" %i@,)(in custom zoo_tag@,).|}
          tag var i
      ) ppf tags

let pattern ppf = function
  | Pat_var var ->
      local_variable ppf var
  | Pat_tuple bdrs ->
      Fmt.(list ~sep:(const string ", ") binder) ppf bdrs
  | Pat_constr (tag, bdrs) ->
      Fmt.pf ppf "‘%s %a"
        tag
        Fmt.(list ~sep:(const string ", ") binder) bdrs

let unop ppf op =
  Fmt.char ppf
    begin match op with
    | Unop_neg ->
        '~'
    | Unop_minus ->
        '-'
    end

let binop ppf op =
  Fmt.string ppf
    begin match op with
    | Binop_plus ->
        "+"
    | Binop_minus ->
        "-"
    | Binop_mult ->
        "*"
    | Binop_quot ->
        "`quot`"
    | Binop_rem ->
        "`rem`"
    | Binop_eq ->
        "=="
    | Binop_ne ->
        "!="
    | Binop_le ->
        "≤"
    | Binop_lt ->
        "<"
    | Binop_ge ->
        "≥"
    | Binop_gt ->
        ">"
    | Binop_and ->
        "and"
    | Binop_or ->
        "or"
    | Binop_structeq ->
        "="
    | Binop_structne ->
        "≠"
    end

let max_level =
  200
let next_level lvl =
  lvl - 1
let level = function
  | Constr (_, "::", _) ->
      60
  | Global _
  | Local _
  | If _
  | For _
  | Tuple _
  | Record _
  | Constr _
  | Match _
  | Fail
  | Yield
  | Proph
  | Id ->
      1
  | Proj _ ->
      2
  | Bool _
  | Int _ ->
      8
  | Ref_get _
  | Record_get _
  | Atomic_loc _ ->
      9
  | Apply _
  | Alloc _
  | Ref _
  | Reveal _
  | Get_tag _
  | Get_size _
  | Load _
  | Store _
  | Resolve _
  | Xchg _
  | Cas _
  | Faa _ ->
      10
  | Unop (Unop_minus, _)
  | Binop (Binop_quot, _, _)
  | Binop (Binop_rem, _, _) ->
      35
  | Binop (Binop_mult, _, _) ->
      40
  | Binop (Binop_plus, _, _)
  | Binop (Binop_minus, _, _) ->
      50
  | Binop (Binop_eq, _, _)
  | Binop (Binop_ne, _, _)
  | Binop (Binop_le, _, _)
  | Binop (Binop_lt, _, _)
  | Binop (Binop_ge, _, _)
  | Binop (Binop_gt, _, _)
  | Binop (Binop_structeq, _, _)
  | Binop (Binop_structne, _, _) ->
      70
  | Unop (Unop_neg, _) ->
      75
  | Binop (Binop_and, _, _) ->
      76
  | Binop (Binop_or, _, _) ->
      77
  | Ref_set _
  | Record_set _ ->
      80
  | Seq _ ->
      100
  | Let _
  | Letrec _
  | Fun _ ->
      max_level
let rec expression' lvl ppf = function
  | Global global ->
      global_variable ppf global
  | Local local ->
      local_variable ppf local
  | Bool bool ->
      boolean ppf bool
  | Int int ->
      integer ppf int
  | Let (pat, expr1, expr2) ->
      Fmt.pf ppf "@[<v>@[<hv>let: %a :=@;<1 2>@[%a@]@;in@]@,%a@]"
        pattern pat
        (expression max_level) expr1
        (expression max_level) expr2
  | Letrec (rec_flag, local, bdrs, expr1, expr2) ->
      Fmt.pf ppf "@[<v>@[<hv>let%s: %a %a :=@;<1 2>@[%a@]@;in@]@,%a@]"
        (match rec_flag with Nonrecursive -> "" | Recursive -> "rec")
        local_variable local
        Fmt.(list ~sep:(const char ' ') binder) bdrs
        (expression max_level) expr1
        (expression max_level) expr2
  | Seq (expr1, expr2) ->
      Fmt.pf ppf "@[<v>@[" ;
      begin match expr1 with
      | If (expr1, expr2, expr3) ->
          expression_if ~force_else:true ppf expr1 expr2 expr3
      | _ ->
          expression (next_level lvl) ppf expr1
      end ;
      Fmt.pf ppf "@] ;;@,%a@]"
        (expression max_level) expr2
  | Fun (bdrs, expr) ->
      Fmt.pf ppf "@[<hv>fun: %a =>@;<1 2>%a@]"
        Fmt.(list ~sep:(const char ' ') binder) bdrs
        (expression max_level) expr
  | Apply (expr, exprs) ->
      Fmt.pf ppf "@[<hv>@[%a@]%a@]"
        (expression lvl) expr
        Fmt.(list ~sep:nop (fun ppf -> pf ppf "@;<1 2>@[%a@]" (expression @@ next_level lvl))) exprs
  | Unop (op, expr) ->
      Fmt.pf ppf "@[%a %a@]"
        unop op
        (expression lvl) expr
  | Binop (op, expr1, expr2) ->
      Fmt.pf ppf "@[%a %a@;%a@]"
        (expression lvl) expr1
        binop op
        (expression @@ next_level lvl) expr2
  | If (expr1, expr2, expr3) ->
      expression_if ppf expr1 expr2 expr3
  | For (local, expr1, expr2, expr3) ->
      Fmt.pf ppf "@[<v>for: %a := %a to %a begin@,  @[%a@]@,end@]"
        binder local
        (expression max_level) expr1
        (expression max_level) expr2
        (expression max_level) expr3
  | Alloc (expr1, expr2) ->
      Fmt.pf ppf "@[<hv>Alloc@;<1 2>@[%a@]@;<1 2>@[%a@]@]"
        (expression @@ next_level lvl) expr1
        (expression @@ next_level lvl) expr2
  | Tuple exprs ->
      Fmt.pf ppf "@[<hv>(%a@,)@]"
        Fmt.(list ~sep:(any ",@;<1 1>") (fun ppf -> pf ppf "@[%a@]" (expression max_level))) exprs
  | Ref expr ->
      Fmt.pf ppf "@[<hv>ref@;<1 2>@[%a@]@]"
        (expression @@ next_level lvl) expr
  | Record exprs ->
      Fmt.pf ppf "@[<hv>{ %a@;}@]"
        Fmt.(list ~sep:(any ",@;<1 2>") (fun ppf -> pf ppf "@[%a@]" (expression max_level))) exprs
  | Constr (_, "[]", _) ->
      Fmt.pf ppf "[]"
  | Constr (_, "::", exprs) ->
      let[@warning "-8"] [expr1; expr2] = exprs in
      Fmt.pf ppf "@[<hv>%a ::@;<1 2>@[%a@]@]"
        (expression @@ next_level lvl) expr1
        (expression lvl) expr2
  | Constr (_, tag, []) ->
      Fmt.pf ppf "§%s"
        tag
  | Constr (mut, tag, exprs) ->
      Fmt.pf ppf "@[<hv>‘%s%c %a@;%c@]"
        tag
        (if mut = Mutable then '{' else '(')
        Fmt.(list ~sep:(any ",@;<1 2>") (fun ppf -> pf ppf "@[%a@]" (expression max_level))) exprs
        (if mut = Mutable then '}' else ')')
  | Reveal expr ->
      Fmt.pf ppf "@[<hv>Reveal@;<1 2>@[%a@]@]"
        (expression @@ next_level lvl) expr
  | Proj (expr, fld) ->
      Fmt.pf ppf "@[%a@].<%s>"
        (expression lvl) expr
        fld
  | Match (expr, brs, fb) ->
      Fmt.pf ppf "@[<v>@[<hv>match:@;<1 2>@[%a@]@;with@]@,%a%aend@]"
        (expression max_level) expr
        Fmt.(list ~sep:nop branch) brs
        Fmt.(option fallback) fb
  | Ref_get expr ->
      Fmt.pf ppf "!@[%a@]"
        (expression lvl) expr
  | Ref_set (expr1, expr2) ->
      Fmt.pf ppf "@[<hv>@[<hv>@[%a@]@;<1 2><-@]@;<1 2>@[%a@]@]"
        (expression @@ next_level lvl) expr1
        (expression lvl) expr2
  | Record_get (expr, fld) ->
      Fmt.pf ppf "@[%a@].{%s}"
        (expression lvl) expr
        fld
  | Record_set (expr1, fld, expr2) ->
      Fmt.pf ppf "@[<hv>@[<hv>@[%a@]@;<1 2><-{%s}@]@;<1 2>@[%a@]@]"
        (expression @@ next_level lvl) expr1
        fld
        (expression lvl) expr2
  | Get_tag expr ->
      Fmt.pf ppf "@[<hv>GetTag@;<1 2>@[%a@]@]"
        (expression @@ next_level lvl) expr
  | Get_size expr ->
      Fmt.pf ppf "@[<hv>GetSize@;<1 2>@[%a@]@]"
        (expression @@ next_level lvl) expr
  | Atomic_loc (expr, fld) ->
      Fmt.pf ppf "@[%a@].[%s]"
        (expression lvl) expr
        fld
  | Load (expr1, expr2) ->
      Fmt.pf ppf "@[<hv>Load@;<1 2>@[%a@]@;<1 2>@[%a@]@]"
        (expression @@ next_level lvl) expr1
        (expression @@ next_level lvl) expr2
  | Store (expr1, expr2, expr3) ->
      Fmt.pf ppf "@[<hv>Store@;<1 2>@[%a@]@;<1 2>@[%a@]@;<1 2>@[%a@]@]"
        (expression @@ next_level lvl) expr1
        (expression @@ next_level lvl) expr2
        (expression @@ next_level lvl) expr3
  | Xchg (expr1, expr2) ->
      Fmt.pf ppf "@[<hv>Xchg@;<1 2>@[%a@]@;<1 2>@[%a@]@]"
        (expression @@ next_level lvl) expr1
        (expression @@ next_level lvl) expr2
  | Cas (expr1, expr2, expr3) ->
      Fmt.pf ppf "@[<hv>CAS@;<1 2>@[%a@]@;<1 2>@[%a@]@;<1 2>@[%a@]@]"
        (expression @@ next_level lvl) expr1
        (expression @@ next_level lvl) expr2
        (expression @@ next_level lvl) expr3
  | Faa (expr1, expr2) ->
      Fmt.pf ppf "@[<hv>FAA@;<1 2>@[%a@]@;<1 2>@[%a@]@]"
        (expression @@ next_level lvl) expr1
        (expression @@ next_level lvl) expr2
  | Fail ->
      Fmt.pf ppf "Fail"
  | Yield ->
      Fmt.pf ppf "Yield"
  | Proph ->
      Fmt.pf ppf "Proph"
  | Resolve (expr1, expr2, expr3) ->
      Fmt.pf ppf "@[<hv>Resolve@;<1 2>@[%a@]@;<1 2>@[%a@]@;<1 2>@[%a@]@]"
        (expression @@ next_level lvl) expr1
        (expression @@ next_level lvl) expr2
        (expression @@ next_level lvl) expr3
  | Id ->
      Fmt.pf ppf "Id"
and expression lvl ppf expr =
  let lvl_expr = level expr in
  if lvl < lvl_expr then
    Fmt.pf ppf "(%a)" (expression' lvl_expr) expr
  else
    Fmt.pf ppf "%a" (expression' lvl_expr) expr
and expression_if_aux ?(nested = false) ?(force_else = false) ppf expr1 expr2 expr3 =
  let neg, expr1 =
    begin match expr1 with
    | Unop (Unop_neg, expr1) ->
        true, expr1
    | _ ->
        false, expr1
    end
  in
  Fmt.pf ppf "@[<hv>%sif%s:@;<1 2>@[%a@]@;then (@]@,  @[%a@]@,)"
    (if nested then " else " else "")
    (if neg then "not" else "")
    (expression max_level) expr1
    (expression max_level) expr2 ;
  match expr3 with
  | None ->
      if force_else then
        Fmt.pf ppf " else (@,  ()@,)"
  | Some expr3 ->
      match expr3 with
      | If (expr1, expr2, expr3) ->
          expression_if_aux ~nested:true ppf expr1 expr2 expr3
      | expr ->
          Fmt.pf ppf " else (@,  @[%a@]@,)"
            (expression max_level) expr
and expression_if ?force_else ppf expr1 expr2 expr3 =
  Fmt.pf ppf "@[<v>" ;
  expression_if_aux ?force_else ppf expr1 expr2 expr3 ;
  Fmt.pf ppf "@]"
and branch ppf br =
  Fmt.pf ppf "| " ;
  begin match br.branch_tag with
  | "[]" ->
      Fmt.pf ppf "[]"
  | "::" ->
      let[@warning "-8"] [bdr1; bdr2] = br.branch_fields in
      Fmt.pf ppf "%a :: %a"
        binder bdr1
        binder bdr2
  | _ ->
      Fmt.pf ppf "%s%s%a"
        br.branch_tag
        (match br.branch_fields with [] -> "" | _ -> " ")
        Fmt.(list ~sep:(const char ' ') binder) br.branch_fields
  end ;
  Fmt.pf ppf "%a =>@,    @[%a@]@,"
    Fmt.(option @@ fun ppf -> pf ppf " as %a" local_variable) br.branch_as
    (expression max_level) br.branch_expr
and fallback ppf fb =
  Fmt.pf ppf "|_%a =>@,    @[%a@]@,"
    Fmt.(option @@ fun ppf -> pf ppf " as %a" local_variable) fb.fallback_as
    (expression max_level) fb.fallback_expr
let expression =
  expression max_level

let value fresh ppf = function
  | Val_expr (global, expr) ->
      Fmt.pf ppf "Definition %a : val :=@,  @[%a@]."
        global_variable global
        expression expr
  | Val_fun (global, params, expr) ->
      Fmt.pf ppf "Definition %a : val :=@,  @[<v>fun: %a =>@,  @[%a@]@]."
        global_variable global
        Fmt.(list ~sep:(const char ' ') binder) params
        expression expr
  | Val_recs [global, local, params, body] ->
      Fmt.pf ppf "Definition %a : val :=@,  @[<v>rec: %a %a =>@,  @[%a@]@]."
        global_variable global
        local_variable local
        Fmt.(list ~sep:(const char ' ') binder) params
        expression body
  | Val_recs recs ->
      let id = fresh () in
      Fmt.pf ppf "#[local] Definition __zoo_recs_%i := (@,  @[<v>recs: %a@]@,)%%zoo_recs.@,%a@,%a"
        id
        Fmt.(
          list
            ~sep:(
              fun ppf () ->
                pf ppf "@,and: "
            )
            ( fun ppf (_, local, params, body) ->
                pf ppf "%a %a =>@,  @[%a@]"
                  local_variable local
                  (list ~sep:(const char ' ') binder) params
                  expression body
            )
        ) recs
        ( Fmt.list_index (fun ppf i (global, _, _, _) ->
            Fmt.pf ppf "Definition %a :=@,  ValRecs %i __zoo_recs_%i."
              global_variable global
              i
              id
          )
        ) recs
        ( Fmt.list_index (fun ppf i (global, _, _, _) ->
            Fmt.pf ppf "#[global] Instance :@,  @[<v>AsValRecs' %a %i __zoo_recs_%i [@,  @[<v>%a@]@,].@]@,Proof.@,  done.@,Qed."
              global_variable global
              i
              id
              Fmt.(list ~sep:(any " ;@,") (fun ppf (global, _, _, _) -> global_variable ppf global)) recs
          )
        ) recs
  | Val_opaque global ->
      Fmt.pf ppf "Parameter %a : val."
        global_variable global
let value () =
  let gen = ref 0 in
  value (fun () -> let i = !gen in gen := i + 1 ; i)

let structure ?dir pp select ppf str =
  Fmt.pf ppf "@[<v>" ;
  Fmt.pf ppf "From zoo Require Import@,  prelude.@," ;
  Fmt.pf ppf "From zoo.language Require Import@,  typeclasses@,  notations.@," ;
  if str.dependencies <> [] then (
    Fmt.pf ppf "From zoo Require Import@," ;
    Fmt.(list (fun ppf -> pf ppf "  %s")) ppf str.dependencies ;
    Fmt.pf ppf ".@,"
  ) ;
  begin match dir with
  | None ->
      ()
  | Some dir ->
      Fmt.pf ppf "From zoo.%s Require Import@,  %s__types.@," dir str.modname
  end ;
  Fmt.pf ppf "From zoo Require Import@,  options.@,@," ;
  Fmt.(list ~sep:(any "@,@,")) pp ppf (select str) ;
  Fmt.pf ppf "@]@."
let structure ~dir ~types:ppf_types ~code:ppf_code str =
  structure typ structure_types ppf_types str ;
  structure ~dir (value ()) structure_values ppf_code str
