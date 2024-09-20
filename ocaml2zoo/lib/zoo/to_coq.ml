open Syntax

let pp_nothing _ppf () =
  ()
let pp_space ppf () =
  Format.pp_print_char ppf ' '
let pp_comma ppf () =
  Format.pp_print_string ppf ", "

let rec pp_list_index ~pp_sep pp_item ppf i = function
  | [] ->
      ()
  | x :: xs ->
      pp_sep ppf () ;
      pp_item ppf i x ;
      pp_list_index ~pp_sep pp_item ppf (i + 1) xs
let pp_list_index ?(pp_sep = Format.pp_print_cut) pp_item ppf = function
  | [] ->
      ()
  | x :: xs ->
      pp_item ppf 0 x ;
      pp_list_index ~pp_sep pp_item ppf 1 xs

let boolean ppf =
  Format.fprintf ppf "#%B"
let integer ppf =
  Format.fprintf ppf "#%i"

let global_variable ppf global =
  Format.fprintf ppf "%s" global
let local_variable ppf local =
  Format.fprintf ppf {|"%s"|} local

let binder ppf = function
  | None ->
      Format.fprintf ppf "<>"
  | Some local ->
      local_variable ppf local

let typ ppf (var, ty) =
  match ty with
  | Type_product flds ->
      pp_list_index (fun ppf i fld ->
        Format.fprintf ppf {|Notation "'%s'" := (@,  in_type "%s" %i@,)(in custom zoo_proj@,).|}
          fld var i
      ) ppf flds
  | Type_record flds ->
      pp_list_index (fun ppf i fld ->
        Format.fprintf ppf {|Notation "'%s'" := (@,  in_type "%s" %i@,)(in custom zoo_field@,).|}
          fld var i
      ) ppf flds
  | Type_variant tags ->
      pp_list_index (fun ppf i tag ->
        Format.fprintf ppf {|Notation "'%s'" := (@,  in_type "%s" %i@,)(in custom zoo_tag@,).|}
          tag var i
      ) ppf tags

let pattern ppf = function
  | Pat_var var ->
      local_variable ppf var
  | Pat_tuple bdrs ->
      Format.pp_print_list ~pp_sep:pp_comma binder ppf bdrs
  | Pat_constr (tag, bdrs) ->
      Format.fprintf ppf "‘%s %a"
      tag
      (Format.pp_print_list ~pp_sep:pp_comma binder) bdrs

let unop ppf op =
  Format.pp_print_char ppf
    begin match op with
    | Unop_neg ->
        '~'
    | Unop_minus ->
        '-'
    end

let binop ppf op =
  Format.pp_print_string ppf
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
        "="
    | Binop_ne ->
        "≠"
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
    end

let max_level =
  200
let next_level lvl =
  lvl - 1
let level = function
  | Constr (_, "[]", _) ->
      1
  | Constr (_, "::", _) ->
      60
  | Tuple _
  | Record _
  | Constr _ ->
      0
  | Global _
  | Local _
  | If _
  | For _
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
  | Binop (Binop_gt, _, _) ->
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
  | Fun _
  | Match _ ->
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
      Format.fprintf ppf "@[<v>@[<hv>let: %a :=@;<1 2>@[%a@]@;in@]@,%a@]"
        pattern pat
        (expression max_level) expr1
        (expression max_level) expr2
  | Letrec (rec_flag, local, bdrs, expr1, expr2) ->
      Format.fprintf ppf "@[<v>@[<hv>let%s: %a %a :=@;<1 2>@[%a@]@;in@]@,%a@]"
        (match rec_flag with Nonrecursive -> "" | Recursive -> "rec")
        local_variable local
        (Format.pp_print_list ~pp_sep:pp_space binder) bdrs
        (expression max_level) expr1
        (expression max_level) expr2
  | Seq (expr1, expr2) ->
      Format.fprintf ppf "@[<v>@[" ;
      begin match expr1 with
      | If (expr1, expr2, expr3) ->
          expression_if ~force_else:true ppf expr1 expr2 expr3
      | _ ->
          expression (next_level lvl) ppf expr1
      end ;
      Format.fprintf ppf "@] ;;@,%a@]"
        (expression max_level) expr2
  | Fun (bdrs, expr) ->
      Format.fprintf ppf "@[<hv>fun: %a =>@;<1 2>%a@]"
        (Format.pp_print_list ~pp_sep:pp_space binder) bdrs
        (expression max_level) expr
  | Apply (expr, exprs) ->
      Format.fprintf ppf "@[<hv>@[%a@]%a@]"
        (expression lvl) expr
        Format.(pp_print_list ~pp_sep:pp_nothing (fun ppf -> fprintf ppf "@;<1 2>@[%a@]" (expression @@ next_level lvl))) exprs
  | Unop (op, expr) ->
      Format.fprintf ppf "%a %a"
        unop op
        (expression lvl) expr
  | Binop (op, expr1, expr2) ->
      Format.fprintf ppf "%a %a %a"
        (expression lvl) expr1
        binop op
        (expression @@ next_level lvl) expr2
  | If (expr1, expr2, expr3) ->
      expression_if ppf expr1 expr2 expr3
  | For (local, expr1, expr2, expr3) ->
      Format.fprintf ppf "@[<v>for: %a := %a to %a begin@,  @[%a@]@,end@]"
        binder local
        (expression max_level) expr1
        (expression max_level) expr2
        (expression max_level) expr3
  | Alloc (expr1, expr2) ->
      Format.fprintf ppf "@[<hv>Alloc@;<1 2>@[%a@]@;<1 2>@[%a@]@]"
        (expression @@ next_level lvl) expr1
        (expression @@ next_level lvl) expr2
  | Tuple exprs ->
      Format.fprintf ppf "@[<hv>(%a@,)@]"
        Format.(pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf ",@;<1 1>") (fun ppf -> fprintf ppf "@[%a@]" (expression max_level))) exprs
  | Ref expr ->
      Format.fprintf ppf "@[<hv>ref@;<1 2>@[%a@]@]"
        (expression @@ next_level lvl) expr
  | Record exprs ->
      Format.fprintf ppf "@[<hv>{ %a@;}@]"
        Format.(pp_print_array ~pp_sep:(fun ppf () -> fprintf ppf ",@;<1 2>") (fun ppf -> fprintf ppf "@[%a@]" (expression max_level))) exprs
  | Constr (_, "[]", _) ->
      Format.fprintf ppf "[]"
  | Constr (_, "::", exprs) ->
      let[@warning "-8"] [expr1; expr2] = exprs in
      Format.fprintf ppf "@[<hv>%a ::@;<1 2>@[%a@]@]"
        (expression @@ next_level lvl) expr1
        (expression lvl) expr2
  | Constr (_, tag, []) ->
      Format.fprintf ppf "§%s"
        tag
  | Constr (concrete, tag, exprs) ->
      Format.fprintf ppf "@[<hv>‘%s%c %a@;%c@]"
        tag
        (match concrete with Concrete -> '{' | Abstract -> '(')
        Format.(pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf ",@;<1 2>") (fun ppf -> fprintf ppf "@[%a@]" (expression max_level))) exprs
        (match concrete with Concrete -> '}' | Abstract -> ')')
  | Proj (expr, fld) ->
      Format.fprintf ppf "@[%a@].<%s>"
        (expression lvl) expr
        fld
  | Match (expr, brs, fb) ->
      Format.fprintf ppf "@[<v>@[<hv>match:@;<1 2>@[%a@]@;with@]@,%a%aend@]"
        (expression max_level) expr
        Format.(pp_print_list ~pp_sep:pp_nothing branch) brs
        Format.(pp_print_option fallback) fb
  | Ref_get expr ->
      Format.fprintf ppf "!@[%a@]"
        (expression lvl) expr
  | Ref_set (expr1, expr2) ->
      Format.fprintf ppf "@[<hv>@[<hv>@[%a@]@;<1 2><-@]@;<1 2>@[%a@]@]"
        (expression @@ next_level lvl) expr1
        (expression lvl) expr2
  | Record_get (expr, fld) ->
      Format.fprintf ppf "@[%a@].{%s}"
        (expression lvl) expr
        fld
  | Record_set (expr1, fld, expr2) ->
      Format.fprintf ppf "@[<hv>@[<hv>@[%a@]@;<1 2><-{%s}@]@;<1 2>@[%a@]@]"
        (expression @@ next_level lvl) expr1
        fld
        (expression lvl) expr2
  | Get_tag expr ->
      Format.fprintf ppf "@[<hv>GetTag@;<1 2>@[%a@]@]"
        (expression @@ next_level lvl) expr
  | Get_size expr ->
      Format.fprintf ppf "@[<hv>GetSize@;<1 2>@[%a@]@]"
        (expression @@ next_level lvl) expr
  | Atomic_loc (expr, fld) ->
      Format.fprintf ppf "@[%a@].[%s]"
        (expression lvl) expr
        fld
  | Load (expr1, expr2) ->
      Format.fprintf ppf "@[<hv>Load@;<1 2>@[%a@]@;<1 2>@[%a@]@]"
        (expression @@ next_level lvl) expr1
        (expression @@ next_level lvl) expr2
  | Store (expr1, expr2, expr3) ->
      Format.fprintf ppf "@[<hv>Store@;<1 2>@[%a@]@;<1 2>@[%a@]@;<1 2>@[%a@]@]"
        (expression @@ next_level lvl) expr1
        (expression @@ next_level lvl) expr2
        (expression @@ next_level lvl) expr3
  | Xchg (expr1, expr2) ->
      Format.fprintf ppf "@[<hv>Xchg@;<1 2>@[%a@]@;<1 2>@[%a@]@]"
        (expression @@ next_level lvl) expr1
        (expression @@ next_level lvl) expr2
  | Cas (expr1, expr2, expr3) ->
      Format.fprintf ppf "@[<hv>CAS@;<1 2>@[%a@]@;<1 2>@[%a@]@;<1 2>@[%a@]@]"
        (expression @@ next_level lvl) expr1
        (expression @@ next_level lvl) expr2
        (expression @@ next_level lvl) expr3
  | Faa (expr1, expr2) ->
      Format.fprintf ppf "@[<hv>FAA@;<1 2>@[%a@]@;<1 2>@[%a@]@]"
        (expression @@ next_level lvl) expr1
        (expression @@ next_level lvl) expr2
  | Fail ->
      Format.fprintf ppf "Fail"
  | Yield ->
      Format.fprintf ppf "Yield"
  | Proph ->
      Format.fprintf ppf "Proph"
  | Resolve (expr1, expr2, expr3) ->
      Format.fprintf ppf "@[<hv>Resolve@;<1 2>@[%a@]@;<1 2>@[%a@]@;<1 2>@[%a@]@]"
        (expression @@ next_level lvl) expr1
        (expression @@ next_level lvl) expr2
        (expression @@ next_level lvl) expr3
  | Id ->
      Format.fprintf ppf "Id"
and expression lvl ppf expr =
  let lvl_expr = level expr in
  if lvl < lvl_expr then
    Format.fprintf ppf "(%a)" (expression' lvl_expr) expr
  else
    Format.fprintf ppf "%a" (expression' lvl_expr) expr
and expression_if_aux ?(nested = false) ?(force_else = false) ppf expr1 expr2 expr3 =
  let neg, expr1 =
    begin match expr1 with
    | Unop (Unop_neg, expr1) ->
        true, expr1
    | _ ->
        false, expr1
    end
  in
  Format.fprintf ppf "@[<hv>%sif%s:@;<1 2>@[%a@]@;then (@]@,  @[%a@]@,)"
    (if nested then " else " else "")
    (if neg then "not" else "")
    (expression max_level) expr1
    (expression max_level) expr2 ;
  match expr3 with
  | None ->
      if force_else then
        Format.fprintf ppf " else (@,  ()@,)"
  | Some expr3 ->
      match expr3 with
      | If (expr1, expr2, expr3) ->
          expression_if_aux ~nested:true ppf expr1 expr2 expr3
      | expr ->
          Format.fprintf ppf " else (@,  @[%a@]@,)"
            (expression max_level) expr
and expression_if ?force_else ppf expr1 expr2 expr3 =
  Format.fprintf ppf "@[<v>" ;
  expression_if_aux ?force_else ppf expr1 expr2 expr3 ;
  Format.fprintf ppf "@]"
and branch ppf br =
  begin match br.branch_tag with
  | "[]" ->
      Format.fprintf ppf "| []"
  | "::" ->
      let[@warning "-8"] [bdr1; bdr2] = br.branch_binders in
      Format.fprintf ppf "| %a :: %a"
        binder bdr1
        binder bdr2
  | _ ->
      Format.fprintf ppf "| %s%s%a"
        br.branch_tag
        (match br.branch_binders with [] -> "" | _ -> " ")
        Format.(pp_print_list ~pp_sep:pp_space binder) br.branch_binders
  end ;
  Format.fprintf ppf "%a =>@,    @[%a@]@,"
    Format.(pp_print_option @@ fun ppf -> fprintf ppf " as %a" local_variable) br.branch_as
    (expression max_level) br.branch_expr
and fallback ppf fb =
  Format.fprintf ppf "|_%a =>@,    @[%a@]@,"
    Format.(pp_print_option @@ fun ppf -> fprintf ppf " as %a" local_variable) fb.fallback_as
    (expression max_level) fb.fallback_expr
let expression =
  expression max_level

let value ppf (global, val_) =
  match val_ with
  | Val_expr expr ->
      Format.fprintf ppf "Definition %a : val :=@,  @[%a@]."
        global_variable global
        expression expr
  | Val_rec (local, params, expr) ->
      Format.fprintf ppf "Definition %a : val :=@,  @[<v>%s: %a%a =>@,  @[%a@]@]."
        global_variable global
        (if Option.is_none local then "fun" else "rec")
        Format.(pp_print_option @@ fun ppf -> fprintf ppf "%a " local_variable) local
        (Format.pp_print_list ~pp_sep:pp_space binder) params
        expression expr
  | Val_opaque ->
      Format.fprintf ppf "Parameter %a : val."
        global_variable global

let structure ?dir pp select ppf str =
  Format.fprintf ppf "@[<v>" ;
  Format.fprintf ppf "From zoo Require Import@,  prelude.@," ;
  Format.fprintf ppf "From zoo.language Require Import@,  notations.@," ;
  if str.dependencies <> [] then (
    Format.fprintf ppf "From zoo Require Import@," ;
    Format.(pp_print_list ~pp_sep:pp_print_cut (fun ppf -> fprintf ppf "  %s")) ppf str.dependencies ;
    Format.fprintf ppf ".@,"
  ) ;
  begin match dir with
  | None ->
      ()
  | Some dir ->
      Format.fprintf ppf "From zoo.%s Require Import@,  %s__types.@," dir str.modname
  end ;
  Format.fprintf ppf "From zoo Require Import@,  options.@,@," ;
  Format.(pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "@,@,")) pp ppf (select str) ;
  Format.fprintf ppf "@]@."
let structure ~dir ~types:ppf_types ~code:ppf_code str =
  structure typ structure_types ppf_types str ;
  structure ~dir value structure_values ppf_code str
