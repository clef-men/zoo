let usage =
  "usage: ocaml2zoo <cmt_file>"

let error ?(with_usage = true) fmt =
  Fmt.kpf (fun ppf ->
    if with_usage then
      Fmt.pf ppf "@,%s" usage ;
    Fmt.pf ppf "@]@." ;
    exit 1
  ) Fmt.stderr ("@[<v>" ^^ fmt)

let filename =
  try
    Sys.argv.(1)
  with Invalid_argument _ ->
    error "no input file"

let () =
  match Cmt_format.read_cmt filename with
  | exception Sys_error err ->
      error "invalid input file: %s" err
  | exception Cmt_format.Error _
  | exception Cmi_format.Error _ ->
      error "invalid input file"
  | cmt ->
      match cmt.cmt_annots with
      | Implementation str ->
          Load_path.(init ~auto_include:no_auto_include ~visible:cmt.cmt_loadpath.visible ~hidden:cmt.cmt_loadpath.hidden) ;
          let modname = String.uncapitalize_ascii cmt.cmt_modname in
          begin match Zoo.Of_ocaml.structure modname str with
          | exception Zoo.Of_ocaml.Error (loc, err) ->
              error ~with_usage:false "%a:@,%a"
                Location.print_loc loc
                Zoo.Of_ocaml.Error.pp err
          | str ->
              let filename = Filename.remove_extension filename in
              let dir = Filename.(basename @@ dirname filename) in
              let file_types = Format.formatter_of_out_channel @@ open_out @@ filename ^ "__types.v" in
              let file_code = Format.formatter_of_out_channel @@ open_out @@ filename ^ "__code.v" in
              Zoo.To_coq.structure ~dir ~types:file_types ~code:file_code str
          end
      | _ ->
          error "invalid input file: not an implementation"
