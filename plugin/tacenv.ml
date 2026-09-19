include Ltac_plugin.Tacenv

let locate_tactic id =
  try
    locate_tactic id
  with Not_found ->
    CErrors.user_err @@
      Pp.fmt "Tactic %s was not found."
        (id |> Libnames.string_of_qualid)
