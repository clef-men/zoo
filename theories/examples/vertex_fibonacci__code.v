Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_parabs.pool.
Require Import zoo_parabs.vertex.
Require Import zoo_std.ivar_4.
Require Import examples.vertex_fibonacci__types.
Require Import zoo.options.

Definition vertex_fibonacci٠main₀ : val :=
  𝗿𝗲𝗰 "main" "ctx" "vtx" "r" "n" ->
    𝗶𝗳 "n" ≤ 1 𝘁𝗵𝗲𝗻 (
      "r" <- "n" ⍮
      true
    ) 𝗲𝗹𝘀𝗲 (
      𝗹𝗲𝘁 "r1" = 𝗿𝗲𝗳 0 𝗶𝗻
      𝗹𝗲𝘁 "vtx1" = vertex٠create §None 𝗶𝗻
      𝗹𝗲𝘁 "n1" = "n" - 1 𝗶𝗻
      vertex٠set_task
        "vtx1"
        (𝗳𝘂𝗻 "ctx" -> "main" "ctx" "vtx1" "r1" "n1") ⍮
      vertex٠release "ctx" "vtx1" ⍮
      𝗹𝗲𝘁 "r2" = 𝗿𝗲𝗳 0 𝗶𝗻
      𝗹𝗲𝘁 "vtx2" = vertex٠create §None 𝗶𝗻
      𝗹𝗲𝘁 "n2" = "n" - 2 𝗶𝗻
      vertex٠set_task
        "vtx2"
        (𝗳𝘂𝗻 "ctx" -> "main" "ctx" "vtx2" "r2" "n2") ⍮
      vertex٠release "ctx" "vtx2" ⍮
      vertex٠precede "vtx1" "vtx" ⍮
      vertex٠precede "vtx2" "vtx" ⍮
      vertex٠yield "vtx"
        (𝗳𝘂𝗻 "_ctx" -> "r" <- !"r1" + !"r2" ⍮
                                true)
    ).

Definition vertex_fibonacci٠main : val :=
  𝗳𝘂𝗻 "num_worker" "n" ->
    pool٠run
      "num_worker"
      (𝗳𝘂𝗻 "ctx" ->
         𝗹𝗲𝘁 "r" = 𝗿𝗲𝗳 0 𝗶𝗻
         𝗹𝗲𝘁 "vtx1" = vertex٠create §None 𝗶𝗻
         vertex٠set_task
           "vtx1"
           (𝗳𝘂𝗻 "ctx" ->
              vertex_fibonacci٠main₀ "ctx" "vtx1" "r" "n") ⍮
         vertex٠release "ctx" "vtx1" ⍮
         𝗹𝗲𝘁 "ivar" = ivar_4٠create () 𝗶𝗻
         𝗹𝗲𝘁 "vtx2" =
           vertex٠create'
             (𝗳𝘂𝗻 "ctx" -> ivar_4٠notify "ivar" "ctx" ())
         𝗶𝗻
         vertex٠precede "vtx1" "vtx2" ⍮
         vertex٠release "ctx" "vtx2" ⍮
         pool٠wait_ivar "ctx" "ivar" ⍮
         !"r").
