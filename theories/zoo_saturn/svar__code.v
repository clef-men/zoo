Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo.program_logic.identifier.
Require Import zoo.options.

Notation "'svar٠snapshot_value'" := (
  in_type "zoo_saturn.svar.snapshot" 0
)(in custom zoo_proj
).
Notation "'svar٠snapshot_gen'" := (
  in_type "zoo_saturn.svar.snapshot" 1
)(in custom zoo_proj
).

Notation "'svar٠Forward'" := (
  in_type "zoo_saturn.svar.prophecy" 0
)(in custom zoo_tag
).
Notation "'svar٠Set'" := (
  in_type "zoo_saturn.svar.prophecy" 1
)(in custom zoo_tag
).

Notation "'svar٠value'" := (
  in_type "zoo_saturn.svar.t" 0
)(in custom zoo_field
).
Notation "'svar٠gen'" := (
  in_type "zoo_saturn.svar.t" 1
)(in custom zoo_field
).
Notation "'svar٠snapshot'" := (
  in_type "zoo_saturn.svar.t" 2
)(in custom zoo_field
).
Notation "'svar٠proph'" := (
  in_type "zoo_saturn.svar.t" 3
)(in custom zoo_field
).

Definition svar٠make : val :=
  𝗳𝘂𝗻 "v" ->
    𝗹𝗲𝘁 "snap" = ("v", 0) 𝗶𝗻
    { "v", 0, "snap", 𝗽𝗿𝗼𝗽𝗵 }.

Definition svar٠forward : val :=
  𝗳𝘂𝗻 "t" ->
    𝗹𝗲𝘁 "snap" = "t".{svar٠snapshot} 𝗶𝗻
    𝗹𝗲𝘁 "g" = "t".{svar٠gen} 𝗶𝗻
    𝗶𝗳 "snap".<svar٠snapshot_gen> != "g" 𝘁𝗵𝗲𝗻 (
      𝗹𝗲𝘁 "v" = "t".{svar٠value} 𝗶𝗻
      𝗹𝗲𝘁 "snap'" = ("v", "g") 𝗶𝗻
      𝗶𝗳
        ~
        𝗿𝗲𝘀𝗼𝗹𝘃𝗲
          (𝗰𝗮𝘀 "t".[svar٠snapshot] "snap" "snap'")
          "t".{svar٠proph}
          ‘svar٠Forward( "v", "g" )
      𝘁𝗵𝗲𝗻 (
        𝗹𝗲𝘁 "snap" = "t".{svar٠snapshot} 𝗶𝗻
        𝗹𝗲𝘁 "g" = "t".{svar٠gen} 𝗶𝗻
        𝗶𝗳 "snap".<svar٠snapshot_gen> != "g" 𝘁𝗵𝗲𝗻 (
          𝗹𝗲𝘁 "v" = "t".{svar٠value} 𝗶𝗻
          𝗹𝗲𝘁 "snap'" = ("v", "g") 𝗶𝗻
          𝗿𝗲𝘀𝗼𝗹𝘃𝗲
            (𝗰𝗮𝘀 "t".[svar٠snapshot] "snap" "snap'")
            "t".{svar٠proph}
            ‘svar٠Forward( "v", "g" ) ⍮
          ()
        )
      )
    ).

Definition svar٠get : val :=
  𝗳𝘂𝗻 "t" ->
    svar٠forward "t" ⍮
    "t".{svar٠value}.

Definition svar٠set : val :=
  𝗳𝘂𝗻 "t" "v" ->
    𝗹𝗲𝘁 "id" = 𝗶𝗱 𝗶𝗻
    svar٠forward "t" ⍮
    𝗿𝗲𝘀𝗼𝗹𝘃𝗲
      ("t" <-{svar٠value} "v")
      "t".{svar٠proph}
      ‘svar٠Set( "id", "v" ).

Definition svar٠click : val :=
  𝗳𝘂𝗻 "t" ->
    "t" <-{svar٠gen} "t".{svar٠gen} + 1.

Definition svar٠observe : val :=
  𝗳𝘂𝗻 "t" ->
    svar٠forward "t" ⍮
    ("t".{svar٠snapshot}).<svar٠snapshot_value>.
