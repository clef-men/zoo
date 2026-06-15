From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo Require Import
  identifier.
From zoo_saturn Require Import
  svar__types.
From zoo Require Import
  options.

Definition svar٠make : val :=
  𝗳𝘂𝗻 "v" ->
    𝗹𝗲𝘁 "snap" = ("v", 0) 𝗶𝗻
    { "v", 0, "snap", 𝗽𝗿𝗼𝗽𝗵 }.

Definition svar٠forward : val :=
  𝗳𝘂𝗻 "t" ->
    𝗹𝗲𝘁 "snap" = "t".{snapshot} 𝗶𝗻
    𝗹𝗲𝘁 "g" = "t".{gen} 𝗶𝗻
    𝗶𝗳 "snap".<snapshot_gen> != "g" 𝘁𝗵𝗲𝗻 (
      𝗹𝗲𝘁 "v" = "t".{value} 𝗶𝗻
      𝗹𝗲𝘁 "snap'" = ("v", "g") 𝗶𝗻
      𝗶𝗳
        ~
        𝗿𝗲𝘀𝗼𝗹𝘃𝗲
          (𝗰𝗮𝘀 "t".[snapshot] "snap" "snap'")
          "t".{proph}
          ‘Forward( "v", "g" )
      𝘁𝗵𝗲𝗻 (
        𝗹𝗲𝘁 "snap" = "t".{snapshot} 𝗶𝗻
        𝗹𝗲𝘁 "g" = "t".{gen} 𝗶𝗻
        𝗶𝗳 "snap".<snapshot_gen> != "g" 𝘁𝗵𝗲𝗻 (
          𝗹𝗲𝘁 "v" = "t".{value} 𝗶𝗻
          𝗹𝗲𝘁 "snap'" = ("v", "g") 𝗶𝗻
          𝗿𝗲𝘀𝗼𝗹𝘃𝗲
            (𝗰𝗮𝘀 "t".[snapshot] "snap" "snap'")
            "t".{proph}
            ‘Forward( "v", "g" ) ⍮
          ()
        )
      )
    ).

Definition svar٠get : val :=
  𝗳𝘂𝗻 "t" ->
    svar٠forward "t" ⍮
    "t".{value}.

Definition svar٠set : val :=
  𝗳𝘂𝗻 "t" "v" ->
    𝗹𝗲𝘁 "id" = 𝗶𝗱 𝗶𝗻
    svar٠forward "t" ⍮
    𝗿𝗲𝘀𝗼𝗹𝘃𝗲
      ("t" <-{value} "v")
      "t".{proph}
      ‘Set( "id", "v" ).

Definition svar٠click : val :=
  𝗳𝘂𝗻 "t" ->
    "t" <-{gen} "t".{gen} + 1.

Definition svar٠observe : val :=
  𝗳𝘂𝗻 "t" ->
    svar٠forward "t" ⍮
    ("t".{snapshot}).<snapshot_value>.
