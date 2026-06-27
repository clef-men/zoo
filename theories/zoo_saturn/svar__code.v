Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo.program_logic.identifier.
Require Import zoo_saturn.svar__types.
Require Import zoo.options.

Definition svar٠make : val :=
  fun: "v" =>
    let: "snap" := ("v", 0) in
    { "v", 0, "snap", Proph }.

Definition svar٠forward : val :=
  fun: "t" =>
    let: "snap" := "t".{snapshot} in
    let: "g" := "t".{gen} in
    if: "snap".<snapshot_gen> != "g" then (
      let: "v" := "t".{value} in
      let: "snap'" := ("v", "g") in
      if:
        ~
        Resolve
          (CAS "t".[snapshot] "snap" "snap'")
          "t".{proph}
          ‘Forward( "v", "g" )
      then (
        let: "snap" := "t".{snapshot} in
        let: "g" := "t".{gen} in
        if: "snap".<snapshot_gen> != "g" then (
          let: "v" := "t".{value} in
          let: "snap'" := ("v", "g") in
          Resolve
            (CAS "t".[snapshot] "snap" "snap'")
            "t".{proph}
            ‘Forward( "v", "g" ) ;;
          ()
        )
      )
    ).

Definition svar٠get : val :=
  fun: "t" =>
    svar٠forward "t" ;;
    "t".{value}.

Definition svar٠set : val :=
  fun: "t" "v" =>
    let: "id" := Id in
    svar٠forward "t" ;;
    Resolve ("t" <-{value} "v") "t".{proph} ‘Set( "id", "v" ).

Definition svar٠click : val :=
  fun: "t" =>
    "t" <-{gen} "t".{gen} + 1.

Definition svar٠observe : val :=
  fun: "t" =>
    svar٠forward "t" ;;
    ("t".{snapshot}).<snapshot_value>.
