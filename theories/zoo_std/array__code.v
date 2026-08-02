Require Import zoo.prelude.
Require Import zoo.language.typeclasses.
Require Import zoo.language.notations.
Require Import zoo_std.assume.
Require Import zoo.options.

Definition array٠unsafe_alloc : val :=
  𝗳𝘂𝗻 "sz" ->
    𝗮𝗹𝗹𝗼𝗰 0 "sz".

Definition array٠alloc : val :=
  𝗳𝘂𝗻 "sz" ->
    𝗮𝘀𝘀𝘂𝗺𝗲 (0 ≤ "sz") ⍮
    array٠unsafe_alloc "sz".

Definition array٠create : val :=
  𝗳𝘂𝗻 ⎽ ->
    array٠unsafe_alloc 0.

Definition array٠size : val :=
  𝗳𝘂𝗻 "t" ->
    𝘀𝗶𝘇𝗲 "t".

Definition array٠unsafe_get : val :=
  𝗳𝘂𝗻 "t" "i" ->
    𝗹𝗼𝗮𝗱 "t" "i".

Definition array٠get : val :=
  𝗳𝘂𝗻 "t" "i" ->
    𝗮𝘀𝘀𝘂𝗺𝗲 (0 ≤ "i") ⍮
    𝗮𝘀𝘀𝘂𝗺𝗲 ("i" < array٠size "t") ⍮
    array٠unsafe_get "t" "i".

Definition array٠unsafe_set : val :=
  𝗳𝘂𝗻 "t" "i" "v" ->
    𝘀𝘁𝗼𝗿𝗲 "t" "i" "v".

Definition array٠set : val :=
  𝗳𝘂𝗻 "t" "i" "v" ->
    𝗮𝘀𝘀𝘂𝗺𝗲 (0 ≤ "i") ⍮
    𝗮𝘀𝘀𝘂𝗺𝗲 ("i" < array٠size "t") ⍮
    array٠unsafe_set "t" "i" "v".

Definition array٠unsafe_swap : val :=
  𝗳𝘂𝗻 "t" "i1" "i2" ->
    𝗹𝗲𝘁 "v1" = array٠unsafe_get "t" "i1" 𝗶𝗻
    𝗹𝗲𝘁 "v2" = array٠unsafe_get "t" "i2" 𝗶𝗻
    array٠unsafe_set "t" "i1" "v2" ⍮
    array٠unsafe_set "t" "i2" "v1".

Definition array٠unsafe_fill_slice : val :=
  𝗳𝘂𝗻 "t" "i" "n" "v" ->
    𝗳𝗼𝗿 "j" = 0 𝘁𝗼 "n" 𝗱𝗼
      array٠unsafe_set "t" ("i" + "j") "v"
    𝗱𝗼𝗻𝗲.

Definition array٠fill_slice : val :=
  𝗳𝘂𝗻 "t" "i" "n" "v" ->
    𝗹𝗲𝘁 "sz" = array٠size "t" 𝗶𝗻
    𝗮𝘀𝘀𝘂𝗺𝗲 (0 ≤ "i") ⍮
    𝗮𝘀𝘀𝘂𝗺𝗲 (0 ≤ "n") ⍮
    𝗮𝘀𝘀𝘂𝗺𝗲 ("i" + "n" ≤ "sz") ⍮
    array٠unsafe_fill_slice "t" "i" "n" "v".

Definition array٠fill : val :=
  𝗳𝘂𝗻 "t" "v" ->
    array٠unsafe_fill_slice "t" 0 (array٠size "t") "v".

Definition array٠unsafe_make : val :=
  𝗳𝘂𝗻 "sz" "v" ->
    𝗹𝗲𝘁 "t" = array٠unsafe_alloc "sz" 𝗶𝗻
    array٠fill "t" "v" ⍮
    "t".

Definition array٠make : val :=
  𝗳𝘂𝗻 "sz" "v" ->
    𝗮𝘀𝘀𝘂𝗺𝗲 (0 ≤ "sz") ⍮
    array٠unsafe_make "sz" "v".

Definition array٠foldli_aux : val :=
  𝗿𝗲𝗰 "foldli_aux" "fn" "t" "sz" "i" "acc" ->
    𝗶𝗳 "sz" ≤ "i" 𝘁𝗵𝗲𝗻 (
      "acc"
    ) 𝗲𝗹𝘀𝗲 (
      𝗹𝗲𝘁 "v" = array٠unsafe_get "t" "i" 𝗶𝗻
      "foldli_aux" "fn" "t" "sz" ("i" + 1) ("fn" "i" "acc" "v")
    ).

Definition array٠foldli : val :=
  𝗳𝘂𝗻 "fn" "acc" "t" ->
    array٠foldli_aux "fn" "t" (array٠size "t") 0 "acc".

Definition array٠foldl : val :=
  𝗳𝘂𝗻 "fn" ->
    array٠foldli (𝗳𝘂𝗻 "_i" -> "fn").

Definition array٠foldri_aux : val :=
  𝗿𝗲𝗰 "foldri_aux" "fn" "t" "i" "acc" ->
    𝗶𝗳 "i" ≤ 0 𝘁𝗵𝗲𝗻 (
      "acc"
    ) 𝗲𝗹𝘀𝗲 (
      𝗹𝗲𝘁 "i" = "i" - 1 𝗶𝗻
      𝗹𝗲𝘁 "v" = array٠unsafe_get "t" "i" 𝗶𝗻
      "foldri_aux" "fn" "t" "i" ("fn" "i" "v" "acc")
    ).

Definition array٠foldri : val :=
  𝗳𝘂𝗻 "fn" "t" "acc" ->
    array٠foldri_aux "fn" "t" (array٠size "t") "acc".

Definition array٠foldr : val :=
  𝗳𝘂𝗻 "fn" ->
    array٠foldri (𝗳𝘂𝗻 "_i" -> "fn").

Definition array٠sum : val :=
  𝗳𝘂𝗻 "t" ->
    array٠foldl (𝗳𝘂𝗻 "1" "2" -> "1" + "2") 0 "t".

Definition array٠unsafe_iteri_slice : val :=
  𝗳𝘂𝗻 "fn" "t" "i" "n" ->
    𝗳𝗼𝗿 "k" = 0 𝘁𝗼 "n" 𝗱𝗼
      "fn" "k" (array٠unsafe_get "t" ("i" + "k"))
    𝗱𝗼𝗻𝗲.

Definition array٠iteri_slice : val :=
  𝗳𝘂𝗻 "fn" "t" "i" "n" ->
    𝗮𝘀𝘀𝘂𝗺𝗲 (0 ≤ "i") ⍮
    𝗮𝘀𝘀𝘂𝗺𝗲 (0 ≤ "n") ⍮
    𝗹𝗲𝘁 "sz" = array٠size "t" 𝗶𝗻
    𝗮𝘀𝘀𝘂𝗺𝗲 ("i" ≤ "sz") ⍮
    𝗮𝘀𝘀𝘂𝗺𝗲 ("i" + "n" ≤ "sz") ⍮
    array٠unsafe_iteri_slice "fn" "t" "i" "n".

Definition array٠unsafe_iter_slice : val :=
  𝗳𝘂𝗻 "fn" ->
    array٠unsafe_iteri_slice (𝗳𝘂𝗻 "_i" -> "fn").

Definition array٠iter_slice : val :=
  𝗳𝘂𝗻 "fn" "t" "i" "n" ->
    𝗮𝘀𝘀𝘂𝗺𝗲 (0 ≤ "i") ⍮
    𝗮𝘀𝘀𝘂𝗺𝗲 (0 ≤ "n") ⍮
    𝗹𝗲𝘁 "sz" = array٠size "t" 𝗶𝗻
    𝗮𝘀𝘀𝘂𝗺𝗲 ("i" ≤ "sz") ⍮
    𝗮𝘀𝘀𝘂𝗺𝗲 ("i" + "n" ≤ "sz") ⍮
    array٠unsafe_iter_slice "fn" "t" "i" "n".

Definition array٠iteri : val :=
  𝗳𝘂𝗻 "fn" "t" ->
    array٠unsafe_iteri_slice "fn" "t" 0 (array٠size "t").

Definition array٠iter : val :=
  𝗳𝘂𝗻 "fn" ->
    array٠iteri (𝗳𝘂𝗻 "_i" -> "fn").

Definition array٠unsafe_applyi_slice : val :=
  𝗳𝘂𝗻 "fn" "t" "i" "n" ->
    array٠unsafe_iteri_slice
      (𝗳𝘂𝗻 "k" "v" ->
         array٠unsafe_set "t" ("i" + "k") ("fn" "k" "v"))
      "t"
      "i"
      "n".

Definition array٠applyi_slice : val :=
  𝗳𝘂𝗻 "fn" "t" "i" "n" ->
    𝗮𝘀𝘀𝘂𝗺𝗲 (0 ≤ "i") ⍮
    𝗮𝘀𝘀𝘂𝗺𝗲 (0 ≤ "n") ⍮
    𝗹𝗲𝘁 "sz" = array٠size "t" 𝗶𝗻
    𝗮𝘀𝘀𝘂𝗺𝗲 ("i" ≤ "sz") ⍮
    𝗮𝘀𝘀𝘂𝗺𝗲 ("i" + "n" ≤ "sz") ⍮
    array٠unsafe_applyi_slice "fn" "t" "i" "n".

Definition array٠unsafe_apply_slice : val :=
  𝗳𝘂𝗻 "fn" ->
    array٠unsafe_applyi_slice (𝗳𝘂𝗻 "_i" -> "fn").

Definition array٠apply_slice : val :=
  𝗳𝘂𝗻 "fn" "t" "i" "n" ->
    𝗮𝘀𝘀𝘂𝗺𝗲 (0 ≤ "i") ⍮
    𝗮𝘀𝘀𝘂𝗺𝗲 (0 ≤ "n") ⍮
    𝗹𝗲𝘁 "sz" = array٠size "t" 𝗶𝗻
    𝗮𝘀𝘀𝘂𝗺𝗲 ("i" ≤ "sz") ⍮
    𝗮𝘀𝘀𝘂𝗺𝗲 ("i" + "n" ≤ "sz") ⍮
    array٠unsafe_apply_slice "fn" "t" "i" "n".

Definition array٠applyi : val :=
  𝗳𝘂𝗻 "fn" "t" ->
    array٠unsafe_applyi_slice "fn" "t" 0 (array٠size "t").

Definition array٠apply : val :=
  𝗳𝘂𝗻 "fn" ->
    array٠applyi (𝗳𝘂𝗻 "_i" -> "fn").

Definition array٠unsafe_initi : val :=
  𝗳𝘂𝗻 "sz" "fn" ->
    𝗹𝗲𝘁 "t" = array٠unsafe_alloc "sz" 𝗶𝗻
    array٠applyi (𝗳𝘂𝗻 "i" ⎽ -> "fn" "i") "t" ⍮
    "t".

Definition array٠initi : val :=
  𝗳𝘂𝗻 "sz" "fn" ->
    𝗮𝘀𝘀𝘂𝗺𝗲 (0 ≤ "sz") ⍮
    array٠unsafe_initi "sz" "fn".

Definition array٠unsafe_init : val :=
  𝗳𝘂𝗻 "sz" "fn" ->
    array٠unsafe_initi "sz" (𝗳𝘂𝗻 "_i" -> "fn" ()).

Definition array٠init : val :=
  𝗳𝘂𝗻 "sz" "fn" ->
    𝗮𝘀𝘀𝘂𝗺𝗲 (0 ≤ "sz") ⍮
    array٠unsafe_init "sz" "fn".

Definition array٠mapi : val :=
  𝗳𝘂𝗻 "fn" "t" ->
    array٠unsafe_initi
      (array٠size "t")
      (𝗳𝘂𝗻 "i" -> "fn" "i" (array٠unsafe_get "t" "i")).

Definition array٠map : val :=
  𝗳𝘂𝗻 "fn" ->
    array٠mapi (𝗳𝘂𝗻 "_i" -> "fn").

Definition array٠unsafe_copy_slice : val :=
  𝗳𝘂𝗻 "t1" "i1" "t2" "i2" "n" ->
    𝗳𝗼𝗿 "k" = 0 𝘁𝗼 "n" 𝗱𝗼
      𝗹𝗲𝘁 "v" = array٠unsafe_get "t1" ("i1" + "k") 𝗶𝗻
      array٠unsafe_set "t2" ("i2" + "k") "v"
    𝗱𝗼𝗻𝗲.

Definition array٠copy_slice : val :=
  𝗳𝘂𝗻 "t1" "i1" "t2" "i2" "n" ->
    𝗹𝗲𝘁 "sz1" = array٠size "t1" 𝗶𝗻
    𝗹𝗲𝘁 "sz2" = array٠size "t2" 𝗶𝗻
    𝗮𝘀𝘀𝘂𝗺𝗲 (0 ≤ "i1") ⍮
    𝗮𝘀𝘀𝘂𝗺𝗲 (0 ≤ "i2") ⍮
    𝗮𝘀𝘀𝘂𝗺𝗲 (0 ≤ "n") ⍮
    𝗮𝘀𝘀𝘂𝗺𝗲 ("i1" + "n" ≤ "sz1") ⍮
    𝗮𝘀𝘀𝘂𝗺𝗲 ("i2" + "n" ≤ "sz2") ⍮
    array٠unsafe_copy_slice "t1" "i1" "t2" "i2" "n".

Definition array٠unsafe_copy : val :=
  𝗳𝘂𝗻 "t1" "t2" "i2" ->
    array٠unsafe_copy_slice "t1" 0 "t2" "i2" (array٠size "t1").

Definition array٠copy : val :=
  𝗳𝘂𝗻 "t1" "t2" "i2" ->
    𝗮𝘀𝘀𝘂𝗺𝗲 (0 ≤ "i2") ⍮
    𝗮𝘀𝘀𝘂𝗺𝗲 ("i2" + array٠size "t1" ≤ array٠size "t2") ⍮
    array٠unsafe_copy "t1" "t2" "i2".

Definition array٠unsafe_grow : val :=
  𝗳𝘂𝗻 "t" "sz'" "v'" ->
    𝗹𝗲𝘁 "sz" = array٠size "t" 𝗶𝗻
    𝗹𝗲𝘁 "t'" = array٠unsafe_alloc "sz'" 𝗶𝗻
    array٠unsafe_copy "t" "t'" 0 ⍮
    array٠unsafe_fill_slice "t'" "sz" ("sz'" - "sz") "v'" ⍮
    "t'".

Definition array٠grow : val :=
  𝗳𝘂𝗻 "t" "sz'" "v'" ->
    𝗮𝘀𝘀𝘂𝗺𝗲 (array٠size "t" ≤ "sz'") ⍮
    array٠unsafe_grow "t" "sz'" "v'".

Definition array٠unsafe_sub : val :=
  𝗳𝘂𝗻 "t" "i" "n" ->
    𝗹𝗲𝘁 "t'" = array٠unsafe_alloc "n" 𝗶𝗻
    array٠unsafe_copy_slice "t" "i" "t'" 0 "n" ⍮
    "t'".

Definition array٠sub : val :=
  𝗳𝘂𝗻 "t" "i" "n" ->
    𝗮𝘀𝘀𝘂𝗺𝗲 (0 ≤ "i") ⍮
    𝗮𝘀𝘀𝘂𝗺𝗲 (0 ≤ "n") ⍮
    𝗮𝘀𝘀𝘂𝗺𝗲 ("i" + "n" ≤ array٠size "t") ⍮
    array٠unsafe_sub "t" "i" "n".

Definition array٠unsafe_shrink : val :=
  𝗳𝘂𝗻 "t" "sz'" ->
    array٠unsafe_sub "t" 0 "sz'".

Definition array٠shrink : val :=
  𝗳𝘂𝗻 "t" "sz'" ->
    𝗮𝘀𝘀𝘂𝗺𝗲 (0 ≤ "sz'") ⍮
    𝗮𝘀𝘀𝘂𝗺𝗲 ("sz'" ≤ array٠size "t") ⍮
    array٠unsafe_shrink "t" "sz'".

Definition array٠clone : val :=
  𝗳𝘂𝗻 "t" ->
    array٠unsafe_shrink "t" (array٠size "t").

Definition array٠unsafe_cget : val :=
  𝗳𝘂𝗻 "t" "i" ->
    array٠unsafe_get "t" ("i" 𝗿𝗲𝗺 array٠size "t").

Definition array٠cget : val :=
  𝗳𝘂𝗻 "t" "i" ->
    𝗮𝘀𝘀𝘂𝗺𝗲 (0 ≤ "i") ⍮
    𝗮𝘀𝘀𝘂𝗺𝗲 (0 < array٠size "t") ⍮
    array٠unsafe_cget "t" "i".

Definition array٠unsafe_cset : val :=
  𝗳𝘂𝗻 "t" "i" "v" ->
    array٠unsafe_set "t" ("i" 𝗿𝗲𝗺 array٠size "t") "v".

Definition array٠cset : val :=
  𝗳𝘂𝗻 "t" "i" "v" ->
    𝗮𝘀𝘀𝘂𝗺𝗲 (0 ≤ "i") ⍮
    𝗮𝘀𝘀𝘂𝗺𝗲 (0 < array٠size "t") ⍮
    array٠unsafe_cset "t" "i" "v".

Definition array٠unsafe_ccopy_slice₁ : val :=
  𝗳𝘂𝗻 "t1" "i1" "t2" "i2" "n" ->
    𝗹𝗲𝘁 "sz2" = array٠size "t2" 𝗶𝗻
    𝗹𝗲𝘁 "i2" = "i2" 𝗿𝗲𝗺 "sz2" 𝗶𝗻
    𝗶𝗳 "i2" + "n" ≤ "sz2" 𝘁𝗵𝗲𝗻 (
      array٠unsafe_copy_slice "t1" "i1" "t2" "i2" "n"
    ) 𝗲𝗹𝘀𝗲 (
      𝗹𝗲𝘁 "n1" = "sz2" - "i2" 𝗶𝗻
      𝗹𝗲𝘁 "n2" = "n" - "n1" 𝗶𝗻
      array٠unsafe_copy_slice "t1" "i1" "t2" "i2" "n1" ⍮
      array٠unsafe_copy_slice "t1" ("i1" + "n1") "t2" 0 "n2"
    ).

Definition array٠unsafe_ccopy_slice : val :=
  𝗳𝘂𝗻 "t1" "i1" "t2" "i2" "n" ->
    𝗹𝗲𝘁 "sz1" = array٠size "t1" 𝗶𝗻
    𝗹𝗲𝘁 "i1" = "i1" 𝗿𝗲𝗺 "sz1" 𝗶𝗻
    𝗶𝗳 "i1" + "n" ≤ "sz1" 𝘁𝗵𝗲𝗻 (
      array٠unsafe_ccopy_slice₁ "t1" "i1" "t2" "i2" "n"
    ) 𝗲𝗹𝘀𝗲 (
      𝗹𝗲𝘁 "n1" = "sz1" - "i1" 𝗶𝗻
      𝗹𝗲𝘁 "n2" = "n" - "n1" 𝗶𝗻
      array٠unsafe_ccopy_slice₁ "t1" "i1" "t2" "i2" "n1" ⍮
      array٠unsafe_ccopy_slice₁ "t1" 0 "t2" ("i2" + "n1") "n2"
    ).

Definition array٠ccopy_slice : val :=
  𝗳𝘂𝗻 "t1" "i1" "t2" "i2" "n" ->
    𝗮𝘀𝘀𝘂𝗺𝗲 (0 ≤ "i1") ⍮
    𝗮𝘀𝘀𝘂𝗺𝗲 (0 ≤ "i2") ⍮
    𝗮𝘀𝘀𝘂𝗺𝗲 (0 ≤ "n") ⍮
    𝗹𝗲𝘁 "sz1" = array٠size "t1" 𝗶𝗻
    𝗹𝗲𝘁 "sz2" = array٠size "t2" 𝗶𝗻
    𝗮𝘀𝘀𝘂𝗺𝗲 (0 < "sz1") ⍮
    𝗮𝘀𝘀𝘂𝗺𝗲 (0 < "sz2") ⍮
    𝗮𝘀𝘀𝘂𝗺𝗲 ("n" ≤ "sz1") ⍮
    𝗮𝘀𝘀𝘂𝗺𝗲 ("n" ≤ "sz2") ⍮
    array٠unsafe_ccopy_slice "t1" "i1" "t2" "i2" "n".

Definition array٠unsafe_ccopy : val :=
  𝗳𝘂𝗻 "t1" "i1" "t2" "i2" ->
    array٠unsafe_ccopy_slice "t1" "i1" "t2" "i2" (array٠size "t1").

Definition array٠ccopy : val :=
  𝗳𝘂𝗻 "t1" "i1" "t2" "i2" ->
    𝗮𝘀𝘀𝘂𝗺𝗲 (0 ≤ "i1") ⍮
    𝗮𝘀𝘀𝘂𝗺𝗲 (0 ≤ "i2") ⍮
    𝗹𝗲𝘁 "sz1" = array٠size "t1" 𝗶𝗻
    𝗹𝗲𝘁 "sz2" = array٠size "t2" 𝗶𝗻
    𝗮𝘀𝘀𝘂𝗺𝗲 (0 < "sz1") ⍮
    𝗮𝘀𝘀𝘂𝗺𝗲 ("sz1" ≤ "sz2") ⍮
    array٠unsafe_ccopy "t1" "i1" "t2" "i2".

Definition array٠unsafe_cgrow_slice : val :=
  𝗳𝘂𝗻 "t" "i" "n" "sz'" "v" ->
    𝗹𝗲𝘁 "t'" = array٠unsafe_make "sz'" "v" 𝗶𝗻
    array٠unsafe_ccopy_slice "t" "i" "t'" "i" "n" ⍮
    "t'".

Definition array٠unsafe_cgrow : val :=
  𝗳𝘂𝗻 "t" "i" "sz'" "v" ->
    array٠unsafe_cgrow_slice "t" "i" (array٠size "t") "sz'" "v".

Definition array٠unsafe_cshrink_slice : val :=
  𝗳𝘂𝗻 "t" "i" "sz'" ->
    𝗹𝗲𝘁 "t'" = array٠unsafe_alloc "sz'" 𝗶𝗻
    array٠unsafe_ccopy_slice "t" "i" "t'" "i" "sz'" ⍮
    "t'".
