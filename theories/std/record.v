From zebre Require Import
  prelude.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Export
  base.
From zebre Require Import
  options.

Implicit Types l : loc.

Definition record2 : val :=
  λ: "v0" "v1",
    let: "l" := Alloc #2 "v0" in
    "l".[#1] <- "v1" ;;
    "l".

Definition record3 : val :=
  λ: "v0" "v1" "v2",
    let: "l" := Alloc #3 "v0" in
    "l".[#1] <- "v1" ;;
    "l".[#2] <- "v2" ;;
    "l".

Definition record4 : val :=
  λ: "v0" "v1" "v2" "v3",
    let: "l" := Alloc #4 "v0" in
    "l".[#1] <- "v1" ;;
    "l".[#2] <- "v2" ;;
    "l".[#3] <- "v3" ;;
    "l".

Definition record5 : val :=
  λ: "v0" "v1" "v2" "v3" "v4",
    let: "l" := Alloc #5 "v0" in
    "l".[#1] <- "v1" ;;
    "l".[#2] <- "v2" ;;
    "l".[#3] <- "v3" ;;
    "l".[#4] <- "v4" ;;
    "l".

Section zebre_G.
  Context `{zebre_G : !ZebreG Σ}.

  Lemma record2_spec v0 v1 :
    {{{ True }}}
      record2 v0 v1
    {{{ l,
      RET #l;
      meta_token l ⊤ ∗
      l.[0] ↦ v0 ∗
      l.[1] ↦ v1
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    wp_smart_apply (wp_alloc with "[//]") as "%l (Hmeta & Hl)"; first done.
    iSteps.
  Qed.

  Lemma record3_spec v0 v1 v2 :
    {{{ True }}}
      record3 v0 v1 v2
    {{{ l,
      RET #l;
      meta_token l ⊤ ∗
      l.[0] ↦ v0 ∗
      l.[1] ↦ v1 ∗
      l.[2] ↦ v2
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    wp_smart_apply (wp_alloc with "[//]") as "%l (Hmeta & Hl)"; first done.
    iSteps.
  Qed.

  Lemma record4_spec v0 v1 v2 v3 :
    {{{ True }}}
      record4 v0 v1 v2 v3
    {{{ l,
      RET #l;
      meta_token l ⊤ ∗
      l.[0] ↦ v0 ∗
      l.[1] ↦ v1 ∗
      l.[2] ↦ v2 ∗
      l.[3] ↦ v3
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    wp_smart_apply (wp_alloc with "[//]") as "%l (Hmeta & Hl)"; first done.
    iSteps.
  Qed.

  Lemma record5_spec v0 v1 v2 v3 v4 :
    {{{ True }}}
      record5 v0 v1 v2 v3 v4
    {{{ l,
      RET #l;
      meta_token l ⊤ ∗
      l.[0] ↦ v0 ∗
      l.[1] ↦ v1 ∗
      l.[2] ↦ v2 ∗
      l.[3] ↦ v3 ∗
      l.[4] ↦ v4
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".
    wp_rec.
    wp_smart_apply (wp_alloc with "[//]") as "%l (Hmeta & Hl)"; first done.
    iSteps.
  Qed.
End zebre_G.

#[global] Opaque record2.
#[global] Opaque record3.
#[global] Opaque record4.
#[global] Opaque record5.
