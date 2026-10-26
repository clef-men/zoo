Require Import iris.base_logic.lib.ghost_map.

Require Import zoo.prelude.
Require Import zoo.common.gset.
Require Import zoo.iris.base_logic.lib.auth_dgset.
Require Import zoo.iris.bi.big_op.
Require Import zoo.base.
Require Export zoo_std.latch__code.
Require Import zoo_std.latch__types.
Require Import zoo.options.

Implicit Type cnt : nat.
Implicit Type pending : gset nat.

Zoo name :=
  { self : location
  ; size : nat
  ; mutex : val
  ; condition : val
  ; tokens : gname
  ; receipts : gname
  }.

Zoo global X :=
  { mutex : mutex
  ; tokens : auth_dgset nat
  ; receipts : ghost_map nat X : iris
  }.

Section latch_G.
  Context `{latch_G : LatchG Σ X}.

  Implicit Type x : X.
  Implicit Type xs : gmap nat X.
  Implicit Type ready : gmap nat X.
  Implicit Type Ψ : nat → X → iProp Σ.
  Implicit Type Χ : nat → X → gmap nat X → iProp Σ.

  Definition latch۰valid sz Ψ Χ : iProp Σ :=
    ∀ xs,
    ⌜dom xs = set_seq 0 sz⌝ -∗
    ([∗ map] i ↦ x ∈ xs, Ψ i x) ={⊤}=∗
    [∗ map] i ↦ x ∈ xs, Χ i x xs.

  #[local] Definition tokens۰auth' γ۰tokens pending :=
    auth_dgset۰auth γ۰tokens Own pending.
  #[local] Definition tokens۰auth γ :=
    tokens۰auth' γ.(latch۰name۰tokens).
  #[local] Definition tokens۰at' γ۰tokens i :=
    auth_dgset۰frag γ۰tokens {[i]}.
  #[local] Definition tokens۰at γ i :=
    tokens۰at' γ.(latch۰name۰tokens) i.

  #[local] Definition receipts۰auth' γ۰receipts ready : iProp Σ :=
    ghost_map_auth γ۰receipts Own ready.
  #[local] Definition receipts۰auth γ :=
    receipts۰auth' γ.(latch۰name۰receipts).
  #[local] Definition receipts۰at' γ۰receipts i x :=
    ghost_map_elem γ۰receipts i Own x.
  #[local] Definition receipts۰at γ :=
    receipts۰at' γ.(latch۰name۰receipts).

  Please Definition latch۰init γ sz : iProp Σ :=
    ⌜sz = γ.(latch۰name۰size)⌝ ∗
    γ.(latch۰name۰self).[counter] ↦ #γ.(latch۰name۰size) ∗
    γ.(latch۰name۰self).[mutex] ↦□ γ.(latch۰name۰mutex) ∗
    mutex۰init γ.(latch۰name۰mutex) false ∗
    γ.(latch۰name۰self).[condition] ↦□ γ.(latch۰name۰condition) ∗
    condition۰inv γ.(latch۰name۰condition) ∗
    tokens۰auth γ (set_seq 0 γ.(latch۰name۰size)) ∗
    receipts۰auth γ ∅.
  #[local] Instance : CustomIpat "init" :=
    " ( ->
      & Hself۰counter
      & Hself۰mutex
      & Hmutex۰init
      & Hself۰condition
      & Hcondition۰inv
      & Htokens۰auth
      & Hreceipts۰auth
      )
    ".

  #[local] Definition inv۰pre γ Ψ Χ pending ready : iProp Σ :=
    ⌜pending ## dom ready⌝ ∗
    ⌜pending ∪ dom ready = set_seq 0 γ.(latch۰name۰size)⌝ ∗
    ([∗ map] i ↦ x ∈ ready, Ψ i x) ∗
    latch۰valid γ.(latch۰name۰size) Ψ Χ.
  #[local] Instance : CustomIpat "inv۰pre" :=
    " ( %
      & %
      & Hready
      & Hvalid
      )
    ".
  #[local] Definition inv۰post γ Χ ready : iProp Σ :=
    [∗ map] i ↦ x ∈ ready,
      ∃ xs,
      ⌜xs !! i = Some x⌝ ∗
      ⌜dom xs = set_seq 0 γ.(latch۰name۰size)⌝ ∗
      Χ i x xs.
  #[local] Instance : CustomIpat "inv۰post" :=
    " Hready
    ".
  #[local] Definition inv۰inner γ Ψ Χ : iProp Σ :=
    ∃ cnt pending ready,
    γ.(latch۰name۰self).[counter] ↦ #cnt ∗
    ⌜size pending = cnt⌝ ∗
    tokens۰auth γ pending ∗
    receipts۰auth γ ready ∗
    if decide (cnt = 0) then
      inv۰post γ Χ ready
    else
      inv۰pre γ Ψ Χ pending ready.
  #[local] Instance : CustomIpat "inv۰inner" :=
    " ( %cnt{}
      & %pending{}
      & %ready{}
      & Hself۰counter
      & %Hpending{}
      & Htokens۰auth
      & Hreceipts۰auth
      & Hinv
      )
    ".
  Please Definition latch۰inv γ sz Ψ Χ : iProp Σ :=
    ⌜sz = γ.(latch۰name۰size)⌝ ∗
    γ.(latch۰name۰self).[mutex] ↦□ γ.(latch۰name۰mutex) ∗
    mutex۰inv γ.(latch۰name۰mutex) (inv۰inner γ Ψ Χ) ∗
    γ.(latch۰name۰self).[condition] ↦□ γ.(latch۰name۰condition) ∗
    condition۰inv γ.(latch۰name۰condition).
  #[local] Instance : CustomIpat "inv" :=
    " ( ->
      & #Hself۰mutex
      & #Hmutex۰inv
      & #Hself۰condition
      & #Hcondition۰inv
      )
    ".

  Please Definition latch۰token γ :=
    tokens۰at γ.
  #[local] Instance : CustomIpat "token" :=
    " Htokens۰at
    ".

  #[global] Instance latch۰invｰcontractive γ sz n :
    Proper (
      (pointwise_relation _ $ pointwise_relation _ $ dist_later n) ==>
      (pointwise_relation _ $ pointwise_relation _ $ pointwise_relation _ $ dist_later n) ==>
      (≡{n}≡)
    ) (latch۰inv γ sz).
  Proof.
    rewrite /latch۰inv /inv۰inner /inv۰pre /inv۰post /latch۰valid.
    solve_contractive.
  Qed.
  #[global] Instance latch۰invｰproper γ sz :
    Proper (
      (pointwise_relation _ $ pointwise_relation _ $ (≡)) ==>
      (pointwise_relation _ $ pointwise_relation _ $ pointwise_relation _ $ (≡)) ==>
      (≡)
    ) (latch۰inv γ sz).
  Proof.
    rewrite /latch۰inv /inv۰inner /inv۰pre /inv۰post /latch۰valid.
    solve_proper.
  Qed.

  Zoo derive Timeless for latch۰init.
  Zoo derive Timeless for latch۰token.

  Zoo derive Persistent for latch۰inv.

  #[local] Lemma tokensｰalloc sz :
    ⊢ |==>
      ∃ γ۰tokens,
      tokens۰auth' γ۰tokens (set_seq 0 sz) ∗
      [∗ list] i ∈ seq 0 sz, tokens۰at' γ۰tokens i.
  Proof.
    iMod (auth_dgsetｰalloc (set_seq 0 sz)) as "(%γ۰tokens & $ & Hfrag)".
    iApply big_sepSｰset_seqｰtoｰbig_sepL.
    iApply (auth_dgset۰fragｰatomize with "Hfrag").
  Qed.
  #[local] Lemma tokens۰atｰelem_of γ pending i :
    tokens۰auth γ pending -∗
    tokens۰at γ i -∗
    ⌜i ∈ pending⌝.
  Proof.
    apply auth_dgsetｰelem_of.
  Qed.
  #[local] Lemma tokensｰremove γ pending i :
    tokens۰auth γ pending -∗
    tokens۰at γ i ==∗
    tokens۰auth γ (pending ∖ {[i]}).
  Proof.
    apply auth_dgsetｰupdateｰdealloc.
  Qed.

  Opaque tokens۰auth'.
  Opaque tokens۰at'.

  #[local] Lemma receiptsｰalloc :
    ⊢ |==>
      ∃ γ۰receipts,
      receipts۰auth' γ۰receipts ∅.
  Proof.
    apply ghost_map_alloc_empty.
  Qed.
  #[local] Lemma receipts۰atｰlookup γ ready i x :
    receipts۰auth γ ready -∗
    receipts۰at γ i x -∗
    ⌜ready !! i = Some x⌝.
  Proof.
    apply ghost_map_lookup.
  Qed.
  #[local] Lemma receiptsｰinsert {γ ready} i x :
    ready !! i = None →
    receipts۰auth γ ready ==∗
      receipts۰auth γ (<[i := x]> ready) ∗
      receipts۰at γ i x.
  Proof.
    apply ghost_map_insert.
  Qed.
  #[local] Lemma receiptsｰdelete γ ready i x :
    receipts۰auth γ ready -∗
    receipts۰at γ i x ==∗
    receipts۰auth γ (delete i ready).
  Proof.
    apply ghost_map_delete.
  Qed.

  Opaque receipts۰auth'.
  Opaque receipts۰at'.

  Lemma latch۰initｰexclusive γ sz1 sz2 :
    latch۰init γ sz1 -∗
    latch۰init γ sz2 -∗
    False.
  Proof.
    iSteps.
  Qed.
  Lemma latch۰initｰtoｰinv {γ sz} Ψ Χ E :
    latch۰init γ sz -∗
    latch۰valid sz Ψ Χ ={E}=∗
    latch۰inv γ sz Ψ Χ.
  Proof.
    iIntros "(:init) Hvalid".
    iFrameStep.
    iApply (mutex۰initｰtoｰinv with "Hmutex۰init").
    iFrameSteps.
    - iPureIntro. rewrite size_set_seq //.
    - case_decide.
      + iSteps.
      + iFrameSteps. iPureIntro. set_solver.
  Qed.

  Lemma latch٠createｰspecｰinit sz :
    (0 ≤ sz)%Z →
    {{{
      True
    }}}
      latch٠create #sz
    {{{
      γ
    , RET γ;
      latch۰init γ ₊sz ∗
      [∗ list] i ∈ seq 0 ₊sz, latch۰token γ i
    }}}.
  Proof.
    iIntros "%Hsz %Φ _ HΦ".

    wp۰rec.
    wp۰apply (condition٠createｰspec with "[//]") as (cond) "Hcond۰inv".
    wp۰apply (mutex٠createｰspecｰinit with "[//]") as (mtx) "Hmtx۰init".
    wp۰block t as "Ht۰counter #Ht۰mutex #Ht۰condition".

    iMod (tokensｰalloc ₊sz) as (γ_tokens) "(Htokens۰auth & Htokens۰ats)".
    iMod receiptsｰalloc as (γ_receipts) "Hreceipts۰auth".

    pose γ :=
      {|latch۰name۰self := t
      ; latch۰name۰size := ₊sz
      ; latch۰name۰mutex := mtx
      ; latch۰name۰condition := cond
      ; latch۰name۰tokens := γ_tokens
      ; latch۰name۰receipts := γ_receipts
      |}.

    iApply ("HΦ" $! γ).
    iFrameSteps.
  Qed.
  Lemma latch٠createｰspec Ψ Χ sz :
    (0 ≤ sz)%Z →
    {{{
      latch۰valid ₊sz Ψ Χ
    }}}
      latch٠create #sz
    {{{
      γ
    , RET γ;
      latch۰inv γ ₊sz Ψ Χ ∗
      [∗ list] i ∈ seq 0 ₊sz, latch۰token γ i
    }}}.
  Proof.
    iIntros "%Hsz %Φ Hvalid HΦ".

    iApply wpｰfupd.
    wp۰apply (latch٠createｰspecｰinit with "[//]") as (γ) "(Hinit & Htokens)". 1: done.
    iMod (latch۰initｰtoｰinv with "Hinit Hvalid") as "Hinv".
    iApply ("HΦ" with "[$]").
  Qed.

  Lemma latch٠waitｰspec {γ sz Ψ Χ} i x :
    {{{
      latch۰inv γ sz Ψ Χ ∗
      latch۰token γ i ∗
      ▷ Ψ i x
    }}}
      latch٠wait γ
    {{{
      xs
    , RET ();
      ⌜xs !! i = Some x⌝ ∗
      ⌜dom xs = set_seq 0 γ.(latch۰name۰size)⌝ ∗
      Χ i x xs
    }}}.
  Proof.
    iIntros "%Φ ((:inv) & (:token) & HΨ) HΦ".

    wp۰rec. wp۰load.
    wp۰apply (mutex٠protectｰspec (λ res,
      ∃ xs,
      ⌜res = ()%V⌝ ∗
      ⌜xs !! i = Some x⌝ ∗
      ⌜dom xs = set_seq 0 γ.(latch۰name۰size)⌝ ∗
      Χ i x xs
    )%I with "[$Hmutex۰inv Htokens۰at HΨ]").
    { iIntros "Hmutex۰locked (:inv۰inner =1)".

      wp۰load. wp۰store. do 2 wp۰load.

      iDestruct (tokens۰atｰelem_of with "Htokens۰auth Htokens۰at") as %Hi.
      apply elem_ofｰsizeｰpos in Hi as ?.
      iEval (rewrite decide_False; first lia) in "Hinv".
      iDestruct "Hinv" as "(:inv۰pre)".
      iMod (tokensｰremove with "Htokens۰auth Htokens۰at") as "Htokens۰auth".
      iMod (receiptsｰinsert i x with "Hreceipts۰auth") as "(Hreceipts۰auth & Hreceipts۰at)".
      { apply not_elem_of_dom. set_solver. }
      iAssert (inv۰inner γ Ψ Χ) with "[> - Hreceipts۰at Hmutex۰locked]" as "Hinv".
      { iFrameSteps.

        - iPureIntro.
          rewrite size_difference. 1: set_solver.
          rewrite size_singleton. lia.

        - iDestruct (big_sepM_insert_2 with "HΨ Hready") as "Hready".
          case_decide as Hcase.

          + replace cnt1 with 1 in * by lia.
            apply size_1_elem_of in Hpending1 as (j & ->%leibniz_equiv).
            apply elem_of_singleton in Hi as <-.

            set ready := <[i := x]> ready1.
            assert (dom ready = set_seq 0 γ.(latch۰name۰size)) as Hready_dom.
            { set_solver. }
            clearbody ready.

            iMod ("Hvalid" with "[%] Hready") as "Hready". 1: done.
            iApply (big_sepM_impl with "Hready").
            iSteps.

          + iFrameSteps; iPureIntro.
            { set_solver. }
            { rewrite dom_insert_L union_assoc_L difference_union_L.
              set_solver.
            }
      }

      wp۰apply (condition٠wait_untilｰspec (λ b,
        if b then
          ∃ xs,
          ⌜xs !! i = Some x⌝ ∗
          ⌜dom xs = set_seq 0 γ.(latch۰name۰size)⌝ ∗
          Χ i x xs
        else
          receipts۰at γ i x
      )%I with "[-]").
      { iFrame "#∗".
        iIntros "!> Hmutex۰locked (:inv۰inner =2) Hreceipts۰at".

        wp۰load. wp۰pures.
        case_bool_decide.

        - replace cnt2 with 0 by lia.

          iDestruct "Hinv" as "(:inv۰post)".
          iDestruct (receipts۰atｰlookup with "Hreceipts۰auth Hreceipts۰at") as %Hready2_lookup.
          iMod (receiptsｰdelete with "Hreceipts۰auth Hreceipts۰at") as "Hreceipts۰auth".
          iDestruct (big_sepM_delete with "Hready") as "(HΧ & Hready)". 1: done.
          iExists true. iFrameSteps.

        - iFrameSteps.
      }

      iSteps.
    }

    iSteps.
  Qed.
End latch_G.

Require zoo_std.latch__opaque.

Please opacify.
