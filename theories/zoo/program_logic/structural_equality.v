Require Import zoo.prelude.
Require Import zoo.common.list.
Require Import zoo.base.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type tag : nat.
Implicit Type n : Z.
Implicit Type l : location.
Implicit Type gen : generativity.
Implicit Type v w : val.
Implicit Type vs : list val.
Implicit Type lv : lowval.

#[local] Definition __zoo_recs := (
  𝗿𝗲𝗰𝘀 "structeq" "v1" "v2" ->
    𝗶𝗳 𝗶𝗺𝗺𝗲𝗱𝗶𝗮𝘁𝗲 "v1" 𝘁𝗵𝗲𝗻
      𝗶𝗳 𝗶𝗺𝗺𝗲𝗱𝗶𝗮𝘁𝗲 "v2" 𝘁𝗵𝗲𝗻
        "v1" == "v2"
      𝗲𝗹𝘀𝗲
        false
    𝗲𝗹𝘀𝗲 𝗶𝗳 𝗶𝗺𝗺𝗲𝗱𝗶𝗮𝘁𝗲 "v2" 𝘁𝗵𝗲𝗻
      false
    𝗲𝗹𝘀𝗲 (
      𝘁𝗮𝗴 "v1" == 𝘁𝗮𝗴 "v2" 𝗮𝗻𝗱
      𝗹𝗲𝘁 "sz" = 𝘀𝗶𝘇𝗲 "v1" 𝗶𝗻
      "sz" == 𝘀𝗶𝘇𝗲 "v2" 𝗮𝗻𝗱
      "structeq_aux" "v1" "v2" "sz"
    )
  𝘄𝗶𝘁𝗵 "structeq_aux" "v1" "v2" "i" ->
    𝗶𝗳 "i" == 0 𝘁𝗵𝗲𝗻
      true
    𝗲𝗹𝘀𝗲
      𝗹𝗲𝘁 "i" = "i" - 1 𝗶𝗻
      "structeq" (𝗹𝗼𝗮𝗱 "v1" "i") (𝗹𝗼𝗮𝗱 "v2" "i") 𝗮𝗻𝗱
      "structeq_aux" "v1" "v2" "i"
)%zoo_recs.
Definition structeq :=
  ValRecs 0 __zoo_recs.
#[local] Definition structeq۰aux :=
  ValRecs 1 __zoo_recs.
#[global] Instance :
  AsValRecs' structeq 0 __zoo_recs [
    structeq ;
    structeq۰aux
  ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs' structeq۰aux 1 __zoo_recs [
    structeq ;
    structeq۰aux
  ].
Proof.
  done.
Qed.

Notation "e1 = e2" := (
  App (App (Val structeq) e1%E) e2%E
)(at level 70,
  no associativity
) : expr_scope.
Notation "e1 ≠ e2" := (
  Unop UnopNeg (App (App (Val structeq) e1%E) e2%E)
)(at level 70,
  no associativity
) : expr_scope.

Record structeq۰field := StructeqField
  { structeq۰field۰dfrac : dfrac
  ; structeq۰field۰val : val
  }.
Add Printing Constructor structeq۰field.
Implicit Type fld : structeq۰field.

#[global] Instance structeq۰fieldｰinhabited : Inhabited structeq۰field :=
  populate
    {|structeq۰field۰dfrac := inhabitant
    ; structeq۰field۰val := inhabitant
    |}.

Record structeq۰block := StructeqBlock
  { structeq۰block۰tag : nat
  ; structeq۰block۰fields : list structeq۰field
  }.
Add Printing Constructor structeq۰block.
Implicit Type blk : structeq۰block.
Implicit Type footprint : gmap location structeq۰block.

#[global] Instance structeq۰blockｰinhabited : Inhabited structeq۰block :=
  populate
    {|structeq۰block۰tag := inhabitant
    ; structeq۰block۰fields := inhabitant
    |}.

Fixpoint val۰traversable footprint v :=
  match v with
  | ValBool _
  | ValInt _ =>
      True
  | ValLoc l =>
      l ∈ dom footprint
  | ValBlock _ _ vs =>
      Forall' (val۰traversable footprint) vs
  | _ =>
      False
  end.
#[global] Arguments val۰traversable _ !_ / : assert.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Definition structeq۰footprint footprint : iProp Σ :=
    [∗ map] l ↦ blk ∈ footprint,
      l ↦ₕ Header blk.(structeq۰block۰tag) (length blk.(structeq۰block۰fields)) ∗
      [∗ list] i ↦ fld ∈ blk.(structeq۰block۰fields),
        (l +ₗ i) ↦{fld.(structeq۰field۰dfrac)} fld.(structeq۰field۰val) ∗
        ⌜val۰traversable footprint fld.(structeq۰field۰val)⌝.

  Lemma structeq۰footprintｰempty :
    ⊢ structeq۰footprint ∅.
  Proof.
    rewrite /structeq۰footprint big_sepM_empty //.
  Qed.

  Lemma structeq۰footprintｰheader {footprint} l blk :
    footprint !! l = Some blk →
    structeq۰footprint footprint ⊢
    l ↦ₕ Header blk.(structeq۰block۰tag) (length blk.(structeq۰block۰fields)).
  Proof.
    iIntros "%Hlookup Hfootprint".
    iDestruct (big_sepM_lookup with "Hfootprint") as "($ & _)"; first done.
  Qed.

  Lemma structeq۰footprintｰlookup {footprint} l blk (i : nat) fld :
    footprint !! l = Some blk →
    blk.(structeq۰block۰fields) !! i = Some fld →
    structeq۰footprint footprint ⊢
      (l +ₗ i) ↦{fld.(structeq۰field۰dfrac)} fld.(structeq۰field۰val) ∗
      ⌜val۰traversable footprint fld.(structeq۰field۰val)⌝ ∗
      ( (l +ₗ i) ↦{fld.(structeq۰field۰dfrac)} fld.(structeq۰field۰val) -∗
        structeq۰footprint footprint
      ).
  Proof.
    iIntros "%Hfootprint_lookup %Hfields_lookup Hfootprint".
    iDestruct (big_sepM_lookup_acc with "Hfootprint") as "((#Hl_header & Hblk) & Hfootprint)"; first done.
    iDestruct (big_sepL_lookup_acc with "Hblk") as "(HHfld & Hblk)"; first done.
    iSteps.
  Qed.
  Lemma structeq۰footprintｰlookup' {footprint} l blk i :
    footprint !! l = Some blk →
    i < length blk.(structeq۰block۰fields) →
    structeq۰footprint footprint ⊢
      ∃ fld,
      ⌜blk.(structeq۰block۰fields) !! i = Some fld⌝ ∗
      (l +ₗ i) ↦{fld.(structeq۰field۰dfrac)} fld.(structeq۰field۰val) ∗
      ⌜val۰traversable footprint fld.(structeq۰field۰val)⌝ ∗
      ( (l +ₗ i) ↦{fld.(structeq۰field۰dfrac)} fld.(structeq۰field۰val) -∗
        structeq۰footprint footprint
      ).
  Proof.
    iIntros "%Hfootprint_lookup %Hi Hfootprint".
    destruct (lookup_lt_is_Some_2 blk.(structeq۰block۰fields) i) as (fld & Hfields_lookup); first done.
    iExists fld. iStep.
    iApply (structeq۰footprintｰlookup with "Hfootprint"); done.
  Qed.

  Lemma structeq۰footprintｰwpｰtag {footprint} l blk :
    footprint !! l = Some blk →
    {{{
      structeq۰footprint footprint
    }}}
      GetTag #l
    {{{
      RET #(encode_tag blk.(structeq۰block۰tag));
      structeq۰footprint footprint
    }}}.
  Proof.
    iIntros "%Hlookup %Φ Hfootprint HΦ".

    iDestruct (structeq۰footprintｰheader with "Hfootprint") as "#Hl_header"; first done.
    iSteps.
  Qed.
  Lemma structeq۰footprintｰwpｰsize {footprint} l blk :
    footprint !! l = Some blk →
    {{{
      structeq۰footprint footprint
    }}}
      GetSize #l
    {{{
      RET #(length blk.(structeq۰block۰fields));
      structeq۰footprint footprint
    }}}.
  Proof.
    iIntros "%Hlookup %Φ Hfootprint HΦ".

    iDestruct (structeq۰footprintｰheader with "Hfootprint") as "#Hl_header"; first done.
    iSteps.
  Qed.

  Lemma structeq۰footprintｰwpｰload {footprint} l blk (i : nat) fld :
    footprint !! l = Some blk →
    blk.(structeq۰block۰fields) !! i = Some fld →
    {{{
      structeq۰footprint footprint
    }}}
      Load #l #i
    {{{
      RET fld.(structeq۰field۰val);
      ⌜val۰traversable footprint fld.(structeq۰field۰val)⌝ ∗
      structeq۰footprint footprint
    }}}.
  Proof.
    iIntros "%Hfootprint_lookup %Hfields_lookup %Φ Hfootprint HΦ".

    iDestruct (structeq۰footprintｰlookup with "Hfootprint") as "(Hl & %Htraversable & Hfootprint)"; [done.. |].
    iSteps.
  Qed.
  Lemma structeq۰footprintｰwpｰload' {footprint} l blk i :
    footprint !! l = Some blk →
    i < length blk.(structeq۰block۰fields) →
    {{{
      structeq۰footprint footprint
    }}}
      Load #l #i
    {{{
      fld
    , RET fld.(structeq۰field۰val);
      ⌜blk.(structeq۰block۰fields) !! i = Some fld⌝ ∗
      ⌜val۰traversable footprint fld.(structeq۰field۰val)⌝ ∗
      structeq۰footprint footprint
    }}}.
  Proof.
    iIntros "%Hfootprint_lookup %Hi %Φ Hfootprint HΦ".

    iDestruct (structeq۰footprintｰlookup' with "Hfootprint") as "(%fld & %Hfields_lookup & Hl & %Htraversable & Hfootprint)"; [done.. |].
    iSteps.
  Qed.
End zoo۰G.

Fixpoint val۰reachable footprint src path dst :=
  match path with
  | [] =>
      src = dst
  | i :: path =>
      match src with
      | ValLoc l =>
          match footprint !! l with
          | None =>
              False
          | Some blk =>
              match blk.(structeq۰block۰fields) !! i with
              | None =>
                  False
              | Some fld =>
                  val۰reachable footprint fld.(structeq۰field۰val) path dst
              end
          end
      | ValBlock _ _ vs =>
          match vs !! i with
          | None =>
              False
          | Some src =>
              val۰reachable footprint src path dst
          end
      | _ =>
          False
      end
  end.
#[global] Arguments val۰reachable _ !_ !_ / _ : assert.

#[global] Instance val۰reachableｰdec footprint src path dst :
  Decision (val۰reachable footprint src path dst).
Proof.
  move: src path.
  refine (
    fix go src path {struct path} :=
      match path with
      | [] =>
          cast_if (decide (src = dst))
      | i :: path =>
          match src with
          | ValLoc l =>
              (match footprint !! l as x return _ = x → _ with
              | None => λ Hfootprint_lookup,
                  right _
              | Some blk => λ Hfootprint_lookup,
                  (match blk.(structeq۰block۰fields) !! i as x return _ = x → _ with
                  | None => λ Hfields_lookup,
                      right _
                  | Some fld => λ Hfields_lookup,
                      cast_if (go fld.(structeq۰field۰val) path)
                  end) (eq_refl (blk.(structeq۰block۰fields) !! i))
              end) (eq_refl (footprint !! l))
          | ValBlock _ _ vs =>
              (match vs !! i as x return _ = x → _ with
              | None => λ Hvs_lookup,
                  right _
              | Some src => λ Hvs_lookup,
                  cast_if (go src path)
              end) (eq_refl (vs !! i))
          | _ =>
              right _
          end
      end
  ).
  all:
    abstract (
      rewrite /= ?Hfootprint_lookup ?Hfields_lookup ?Hvs_lookup;
      congruence
    ).
Defined.

Definition lowval۰compatible footprint lv1 lv2 :=
  match lv1 with
  | LowvalLit lit1 =>
      match lit1 with
      | LowlitLoc l1 =>
          match lv2 with
          | LowvalLoc l2 =>
              let blk1 := footprint !!! l1 in
              let blk2 := footprint !!! l2 in
              blk1.(structeq۰block۰tag) ≟ blk2.(structeq۰block۰tag) &&
              length blk1.(structeq۰block۰fields) ≟ length blk2.(structeq۰block۰fields)
          | LowvalBlock _ tag2 vs2 _ =>
              let blk1 := footprint !!! l1 in
              blk1.(structeq۰block۰tag) ≟ tag2 &&
              length blk1.(structeq۰block۰fields) ≟ length vs2
          | _ =>
              false
          end
      | _ =>
          bool_decide (lv2 = LowvalLit lit1)
      end
  | LowvalRecs =>
      bool_decide (lv2 = LowvalRecs)
  | LowvalBlock _ tag1 vs1 _ =>
      match lv2 with
      | LowvalLoc l2 =>
          let blk2 := footprint !!! l2 in
          tag1 ≟ blk2.(structeq۰block۰tag) &&
          length vs1 ≟ length blk2.(structeq۰block۰fields)
      | LowvalBlock _ tag2 vs2 _ =>
          tag1 ≟ tag2 &&
          length vs1 ≟ length vs2
      | _ =>
          false
      end
  end.
#[global] Arguments lowval۰compatible _ !_ !_ / : assert.

Definition val۰compatible footprint v1 v2 :=
  lowval۰compatible footprint (val۰to_low v1) (val۰to_low v2).

Definition val۰structeq footprint v1 v2 :=
  ∀ path v1' v2',
  val۰reachable footprint v1 path v1' →
  val۰reachable footprint v2 path v2' →
  val۰compatible footprint v1' v2' = true.

Definition val۰structneq footprint v1 v2 :=
  ∃ path v1' v2',
  val۰reachable footprint v1 path v1' ∧
  val۰reachable footprint v2 path v2' ∧
  val۰compatible footprint v1' v2' = false.

Lemma valｰimmediateｰstructeq footprint v1 v2 :
  val۰immediate v1 →
  val۰immediate v2 →
  v1 ≈ v2 →
  val۰structeq footprint v1 v2.
Proof.
  intros Himmediate1 Himmediate2 Hsimilar.
  intros path v1_ v2_ Hreachable1 Hreachable2.
  destruct v1 as [[b1 | n1 | l1 | |] | | gen1 tag1 []]; try done.
  all: destruct v2 as [[b2 | n2 | l2 | |] | | gen2 tag2 []]; try done.
  all: destruct path; last done.
  all: simp.
  all: cbn.
  all: rewrite bool_decide_eq_true_2 //.
Qed.
Lemma valｰimmediateｰstructneq footprint v1 v2 :
  val۰immediate v1 →
  val۰immediate v2 →
  v1 ≉ v2 →
  val۰structneq footprint v1 v2.
Proof.
  intros Himmediate1 Himmediate2 Hnonsimilar.
  eexists [], v1, v2. split_and!; try done.
  destruct v1 as [[b1 | n1 | l1 | |] | | gen1 tag1 []]; try done.
  all: destruct v2 as [[b2 | n2 | l2 | |] | | gen2 tag2 []]; try done.
  all: cbn.
  all: rewrite bool_decide_eq_false_2 //.
  all: naive_solver.
Qed.

Lemma val۰structeqｰrefl footprint v :
  val۰immediate v →
  val۰structeq footprint v v.
Proof.
  intros Himmediate.
  apply valｰimmediateｰstructeq; done.
Qed.
Lemma val۰structeqｰrefl' footprint v1 v2 :
  v1 = v2 →
  val۰immediate v1 →
  val۰structeq footprint v1 v2.
Proof.
  intros ->.
  apply val۰structeqｰrefl.
Qed.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  #[local] Lemma structeqｰspecｰaux :
    ⊢ (
      ∀ v1 v2 footprint,
      {{{
        ⌜val۰traversable footprint v1⌝ ∗
        ⌜val۰traversable footprint v2⌝ ∗
        structeq۰footprint footprint
      }}}
        v1 = v2
      {{{
        b
      , RET #b;
        ⌜(if b then val۰structeq else val۰structneq) footprint v1 v2⌝ ∗
        structeq۰footprint footprint
      }}}
    ) ∧ (
      ∀ l1 blk1 l2 blk2 footprint i,
      {{{
        ⌜0 ≤ i ≤ length blk1.(structeq۰block۰fields)⌝%Z ∗
        ⌜footprint !! l1 = Some blk1⌝ ∗
        ⌜footprint !! l2 = Some blk2⌝ ∗
        ⌜blk1.(structeq۰block۰tag) = blk2.(structeq۰block۰tag)⌝ ∗
        ⌜length blk1.(structeq۰block۰fields) = length blk2.(structeq۰block۰fields)⌝ ∗
        structeq۰footprint footprint ∗
        ⌜ ∀ j fld1 fld2,
          blk1.(structeq۰block۰fields) !! j = Some fld1 →
          blk2.(structeq۰block۰fields) !! j = Some fld2 →
          ₊i ≤ j →
          val۰structeq footprint fld1.(structeq۰field۰val) fld2.(structeq۰field۰val)
        ⌝
      }}}
        structeq۰aux #l1 #l2 #i
      {{{
        b
      , RET #b;
        ⌜(if b then val۰structeq else val۰structneq) footprint #l1 #l2⌝ ∗
        structeq۰footprint footprint
      }}}
    ) ∧ (
      ∀ l1 blk1 gen2 tag2 vs2 footprint i,
      let v2 := ValBlock gen2 tag2 vs2 in
      {{{
        ⌜0 ≤ i ≤ length vs2⌝%Z ∗
        ⌜footprint !! l1 = Some blk1⌝ ∗
        ⌜blk1.(structeq۰block۰tag) = tag2⌝ ∗
        ⌜length blk1.(structeq۰block۰fields) = length vs2⌝ ∗
        ⌜0 < length vs2⌝ ∗
        ⌜val۰traversable footprint v2⌝ ∗
        structeq۰footprint footprint ∗
        ⌜ ∀ j fld1 v2,
          blk1.(structeq۰block۰fields) !! j = Some fld1 →
          vs2 !! j = Some v2 →
          ₊i ≤ j →
          val۰structeq footprint fld1.(structeq۰field۰val) v2
        ⌝
      }}}
        structeq۰aux #l1 v2 #i
      {{{
        b
      , RET #b;
        ⌜(if b then val۰structeq else val۰structneq) footprint #l1 v2⌝ ∗
        structeq۰footprint footprint
      }}}
    ) ∧ (
      ∀ gen1 tag1 vs1 l2 blk2 footprint i,
      let v1 := ValBlock gen1 tag1 vs1 in
      {{{
        ⌜0 ≤ i ≤ length vs1⌝%Z ∗
        ⌜footprint !! l2 = Some blk2⌝ ∗
        ⌜tag1 = blk2.(structeq۰block۰tag)⌝ ∗
        ⌜length vs1 = length blk2.(structeq۰block۰fields)⌝ ∗
        ⌜0 < length vs1⌝ ∗
        ⌜val۰traversable footprint v1⌝ ∗
        structeq۰footprint footprint ∗
        ⌜ ∀ j v1 fld2,
          vs1 !! j = Some v1 →
          blk2.(structeq۰block۰fields) !! j = Some fld2 →
          ₊i ≤ j →
          val۰structeq footprint v1 fld2.(structeq۰field۰val)
        ⌝
      }}}
        structeq۰aux v1 #l2 #i
      {{{
        b
      , RET #b;
        ⌜(if b then val۰structeq else val۰structneq) footprint v1 #l2⌝ ∗
        structeq۰footprint footprint
      }}}
    ) ∧ (
      ∀ gen1 tag1 vs1 gen2 tag2 vs2 footprint i,
      let v1 := ValBlock gen1 tag1 vs1 in
      let v2 := ValBlock gen2 tag2 vs2 in
      {{{
        ⌜0 ≤ i ≤ length vs1⌝%Z ∗
        ⌜tag1 = tag2⌝ ∗
        ⌜length vs1 = length vs2⌝ ∗
        ⌜0 < length vs1⌝ ∗
        ⌜val۰traversable footprint v1⌝ ∗
        ⌜val۰traversable footprint v2⌝ ∗
        structeq۰footprint footprint ∗
        ⌜ ∀ j v1 v2,
          vs1 !! j = Some v1 →
          vs2 !! j = Some v2 →
          ₊i ≤ j →
          val۰structeq footprint v1 v2
        ⌝
      }}}
        structeq۰aux v1 v2 #i
      {{{
        b
      , RET #b;
        ⌜(if b then val۰structeq else val۰structneq) footprint v1 v2⌝ ∗
        structeq۰footprint footprint
      }}}
    ).
  Proof.
    iLöb as "HLöb".
    iDestruct "HLöb" as "(IHstructeq & IHstructeq_aux_loc_loc & IHstructeq_aux_loc_block & IHstructeq_aux_block_loc & IHstructeq_aux_block_block)".
    repeat iSplit.

    { iClear "IHstructeq".
      iIntros "%v1 %v2 %footprint !> %Φ (%Htraversable1 & %Htraversable2 & Hfootprint) HΦ".

      wp۰rec. wp۰pures.

      all: destruct v1 as [[b1 | n1 | l1 | |] | | gen1 tag1 [| v1 vs1]].
      all: try done.
      all: wp۰pures.

      all: destruct v2 as [[b2 | n2 | l2 | |] | | gen2 tag2 [| v2 vs2]].
      all: try done.
      all: wp۰pures.

      all:
        try match goal with |- _ _ (WP _ == _ {{ _ }})%I =>
          wp۰apply wpｰequalｰnobranch as (b) "%Hb"
        end.
      all:
        try match goal with |- _ _ ?P =>
          tryif eunify P (wp _ _ _ _) then idtac else
            iSteps
        end.
      all:
        try (
          iPureIntro;
          try (eexists [], _, _; done);
          try (
            destruct b; cbn in Hb;
            [ apply valｰimmediateｰstructeq; done
            | apply valｰimmediateｰstructneq; done
            ]
          );
          try (
            case_bool_decide;
            [ apply val۰structeqｰrefl'; naive_solver
            | apply valｰimmediateｰstructneq; [done.. |];
              cbn; naive_solver
            ]
          )
        ).

      - apply elem_of_dom in Htraversable1 as (blk1 & Hfootprint_lookup_1).
        apply elem_of_dom in Htraversable2 as (blk2 & Hfootprint_lookup_2).
        wp۰apply (structeq۰footprintｰwpｰtag with "Hfootprint") as "Hfootprint"; first done.
        wp۰apply (structeq۰footprintｰwpｰtag with "Hfootprint") as "Hfootprint"; first done.
        wp۰pures.
        case_bool_decide; wp۰pures.
        + wp۰apply (structeq۰footprintｰwpｰsize with "Hfootprint") as "Hfootprint"; first done.
          wp۰apply+ (structeq۰footprintｰwpｰsize with "Hfootprint") as "Hfootprint"; first done.
          wp۰pures.
          case_bool_decide; wp۰pures.
          * wp۰apply ("IHstructeq_aux_loc_loc" with "[$Hfootprint] HΦ").
            iPureIntro. split_and!; [naive_solver lia.. |].
            intros j ? ? ? Hj%lookup_lt_Some. lia.
          * iSteps. iPureIntro.
            eexists [], _, _. split_and!; try done.
            cbn. erewrite !lookup_total_correct; [| done..].
            rewrite andb_false_iff !beqｰspec'. naive_solver.
        + iSteps. iPureIntro.
          eexists [], _, _. split_and!; try done.
          cbn. erewrite !lookup_total_correct; [| done..].
          rewrite andb_false_iff !beqｰspec'. naive_solver.

      - apply elem_of_dom in Htraversable1 as (blk1 & Hfootprint_lookup_1).
        wp۰apply (structeq۰footprintｰwpｰtag with "Hfootprint") as "Hfootprint"; first done.
        wp۰pures.
        case_bool_decide; wp۰pures.
        + wp۰apply (structeq۰footprintｰwpｰsize with "Hfootprint") as "Hfootprint"; first done.
          wp۰pures.
          case_bool_decide; wp۰pures.
          * wp۰apply ("IHstructeq_aux_loc_block" with "[$Hfootprint] HΦ").
            iPureIntro. split_and!; [naive_solver lia.. |].
            intros j ? ? ? Hj%lookup_lt_Some. simpl in Hj. lia.
          * iSteps. iPureIntro.
            eexists [], _, _. split_and!; try done.
            cbn. erewrite !lookup_total_correct; [| done..].
            rewrite andb_false_iff !beqｰspec'. naive_solver.
        + iSteps. iPureIntro.
          eexists [], _, _. split_and!; try done.
          cbn. erewrite !lookup_total_correct; [| done..].
          rewrite andb_false_iff !beqｰspec'. naive_solver.

      - apply elem_of_dom in Htraversable2 as (blk2 & Hfootprint_lookup_2).
        wp۰apply (structeq۰footprintｰwpｰtag with "Hfootprint") as "Hfootprint"; first done.
        wp۰pures.
        case_bool_decide; wp۰pures.
        + wp۰apply (structeq۰footprintｰwpｰsize with "Hfootprint") as "Hfootprint"; first done.
          wp۰pures.
          case_bool_decide; wp۰pures.
          * wp۰apply ("IHstructeq_aux_block_loc" with "[$Hfootprint] HΦ").
            iPureIntro. split_and!; [naive_solver lia.. |].
            intros j ? ? ? Hj%lookup_lt_Some. lia.
          * iSteps. iPureIntro.
            eexists [], _, _. split_and!; try done.
            cbn. erewrite !lookup_total_correct; [| done..].
            rewrite andb_false_iff !beqｰspec'. naive_solver.
        + iSteps. iPureIntro.
          eexists [], _, _. split_and!; try done.
          cbn. erewrite !lookup_total_correct; [| done..].
          rewrite andb_false_iff !beqｰspec'. naive_solver.

      - case_bool_decide; wp۰pures.
        + case_bool_decide; wp۰pures.
          * wp۰apply ("IHstructeq_aux_block_block" with "[$Hfootprint] HΦ").
            iPureIntro. split_and!; [naive_solver lia.. |].
            intros j ? ? ? Hj%lookup_lt_Some. simpl in Hj. lia.
          * iSteps. iPureIntro.
            eexists [], _, _. split_and!; try done.
            rewrite andb_false_iff !beqｰspec'. naive_solver.
        + iSteps. iPureIntro.
          eexists [], _, _. split_and!; try done.
          rewrite andb_false_iff !beqｰspec'. naive_solver.
    }

    { iClear "IHstructeq_aux_loc_block IHstructeq_aux_block_loc IHstructeq_aux_block_block".
      iIntros "%l1 %blk1 %l2 %blk2 %footprint %i !> %Φ (%Hi & %Hfootprint_lookup_1 & %Hfootprint_lookup_2 & % & % & Hfootprint & %Hstructeq) HΦ".

      wp۰rec. wp۰pures.
      case_bool_decide; wp۰pures.

      - iSteps. iPureIntro.
        intros [| j path] dst1 dst2 Hreachable1 Hreachable2.
        all: simp.

        + rewrite andb_true_iff !beqｰspec.
          erewrite !lookup_total_correct; done.

        + rewrite Hfootprint_lookup_1 in Hreachable1.
          destruct (blk1.(structeq۰block۰fields) !! j) as [fld1 |] eqn:Hfields1_lookup; last done.
          rewrite Hfootprint_lookup_2 in Hreachable2.
          destruct (blk2.(structeq۰block۰fields) !! j) as [fld2 |] eqn:Hfields2_lookup; last done.
          eapply Hstructeq; done || lia.

      - replace (i - 1)%Z with ⁺(₊i - 1) by lia.

        wp۰apply (structeq۰footprintｰwpｰload' with "Hfootprint") as (fld2) "(%Hfields2_lookup & %Htraversable2 & Hfootprint)"; [done | lia |].
        wp۰apply (structeq۰footprintｰwpｰload' with "Hfootprint") as (fld1) "(%Hfields1_lookup & %Htraversable1 & Hfootprint)"; [done | lia |].
        wp۰apply+ ("IHstructeq" with "[$Hfootprint]") as (b) "(%Hb & Hfootprint)"; first iSteps.
        destruct b; wp۰pures.

        + wp۰apply ("IHstructeq_aux_loc_loc" with "[$Hfootprint] HΦ").
          iPureIntro. split_and!; try done; try lia.
          intros j.
          destruct_decide (j = ₊i - 1); naive_solver lia.

        + iSteps. iPureIntro.
          destruct Hb as (path & w1 & w2 & Hreachable1 & Hreachable2 & Hcompatible).
          eexists (₊i - 1 :: path), w1, w2. split_and!; last done.
          * rewrite /= Hfootprint_lookup_1 Hfields1_lookup //.
          * rewrite /= Hfootprint_lookup_2 Hfields2_lookup //.
    }

    { iClear "IHstructeq_aux_loc_loc IHstructeq_aux_block_loc IHstructeq_aux_block_block".
      iIntros "%l1 %blk1 %gen2 %tag2 %vs2 %footprint %i !> %Φ (%Hi & %Hfootprint_lookup_1 & % & % & % & %Htraversable2 & Hfootprint & %Hstructeq) HΦ".

      wp۰rec. wp۰pures.
      case_bool_decide; wp۰pures.

      - iSteps. iPureIntro.
        intros [| j path] dst1 dst2 Hreachable1 Hreachable2.
        all: simp.

        + destruct vs2 as [| v2 vs2]; first naive_solver lia.
          rewrite andb_true_iff !beqｰspec.
          erewrite !lookup_total_correct; done.

        + rewrite Hfootprint_lookup_1 in Hreachable1.
          destruct (blk1.(structeq۰block۰fields) !! j) as [fld1 |] eqn:Hfields1_lookup; last done.
          destruct (vs2 !! j) as [v2 |] eqn:Hvs2_lookup; last done.
          eapply Hstructeq; done || lia.

      - replace (i - 1)%Z with ⁺(₊i - 1) by lia.

        destruct (lookup_lt_is_Some_2 vs2 (₊i - 1)) as (v2 & Hvs2_lookup); first lia.

        wp۰pures.
        wp۰apply (structeq۰footprintｰwpｰload' with "Hfootprint") as (fld1) "(%Hfields1_lookup & %Htraversable1 & Hfootprint)"; [done | lia |].
        wp۰apply+ ("IHstructeq" with "[$Hfootprint]") as (b) "(%Hb & Hfootprint)"; first iSteps.
        { iPureIntro.
          rewrite /= Forall'ｰForall Forall_lookup in Htraversable2.
          naive_solver.
        }
        destruct b; wp۰pures.

        + wp۰apply ("IHstructeq_aux_loc_block" with "[$Hfootprint] HΦ").
          iPureIntro. split_and!; try done; try lia.
          intros j.
          destruct_decide (j = ₊i - 1); naive_solver lia.

        + iSteps. iPureIntro.
          destruct Hb as (path & w1 & w2 & Hreachable1 & Hreachable2 & Hcompatible).
          eexists (₊i - 1 :: path), w1, w2. split_and!; last done.
          * rewrite /= Hfootprint_lookup_1 Hfields1_lookup //.
          * rewrite /= Hvs2_lookup //.
    }

    { iClear "IHstructeq_aux_loc_loc IHstructeq_aux_loc_block IHstructeq_aux_block_block".
      iIntros "%gen1 %tag1 %vs1 %l2 %blk2 %footprint %i !> %Φ (%Hi & %Hfootprint_lookup_2 & % & % & % & %Htraversable1 & Hfootprint & %Hstructeq) HΦ".

      wp۰rec. wp۰pures.
      case_bool_decide; wp۰pures.

      - iSteps. iPureIntro.
        intros [| j path] dst1 dst2 Hreachable1 Hreachable2.
        all: simp.

        + destruct vs1 as [| v1 vs1]; first naive_solver lia.
          rewrite andb_true_iff !beqｰspec.
          erewrite !lookup_total_correct; done.

        + destruct (vs1 !! j) as [v1 |] eqn:Hvs1_lookup; last done.
          rewrite Hfootprint_lookup_2 in Hreachable2.
          destruct (blk2.(structeq۰block۰fields) !! j) as [fld2 |] eqn:Hfields2_lookup; last done.
          eapply Hstructeq; done || lia.

      - replace (i - 1)%Z with ⁺(₊i - 1) by lia.

        destruct (lookup_lt_is_Some_2 vs1 (₊i - 1)) as (v1 & Hvs1_lookup); first lia.

        wp۰pures.
        wp۰apply (structeq۰footprintｰwpｰload' with "Hfootprint") as (fld2) "(%Hfields2_lookup & %Htraversable2 & Hfootprint)"; [done | lia |].
        wp۰apply+ ("IHstructeq" with "[$Hfootprint]") as (b) "(%Hb & Hfootprint)"; first iSteps.
        { iPureIntro.
          rewrite /= Forall'ｰForall Forall_lookup in Htraversable1.
          naive_solver.
        }
        destruct b; wp۰pures.

        + wp۰apply ("IHstructeq_aux_block_loc" with "[$Hfootprint] HΦ").
          iPureIntro. split_and!; try done; try lia.
          intros j.
          destruct_decide (j = ₊i - 1); naive_solver lia.

        + iSteps. iPureIntro.
          destruct Hb as (path & w1 & w2 & Hreachable1 & Hreachable2 & Hcompatible).
          eexists (₊i - 1 :: path), w1, w2. split_and!; last done.
          * rewrite /= Hvs1_lookup //.
          * rewrite /= Hfootprint_lookup_2 Hfields2_lookup //.
    }

    { iClear "IHstructeq_aux_loc_loc IHstructeq_aux_loc_block IHstructeq_aux_block_loc".
      iIntros "%gen1 %tag1 %vs1 %gen2 %tag2 %vs2 %footprint %i !> %Φ (%Hi & -> & % & % & %Htraversable1 & %Htraversable2 & Hfootprint & %Hstructeq) HΦ".

      wp۰rec. wp۰pures.
      case_bool_decide; wp۰pures.

      - iSteps. iPureIntro.
        intros [| j path] dst1 dst2 Hreachable1 Hreachable2.
        all: simp.

        + destruct vs1 as [| v1 vs1]; first naive_solver lia.
          destruct vs2 as [| v2 vs2]; first naive_solver lia.
          rewrite andb_true_iff !beqｰspec //.

        + destruct (vs1 !! j) as [v1 |] eqn:Hvs1_lookup; last done.
          destruct (vs2 !! j) as [v2 |] eqn:Hvs2_lookup; last done.
          eapply Hstructeq; done || lia.

      - replace (i - 1)%Z with ⁺(₊i - 1) by lia.

        destruct (lookup_lt_is_Some_2 vs1 (₊i - 1)) as (v1 & Hvs1_lookup); first lia.
        destruct (lookup_lt_is_Some_2 vs2 (₊i - 1)) as (v2 & Hvs2_lookup); first lia.

        wp۰pures.
        wp۰apply+ ("IHstructeq" with "[$Hfootprint]") as (b) "(%Hb & Hfootprint)".
        { iPureIntro.
          rewrite /= !Forall'ｰForall !Forall_lookup in Htraversable1 Htraversable2.
          naive_solver.
        }
        destruct b; wp۰pures.

        + wp۰apply ("IHstructeq_aux_block_block" with "[$Hfootprint] HΦ").
          iPureIntro. split_and!; try done; try lia.
          intros j.
          destruct_decide (j = ₊i - 1); naive_solver lia.

        + iSteps. iPureIntro.
          destruct Hb as (path & w1 & w2 & Hreachable1 & Hreachable2 & Hcompatible).
          eexists (₊i - 1 :: path), w1, w2. split_and!; last done.
          * rewrite /= Hvs1_lookup //.
          * rewrite /= Hvs2_lookup //.
    }
  Qed.
  Lemma structeqｰspec {v1 v2} footprint :
    val۰traversable footprint v1 →
    val۰traversable footprint v2 →
    {{{
      structeq۰footprint footprint
    }}}
      v1 = v2
    {{{
      b
    , RET #b;
      ⌜(if b then val۰structeq else val۰structneq) footprint v1 v2⌝ ∗
      structeq۰footprint footprint
    }}}.
  Proof.
    iIntros "%Htraversable1 %Htraversable2 %Φ Hfootprint HΦ".
    iDestruct structeqｰspecｰaux as "(H & _)".
    iApply ("H" with "[$Hfootprint]"); iSteps.
  Qed.
End zoo۰G.

#[global] Opaque structeq.

(* Abstract (tree-like) values *)

Fixpoint val۰abstract v :=
  match v with
  | ValBool _
  | ValInt _ =>
      True
  | ValBlock Nongenerative _ vs =>
      Forall' val۰abstract vs
  | _ =>
      False
  end.
#[global] Arguments val۰abstract !_ / : assert.

Lemma val۰abstractｰtraversable v :
  val۰abstract v →
  val۰traversable ∅ v.
Proof.
  induction v as [[] | | [] tag vs IH] => //.
  rewrite /= !Forall'ｰForall !Forall_forall in IH |- *.
  naive_solver.
Qed.

Lemma val۰compatibleｰreflｰabstract footprint v1 v2 :
  val۰abstract v1 →
  val۰abstract v2 →
  v1 ≈ v2 →
  val۰compatible footprint v1 v2 = true.
Proof.
  destruct v1 as [[] | | [] tag1 [| v1 vs1]] => //.
  all: destruct v2 as [[] | | [] tag2 [| v2 vs2]] => //.
  all: try rewrite bool_decide_eq_true //.
  intros Habstract1 Habstract2 Hsimilar.
  zoo_simp in Hsimilar.
  rewrite andb_true_iff.
  split; apply beqｰtrue; naive_solver.
Qed.

Lemma valｰstructeqｰabstract₁ footprint v1 v2 :
  val۰abstract v1 →
  val۰abstract v2 →
  val۰structeq footprint v1 v2 →
  v1 ≈ v2.
Proof.
  move: v2. induction v1 as [[] | | [] tag1 [| v1 vs1'] IH] => //.
  all: intros [[] | | [] tag2 [| v2 vs2']] => //.
  all: intros Habstract1 Habstract2 Hstructeq.
  all:
    try (
      ospecialize* (Hstructeq []) => //;
      apply bool_decide_eq_true in Hstructeq;
      naive_solver
    ).
  opose proof* (Hstructeq []) as Hcompatible => //.
  apply andb_prop in Hcompatible as (<-%beqｰeq & Hlen%beqｰeq).
  split; first done.
  set (vs1 := v1 :: vs1') in *. clearbody vs1 => {v1 vs1'}.
  set (vs2 := v2 :: vs2') in *. clearbody vs2 => {v2 vs2'}.
  rewrite Forall2'ｰForall2 Forall2_fmap Forall2_same_length_lookup.
  split; first done. intros i v1 v2 Hlookup1 Hlookup2.
  rewrite /= !Forall'ｰForall !Forall_lookup in IH Habstract1 Habstract2.
  eapply IH; [naive_solver.. |]. intros path v1' v2' Hreachable1 Hreachable2.
  apply (Hstructeq (i :: path)); rewrite /= ?Hlookup1 ?Hlookup2 //.
Qed.
Lemma valｰstructeqｰabstract₂ v1 v2 :
  val۰abstract v1 →
  val۰abstract v2 →
  v1 ≈ v2 →
  val۰structeq ∅ v1 v2.
Proof.
  move: v2. induction v1 as [[] | | [] tag1 [| v1 vs1'] IH] => //.
  all: intros [[] | | [] tag2 [| v2 vs2']] => //.
  all: intros Habstract1 Habstract2 Hsimilar.
  all:
    try (
      intros [] v1 v2; last done; intros <- <-;
      apply val۰compatibleｰreflｰabstract; done
    ).
  intros [| i path] w1 w2.
  - intros <- <-.
    apply val۰compatibleｰreflｰabstract; done.
  - destruct Hsimilar as (<- & Hsimilar).
    set (vs1 := v1 :: vs1') in *. clearbody vs1 => {v1 vs1'}.
    set (vs2 := v2 :: vs2') in *. clearbody vs2 => {v2 vs2'}.
    move=> /= Hreachable1 Hreachable2.
    destruct (vs1 !! i) as [v1 |] eqn:Hlookup1; last done.
    destruct (vs2 !! i) as [v2 |] eqn:Hlookup2; last done.
    rewrite /= !Forall'ｰForall !Forall_lookup in IH Habstract1 Habstract2.
    rewrite Forall2'ｰForall2 Forall2_fmap Forall2_same_length_lookup in Hsimilar.
    eapply IH; last done; naive_solver.
Qed.
Lemma valｰstructeqｰabstract v1 v2 :
  val۰abstract v1 →
  val۰abstract v2 →
  val۰structeq ∅ v1 v2 ↔
  v1 ≈ v2.
Proof.
  intros Habstract1 Habstract2. split.
  - apply valｰstructeqｰabstract₁; done.
  - apply valｰstructeqｰabstract₂; done.
Qed.

Lemma valｰstructneqｰabstract v1 v2 :
  val۰abstract v1 →
  val۰abstract v2 →
  val۰structneq ∅ v1 v2 →
  v1 ≉ v2.
Proof.
  move: v2. induction v1 as [[] | | [] tag1 [| v1 vs1'] IH] => //.
  all: intros [[] | | [] tag2 [| v2 vs2']] => //.
  all: intros Habstract1 Habstract2 (path & v1 & v2 & Hreachable1 & Hreachable2 & Hcompatible).
  all: destruct path; last done; simp.
  all: rewrite bool_decide_eq_false in Hcompatible.
  all: cbn; naive_solver.
Qed.

Lemma structeqｰspecｰabstract `{zoo۰G : !ZooG Σ} {v1 v2} :
  val۰abstract v1 →
  val۰abstract v2 →
  {{{
    True
  }}}
    v1 = v2
  {{{
    b
  , RET #b;
    ⌜(if b then (≈) else (≉)) v1 v2⌝
  }}}.
Proof.
  iIntros "%Habstract1 %Habstract2 %Φ _ HΦ".
  wp۰apply (structeqｰspec ∅) as ([]) "(%H & _)".
  { apply val۰abstractｰtraversable => //. }
  { apply val۰abstractｰtraversable => //. }
  { iApply structeq۰footprintｰempty. }
  - apply valｰstructeqｰabstract in H; [| done..].
    iSteps.
  - apply valｰstructneqｰabstract in H; [| done..].
    iSteps.
Qed.
