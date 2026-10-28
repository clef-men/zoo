Require Import zoo.prelude.
Require Import zoo.common.list.
Require Import zoo.base.
Require Import zoo.options.

Implicit Type b : bool.
Implicit Type chr : ascii.
Implicit Type n : Z.
Implicit Type str : string.
Implicit Type tag : tag.
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
      𝗹𝗲𝘁 "tag" = 𝘁𝗮𝗴 "v1" 𝗶𝗻
      𝗶𝗳 "tag" == 𝘁𝗮𝗴 "v2" 𝘁𝗵𝗲𝗻
        𝗶𝗳 "tag" == #tag۰string 𝘁𝗵𝗲𝗻
          "v1" =ₛ "v2"
        𝗲𝗹𝘀𝗲
          𝗹𝗲𝘁 "sz" = 𝘀𝗶𝘇𝗲 "v1" 𝗶𝗻
          "sz" == 𝘀𝗶𝘇𝗲 "v2" 𝗮𝗻𝗱
          "structeq_aux" "v1" "v2" "sz"
      𝗲𝗹𝘀𝗲
        false
    )
  𝘄𝗶𝘁𝗵 "structeq_aux" "v1" "v2" "i" ->
    𝗶𝗳 "i" == 0 𝘁𝗵𝗲𝗻
      true
    𝗲𝗹𝘀𝗲
      𝗹𝗲𝘁 "i" = "i" - 1 𝗶𝗻
      "structeq" (𝗹𝗼𝗮𝗱 "v1" "i") (𝗹𝗼𝗮𝗱 "v2" "i") 𝗮𝗻𝗱
      "structeq_aux" "v1" "v2" "i"
)%zoo_recs.
Please Definition structeq :=
  ValRecs 0 __zoo_recs.
#[local] Definition structeq۰aux :=
  ValRecs 1 __zoo_recs.
#[global] Instance :
  AsValRecs'
    structeq
    0
    __zoo_recs
    [ structeq
    ; structeq۰aux
    ].
Proof.
  done.
Qed.
#[global] Instance :
  AsValRecs'
    structeq۰aux
    1
    __zoo_recs
    [ structeq
    ; structeq۰aux
    ].
Proof.
  done.
Qed.

Notation "e1 = e2" := (
  Apply (Apply (Val structeq) e1%E) e2%E
)(at level 70,
  no associativity
) : expr_scope.
Notation "e1 ≠ e2" := (
  Unop UnopNeg (Apply (Apply (Val structeq) e1%E) e2%E)
)(at level 70,
  no associativity
) : expr_scope.

Record structeq۰field := StructeqField
  { structeq۰field۰dfrac : dfrac
  ; structeq۰field۰val : val
  }.
Add Printing Constructor structeq۰field.
Implicit Type fld : structeq۰field.

Please derive Inhabited for structeq۰field.

Record structeq۰block := StructeqBlock
  { structeq۰block۰tag : tag
  ; structeq۰block۰fields : list structeq۰field
  }.
Add Printing Constructor structeq۰block.
Implicit Type blk : structeq۰block.
Implicit Type fp : gmap location structeq۰block.

Please derive Inhabited for structeq۰block.

Definition literal۰traversable fp lit :=
  match lit with
  | LitBool _
  | LitChar _
  | LitInt _
  | LitString _ =>
      True
  | LitLoc l =>
      l ∈ dom fp
  | LitBytes _
  | LitProph _ =>
      False
  end.
#[global] Arguments literal۰traversable _ !_ / : assert.

Fixpoint val۰traversable fp v :=
  match v with
  | ValLit lit =>
      literal۰traversable fp lit
  | ValBlock _ _ vs =>
      Forall' (val۰traversable fp) vs
  | ValRecs _ _ =>
      False
  end.
#[global] Arguments val۰traversable _ !_ / : assert.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Definition structeq۰footprint fp : iProp Σ :=
    [∗ map] l ↦ blk ∈ fp,
      l ↦ₕ Header blk.(structeq۰block۰tag) (length blk.(structeq۰block۰fields)) ∗
      [∗ list] i ↦ fld ∈ blk.(structeq۰block۰fields),
        (l +ₗ i) ↦{fld.(structeq۰field۰dfrac)} fld.(structeq۰field۰val) ∗
        ⌜val۰traversable fp fld.(structeq۰field۰val)⌝.

  Lemma structeq۰footprintｰempty :
    ⊢ structeq۰footprint ∅.
  Proof.
    iSteps.
  Qed.

  Lemma structeq۰footprintｰheader {fp} l blk :
    fp !! l = Some blk →
    structeq۰footprint fp ⊢
    l ↦ₕ Header blk.(structeq۰block۰tag) (length blk.(structeq۰block۰fields)).
  Proof.
    iIntros "%Hlookup Hfp".
    iDestruct (big_sepM_lookup with "Hfp") as "($ & _)"; first done.
  Qed.

  Lemma structeq۰footprintｰlookup {fp} l blk (i : nat) fld :
    fp !! l = Some blk →
    blk.(structeq۰block۰fields) !! i = Some fld →
    structeq۰footprint fp ⊢
      (l +ₗ i) ↦{fld.(structeq۰field۰dfrac)} fld.(structeq۰field۰val) ∗
      ⌜val۰traversable fp fld.(structeq۰field۰val)⌝ ∗
      ( (l +ₗ i) ↦{fld.(structeq۰field۰dfrac)} fld.(structeq۰field۰val) -∗
        structeq۰footprint fp
      ).
  Proof.
    iIntros "%Hfp_lookup %Hfields_lookup Hfp".
    iDestruct (big_sepM_lookup_acc with "Hfp") as "((#Hl_header & Hblk) & Hfp)"; first done.
    iDestruct (big_sepL_lookup_acc with "Hblk") as "(HHfld & Hblk)"; first done.
    iSteps.
  Qed.
  Lemma structeq۰footprintｰlookup' {fp} l blk i :
    fp !! l = Some blk →
    i < length blk.(structeq۰block۰fields) →
    structeq۰footprint fp ⊢
      ∃ fld,
      ⌜blk.(structeq۰block۰fields) !! i = Some fld⌝ ∗
      (l +ₗ i) ↦{fld.(structeq۰field۰dfrac)} fld.(structeq۰field۰val) ∗
      ⌜val۰traversable fp fld.(structeq۰field۰val)⌝ ∗
      ( (l +ₗ i) ↦{fld.(structeq۰field۰dfrac)} fld.(structeq۰field۰val) -∗
        structeq۰footprint fp
      ).
  Proof.
    iIntros "%Hfp_lookup %Hi Hfp".
    destruct (lookup_lt_is_Some_2 blk.(structeq۰block۰fields) i) as (fld & Hfields_lookup); first done.
    iExists fld. iStep.
    iApply (structeq۰footprintｰlookup with "Hfp"); done.
  Qed.

  Lemma structeq۰footprintｰwpｰget_tag {fp} l blk :
    fp !! l = Some blk →
    {{{
      structeq۰footprint fp
    }}}
      𝘁𝗮𝗴 #l
    {{{
      RET #blk.(structeq۰block۰tag);
      structeq۰footprint fp
    }}}.
  Proof.
    iIntros "%Hlookup %Φ Hfp HΦ".

    iDestruct (structeq۰footprintｰheader with "Hfp") as "#Hl_header"; first done.
    iSteps.
  Qed.
  Lemma structeq۰footprintｰwpｰget_size {fp} l blk :
    fp !! l = Some blk →
    {{{
      structeq۰footprint fp
    }}}
      𝘀𝗶𝘇𝗲 #l
    {{{
      RET #(length blk.(structeq۰block۰fields));
      structeq۰footprint fp
    }}}.
  Proof.
    iIntros "%Hlookup %Φ Hfp HΦ".

    iDestruct (structeq۰footprintｰheader with "Hfp") as "#Hl_header"; first done.
    iSteps.
  Qed.

  Lemma structeq۰footprintｰwpｰload {fp} l blk (i : nat) fld :
    fp !! l = Some blk →
    blk.(structeq۰block۰fields) !! i = Some fld →
    {{{
      structeq۰footprint fp
    }}}
      𝗹𝗼𝗮𝗱 #l #i
    {{{
      RET fld.(structeq۰field۰val);
      ⌜val۰traversable fp fld.(structeq۰field۰val)⌝ ∗
      structeq۰footprint fp
    }}}.
  Proof.
    iIntros "%Hfp_lookup %Hfields_lookup %Φ Hfp HΦ".

    iDestruct (structeq۰footprintｰlookup with "Hfp") as "(Hl & %Htraversable & Hfp)"; [done.. |].
    iSteps.
  Qed.
  Lemma structeq۰footprintｰwpｰload' {fp} l blk i :
    fp !! l = Some blk →
    i < length blk.(structeq۰block۰fields) →
    {{{
      structeq۰footprint fp
    }}}
      𝗹𝗼𝗮𝗱 #l #i
    {{{
      fld
    , RET fld.(structeq۰field۰val);
      ⌜blk.(structeq۰block۰fields) !! i = Some fld⌝ ∗
      ⌜val۰traversable fp fld.(structeq۰field۰val)⌝ ∗
      structeq۰footprint fp
    }}}.
  Proof.
    iIntros "%Hfp_lookup %Hi %Φ Hfp HΦ".

    iDestruct (structeq۰footprintｰlookup' with "Hfp") as "(%fld & %Hfields_lookup & Hl & %Htraversable & Hfp)"; [done.. |].
    iSteps.
  Qed.
End zoo۰G.

Fixpoint val۰reachable fp src path dst :=
  match path with
  | [] =>
      src = dst
  | i :: path =>
      match src with
      | ValLoc l =>
          match fp !! l with
          | None =>
              False
          | Some blk =>
              match blk.(structeq۰block۰fields) !! i with
              | None =>
                  False
              | Some fld =>
                  val۰reachable fp fld.(structeq۰field۰val) path dst
              end
          end
      | ValBlock _ _ vs =>
          match vs !! i with
          | None =>
              False
          | Some src =>
              val۰reachable fp src path dst
          end
      | _ =>
          False
      end
  end.
#[global] Arguments val۰reachable _ !_ !_ / _ : assert.

#[global] Instance val۰reachableｰdec fp src path dst :
  Decision (val۰reachable fp src path dst).
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
              (match fp !! l as x return _ = x → _ with
              | None => λ Hfp_lookup,
                  right _
              | Some blk => λ Hfp_lookup,
                  (match blk.(structeq۰block۰fields) !! i as x return _ = x → _ with
                  | None => λ Hfields_lookup,
                      right _
                  | Some fld => λ Hfields_lookup,
                      cast_if (go fld.(structeq۰field۰val) path)
                  end) (eq_refl (blk.(structeq۰block۰fields) !! i))
              end) (eq_refl (fp !! l))
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
      rewrite /= ?Hfp_lookup ?Hfields_lookup ?Hvs_lookup;
      congruence
    ).
Defined.

Definition lowval۰compatible fp lv1 lv2 :=
  match lv1 with
  | LowvalLit lit1 =>
      match lit1 with
      | LowlitBytes _ =>
          false
      | LowlitLoc l1 =>
          match lv2 with
          | LowvalLoc l2 =>
              let blk1 := fp !!! l1 in
              let blk2 := fp !!! l2 in
              blk1.(structeq۰block۰tag) ≟ blk2.(structeq۰block۰tag) &&
              length blk1.(structeq۰block۰fields) ≟ length blk2.(structeq۰block۰fields)
          | LowvalBlock _ tag2 vs2 _ =>
              let blk1 := fp !!! l1 in
              blk1.(structeq۰block۰tag) ≟ tag2 &&
              length blk1.(structeq۰block۰fields) ≟ length vs2
          | _ =>
              false
          end
      | _ =>
          bool_decide (lv1 = lv2)
      end
  | LowvalRecs =>
      bool_decide (lv1 = lv2)
  | LowvalBlock _ tag1 vs1 _ =>
      match lv2 with
      | LowvalLoc l2 =>
          let blk2 := fp !!! l2 in
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

Definition val۰compatible fp v1 v2 :=
  lowval۰compatible fp (val۰to_low v1) (val۰to_low v2).

Lemma lowval۰compatibleｰsym fp lv1 lv2 :
  lowval۰compatible fp lv1 lv2 =
  lowval۰compatible fp lv2 lv1.
Proof.
  all: destruct lv1 as [[] | |].
  all: destruct lv2 as [[] | |].
  all: simpl.
  all: try done.
  1,2: apply bool_decide_ext => //.
  all: setoid_rewrite beqｰsym at 1 2 => //.
Qed.
Lemma val۰compatibleｰsym fp v1 v2 :
  val۰compatible fp v1 v2 =
  val۰compatible fp v2 v1.
Proof.
  rewrite /val۰compatible lowval۰compatibleｰsym //.
Qed.

Definition val۰structeq fp v1 v2 :=
  ∀ path v1' v2',
  val۰reachable fp v1 path v1' →
  val۰reachable fp v2 path v2' →
  val۰compatible fp v1' v2' = true.

Definition val۰structneq fp v1 v2 :=
  ∃ path v1' v2',
  val۰reachable fp v1 path v1' ∧
  val۰reachable fp v2 path v2' ∧
  val۰compatible fp v1' v2' = false.

Lemma val۰structeqｰsym fp v1 v2 :
  val۰structeq fp v1 v2 →
  val۰structeq fp v2 v1.
Proof.
  intros Hstructeq path v1' v2' Hreachable1 Hreachable2.
  rewrite val۰compatibleｰsym. eauto.
Qed.

Lemma val۰structneqｰsym fp v1 v2 :
  val۰structneq fp v1 v2 →
  val۰structneq fp v2 v1.
Proof.
  intros (path & v1' & v2' & Hreachable1 & Hreachable2 & Hcompatible).
  rewrite val۰compatibleｰsym in Hcompatible.
  rewrite /val۰structneq. naive.
Qed.

Lemma valｰimmediateｰstructeq fp v1 v2 :
  val۰immediate v1 →
  val۰immediate v2 →
  v1 ≈ v2 →
  val۰structeq fp v1 v2.
Proof.
  intros Himmediate1 Himmediate2 Hsimilar.
  intros path v1_ v2_ Hreachable1 Hreachable2.
  destruct v1 as [[b1 | chr1 | n1 | str1 | l1 | l1 |] | | gen1 tag1 []] => //.
  all: destruct v2 as [[b2 | chr2 | str2 | n2 | l2 | l2 |] | | gen2 tag2 []] => //.
  all: destruct path; last done.
  all: simp.
  all: cbn.
  all: rewrite bool_decide_eq_true_2 //.
Qed.
Lemma valｰimmediateｰstructneq fp v1 v2 :
  val۰immediate v1 →
  val۰immediate v2 →
  v1 ≉ v2 →
  val۰structneq fp v1 v2.
Proof.
  intros Himmediate1 Himmediate2 Hnonsimilar.
  eexists [], v1, v2. split_and! => //.
  destruct v1 as [[b1 | chr1 | n1 | str1 | l1 | l1 |] | | gen1 tag1 []] => //.
  all: destruct v2 as [[b2 | chr2 | str2 | n2 | l2 | l2 |] | | gen2 tag2 []] => //.
  all: cbn in Hnonsimilar |- *.
  all: rewrite bool_decide_eq_false_2 //.
  all: congruence.
Qed.

Lemma val۰structeqｰreflｰimmediate fp v :
  val۰immediate v →
  val۰structeq fp v v.
Proof.
  intros Himmediate.
  apply valｰimmediateｰstructeq; done.
Qed.
Lemma val۰structeqｰreflｰimmediate' fp v1 v2 :
  v1 = v2 →
  val۰immediate v1 →
  val۰structeq fp v1 v2.
Proof.
  intros ->.
  apply val۰structeqｰreflｰimmediate.
Qed.
Lemma val۰structeqｰreflｰstring fp str :
  val۰structeq fp #str #str.
Proof.
  intros path v1 v2 Hreachable1 Hreachable2.
  destruct path. 2: done.
  simp. cbn.
  rewrite bool_decide_eq_true_2 //.
Qed.
Lemma val۰structeqｰreflｰstring' fp str1 str2 :
  str1 = str2 →
  val۰structeq fp #str1 #str2.
Proof.
  intros ->.
  apply val۰structeqｰreflｰstring.
Qed.

Lemma val۰structneqｰstringｰl fp str v :
  #str ≠ v →
  val۰structneq fp #str v.
Proof.
  intros.
  exists [], #str, v. split_and! => //.
  destruct v as [[] | | gen tag [| v vs]] => //.
  rewrite bool_decide_eq_false. naive.
Qed.
Lemma val۰structneqｰstringｰr fp v str :
  v ≠ #str →
  val۰structneq fp v #str.
Proof.
  intros.
  apply val۰structneqｰsym, val۰structneqｰstringｰl => //.
Qed.
Lemma val۰structneqｰstring fp str1 str2 :
  str1 ≠ str2 →
  val۰structneq fp #str1 #str2.
Proof.
  intros.
  apply val۰structneqｰstringｰl. naive.
Qed.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  #[local] Lemma structeqｰspecｰaux :
    ⊢ (
      ∀ v1 v2 fp,
      {{{
        ⌜val۰traversable fp v1⌝ ∗
        ⌜val۰traversable fp v2⌝ ∗
        structeq۰footprint fp
      }}}
        v1 = v2
      {{{
        b
      , RET #b;
        ⌜(if b then val۰structeq else val۰structneq) fp v1 v2⌝ ∗
        structeq۰footprint fp
      }}}
    ) ∧ (
      ∀ l1 blk1 l2 blk2 fp i,
      {{{
        ⌜0 ≤ i ≤ length blk1.(structeq۰block۰fields)⌝%Z ∗
        ⌜fp !! l1 = Some blk1⌝ ∗
        ⌜fp !! l2 = Some blk2⌝ ∗
        ⌜blk1.(structeq۰block۰tag) = blk2.(structeq۰block۰tag)⌝ ∗
        ⌜length blk1.(structeq۰block۰fields) = length blk2.(structeq۰block۰fields)⌝ ∗
        structeq۰footprint fp ∗
        ⌜ ∀ j fld1 fld2,
          blk1.(structeq۰block۰fields) !! j = Some fld1 →
          blk2.(structeq۰block۰fields) !! j = Some fld2 →
          ₊i ≤ j →
          val۰structeq fp fld1.(structeq۰field۰val) fld2.(structeq۰field۰val)
        ⌝
      }}}
        structeq۰aux #l1 #l2 #i
      {{{
        b
      , RET #b;
        ⌜(if b then val۰structeq else val۰structneq) fp #l1 #l2⌝ ∗
        structeq۰footprint fp
      }}}
    ) ∧ (
      ∀ l1 blk1 gen2 tag2 vs2 fp i,
      let v2 := ValBlock gen2 tag2 vs2 in
      {{{
        ⌜0 ≤ i ≤ length vs2⌝%Z ∗
        ⌜fp !! l1 = Some blk1⌝ ∗
        ⌜blk1.(structeq۰block۰tag) = tag2⌝ ∗
        ⌜length blk1.(structeq۰block۰fields) = length vs2⌝ ∗
        ⌜0 < length vs2⌝ ∗
        ⌜val۰traversable fp v2⌝ ∗
        structeq۰footprint fp ∗
        ⌜ ∀ j fld1 v2,
          blk1.(structeq۰block۰fields) !! j = Some fld1 →
          vs2 !! j = Some v2 →
          ₊i ≤ j →
          val۰structeq fp fld1.(structeq۰field۰val) v2
        ⌝
      }}}
        structeq۰aux #l1 v2 #i
      {{{
        b
      , RET #b;
        ⌜(if b then val۰structeq else val۰structneq) fp #l1 v2⌝ ∗
        structeq۰footprint fp
      }}}
    ) ∧ (
      ∀ gen1 tag1 vs1 l2 blk2 fp i,
      let v1 := ValBlock gen1 tag1 vs1 in
      {{{
        ⌜0 ≤ i ≤ length vs1⌝%Z ∗
        ⌜fp !! l2 = Some blk2⌝ ∗
        ⌜tag1 = blk2.(structeq۰block۰tag)⌝ ∗
        ⌜length vs1 = length blk2.(structeq۰block۰fields)⌝ ∗
        ⌜0 < length vs1⌝ ∗
        ⌜val۰traversable fp v1⌝ ∗
        structeq۰footprint fp ∗
        ⌜ ∀ j v1 fld2,
          vs1 !! j = Some v1 →
          blk2.(structeq۰block۰fields) !! j = Some fld2 →
          ₊i ≤ j →
          val۰structeq fp v1 fld2.(structeq۰field۰val)
        ⌝
      }}}
        structeq۰aux v1 #l2 #i
      {{{
        b
      , RET #b;
        ⌜(if b then val۰structeq else val۰structneq) fp v1 #l2⌝ ∗
        structeq۰footprint fp
      }}}
    ) ∧ (
      ∀ gen1 tag1 vs1 gen2 tag2 vs2 fp i,
      let v1 := ValBlock gen1 tag1 vs1 in
      let v2 := ValBlock gen2 tag2 vs2 in
      {{{
        ⌜0 ≤ i ≤ length vs1⌝%Z ∗
        ⌜tag1 = tag2⌝ ∗
        ⌜length vs1 = length vs2⌝ ∗
        ⌜0 < length vs1⌝ ∗
        ⌜val۰traversable fp v1⌝ ∗
        ⌜val۰traversable fp v2⌝ ∗
        structeq۰footprint fp ∗
        ⌜ ∀ j v1 v2,
          vs1 !! j = Some v1 →
          vs2 !! j = Some v2 →
          ₊i ≤ j →
          val۰structeq fp v1 v2
        ⌝
      }}}
        structeq۰aux v1 v2 #i
      {{{
        b
      , RET #b;
        ⌜(if b then val۰structeq else val۰structneq) fp v1 v2⌝ ∗
        structeq۰footprint fp
      }}}
    ).
  Proof.
    iLöb as "HLöb".
    iDestruct "HLöb" as "(IHstructeq & IHstructeq_aux_loc_loc & IHstructeq_aux_loc_block & IHstructeq_aux_block_loc & IHstructeq_aux_block_block)".
    repeat iSplit.

    { iClear "IHstructeq".
      iIntros "%v1 %v2 %fp !> %Φ (%Htraversable1 & %Htraversable2 & Hfp) HΦ".

      wp۰rec. wp۰pures.

      all: destruct v1 as [[b1 | chr1 | n1 | str1 | l1 | l1 |] | | gen1 tag1 [| v1 vs1]].
      all: try (exfalso; done).
      all: wp۰pures.

      all: destruct v2 as [[b2 | chr2 | n2 | str2 | l2 | l2 |] | | gen2 tag2 [| v2 vs2]].
      all: try (exfalso; done).
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
            [ apply val۰structeqｰreflｰimmediate'; naive
            | apply valｰimmediateｰstructneq; [done.. |];
              cbn; naive
            ]
          )
        ).

      - iEval (rewrite bool_decide_eq_true_2 //).
        wp۰pures.
        iEval (rewrite bool_decide_eq_true_2 //).
        iSteps. iPureIntro.
        case_bool_decide.
        + apply val۰structeqｰreflｰstring' => //.
        + apply val۰structneqｰstring => //.

      - apply elem_of_dom in Htraversable2 as (blk2 & Hfp_lookup_2).
        wp۰apply (structeq۰footprintｰwpｰget_tag with "Hfp") as "Hfp"; first done.
        wp۰pures.
        rewrite bool_decide_eq_false_2.
        { pose proof (tag۰stringｰspec blk2.(structeq۰block۰tag)). lia. }
        iSteps. iPureIntro.
        apply val۰structneqｰstringｰl => //.

      - rewrite bool_decide_eq_false_2.
        { pose proof (tag۰stringｰspec tag2). lia. }
        iSteps. iPureIntro.
        apply val۰structneqｰstringｰl => //.

      - apply elem_of_dom in Htraversable1 as (blk1 & Hfp_lookup_1).
        wp۰apply (structeq۰footprintｰwpｰget_tag with "Hfp") as "Hfp"; first done.
        wp۰pures.
        rewrite bool_decide_eq_false_2.
        { pose proof (tag۰stringｰspec blk1.(structeq۰block۰tag)). lia. }
        iSteps. iPureIntro.
        apply val۰structneqｰstringｰr => //.

      - apply elem_of_dom in Htraversable1 as (blk1 & Hfp_lookup_1).
        apply elem_of_dom in Htraversable2 as (blk2 & Hfp_lookup_2).
        wp۰apply (structeq۰footprintｰwpｰget_tag with "Hfp") as "Hfp"; first done.
        wp۰apply+ (structeq۰footprintｰwpｰget_tag with "Hfp") as "Hfp"; first done.
        wp۰pures.
        case_bool_decide; wp۰pures.
        + rewrite bool_decide_eq_false_2.
          { pose proof (tag۰stringｰspec blk1.(structeq۰block۰tag)). lia. }
          wp۰apply+ (structeq۰footprintｰwpｰget_size with "Hfp") as "Hfp"; first done.
          wp۰apply+ (structeq۰footprintｰwpｰget_size with "Hfp") as "Hfp"; first done.
          wp۰pures.
          case_bool_decide; wp۰pures.
          * wp۰apply ("IHstructeq_aux_loc_loc" with "[$Hfp] HΦ").
            iPureIntro. split_and!; [naive lia.. |].
            intros j ? ? ? Hj%lookup_lt_Some. lia.
          * iSteps. iPureIntro.
            eexists [], _, _. split_and! => //.
            cbn. erewrite !lookup_total_correct; [| done..].
            rewrite andb_false_iff !beqｰspec'. naive.
        + iSteps. iPureIntro.
          eexists [], _, _. split_and! => //.
          cbn. erewrite !lookup_total_correct; [| done..].
          rewrite andb_false_iff !beqｰspec'.
          naive congruence.

      - apply elem_of_dom in Htraversable1 as (blk1 & Hfp_lookup_1).
        wp۰apply (structeq۰footprintｰwpｰget_tag with "Hfp") as "Hfp"; first done.
        wp۰pures.
        case_bool_decide; wp۰pures.
        + rewrite bool_decide_eq_false_2.
          { pose proof (tag۰stringｰspec blk1.(structeq۰block۰tag)). lia. }
          wp۰apply+ (structeq۰footprintｰwpｰget_size with "Hfp") as "Hfp"; first done.
          wp۰pures.
          case_bool_decide; wp۰pures.
          * wp۰apply ("IHstructeq_aux_loc_block" with "[$Hfp] HΦ").
            iPureIntro. split_and!; [naive lia.. |].
            intros j ? ? ? Hj%lookup_lt_Some. simpl in Hj. lia.
          * iSteps. iPureIntro.
            eexists [], _, _. split_and! => //.
            cbn. erewrite !lookup_total_correct; [| done..].
            rewrite andb_false_iff !beqｰspec'. naive.
        + iSteps. iPureIntro.
          eexists [], _, _. split_and! => //.
          cbn. erewrite !lookup_total_correct; [| done..].
          rewrite andb_false_iff !beqｰspec'. naive.

      - rewrite bool_decide_eq_false_2.
        { pose proof (tag۰stringｰspec tag1). lia. }
        iSteps. iPureIntro.
        apply val۰structneqｰstringｰr => //.

      - apply elem_of_dom in Htraversable2 as (blk2 & Hfp_lookup_2).
        wp۰apply (structeq۰footprintｰwpｰget_tag with "Hfp") as "Hfp"; first done.
        wp۰pures.
        case_bool_decide; wp۰pures.
        + rewrite bool_decide_eq_false_2.
          { pose proof (tag۰stringｰspec tag1). lia. }
          wp۰apply+ (structeq۰footprintｰwpｰget_size with "Hfp") as "Hfp"; first done.
          wp۰pures.
          case_bool_decide; wp۰pures.
          * wp۰apply ("IHstructeq_aux_block_loc" with "[$Hfp] HΦ").
            iPureIntro. split_and!; [naive lia.. |].
            intros j ? ? ? Hj%lookup_lt_Some. lia.
          * iSteps. iPureIntro.
            eexists [], _, _. split_and! => //.
            cbn. erewrite !lookup_total_correct; [| done..].
            rewrite andb_false_iff !beqｰspec'. naive.
        + iSteps. iPureIntro.
          eexists [], _, _. split_and! => //.
          cbn. erewrite !lookup_total_correct; [| done..].
          rewrite andb_false_iff !beqｰspec'. naive.

      - case_bool_decide; wp۰pures.
        + rewrite bool_decide_eq_false_2.
          { pose proof (tag۰stringｰspec tag1). lia. }
          wp۰pures. case_bool_decide; wp۰pures.
          * wp۰apply ("IHstructeq_aux_block_block" with "[$Hfp] HΦ").
            iPureIntro. split_and!; [naive lia.. |].
            intros j ? ? ? Hj%lookup_lt_Some. simpl in Hj. lia.
          * iSteps. iPureIntro.
            eexists [], _, _. split_and! => //.
            rewrite andb_false_iff !beqｰspec'. naive.
        + iSteps. iPureIntro.
          eexists [], _, _. split_and! => //.
          rewrite andb_false_iff !beqｰspec'. naive.
    }

    { iClear "IHstructeq_aux_loc_block IHstructeq_aux_block_loc IHstructeq_aux_block_block".
      iIntros "%l1 %blk1 %l2 %blk2 %fp %i !> %Φ (%Hi & %Hfp_lookup_1 & %Hfp_lookup_2 & % & % & Hfp & %Hstructeq) HΦ".

      wp۰rec. wp۰pures.
      case_bool_decide; wp۰pures.

      - iSteps. iPureIntro.
        intros [| j path] dst1 dst2 Hreachable1 Hreachable2.
        all: simp.

        + rewrite andb_true_iff !beqｰspec.
          erewrite !lookup_total_correct; done.

        + rewrite Hfp_lookup_1 in Hreachable1.
          destruct (blk1.(structeq۰block۰fields) !! j) as [fld1 |] eqn:Hfields1_lookup; last done.
          rewrite Hfp_lookup_2 in Hreachable2.
          destruct (blk2.(structeq۰block۰fields) !! j) as [fld2 |] eqn:Hfields2_lookup; last done.
          eapply Hstructeq; done || lia.

      - replace (i - 1)%Z with ⁺(₊i - 1) by lia.

        wp۰apply (structeq۰footprintｰwpｰload' with "Hfp") as (fld2) "(%Hfields2_lookup & %Htraversable2 & Hfp)"; [done | lia |].
        wp۰apply (structeq۰footprintｰwpｰload' with "Hfp") as (fld1) "(%Hfields1_lookup & %Htraversable1 & Hfp)"; [done | lia |].
        wp۰apply+ ("IHstructeq" with "[$Hfp]") as (b) "(%Hb & Hfp)"; first iSteps.
        destruct b; wp۰pures.

        + wp۰apply ("IHstructeq_aux_loc_loc" with "[$Hfp] HΦ").
          iPureIntro. split_and! => //; try lia.
          intros j.
          destruct_decide (j = ₊i - 1); naive lia.

        + iSteps. iPureIntro.
          destruct Hb as (path & w1 & w2 & Hreachable1 & Hreachable2 & Hcompatible).
          eexists (₊i - 1 :: path), w1, w2. split_and!; last done.
          * rewrite /= Hfp_lookup_1 Hfields1_lookup //.
          * rewrite /= Hfp_lookup_2 Hfields2_lookup //.
    }

    { iClear "IHstructeq_aux_loc_loc IHstructeq_aux_block_loc IHstructeq_aux_block_block".
      iIntros "%l1 %blk1 %gen2 %tag2 %vs2 %fp %i !> %Φ (%Hi & %Hfp_lookup_1 & % & % & % & %Htraversable2 & Hfp & %Hstructeq) HΦ".

      wp۰rec. wp۰pures.
      case_bool_decide; wp۰pures.

      - iSteps. iPureIntro.
        intros [| j path] dst1 dst2 Hreachable1 Hreachable2.
        all: simp.

        + destruct vs2 as [| v2 vs2]; first naive lia.
          rewrite andb_true_iff !beqｰspec.
          erewrite !lookup_total_correct; done.

        + rewrite Hfp_lookup_1 in Hreachable1.
          destruct (blk1.(structeq۰block۰fields) !! j) as [fld1 |] eqn:Hfields1_lookup; last done.
          destruct (vs2 !! j) as [v2 |] eqn:Hvs2_lookup; last done.
          eapply Hstructeq; done || lia.

      - replace (i - 1)%Z with ⁺(₊i - 1) by lia.

        destruct (lookup_lt_is_Some_2 vs2 (₊i - 1)) as (v2 & Hvs2_lookup); first lia.

        wp۰pures.
        wp۰apply (structeq۰footprintｰwpｰload' with "Hfp") as (fld1) "(%Hfields1_lookup & %Htraversable1 & Hfp)"; [done | lia |].
        wp۰apply+ ("IHstructeq" with "[$Hfp]") as (b) "(%Hb & Hfp)"; first iSteps.
        { iPureIntro. simp_Forall+/= in *. eauto. }
        destruct b; wp۰pures.

        + wp۰apply ("IHstructeq_aux_loc_block" with "[$Hfp] HΦ").
          iPureIntro. split_and! => //; try lia.
          intros j.
          destruct_decide (j = ₊i - 1); naive lia.

        + iSteps. iPureIntro.
          destruct Hb as (path & w1 & w2 & Hreachable1 & Hreachable2 & Hcompatible).
          eexists (₊i - 1 :: path), w1, w2. split_and!; last done.
          * rewrite /= Hfp_lookup_1 Hfields1_lookup //.
          * rewrite /= Hvs2_lookup //.
    }

    { iClear "IHstructeq_aux_loc_loc IHstructeq_aux_loc_block IHstructeq_aux_block_block".
      iIntros "%gen1 %tag1 %vs1 %l2 %blk2 %fp %i !> %Φ (%Hi & %Hfp_lookup_2 & % & % & % & %Htraversable1 & Hfp & %Hstructeq) HΦ".

      wp۰rec. wp۰pures.
      case_bool_decide; wp۰pures.

      - iSteps. iPureIntro.
        intros [| j path] dst1 dst2 Hreachable1 Hreachable2.
        all: simp.

        + destruct vs1 as [| v1 vs1]; first naive lia.
          rewrite andb_true_iff !beqｰspec.
          erewrite !lookup_total_correct; done.

        + destruct (vs1 !! j) as [v1 |] eqn:Hvs1_lookup; last done.
          rewrite Hfp_lookup_2 in Hreachable2.
          destruct (blk2.(structeq۰block۰fields) !! j) as [fld2 |] eqn:Hfields2_lookup; last done.
          eapply Hstructeq; done || lia.

      - replace (i - 1)%Z with ⁺(₊i - 1) by lia.

        destruct (lookup_lt_is_Some_2 vs1 (₊i - 1)) as (v1 & Hvs1_lookup); first lia.

        wp۰pures.
        wp۰apply (structeq۰footprintｰwpｰload' with "Hfp") as (fld2) "(%Hfields2_lookup & %Htraversable2 & Hfp)"; [done | lia |].
        wp۰apply+ ("IHstructeq" with "[$Hfp]") as (b) "(%Hb & Hfp)"; first iSteps.
        { iPureIntro. simp_Forall+/= in *. eauto. }
        destruct b; wp۰pures.

        + wp۰apply ("IHstructeq_aux_block_loc" with "[$Hfp] HΦ").
          iPureIntro. split_and! => //; try lia.
          intros j.
          destruct_decide (j = ₊i - 1); naive lia.

        + iSteps. iPureIntro.
          destruct Hb as (path & w1 & w2 & Hreachable1 & Hreachable2 & Hcompatible).
          eexists (₊i - 1 :: path), w1, w2. split_and!; last done.
          * rewrite /= Hvs1_lookup //.
          * rewrite /= Hfp_lookup_2 Hfields2_lookup //.
    }

    { iClear "IHstructeq_aux_loc_loc IHstructeq_aux_loc_block IHstructeq_aux_block_loc".
      iIntros "%gen1 %tag1 %vs1 %gen2 %tag2 %vs2 %fp %i !> %Φ (%Hi & -> & % & % & %Htraversable1 & %Htraversable2 & Hfp & %Hstructeq) HΦ".

      wp۰rec. wp۰pures.
      case_bool_decide; wp۰pures.

      - iSteps. iPureIntro.
        intros [| j path] dst1 dst2 Hreachable1 Hreachable2.
        all: simp.

        + destruct vs1 as [| v1 vs1]; first naive lia.
          destruct vs2 as [| v2 vs2]; first naive lia.
          rewrite andb_true_iff !beqｰspec //.

        + destruct (vs1 !! j) as [v1 |] eqn:Hvs1_lookup; last done.
          destruct (vs2 !! j) as [v2 |] eqn:Hvs2_lookup; last done.
          eapply Hstructeq; done || lia.

      - replace (i - 1)%Z with ⁺(₊i - 1) by lia.

        destruct (lookup_lt_is_Some_2 vs1 (₊i - 1)) as (v1 & Hvs1_lookup); first lia.
        destruct (lookup_lt_is_Some_2 vs2 (₊i - 1)) as (v2 & Hvs2_lookup); first lia.

        wp۰pures.
        wp۰apply+ ("IHstructeq" with "[$Hfp]") as (b) "(%Hb & Hfp)".
        { iPureIntro. simp_Forall+/= in *. eauto. }
        destruct b; wp۰pures.

        + wp۰apply ("IHstructeq_aux_block_block" with "[$Hfp] HΦ").
          iPureIntro. split_and! => //; try lia.
          intros j.
          destruct_decide (j = ₊i - 1); naive lia.

        + iSteps. iPureIntro.
          destruct Hb as (path & w1 & w2 & Hreachable1 & Hreachable2 & Hcompatible).
          eexists (₊i - 1 :: path), w1, w2. split_and!; last done.
          * rewrite /= Hvs1_lookup //.
          * rewrite /= Hvs2_lookup //.
    }
  Qed.
  Lemma structeqｰspec {v1 v2} fp :
    val۰traversable fp v1 →
    val۰traversable fp v2 →
    {{{
      structeq۰footprint fp
    }}}
      v1 = v2
    {{{
      b
    , RET #b;
      ⌜(if b then val۰structeq else val۰structneq) fp v1 v2⌝ ∗
      structeq۰footprint fp
    }}}.
  Proof.
    iIntros "%Htraversable1 %Htraversable2 %Φ Hfp HΦ".
    iDestruct structeqｰspecｰaux as "(H & _)".
    iApply ("H" with "[$Hfp]"); iSteps.
  Qed.
End zoo۰G.

Please opacify.

(* Abstract (tree-like) values *)

Definition literal۰abstract lit :=
  match lit with
  | LitBool _
  | LitChar _
  | LitInt _
  | LitString _ =>
      True
  | LitLoc _
  | LitBytes _
  | LitProph _ =>
      False
  end.
#[global] Arguments literal۰abstract !_ / : assert.

Fixpoint val۰abstract v :=
  match v with
  | ValLit lit =>
      literal۰abstract lit
  | ValBlock Nongenerative _ vs =>
      Forall' val۰abstract vs
  | ValBlock (Generative _) _ _
  | ValRecs _ _ =>
      False
  end.
#[global] Arguments val۰abstract !_ / : assert.

Lemma val۰abstractｰtraversable v :
  val۰abstract v →
  val۰traversable ∅ v.
Proof.
  induction v as [[] | | [] tag vs IH] => //.
  simp_Forall+/= in *. eauto.
Qed.

Lemma val۰compatibleｰreflｰabstract fp v1 v2 :
  val۰abstract v1 →
  val۰abstract v2 →
  v1 ≈ v2 →
  val۰compatible fp v1 v2 = true.
Proof.
  destruct v1 as [[] | | [] tag1 [| v1 vs1]] => //.
  all: destruct v2 as [[] | | [] tag2 [| v2 vs2]] => //.
  all: try rewrite bool_decide_eq_true //.
  intros Habstract1 Habstract2 Hsimilar.
  zoo۰simp in Hsimilar.
  rewrite andb_true_iff.
  split; apply beqｰtrue; naive.
Qed.

Lemma valｰstructeqｰabstract₁ fp v1 v2 :
  val۰abstract v1 →
  val۰abstract v2 →
  val۰structeq fp v1 v2 →
  v1 ≈ v2.
Proof.
  move: v2. induction v1 as [[] | | [] tag1 [| v1 vs1'] IH] => //.
  all: intros [[] | | [] tag2 [| v2 vs2']] => //.
  all: intros Habstract1 Habstract2 Hstructeq.
  all:
    try (
      ospecialize* (Hstructeq []) => //;
      apply bool_decide_eq_true in Hstructeq;
      naive
    ).
  opose proof* (Hstructeq []) as Hcompatible => //.
  apply andb_prop in Hcompatible as (<-%beqｰeq & Hlen%beqｰeq).
  split; first done.
  set (vs1 := v1 :: vs1') in *. clearbody vs1 => {v1 vs1'}.
  set (vs2 := v2 :: vs2') in *. clearbody vs2 => {v2 vs2'}.
  simp_Forall+/= in *.
  split; first done. intros i v1 v2 Hlookup1 Hlookup2.
  eapply IH; [naive.. |]. intros path v1' v2' Hreachable1 Hreachable2.
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
    simp_Forall+/= in *.
    eapply IH; last done; naive.
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
  all: cbn.
  all: naive congruence.
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
