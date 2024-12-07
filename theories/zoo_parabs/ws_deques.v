From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Import
  option
  random_round.
From zoo_parabs Require Export
  base.
From zoo Require Import
  options.

Implicit Types v t round : val.
Implicit Types vs : list val.
Implicit Types vss : list (list val).

Record ws_deques `{zoo_G : !ZooG Σ} := {
  ws_deques_create : val ;
  ws_deques_size : val ;
  ws_deques_push : val ;
  ws_deques_pop : val ;
  ws_deques_steal_to : val ;

  ws_deques_inv : val → namespace → nat → iProp Σ ;
  ws_deques_model : val → list (list val) → iProp Σ ;
  ws_deques_owner : val → nat → iProp Σ ;

  #[global] ws_deques_model_timeless t vss ::
    Timeless (ws_deques_model t vss) ;
  #[global] ws_deques_owner_timeless t i ::
    Timeless (ws_deques_owner t i) ;
  #[global] ws_deques_inv_persistent t ι sz ::
    Persistent (ws_deques_inv t ι sz) ;

  ws_deques_owner_valid t ι sz i :
    ws_deques_inv t ι sz -∗
    ws_deques_owner t i -∗
    ⌜i < sz⌝ ;
  ws_deques_owner_exclusive t i :
    ws_deques_owner t i -∗
    ws_deques_owner t i -∗
    False ;

  ws_deques_create_spec ι sz :
    let sz' := Z.to_nat sz in
    (0 ≤ sz)%Z →
    {{{
      True
    }}}
      ws_deques_create #sz
    {{{ t,
      RET t;
      ws_deques_inv t ι sz' ∗
      ws_deques_model t (replicate sz' []) ∗
      [∗ list] i ∈ seq 0 sz',
        ws_deques_owner t i
    }}} ;

  ws_deques_size_spec t ι sz :
    {{{
      ws_deques_inv t ι sz
    }}}
      ws_deques_size t
    {{{
      RET #sz;
      True
    }}} ;

  ws_deques_push_spec t ι sz i i_ v :
    i = Z.of_nat i_ →
    <<<
      ws_deques_inv t ι sz ∗
      ws_deques_owner t i_
    | ∀∀ vss,
      ws_deques_model t vss
    >>>
      ws_deques_push t #i v @ ↑ι
    <<<
      ∃∃ vs,
      ⌜vss !! i_ = Some vs⌝ ∗
      ws_deques_model t (<[i_ := vs ++ [v]]> vss)
    | RET ();
      ws_deques_owner t i_
    >>> ;

  ws_deques_pop_spec t ι sz i i_ :
    i = Z.of_nat i_ →
    <<<
      ws_deques_inv t ι sz ∗
      ws_deques_owner t i_
    | ∀∀ vss,
      ws_deques_model t vss
    >>>
      ws_deques_pop t #i @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ⌜vss !! i_ = Some []⌝ ∗
          ws_deques_model t vss
      | Some v =>
          ∃ vs,
          ⌜vss !! i_ = Some (vs ++ [v])⌝ ∗
          ws_deques_model t (<[i_ := vs]> vss)
      end
    | RET o;
      ws_deques_owner t i_
    >>> ;

  ws_deques_steal_to_spec t ι (sz : nat) i i_ j :
    let j_ := Z.to_nat j in
    i = Z.of_nat i_ →
    (0 ≤ j < sz)%Z →
    <<<
      ws_deques_inv t ι sz ∗
      ws_deques_owner t i_
    | ∀∀ vss,
      ws_deques_model t vss
    >>>
      ws_deques_steal_to t #i #j @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ⌜vss !! j_ = Some []⌝ ∗
          ws_deques_model t vss
      | Some v =>
          ∃ vs,
          ⌜vss !! j_ = Some (v :: vs)⌝ ∗
          ws_deques_model t (<[j_ := vs]> vss)
      end
    | RET o;
      ws_deques_owner t i_
    >>> ;
}.
#[global] Arguments ws_deques _ {_} : assert.
#[global] Arguments Build_ws_deques {_ _ _ _ _ _ _ _ _ _ _ _ _} _ _ _ _ _ _ _ : assert.
#[global] Opaque ws_deques_create.
#[global] Opaque ws_deques_size.
#[global] Opaque ws_deques_push.
#[global] Opaque ws_deques_pop.
#[global] Opaque ws_deques_steal_to.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.
  Context (ws_deques : ws_deques Σ).

  #[local] Definition ws_deques_steal_as_aux : val :=
    rec: "ws_deques_steal_as_aux" "t" "sz" "i" "round" "n" =>
      if: "n" ≤ #0 then (
        §None
      ) else (
        let: "j" := ("i" + #1 + random_round_next "round") `rem` "sz" in
        match: ws_deques.(ws_deques_steal_to) "t" "i" "j" with
        | None =>
            "ws_deques_steal_as_aux" "t" "sz" "i" "round" ("n" - #1)
        |_ as "res" =>
            "res"
        end
      ).
  Definition ws_deques_steal_as : val :=
    fun: "t" "i" "round" =>
      let: "sz" := ws_deques.(ws_deques_size) "t" in
      ws_deques_steal_as_aux "t" "sz" "i" "round" ("sz" - #1).

  #[local] Lemma ws_deques_steal_as_aux_spec t ι (sz : nat) i i_ round (n : nat) :
    i = Z.of_nat i_ →
    <<<
      ws_deques.(ws_deques_inv) t ι sz ∗
      ws_deques.(ws_deques_owner) t i_ ∗
      random_round_model' round (sz - 1) n
    | ∀∀ vss,
      ws_deques.(ws_deques_model) t vss
    >>>
      ws_deques_steal_as_aux t #sz #i round #n @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_deques.(ws_deques_model) t vss
      | Some v =>
          ∃ j vs,
          ⌜Z.to_nat i ≠ j⌝ ∗
          ⌜vss !! j = Some (v :: vs)⌝ ∗
          ws_deques.(ws_deques_model) t (<[j := vs]> vss)
      end
    | RET o;
      ∃ n,
      ws_deques.(ws_deques_owner) t i_ ∗
      random_round_model' round (sz - 1) n
    >>>.
  Proof.
    iIntros (->) "!> %Φ (#Hinv & Howner & Hround) HΦ".
    iDestruct (ws_deques_owner_valid with "Hinv Howner") as %Hi.
    iLöb as "HLöb" forall (n).
    wp_rec. wp_pures.
    case_bool_decide as Hcase; wp_pures.
    - iMod "HΦ" as "(%vss & Hmodel & _ & HΦ)".
      iApply ("HΦ" $! None with "Hmodel [$Howner Hround]"); first iSteps.
    - wp_apply (random_round_next_spec' with "Hround") as (j) "(%Hj & Hround)"; first lia.
      wp_pures.
      rewrite Nat2Z.id.
      pose k := (i_ + 1 + j) `mod` sz.
      assert ((i_ + 1 + j) `rem` sz = k)%Z as ->.
      { rewrite Z.rem_mod_nonneg; lia. }
      awp_smart_apply (ws_deques_steal_to_spec with "[$Hinv $Howner]") without "Hround"; [done | lia |].
      iApply (aacc_aupd with "HΦ"); first done. iIntros "%vss Hmodel".
      iAaccIntro with "Hmodel"; first iSteps. iIntros ([ v |]).
      + rewrite Nat2Z.id.
        iSteps as (vs Hlookup) "Hmodel". iExists (Some v). iSteps. iExists k. iSteps. iPureIntro.
        clear Hlookup. rewrite {}/k.
        destruct (decide (i_ + 1 + j < sz)).
        * rewrite Nat.mod_small //. lia.
        * assert (i_ + 1 + j < sz * 2) as ?%Nat.div_lt_upper_bound by lia; last lia.
          assert ((i_ + 1 + j) `div` sz = 1) by lia.
          lia.
      + iSteps as (_) "HΦ Howner Hround".
        assert (n - 1 = (n - 1)%nat)%Z as -> by lia.
        iSteps.
  Qed.
  Lemma ws_deques_steal_as_spec t ι sz i i_ round :
    i = Z.of_nat i_ →
    0 < sz →
    <<<
      ws_deques.(ws_deques_inv) t ι sz ∗
      ws_deques.(ws_deques_owner) t i_ ∗
      random_round_model' round (sz - 1) (sz - 1)
    | ∀∀ vss,
      ws_deques.(ws_deques_model) t vss
    >>>
      ws_deques_steal_as t #i round @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_deques.(ws_deques_model) t vss
      | Some v =>
          ∃ j vs,
          ⌜Z.to_nat i ≠ j⌝ ∗
          ⌜vss !! j = Some (v :: vs)⌝ ∗
          ws_deques.(ws_deques_model) t (<[j := vs]> vss)
      end
    | RET o;
      ∃ n,
      ws_deques.(ws_deques_owner) t i_ ∗
      random_round_model' round (sz - 1) n
    >>>.
  Proof.
    iIntros (->) "%Hsz !> %Φ (#Hinv & Hround) HΦ".
    wp_rec.
    wp_smart_apply (ws_deques_size_spec with "Hinv") as "_".
    wp_pures.
    assert (sz - 1 = (sz - 1)%nat)%Z as -> by lia.
    wp_apply (ws_deques_steal_as_aux_spec with "[$Hinv $Hround] HΦ"); first done.
  Qed.
End zoo_G.

#[global] Opaque ws_deques_steal_as.
