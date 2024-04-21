From zebre Require Import
  prelude.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Import
  opt
  random_round.
From zebre.parabstr Require Export
  base.
From zebre Require Import
  options.

Implicit Types v t round : val.
Implicit Types vs : list val.
Implicit Types vss : list (list val).

Record ws_deques `{zebre_G : !ZebreG Σ} := {
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
    {{{ True }}}
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
      RET #sz; True
    }}} ;

  ws_deques_push_spec t ι sz i v :
    let i' := Z.to_nat i in
    (0 ≤ i)%Z →
    <<<
      ws_deques_inv t ι sz ∗
      ws_deques_owner t i'
    | ∀∀ vss,
      ws_deques_model t vss
    >>>
      ws_deques_push t #i v @ ↑ι
    <<<
      ∃∃ vs,
      ⌜vss !! i' = Some vs⌝ ∗
      ws_deques_model t (<[i' := vs ++ [v]]> vss)
    | RET ();
      ws_deques_owner t i'
    >>> ;

  ws_deques_pop_spec t ι sz i :
    let i' := Z.to_nat i in
    (0 ≤ i)%Z →
    <<<
      ws_deques_inv t ι sz ∗
      ws_deques_owner t i'
    | ∀∀ vss,
      ws_deques_model t vss
    >>>
      ws_deques_pop t #i @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ⌜vss !! i' = Some []⌝ ∗
          ws_deques_model t vss
      | Some v =>
          ∃ vs,
          ⌜vss !! i' = Some (vs ++ [v])⌝ ∗
          ws_deques_model t (<[i' := vs]> vss)
      end
    | RET o;
      ws_deques_owner t i'
    >>> ;

  ws_deques_steal_to_spec t ι (sz : nat) i :
    let i' := Z.to_nat i in
    (0 ≤ i < sz)%Z →
    <<<
      ws_deques_inv t ι sz
    | ∀∀ vss,
      ws_deques_model t vss
    >>>
      ws_deques_steal_to t #i @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ⌜vss !! i' = Some []⌝ ∗
          ws_deques_model t vss
      | Some v =>
          ∃ vs,
          ⌜vss !! i' = Some (v :: vs)⌝ ∗
          ws_deques_model t (<[i' := vs]> vss)
      end
    | RET o; True
    >>> ;
}.
#[global] Arguments ws_deques _ {_} : assert.
#[global] Arguments Build_ws_deques {_ _ _ _ _ _ _ _ _ _ _ _ _} _ _ _ _ _ _ _ : assert.
#[global] Opaque ws_deques_create.
#[global] Opaque ws_deques_size.
#[global] Opaque ws_deques_push.
#[global] Opaque ws_deques_pop.
#[global] Opaque ws_deques_steal_to.

Section zebre_G.
  Context `{zebre_G : !ZebreG Σ}.
  Context (ws_deques : ws_deques Σ).

  #[local] Definition ws_deques_steal_as_round_aux : val :=
    rec: "ws_deques_steal_as_round_aux" "t" "sz" "i" "round" "n" :=
      if: "n" ≤ #0 then (
        §None
      ) else (
        let: "j" := ("i" + #1 + random_round_next "round") `rem` "sz" in
        match: ws_deques.(ws_deques_steal_to) "t" "j" with
        | None =>
            "ws_deques_steal_as_round_aux" "t" "sz" "i" "round" ("n" - #1)
        |_ as "res" =>
            "res"
        end
      ).
  #[local] Definition ws_deques_steal_as_round : val :=
    λ: "t" "sz" "i" "round",
      ws_deques_steal_as_round_aux "t" "sz" "i" "round" ("sz" - #1).

  #[local] Definition ws_deques_try_steal_as_aux : val :=
    rec: "ws_deques_try_steal_as_aux" "t" "sz" "i" "round" "n" :=
      if: "n" ≤ #0 then (
        §None
      ) else (
        match: ws_deques_steal_as_round "t" "sz" "i" "round" with
        | Some <> as "res" =>
            "res"
        | None =>
            Yield ;;
            random_round_reset "round" ;;
            "ws_deques_try_steal_as_aux" "t" "sz" "i" "round" ("n" - #1)
        end
      ).
  Definition ws_deques_try_steal_as : val :=
    λ: "t" "i" "max_round",
      let: "sz" := ws_deques.(ws_deques_size) "t" in
      let: "round" := random_round_create ("sz" - #1) in
      ws_deques_try_steal_as_aux "t" "sz" "i" "round" "max_round".

  #[local] Definition ws_deques_steal_as_aux : val :=
    rec: "ws_deques_steal_as_aux" "t" "sz" "i" "round" :=
      match: ws_deques_steal_as_round "t" "sz" "i" "round" with
      | Some "v" =>
          "v"
      | None =>
          Yield ;;
          random_round_reset "round" ;;
          "ws_deques_steal_as_aux" "t" "sz" "i" "round"
      end.
  Definition ws_deques_steal_as : val :=
    λ: "t" "i",
      let: "sz" := ws_deques.(ws_deques_size) "t" in
      let: "round" := random_round_create ("sz" - #1) in
      ws_deques_steal_as_aux "t" "sz" "i" "round".

  Definition ws_deques_pop_try_steal : val :=
    λ: "t" "i" "max_round",
      match: ws_deques.(ws_deques_pop) "t" "i" with
      | Some <> as "res" =>
          "res"
      | None =>
          ws_deques_try_steal_as "t" "i" "max_round"
      end.

  Definition ws_deques_pop_steal : val :=
    λ: "t" "i",
      match: ws_deques.(ws_deques_pop) "t" "i" with
      | Some "v" =>
          "v"
      | None =>
          ws_deques_steal_as "t" "i"
      end.

  #[local] Lemma ws_deques_steal_as_round_aux_spec t ι (sz : nat) i round (n : nat) :
    (0 ≤ i < sz)%Z →
    <<<
      ws_deques.(ws_deques_inv) t ι sz ∗
      random_round_model' round (sz - 1) n
    | ∀∀ vss,
      ws_deques.(ws_deques_model) t vss
    >>>
      ws_deques_steal_as_round_aux t #sz #i round #n @ ↑ι
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
      ∃ n',
      random_round_model' round (sz - 1) n'
    >>>.
  Proof.
    iIntros "%Hi !> %Φ (#Ht_inv & Hround) HΦ".
    iLöb as "HLöb" forall (n).
    wp_rec. wp_pures.
    case_bool_decide as Hcase; wp_pures.
    - iMod "HΦ" as "(%vss & Ht_model & _ & HΦ)".
      iApply ("HΦ" $! None with "Ht_model [Hround]"); first iSteps.
    - wp_apply (random_round_next_spec' with "Hround") as (j) "(%Hj & Hround)"; first lia.
      wp_pures.
      Z_to_nat i. rewrite Nat2Z.id.
      pose k := (i + 1 + j) `mod` sz.
      assert ((i + 1 + j) `rem` sz = k)%Z as ->.
      { rewrite Z.rem_mod_nonneg; lia. }
      awp_smart_apply (ws_deques_steal_to_spec with "Ht_inv") without "Hround"; first lia.
      iApply (aacc_aupd with "HΦ"); first done. iIntros "%vss Ht_model".
      iAaccIntro with "Ht_model"; first iSteps. iIntros ([ v |]).
      + rewrite Nat2Z.id.
        iSteps as (vs Hlookup) "Ht_model". iExists (Some v). iSteps. iExists k. iSteps. iPureIntro.
        clear Hlookup. rewrite {}/k.
        destruct (decide (i + 1 + j < sz)).
        * rewrite Nat.mod_small //. lia.
        * assert (i + 1 + j < sz * 2) as ?%Nat.div_lt_upper_bound by lia; last lia.
          assert ((i + 1 + j) `div` sz = 1) by lia.
          lia.
      + iSteps as (_) "HΦ Hround".
        assert (n - 1 = (n - 1)%nat)%Z as -> by lia.
        wp_apply ("HLöb" with "Hround HΦ").
  Qed.
  #[local] Lemma ws_deques_steal_as_round_spec t ι (sz : nat) i round :
    (0 ≤ i < sz)%Z →
    <<<
      ws_deques.(ws_deques_inv) t ι sz ∗
      random_round_model' round (sz - 1) (sz - 1)
    | ∀∀ vss,
      ws_deques.(ws_deques_model) t vss
    >>>
      ws_deques_steal_as_round t #sz #i round @ ↑ι
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
      ∃ n',
      random_round_model' round (sz - 1) n'
    >>>.
  Proof.
    iIntros "%Hi !> %Φ (#Ht_inv & Hround) HΦ".
    wp_rec. wp_pures.
    assert (sz - 1 = (sz - 1)%nat)%Z as -> by lia.
    wp_apply (ws_deques_steal_as_round_aux_spec with "[$Ht_inv $Hround] HΦ"); first done.
  Qed.

  #[local] Lemma ws_deques_try_steal_as_aux_spec t ι (sz : nat) i round n :
    (0 ≤ i < sz)%Z →
    (0 ≤ n)%Z →
    <<<
      ws_deques.(ws_deques_inv) t ι sz ∗
      random_round_model' round (sz - 1) (sz - 1)
    | ∀∀ vss,
      ws_deques.(ws_deques_model) t vss
    >>>
      ws_deques_try_steal_as_aux t #sz #i round #n @ ↑ι
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
      ∃ n',
      random_round_model' round (sz - 1) n'
    >>>.
  Proof.
    iIntros "%Hi %Hn !> %Φ (#Ht_inv & Hround) HΦ".
    iLöb as "HLöb" forall (n Hn).
    wp_rec. wp_pures.
    case_bool_decide as Hcase; wp_pures.
    - iMod "HΦ" as "(%vss & Ht_model & _ & HΦ)".
      iApply ("HΦ" $! None with "Ht_model [Hround]"); first iSteps.
    - awp_apply (ws_deques_steal_as_round_spec with "[$Ht_inv $Hround]"); first done.
      iApply (aacc_aupd with "HΦ"); first done. iIntros "%vss Ht_model".
      iAaccIntro with "Ht_model"; first iSteps. iIntros ([v |]).
      + iSteps as (j vs Hj Hlookup) "Ht_model". iExists (Some v). iSteps.
      + iSteps as (?) "HΦ Hround". iModIntro.
        wp_smart_apply (random_round_reset_spec' with "Hround") as "Hround".
        iSteps.
  Qed.
  Lemma ws_deques_try_steal_as_spec t ι (sz : nat) i max_round :
    (0 ≤ i < sz)%Z →
    (0 ≤ max_round)%Z →
    <<<
      ws_deques.(ws_deques_inv) t ι sz
    | ∀∀ vss,
      ws_deques.(ws_deques_model) t vss
    >>>
      ws_deques_try_steal_as t #i #max_round @ ↑ι
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
    | RET o; True
    >>>.
  Proof.
    iIntros "%Hi %Hmax_round !> %Φ #Ht_inv HΦ".
    wp_rec.
    wp_smart_apply (ws_deques_size_spec with "Ht_inv") as "_".
    wp_smart_apply (random_round_create_spec' with "[//]") as (round) "Hround"; first lia.
    wp_pures.
    assert (Z.to_nat (sz - 1) = sz - 1) as -> by lia.
    wp_apply (ws_deques_try_steal_as_aux_spec with "[$Ht_inv $Hround]"); [done.. |].
    iApply (atomic_update_mono with "[] HΦ").
    iSteps.
  Qed.

  #[local] Lemma ws_deques_steal_as_aux_spec t ι (sz : nat) i round :
    (0 ≤ i < sz)%Z →
    <<<
      ws_deques.(ws_deques_inv) t ι sz ∗
      random_round_model' round (sz - 1) (sz - 1)
    | ∀∀ vss,
      ws_deques.(ws_deques_model) t vss
    >>>
      ws_deques_steal_as_aux t #sz #i round @ ↑ι
    <<<
      ∃∃ j v vs,
      ⌜Z.to_nat i ≠ j⌝ ∗
      ⌜vss !! j = Some (v :: vs)⌝ ∗
      ws_deques.(ws_deques_model) t (<[j := vs]> vss)
    | RET v;
      ∃ n',
      random_round_model' round (sz - 1) n'
    >>>.
  Proof.
    iIntros "%Hi !> %Φ (#Ht_inv & Hround) HΦ".
    iLöb as "HLöb".
    wp_rec. wp_pures.
    awp_apply (ws_deques_steal_as_round_spec with "[$Ht_inv $Hround]"); first done.
    iApply (aacc_aupd with "HΦ"); first done. iIntros "%vss Ht_model".
    iAaccIntro with "Ht_model"; first iSteps. iIntros ([v |]); first iSteps.
    iSteps as (?) "HΦ Hround". iModIntro.
    wp_smart_apply (random_round_reset_spec' with "Hround") as "Hround".
    iSteps.
  Qed.
  Lemma ws_deques_steal_as_spec t ι (sz : nat) i :
    (0 ≤ i < sz)%Z →
    <<<
      ws_deques.(ws_deques_inv) t ι sz
    | ∀∀ vss,
      ws_deques.(ws_deques_model) t vss
    >>>
      ws_deques_steal_as t #i @ ↑ι
    <<<
      ∃∃ j v vs,
      ⌜Z.to_nat i ≠ j⌝ ∗
      ⌜vss !! j = Some (v :: vs)⌝ ∗
      ws_deques.(ws_deques_model) t (<[j := vs]> vss)
    | RET v; True
    >>>.
  Proof.
    iIntros "%Hi !> %Φ #Ht_inv HΦ".
    wp_rec.
    wp_smart_apply (ws_deques_size_spec with "Ht_inv") as "_".
    wp_smart_apply (random_round_create_spec' with "[//]") as (round) "Hround"; first lia.
    wp_pures.
    assert (Z.to_nat (sz - 1) = sz - 1) as -> by lia.
    wp_apply (ws_deques_steal_as_aux_spec with "[$Ht_inv $Hround]"); [done.. |].
    iApply (atomic_update_mono with "[] HΦ").
    iSteps.
  Qed.

  Lemma ws_deques_pop_try_steal_spec t ι (sz : nat) i max_round :
    let i' := Z.to_nat i in
    (0 ≤ i < sz)%Z →
    (0 ≤ max_round)%Z →
    <<<
      ws_deques.(ws_deques_inv) t ι sz ∗
      ws_deques.(ws_deques_owner) t i'
    | ∀∀ vss,
      ws_deques.(ws_deques_model) t vss
    >>>
      ws_deques_pop_try_steal t #i #max_round @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_deques.(ws_deques_model) t vss
      | Some v =>
          ∃ vs,
            ⌜vss !! i' = Some (vs ++ [v])⌝ ∗
            ws_deques.(ws_deques_model) t (<[i' := vs]> vss)
          ∨ ∃ j,
            ⌜Z.to_nat i ≠ j⌝ ∗
            ⌜vss !! j = Some (v :: vs)⌝ ∗
            ws_deques.(ws_deques_model) t (<[j := vs]> vss)
      end
    | RET o;
      ws_deques.(ws_deques_owner) t i'
    >>>.
  Proof.
    iIntros "%i' %Hi %Hmax_round !> %Φ (#Ht_inv & Ht_owner) HΦ".
    wp_rec.
    awp_smart_apply (ws_deques_pop_spec with "[$Ht_inv $Ht_owner]"); first lia.
    iApply (aacc_aupd with "HΦ"); first done. iIntros "%vss Ht_model".
    iAaccIntro with "Ht_model"; first iSteps. iIntros ([v |]).
    - iSteps as (vs Hlookup) "Ht_model". iExists (Some v). iSteps.
    - iStep 6 as (_) "HΦ Ht_owner". iModIntro.
      awp_apply (ws_deques_try_steal_as_spec with "Ht_inv"); [done.. |].
      iApply (aacc_aupd_commit with "HΦ"); first done. clear vss. iIntros "%vss Ht_model".
      iAaccIntro with "Ht_model"; first iSteps. iIntros ([ v |]); iSteps.
      + iExists (Some v). iSteps.
      + iExists None. iSteps.
  Qed.

  Lemma ws_deques_pop_steal_spec t ι (sz : nat) i :
    let i' := Z.to_nat i in
    (0 ≤ i < sz)%Z →
    <<<
      ws_deques.(ws_deques_inv) t ι sz ∗
      ws_deques.(ws_deques_owner) t i'
    | ∀∀ vss,
      ws_deques.(ws_deques_model) t vss
    >>>
      ws_deques_pop_steal t #i @ ↑ι
    <<<
      ∃∃ vs v,
        ⌜vss !! i' = Some (vs ++ [v])⌝ ∗
        ws_deques.(ws_deques_model) t (<[i' := vs]> vss)
      ∨ ∃ j,
        ⌜Z.to_nat i ≠ j⌝ ∗
        ⌜vss !! j = Some (v :: vs)⌝ ∗
        ws_deques.(ws_deques_model) t (<[j := vs]> vss)
    | RET v;
      ws_deques.(ws_deques_owner) t i'
    >>>.
  Proof.
    iIntros "%i' %Hi !> %Φ (#Ht_inv & Ht_owner) HΦ".
    wp_rec.
    awp_smart_apply (ws_deques_pop_spec with "[$Ht_inv $Ht_owner]"); first lia.
    iApply (aacc_aupd with "HΦ"); first done. iIntros "%vss Ht_model".
    iAaccIntro with "Ht_model"; first iSteps. iIntros ([v |]); first iSteps.
    iStep 6 as (_) "HΦ Ht_owner". iModIntro.
    awp_apply (ws_deques_steal_as_spec with "Ht_inv"); first done.
    iApply (aacc_aupd_commit with "HΦ"); first done. clear vss. iIntros "%vss Ht_model".
    iAaccIntro with "Ht_model"; iSteps.
  Qed.
End zebre_G.

#[global] Opaque ws_deques_try_steal_as.
#[global] Opaque ws_deques_steal_as.
#[global] Opaque ws_deques_pop_try_steal.
#[global] Opaque ws_deques_pop_steal.
