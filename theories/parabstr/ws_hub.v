From zebre Require Import
  prelude.
From zebre.language Require Import
  notations
  diaframe.
From zebre.std Require Import
  opt.
From zebre.parabstr Require Export
  base.
From zebre Require Import
  options.

Implicit Types killed : bool.
Implicit Types v t : val.

Record ws_hub `{zebre_G : !ZebreG Σ} := {
  ws_hub_create : val ;
  ws_hub_push : val ;
  ws_hub_push_foreign : val ;
  ws_hub_pop : val ;
  ws_hub_try_steal : val ;
  ws_hub_steal : val ;
  ws_hub_killed : val ;
  ws_hub_kill : val ;

  ws_hub_inv : val → namespace → iProp Σ ;
  ws_hub_model : val → gmultiset val → iProp Σ ;
  ws_hub_owner : val → nat → iProp Σ ;

  #[global] ws_hub_model_timeless t vs ::
    Timeless (ws_hub_model t vs) ;
  #[global] ws_hub_inv_persistent t ι ::
    Persistent (ws_hub_inv t ι) ;

  ws_hub_owner_exclusive t i :
    ws_hub_owner t i -∗
    ws_hub_owner t i -∗
    False ;

  ws_hub_create_spec ι sz :
    (0 ≤ sz)%Z →
    {{{ True }}}
      ws_hub_create #sz
    {{{ t,
      RET t;
      ws_hub_inv t ι ∗
      ws_hub_model t ∅ ∗
      [∗ list] i ∈ seq 0 (Z.to_nat sz),
        ws_hub_owner t i
    }}} ;

  ws_hub_push_spec t ι i i_ v :
    i = Z.of_nat i_ →
    <<<
      ws_hub_inv t ι ∗
      ws_hub_owner t i_
    | ∀∀ vs,
      ws_hub_model t vs
    >>>
      ws_hub_push t #i v @ ↑ι
    <<<
      ws_hub_model t ({[+v+]} ⊎ vs)
    | RET ();
      ws_hub_owner t i_
    >>> ;

  ws_hub_push_foreign_spec t ι v :
    <<<
      ws_hub_inv t ι
    | ∀∀ vs,
      ws_hub_model t vs
    >>>
      ws_hub_push_foreign t v @ ↑ι
    <<<
      ws_hub_model t ({[+v+]} ⊎ vs)
    | RET (); True
    >>> ;

  ws_hub_pop_spec t ι i i_ :
    i = Z.of_nat i_ →
    <<<
      ws_hub_inv t ι ∗
      ws_hub_owner t i_
    | ∀∀ vs,
      ws_hub_model t vs
    >>>
      ws_hub_pop t #i @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_model t vs'
      end
    | RET o;
      ws_hub_owner t i_
    >>> ;

  ws_hub_try_steal_spec t ι i i_ max_round_noyield max_round_yield :
    i = Z.of_nat i_ →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub_inv t ι ∗
      ws_hub_owner t i_
    | ∀∀ vs,
      ws_hub_model t vs
    >>>
      ws_hub_try_steal t #i (#max_round_noyield, #max_round_yield)%V @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_model t vs'
      end
    | RET o;
      ws_hub_owner t i_
    >>> ;

  ws_hub_steal_spec t ι i i_ max_round_noyield max_round_yield :
    i = Z.of_nat i_ →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub_inv t ι ∗
      ws_hub_owner t i_
    | ∀∀ vs,
      ws_hub_model t vs
    >>>
      ws_hub_steal t #i (#max_round_noyield, #max_round_yield)%V @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_model t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_model t vs'
      end
    | RET o;
      ws_hub_owner t i_
    >>> ;

  ws_hub_killed_spec t ι :
    {{{
      ws_hub_inv t ι
    }}}
      ws_hub_killed t
    {{{ killed,
      RET #killed; True
    }}} ;

  ws_hub_kill_spec t ι:
    {{{
      ws_hub_inv t ι
    }}}
      ws_hub_kill t
    {{{
      RET (); True
    }}} ;
}.
#[global] Arguments ws_hub _ {_} : assert.
#[global] Arguments Build_ws_hub {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _} _ _ _ _ _ _ _ _ _ : assert.
#[global] Opaque ws_hub_create.
#[global] Opaque ws_hub_push.
#[global] Opaque ws_hub_push_foreign.
#[global] Opaque ws_hub_pop.
#[global] Opaque ws_hub_try_steal.
#[global] Opaque ws_hub_steal.
#[global] Opaque ws_hub_killed.
#[global] Opaque ws_hub_kill.

Section zebre_G.
  Context `{zebre_G : !ZebreG Σ}.
  Context (ws_hub : ws_hub Σ).

  Definition ws_hub_pop_try_steal : val :=
    λ: "t" "i" "max_round",
      match: ws_hub.(ws_hub_pop) "t" "i" with
      | Some <> as "res" =>
          "res"
      | None =>
          ws_hub.(ws_hub_try_steal) "t" "i" "max_round"
      end.

  Definition ws_hub_pop_steal : val :=
    λ: "t" "i" "max_round",
      match: ws_hub.(ws_hub_pop) "t" "i" with
      | Some <> as "res" =>
          "res"
      | None =>
          ws_hub.(ws_hub_steal) "t" "i" "max_round"
      end.

  Lemma ws_hub_pop_try_steal_spec t ι i i_ max_round_noyield max_round_yield :
    i = Z.of_nat i_ →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub.(ws_hub_inv) t ι ∗
      ws_hub.(ws_hub_owner) t i_
    | ∀∀ vs,
      ws_hub.(ws_hub_model) t vs
    >>>
      ws_hub_pop_try_steal t #i (#max_round_noyield, #max_round_yield)%V @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub.(ws_hub_model) t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub.(ws_hub_model) t vs'
      end
    | RET o;
      ws_hub.(ws_hub_owner) t i_
    >>>.
  Proof.
    iIntros (->) "%Hmax_round_noyield %Hmax_round_yield !> %Φ (#Hinv & Howner) HΦ".

    wp_rec.

    awp_smart_apply (ws_hub_pop_spec with "[$Hinv $Howner]"); [done.. |].
    iApply (aacc_aupd with "HΦ"); first done. iIntros "%vs Hmodel".
    iAaccIntro with "Hmodel"; first iSteps. iIntros ([v |]) "Hmodel !>".

    - iRight. iExists (Some v). iFrame.
      iIntros "HΦ !> Howner". clear.

      iSpecialize ("HΦ" with "Howner").
      iSteps.

    - iLeft. iFrame.
      iIntros "HΦ !> Howner". clear- Hmax_round_noyield Hmax_round_yield.

      wp_smart_apply (ws_hub_try_steal_spec with "[$Hinv $Howner] HΦ"); done.
  Qed.

  Lemma ws_hub_pop_steal_spec t ι i i_ max_round_noyield max_round_yield :
    i = Z.of_nat i_ →
    (0 ≤ max_round_noyield)%Z →
    (0 ≤ max_round_yield)%Z →
    <<<
      ws_hub.(ws_hub_inv) t ι ∗
      ws_hub.(ws_hub_owner) t i_
    | ∀∀ vs,
      ws_hub.(ws_hub_model) t vs
    >>>
      ws_hub_pop_steal t #i (#max_round_noyield, #max_round_yield)%V @ ↑ι
    <<<
      ∃∃ o,
      match o with
      | None =>
          ws_hub_model ws_hub t vs
      | Some v =>
          ∃ vs',
          ⌜vs = {[+v+]} ⊎ vs'⌝ ∗
          ws_hub_model ws_hub t vs'
      end
    | RET o;
      ws_hub_owner ws_hub t i_
    >>>.
  Proof.
    iIntros (->) "%Hmax_round_noyield %Hmax_round_yield !> %Φ (#Hinv & Howner) HΦ".

    wp_rec.

    awp_smart_apply (ws_hub_pop_spec with "[$Hinv $Howner]"); [done.. |].
    iApply (aacc_aupd with "HΦ"); first done. iIntros "%vs Hmodel".
    iAaccIntro with "Hmodel"; first iSteps. iIntros ([v |]) "Hmodel !>".

    - iDestruct "Hmodel" as "(%vs' & -> & Hmodel)".
      iRight. iExists (Some v). iStep.
      iIntros "HΦ !> Howner". clear.

      iSpecialize ("HΦ" with "Howner").
      iSteps.

    - iLeft. iFrame.
      iIntros "HΦ !> Howner". clear- Hmax_round_noyield Hmax_round_yield.

      wp_smart_apply (ws_hub_steal_spec with "[$Hinv $Howner] HΦ"); done.
  Qed.
End zebre_G.

#[global] Opaque ws_hub_pop_try_steal.
#[global] Opaque ws_hub_pop_steal.
