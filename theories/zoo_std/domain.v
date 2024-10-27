From zoo Require Import
  prelude.
From zoo.language Require Import
  notations
  diaframe.
From zoo_std Require Export
  base.
From zoo_std Require Import
  spsc_future.
From zoo Require Import
  options.

Implicit Types v t fn : val.

Definition domain_spawn : val :=
  fun: "fn" =>
    let: "t" := spsc_future_create () in
    Fork (spsc_future_set "t" ("fn" ())) ;;
    "t".

Definition domain_join : val :=
  spsc_future_get.

Class DomainG Σ `{zoo_G : !ZooG Σ} := {
  #[local] domain_G_future_G :: SpscFutureG Σ ;
}.

Definition domain_Σ := #[
  spsc_future_Σ
].
#[global] Instance subG_domain_Σ Σ `{zoo_G : !ZooG Σ} :
  subG domain_Σ Σ →
  DomainG Σ.
Proof.
  solve_inG.
Qed.

Section domain_G.
  Context `{domain_G : DomainG Σ}.

  Definition domain_model t Ψ : iProp Σ :=
    spsc_future_inv t Ψ ∗
    spsc_future_consumer t.

  Lemma domain_spawn_spec Ψ fn :
    {{{
      WP fn () {{ Ψ }}
    }}}
      domain_spawn fn
    {{{ t,
      RET t;
      domain_model t Ψ
    }}}.
  Proof.
    iIntros "%Φ Hfn HΦ".
    wp_rec.
    wp_apply (spsc_future_create_spec with "[//]") as (fut) "(#Hfut_inv & Hfut_producer & Hfut_consumer)".
    wp_pures.
    wp_bind (Fork _). iApply (wp_fork with "[Hfn Hfut_producer]"); last iSteps.
    iModIntro.
    wp_apply (wp_wand with "Hfn") as (v) "HΨ".
    wp_apply (spsc_future_set_spec with "[$Hfut_inv $Hfut_producer $HΨ]").
    iSteps.
  Qed.

  Lemma domain_join_spec t Ψ :
    {{{
      domain_model t Ψ
    }}}
      domain_join t
    {{{ v,
      RET v;
      Ψ v
    }}}.
  Proof.
    apply spsc_future_get_spec.
  Qed.
End domain_G.

#[global] Opaque domain_spawn.
#[global] Opaque domain_join.

#[global] Opaque domain_model.
