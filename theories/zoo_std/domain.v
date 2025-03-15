From zoo Require Import
  prelude.
From zoo.language Require Import
  notations.
From zoo.diaframe Require Import
  diaframe.
From zoo_std Require Export
  base
  domain__code.
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
    wp_smart_apply (wp_fork with "[Hfn Hfut_producer]"); last iSteps. iIntros "!> %tid %v _".
    iApply wp_thread_id_mono.
    wp_apply (wp_wand with "Hfn") as (res) "HΨ".
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

Axiom domain_yield_spec : ∀ `{zoo_G : !ZooG Σ} Φ,
  ▷ Φ ()%V ⊢
  WP domain_yield () {{ Φ }}.

Axiom domain_self_index_spec : ∀ `{zoo_G : !ZooG Σ} Φ,
  (∀ (i : nat), ▷ Φ #i) ⊢
  WP domain_self_index () {{ Φ }}.

Axiom domain_recommended_domain_count_spec : ∀ `{zoo_G : !ZooG Σ} Φ,
  (∀ (i : nat), ▷ Φ #i) ⊢
  WP domain_recommended_domain_count () {{ Φ }}.

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  #[global] Instance domain_yield_diaspec :
    DIASPEC
    {{
      True
    }}
      domain_yield ()%V
    {{
      RET ();
      True
    }}.
  Proof.
    iSteps.
    wp_apply domain_yield_spec.
    iSteps.
  Qed.

  #[global] Instance domain_self_index_diaspec :
    DIASPEC
    {{
      True
    }}
      domain_self_index ()%V
    {{ (i : nat),
      RET #i;
      True
    }}.
  Proof.
    iSteps.
    wp_apply domain_self_index_spec.
    iSteps.
  Qed.

  #[global] Instance domain_recommended_domain_count_diaspec :
    DIASPEC
    {{
      True
    }}
      domain_recommended_domain_count ()%V
    {{ (i : nat),
      RET #i;
      True
    }}.
  Proof.
    iSteps.
    wp_apply domain_recommended_domain_count_spec.
    iSteps.
  Qed.
End zoo_G.

#[global] Opaque domain_spawn.
#[global] Opaque domain_join.

#[global] Opaque domain_model.
