From zoo Require Import
  prelude.
From zoo.language Require Import
  notations
  diaframe.
From boxroot Require Export
  base.
From zoo Require Import
  options.

Implicit Types ofs : nat.
Implicit Types l root : location.
Implicit Types roots : list location.
Implicit Types fn iter : val.

Parameter gc_state : Type.
Implicit Types gc : gc_state.

Parameter gc_location : Type.
Implicit Types ω : gc_location.
Implicit Types ωs : list gc_location.

Parameter gc_location_inhabited : Inhabited gc_location.
#[global] Existing Instance gc_location_inhabited.

Parameter gc_val : Type.
Parameter GcInt : Z → gc_val.
Parameter GcLoc : gc_location → gc_val.
Parameter gc_val_to_val : gc_val → val.
Parameter gc_val_of_val : val → option gc_val.
Implicit Types ν : gc_val.
Implicit Types νs : list gc_val.

Parameter gc_model : ∀ `{zoo_G : !ZooG Σ}, gc_state → iProp Σ.
Parameter gc_pointsto : ∀ `{zoo_G : !ZooG Σ}, gc_location → list gc_val → iProp Σ.
Parameter gc_realized : gc_state → gc_location → location → Prop.
Definition gc_root `{zoo_G : !ZooG Σ} gc root ω : iProp Σ :=
  ∃ l,
  root ↦ #l ∗
  ⌜gc_realized gc ω l⌝.

Notation "ω '↦gc' νs" := (
  gc_pointsto ω νs
)(at level 20,
  format "ω  ↦gc  νs"
) : bi_scope.
Notation "ω '↦gc[' gc ] l" := (
  gc_realized gc ω l
)(at level 20,
  format "ω  ↦gc[ gc ]  l"
) : stdpp_scope.
Notation "root '↦root[' gc ] ω" := (
  gc_root gc root ω
)(at level 20,
  format "root  ↦root[ gc ]  ω"
) : bi_scope.

Axiom gc_realized_agree : ∀ gc ω l1 l2,
  ω ↦gc[gc] l1 →
  ω ↦gc[gc] l2 →
  l1 = l2.

Parameter wp_load_gc : ∀ `{zoo_G : !ZooG Σ} ν gc ω νs l i,
  (0 ≤ i)%Z →
  νs !! Z.to_nat i = Some ν →
  ω ↦gc[gc] l →
  {{{
    gc_model gc ∗
    ω ↦gc νs
  }}}
    Load #l #i
  {{{
    RET gc_val_to_val ν;
    gc_model gc ∗
    ω ↦gc νs
  }}}.

Parameter wp_store_gc : ∀ `{zoo_G : !ZooG Σ} ν gc ω νs l i v,
  (0 ≤ i < length νs)%Z →
  gc_val_of_val v = Some ν →
  ω ↦gc[gc] l →
  {{{
    gc_model gc ∗
    ω ↦gc νs
  }}}
    Store #l #i v
  {{{
    RET gc_val_to_val ν;
    gc_model gc ∗
    ω ↦gc <[Z.to_nat i := ν]> νs
  }}}.

Lemma wp_load_gc_root `{zoo_G : !ZooG Σ} gc root ω root_base root_ofs :
  root = root_base +ₗ root_ofs →
  {{{
    root ↦root[gc] ω
  }}}
    Load #root_base #root_ofs
  {{{ l,
    RET #l;
    ⌜ω ↦gc[gc] l⌝ ∗
    root ↦root[gc] ω
  }}}.
Proof.
  iSteps.
Qed.
Lemma wp_load_gc_root' `{zoo_G : !ZooG Σ} {gc root ω} l root_base root_ofs :
  root = root_base +ₗ root_ofs →
  ω ↦gc[gc] l →
  {{{
    root ↦root[gc] ω
  }}}
    Load #root_base #root_ofs
  {{{
    RET #l;
    root ↦root[gc] ω
  }}}.
Proof.
  iIntros (->) "%Hω %Φ (%_l & Hroot & %_Hω) HΦ".
  opose proof* (gc_realized_agree _ _ l _l) as <-; [done.. |].
  iSteps.
Qed.

Lemma wp_store_gc_root `{zoo_G : !ZooG Σ} {gc root ω'} ω l root_base root_ofs :
  root = root_base +ₗ root_ofs →
  ω ↦gc[gc] l →
  {{{
    root ↦root[gc] ω'
  }}}
    Store #root_base #root_ofs #l
  {{{
    RET ();
    root ↦root[gc] ω
  }}}.
Proof.
  iSteps.
Qed.

Parameter gc_roots : ∀ `{zoo_G : !ZooG Σ}, (gc_state → iProp Σ) → iProp Σ.
Parameter gc_set_roots : val.
Axiom gc_set_roots_spec : ∀ `{zoo_G : !ZooG Σ} {gc Χ' iter} Χ Ξ ofs,
  {{{
    gc_model gc ∗
    gc_roots Χ' ∗
    □ (
      ∀ gc,
      Χ gc ∗-∗
        ∃ roots ωs,
        Ξ roots ωs ∗
        ( [∗ list] root; ω ∈ roots; ωs,
          (root +ₗ ofs) ↦root[gc] ω
        )
    ) ∗
    □ (
      ∀ Ψ roots ωs fn,
      {{{
        ▷ Ψ [] ∗
        Ξ roots ωs ∗
        □ (
          ∀ roots_done root roots_todo,
          ⌜roots = roots_done ++ root :: roots_todo⌝ -∗
          Ψ roots_done -∗
          WP fn #root {{ res,
            ⌜res = ()%V⌝ ∗
            ▷ Ψ (roots_done ++ [root])
          }}
        )
      }}}
        iter fn
      {{{
        RET ();
        Ξ roots ωs ∗
        Ψ roots
      }}}
    )
  }}}
    gc_set_roots iter #ofs
  {{{
    RET ();
    gc_model gc ∗
    gc_roots Χ
  }}}.

Parameter gc_alloc : val.
Axiom gc_alloc_spec : ∀ `{zoo_G : !ZooG Σ} gc Χ n,
  (0 < n)%Z →
  {{{
    gc_model gc ∗
    gc_roots Χ ∗
    Χ gc
  }}}
    gc_alloc #n
  {{{ l gc ω,
    RET #l;
    ⌜ω ↦gc[gc] l⌝ ∗
    gc_model gc ∗
    gc_roots Χ ∗
    Χ gc ∗
    ω ↦gc replicate (Z.to_nat n) (GcInt 0)
  }}}.
