From zebre Require Import
  prelude.
From zebre.language Require Import
  notations
  diaframe.
From zebre.boxroot Require Export
  base.
From zebre Require Import
  options.

Implicit Types l root : loc.
Implicit Types roots : list loc.
Implicit Types fn iter : val.

Parameter gc_state : Type.
Implicit Types gc : gc_state.

Parameter gc_loc : Type.
Implicit Types ω : gc_loc.
Implicit Types ωs : list gc_loc.

Parameter gc_val : Type.
Parameter GcInt : Z → gc_val.
Parameter GcLoc : gc_loc → gc_val.
Parameter gc_val_to_val : gc_val → val.
Parameter gc_val_of_val : val → option gc_val.
Implicit Types ν : gc_val.
Implicit Types νs : list gc_val.

Parameter gc_model : ∀ `{zebre_G : !ZebreG Σ}, gc_state → iProp Σ.
Parameter gc_pointsto : ∀ `{zebre_G : !ZebreG Σ}, gc_loc → list gc_val → iProp Σ.
Parameter gc_realized : gc_state → gc_loc → loc → Prop.
Parameter gc_root : ∀ `{zebre_G : !ZebreG Σ}, loc → gc_loc → iProp Σ.
Definition gc_maybe_root `{zebre_G : !ZebreG Σ} gc root ω : iProp Σ :=
    gc_root root ω
  ∨ ∃ l,
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
Notation "root '↦root' ω" := (
  gc_root root ω
)(at level 20,
  format "root  ↦root  ω"
) : bi_scope.
Notation "root '↦root[' gc ] ω" := (
  gc_maybe_root gc root ω
)(at level 20,
  format "root  ↦root[ gc ]  ω"
) : bi_scope.

Parameter gc_alloc : val.
Axiom gc_alloc_spec : ∀ `{zebre_G : !ZebreG Σ} gc n,
  (0 < n)%Z →
  {{{
    gc_model gc
  }}}
    gc_alloc #n
  {{{ l gc ω,
    RET #l;
    ⌜ω ↦gc[gc] l⌝ ∗
    gc_model gc ∗
    ω ↦gc replicate (Z.to_nat n) (GcInt 0)
  }}}.

Parameter wp_load_gc : ∀ `{zebre_G : !ZebreG Σ} ν gc ω νs l i,
  (0 ≤ i)%Z →
  νs !! Z.to_nat i = Some ν →
  ω ↦gc[gc] l →
  {{{
    gc_model gc ∗
    ω ↦gc νs
  }}}
   !#(l +ₗ i)
  {{{
    RET gc_val_to_val ν;
    gc_model gc ∗
    ω ↦gc νs
  }}}.

Parameter wp_store_gc : ∀ `{zebre_G : !ZebreG Σ} ν gc ω νs l i v,
  (0 ≤ Z.to_nat i < length νs)%Z →
  gc_val_of_val v = Some ν →
  ω ↦gc[gc] l →
  {{{
    gc_model gc ∗
    ω ↦gc νs
  }}}
    #(l +ₗ i) <- v
  {{{
    RET gc_val_to_val ν;
    gc_model gc ∗
    ω ↦gc <[Z.to_nat i := ν]> νs
  }}}.

Axiom wp_load_gc_root : ∀ `{zebre_G : !ZebreG Σ} gc root ω,
  {{{
    gc_model gc ∗
    root ↦root ω
  }}}
    !#root
  {{{ l,
    RET #l;
    ⌜ω ↦gc[gc] l⌝ ∗
    gc_model gc ∗
    root ↦root ω
  }}}.

Parameter gc_roots : ∀ `{zebre_G : !ZebreG Σ}, val → (list loc → iProp Σ) → iProp Σ.
Parameter gc_set_roots : val.
Axiom gc_set_roots_spec : ∀ `{zebre_G : !ZebreG Σ} iter (Χ : list loc → iProp Σ),
  {{{
    ∀ Ψ gc roots ωs fn,
    {{{
      ▷ Ψ [] ∗
      Χ roots ∗
      ( [∗ list] root; ω ∈ roots; ωs,
        root ↦root[gc] ω
      ) ∗
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
      Χ roots ∗
      Ψ roots
    }}}
  }}}
    gc_set_roots iter
  {{{
    RET ();
    gc_roots iter Χ
  }}}.
