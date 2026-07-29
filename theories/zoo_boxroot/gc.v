Require Import zoo.prelude.
Require Import zoo.base.
Require Import zoo.options.

Implicit Type ofs : nat.
Implicit Type l root : location.
Implicit Type roots : list location.
Implicit Type fn iter : val.

Parameter gc۰state : Type.
Implicit Type gc : gc۰state.

Parameter gc۰location : Type.
Implicit Type ω : gc۰location.
Implicit Type ωs : list gc۰location.

Parameter gc۰locationｰinhabited : Inhabited gc۰location.
#[global] Existing Instance gc۰locationｰinhabited.

Parameter gc۰val : Type.
Parameter GcInt : Z → gc۰val.
Parameter GcLoc : gc۰location → gc۰val.
Parameter gc۰val۰to_val : gc۰val → val.
Parameter gc۰val۰of_val : val → option gc۰val.
Implicit Type ν : gc۰val.
Implicit Type νs : list gc۰val.

Parameter gc۰model : ∀ `{zoo۰G : !ZooG Σ}, gc۰state → iProp Σ.
Parameter gc۰pointsto : ∀ `{zoo۰G : !ZooG Σ}, gc۰location → list gc۰val → iProp Σ.
Parameter gc۰realized : gc۰state → gc۰location → location → Prop.
Definition gc۰root `{zoo۰G : !ZooG Σ} gc root ω : iProp Σ :=
  ∃ l,
  root ↦ #l ∗
  ⌜gc۰realized gc ω l⌝.

Notation "ω '↦gc' νs" := (
  gc۰pointsto ω νs
)(at level 20,
  format "ω  ↦gc  νs"
) : bi_scope.
Notation "ω '↦gc[' gc ] l" := (
  gc۰realized gc ω l
)(at level 20,
  format "ω  ↦gc[ gc ]  l"
) : stdpp_scope.
Notation "root '↦root[' gc ] ω" := (
  gc۰root gc root ω
)(at level 20,
  format "root  ↦root[ gc ]  ω"
) : bi_scope.

Axiom gc۰realizedｰagree : ∀ gc ω l1 l2,
  ω ↦gc[gc] l1 →
  ω ↦gc[gc] l2 →
  l1 = l2.

Parameter gcｰwpｰload : ∀ `{zoo۰G : !ZooG Σ} ν gc ω νs l i,
  (0 ≤ i)%Z →
  νs !! ₊i = Some ν →
  ω ↦gc[gc] l →
  {{{
    gc۰model gc ∗
    ω ↦gc νs
  }}}
    Load #l #i
  {{{
    RET gc۰val۰to_val ν;
    gc۰model gc ∗
    ω ↦gc νs
  }}}.

Parameter gcｰwpｰstore : ∀ `{zoo۰G : !ZooG Σ} ν gc ω νs l i v,
  (0 ≤ i < length νs)%Z →
  gc۰val۰of_val v = Some ν →
  ω ↦gc[gc] l →
  {{{
    gc۰model gc ∗
    ω ↦gc νs
  }}}
    Store #l #i v
  {{{
    RET gc۰val۰to_val ν;
    gc۰model gc ∗
    ω ↦gc <[₊i := ν]> νs
  }}}.

Lemma gcｰwpｰloadｰroot `{zoo۰G : !ZooG Σ} gc root ω root_base root_ofs :
  root = root_base +ₗ root_ofs →
  {{{
    root ↦root[gc] ω
  }}}
    Load #root_base #root_ofs
  {{{
    l
  , RET #l;
    ⌜ω ↦gc[gc] l⌝ ∗
    root ↦root[gc] ω
  }}}.
Proof.
  iSteps.
Qed.
Lemma gcｰwpｰloadｰroot' `{zoo۰G : !ZooG Σ} {gc root ω} l root_base root_ofs :
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
  opose proof* (gc۰realizedｰagree _ _ l _l) as <-; [done.. |].
  iSteps.
Qed.

Lemma gcｰwpｰstoreｰroot `{zoo۰G : !ZooG Σ} {gc root ω'} ω l root_base root_ofs :
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

Parameter gc۰roots : ∀ `{zoo۰G : !ZooG Σ}, (gc۰state → iProp Σ) → iProp Σ.
Parameter gc٠set_roots : val.
Axiom gc٠set_rootsｰspec : ∀ `{zoo۰G : !ZooG Σ} {gc Χ' iter} Χ Ξ ofs,
  {{{
    gc۰model gc ∗
    gc۰roots Χ' ∗
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
    gc٠set_roots iter #ofs
  {{{
    RET ();
    gc۰model gc ∗
    gc۰roots Χ
  }}}.

Parameter gc٠alloc : val.
Axiom gc٠allocｰspec : ∀ `{zoo۰G : !ZooG Σ} gc Χ n,
  (0 < n)%Z →
  {{{
    gc۰model gc ∗
    gc۰roots Χ ∗
    Χ gc
  }}}
    gc٠alloc #n
  {{{
    l gc ω
  , RET #l;
    ⌜ω ↦gc[gc] l⌝ ∗
    gc۰model gc ∗
    gc۰roots Χ ∗
    Χ gc ∗
    ω ↦gc replicate ₊n (GcInt 0)
  }}}.
