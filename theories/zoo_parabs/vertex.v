Require Import zoo.prelude.
Require Import zoo.common.countable.
Require Import zoo.common.gmultiset.
Require Import zoo.iris.bi.big_op.
Require Import zoo.iris.base_logic.lib.auth_gmultiset.
Require Import zoo.iris.base_logic.lib.mono_gmultiset.
Require Import zoo.iris.base_logic.lib.subprops.
Require Import zoo.iris.base_logic.lib.twins.
Require Import zoo.base.
Require Import zoo_std.clist.
Require Import zoo_std.option.
Require Import zoo_saturn.mpmc_stack_2.
Require Export zoo_parabs.base.
Require Export zoo_parabs.vertex__code.
Require Import zoo_parabs.vertex__types.
Require Import zoo_parabs.pool.
Require Import zoo.options.

Implicit Types b finished : bool.
Implicit Types preds : nat.
Implicit Types succ : location.
Implicit Types task ctx : val.
Implicit Types own : ownership.

Variant state :=
  | Init
  | Released
  | Ready
  | Finished.
Implicit Types state : state.

#[local] Instance state𑁒inhabited : Inhabited state :=
  populate Init.
#[local] Instance state𑁒eq_dec : EqDecision state :=
  ltac:(solve_decision).

Record vertex۰name :=
  { vertex۰name۰successors : val
  ; vertex۰name۰state : gname
  ; vertex۰name۰iteration : gname
  ; vertex۰name۰predecessors : gname
  ; vertex۰name۰output : gname
  }.
Implicit Types γ δ π : vertex۰name.

#[local] Instance vertex۰name𑁒eq_dec : EqDecision vertex۰name :=
  ltac:(solve_decision).
#[local] Instance vertex۰name𑁒countable :
  Countable vertex۰name.
Proof.
  solve_countable.
Qed.
Implicit Types Δ Π : gmultiset vertex۰name.

Definition vertex۰iteration :=
  gname.
Implicit Types iter : vertex۰iteration.

Class VertexG Σ `{pool۰G : PoolG Σ} :=
  { #[local] vertex۰G۰stack۰G :: MpmcStack2G Σ
  ; #[local] vertex۰G۰state۰G :: TwinsG Σ (leibnizO state)
  ; #[local] vertex۰G۰iteration۰G :: TwinsG Σ (leibnizO vertex۰iteration)
  ; #[local] vertex۰G۰dependencies۰G :: MonoGmultisetG Σ vertex۰name
  ; #[local] vertex۰G۰predecessors۰G :: AuthGmultisetG Σ vertex۰name
  ; #[local] vertex۰G۰output۰G :: SubpropsG Σ
  }.

Definition vertex۰Σ :=
  #[mpmc_stack_2۰Σ
  ; twins۰Σ (leibnizO state)
  ; twins۰Σ (leibnizO vertex۰iteration)
  ; mono_gmultiset۰Σ vertex۰name
  ; auth_gmultiset۰Σ vertex۰name
  ; subprops۰Σ
  ].
#[global] Instance subG𑁒vertex۰Σ Σ `{pool۰G : PoolG Σ}:
  subG vertex۰Σ Σ →
  VertexG Σ.
Proof.
  solve_inG.
Qed.

Module base.
  Section vertex۰G.
    Context `{vertex۰G : VertexG Σ}.

    Implicit Types t : location.
    Implicit Types P Q R : iProp Σ.

    #[local] Definition state₁' γ_state own state :=
      twins۰twin₁ (twins۰G := vertex۰G۰state۰G) γ_state own state.
    #[local] Definition state₁ γ :=
      state₁' γ.(vertex۰name۰state).
    #[local] Definition state₂' γ_state state :=
      twins۰twin₂ (twins۰G := vertex۰G۰state۰G) γ_state state.
    #[local] Definition state₂ γ :=
      state₂' γ.(vertex۰name۰state).

    #[local] Definition iteration₁' γ_iteration iter :=
      twins۰twin₁ γ_iteration (DfracOwn 1) iter.
    #[local] Definition iteration₁ γ :=
      iteration₁' γ.(vertex۰name۰iteration).
    #[local] Definition iteration₂' γ_iteration iter :=
      twins۰twin₂ γ_iteration iter.
    #[local] Definition iteration₂ γ :=
      iteration₂' γ.(vertex۰name۰iteration).

    #[local] Definition dependencies۰auth iter own :=
      mono_gmultiset۰auth iter own.
    #[local] Definition dependencies۰elem iter :=
      mono_gmultiset۰elem iter.

    #[local] Definition predecessors۰auth' γ_predecessors Π :=
      auth_gmultiset۰auth γ_predecessors (DfracOwn 1) Π.
    #[local] Definition predecessors۰auth γ Π :=
      predecessors۰auth' γ.(vertex۰name۰predecessors) Π.
    #[local] Definition predecessors۰elem γ π :=
      auth_gmultiset۰frag γ.(vertex۰name۰predecessors) {[+π+]}.

    #[local] Definition output۰auth' γ_output :=
      subprops۰auth γ_output.
    #[local] Definition output۰auth γ :=
      subprops۰auth γ.(vertex۰name۰output).
    #[local] Definition output۰frag' γ_output :=
      subprops۰frag γ_output.
    #[local] Definition output۰frag γ :=
      output۰frag' γ.(vertex۰name۰output).

    #[local] Definition model' t γ task state iter : iProp Σ :=
      t.[task] ↦ task ∗
      state₁ γ Own state ∗
      iteration₁ γ iter.
    #[local] Instance : CustomIpat "model'" :=
      " ( Ht{which;}_task{_{}}
        & Hstate{which;}₁{_{}}
        & Hiteration{which;}₁{_{}}
        )
      ".
    Definition vertex۰model t γ task iter : iProp Σ :=
      model' t γ task Init iter.
    #[local] Instance : CustomIpat "model" :=
      " (:model')
      ".

    Definition vertex۰ready iter : iProp Σ :=
      ∃ Δ,
      dependencies۰auth iter Discard Δ ∗
      [∗ mset] δ ∈ Δ, state₁ δ Discard Finished.
    #[local] Instance : CustomIpat "ready" :=
      " ( %Δ{}
        & #Hdependencies{which;}_auth{_{}}
        & #HΔ{}
        )
      ".

    Definition vertex۰finished γ :=
      state₁ γ Discard Finished.
    #[local] Instance : CustomIpat "finished" :=
      " #Hstate{which;}₁{_{}}
      ".

    Definition vertex۰wp۰body t γ P R wp task iter : iProp Σ :=
      ∀ pool ctx scope iter',
      pool۰context pool ctx scope -∗
      vertex۰ready iter -∗
      vertex۰model t γ task iter' -∗
      WP task ctx {{ res,
        ∃ b task,
        ⌜res = #b⌝ ∗
        pool۰context pool ctx scope ∗
        vertex۰model t γ task iter' ∗
        if b then
          ▷ P ∗
          ▷ □ R
        else
          ▷ wp task iter'
      }}.
    #[local] Definition vertex۰wp۰pre
    : location → vertex۰name → iProp Σ → iProp Σ →
      (val -d> vertex۰iteration -d> iProp Σ) →
      val -d> vertex۰iteration -d> iProp Σ
    :=
      vertex۰wp۰body.
    #[local] Instance vertex۰wp۰pre𑁒contractive t γ P R :
      Contractive (vertex۰wp۰pre t γ P R).
    Proof.
      rewrite /vertex۰wp۰pre /vertex۰wp۰body.
      solve_contractive.
    Qed.
    #[local] Instance vertex۰wp۰pre𑁒ne t γ P R :
      NonExpansive (vertex۰wp۰pre t γ P R).
    Proof.
      apply _.
    Qed.
    Definition vertex۰wp t γ P R : val → vertex۰iteration → iProp Σ :=
      fixpoint (vertex۰wp۰pre t γ P R).

    Lemma vertex۰wp𑁒unfold t γ P R task iter :
      vertex۰wp t γ P R task iter ⊣⊢
      vertex۰wp۰body t γ P R (vertex۰wp t γ P R) task iter.
    Proof.
      apply (fixpoint_unfold (vertex۰wp۰pre t γ P R)).
    Qed.
    #[global] Instance vertex۰wp𑁒ne n :
      Proper (
        (=) ==>
        (=) ==>
        (≡{n}≡) ==>
        (≡{n}≡) ==>
        (≡{n}≡) ==>
        (≡{n}≡) ==>
        (≡{n}≡)
      ) vertex۰wp.
    Proof.
      intros t t_ <- γ γ_ <-.
      induction (lt_wf n) as [n _ IH] => P1 P2 HP R1 R2 HR task task_ <- iter iter_ <-.
      rewrite !vertex۰wp𑁒unfold /vertex۰wp۰body.
      do 21 f_equiv. 1: solve_proper.
      f_contractive.
      apply (dist_le _ m) in HP; last by apply SIdx.lt_le_incl.
      apply (dist_le _ m) in HR; last by apply SIdx.lt_le_incl.
      apply IH; done.
    Qed.

    #[local] Definition inv۰state۰init preds iter Π : iProp Σ :=
      ∃ Δ,
      dependencies۰auth iter Own (Δ ⊎ Π) ∗
      ⌜preds = ˖(size Π)⌝ ∗
      [∗ mset] δ ∈ Δ, vertex۰finished δ.
    #[local] Instance : CustomIpat "inv۰state۰init" :=
      " ( %Δ
        & {>;}Hdependencies{which;}_auth
        & {>;}->
        & {>;}HΔ
        )
      ".
    #[local] Definition inv۰state۰released t γ P R preds iter Π : iProp Σ :=
      ∃ task Δ,
      model' t γ task Released iter ∗
      dependencies۰auth iter Discard (Δ ⊎ Π) ∗
      ⌜preds = size Π⌝ ∗
      ([∗ mset] δ ∈ Δ, vertex۰finished δ) ∗
      vertex۰wp t γ P R task iter.
    #[local] Instance : CustomIpat "inv۰state۰released" :=
      " ( %task
        & %Δ
        & (:model')
        & {>;}Hdependencies{which;}_auth
        & {>;}->
        & {>;}HΔ
        & Htask
        )
      ".
    #[local] Definition inv۰state۰ready Π : iProp Σ :=
      ⌜Π = ∅⌝.
    #[local] Instance : CustomIpat "inv۰state۰ready" :=
      " {>;}->
      ".
    #[local] Definition inv۰state۰finished γ R preds Π : iProp Σ :=
      vertex۰finished γ ∗
      ⌜preds = ˖(size Π)⌝ ∗
      □ R.
    #[local] Instance : CustomIpat "inv۰state۰finished" :=
      " ( {>;}#Hstate{which;}₁
        & {>;}->
        & #HR{which;}
        )
      ".
    #[local] Definition inv۰state t γ P R state preds iter Π : iProp Σ :=
      match state with
      | Init =>
          inv۰state۰init preds iter Π
      | Released =>
          inv۰state۰released t γ P R preds iter Π
      | Ready =>
          inv۰state۰ready Π
      | Finished =>
          inv۰state۰finished γ R preds Π
      end.

    #[local] Definition inv۰successor (inv : location → vertex۰name → iProp Σ → iProp Σ → iProp Σ) γ succ : iProp Σ :=
      ∃ γ_succ P_succ R_succ,
      inv succ γ_succ P_succ R_succ ∗
      predecessors۰elem γ_succ γ.
    #[local] Instance : CustomIpat "inv۰successor" :=
      " ( %γ_succ
        & %P_succ
        & %R_succ
        & #Hinv_succ
        & Hpredecessors_elem
        )
      ".
    #[local] Definition inv۰successors inv γ finished :=
      if finished then (
        mpmc_stack_2۰model γ.(vertex۰name۰successors) None
      ) else (
        ∃ succs,
        mpmc_stack_2۰model γ.(vertex۰name۰successors) (Some $ #*@{location} succs) ∗
        [∗ list] succ ∈ succs, inv۰successor inv γ succ
      )%I.
    #[local] Instance : CustomIpat "inv۰successors۰finished" :=
      " >Hsuccessors{which;}_model
      ".
    #[local] Instance : CustomIpat "inv۰successors" :=
      " ( %succs
        & >Hsuccessors{which;}_model
        & Hsuccs
        )
      ".

    #[local] Definition inv۰inner inv t γ P R : iProp Σ :=
      ∃ preds state iter Π,
      t.[preds] ↦ #preds ∗
      state₂ γ state ∗
      iteration₂ γ iter ∗
      predecessors۰auth γ Π ∗
      output۰auth γ P (bool_decide (state = Finished)) ∗
      inv۰state t γ P R state preds iter Π ∗
      inv۰successors inv γ (bool_decide (state = Finished)).
    #[local] Instance : CustomIpat "inv۰inner" :=
      " ( %preds{}
        & %state{}
        & %iter{}
        & %Π
        & Ht{which;}_preds
        & >Hstate{which;}₂
        & >Hiteration{which;}₂
        & Hpredecessors{which;}_auth
        & Houtput{which;}_auth
        & Hinv_state{which;}
        & Hinv_successors{which;}
        )
      ".
    #[local] Definition inv۰pre
    : (location -d> vertex۰name -d> iProp Σ -d> iProp Σ -d> iProp Σ) →
      location -d> vertex۰name -d> iProp Σ -d> iProp Σ -d> iProp Σ
    :=
      λ inv t γ P R, (
        t.[succs] ↦□ γ.(vertex۰name۰successors) ∗
        mpmc_stack_2۰inv γ.(vertex۰name۰successors) (nroot.@"successors") ∗
        invariants.inv (nroot.@"inv") (inv۰inner inv t γ P R)
      )%I.
    #[local] Instance : CustomIpat "inv۰pre" :=
      " ( #Ht{}_succs
        & #Hsuccessors{}_inv
        & #Hinv{_{}}
        )
      ".
    #[local] Instance inv۰pre𑁒contractive :
      Contractive inv۰pre.
    Proof.
      rewrite /inv۰pre /inv۰inner /inv۰successors /inv۰successor.
      intros n Ψ1 Ψ2 HΨ t γ P R.
      repeat (apply HΨ || f_contractive || f_equiv).
    Qed.
    Definition vertex۰inv : location → vertex۰name → iProp Σ → iProp Σ → iProp Σ :=
      fixpoint inv۰pre.

    #[local] Lemma vertex۰inv𑁒unfold t γ P R :
      vertex۰inv t γ P R ⊣⊢
      inv۰pre vertex۰inv t γ P R.
    Proof.
      apply (fixpoint_unfold inv۰pre).
    Qed.
    #[local] Instance vertex۰inv𑁒contractive t γ n :
      Proper (
        dist_later n ==>
        dist_later n ==>
        (≡{n}≡)
      ) (vertex۰inv t γ).
    Proof.
      induction (lt_wf n) as [n _ IH] => P1 P2 HP R1 R2 HR.
      rewrite !vertex۰inv𑁒unfold /inv۰pre /inv۰inner /inv۰state /inv۰state۰released /inv۰state۰finished /inv۰successors /inv۰successor.
      solve_contractive.
    Qed.
    #[global] Instance vertex۰inv𑁒ne t γ n :
      Proper (
        (≡{n}≡) ==>
        (≡{n}≡) ==>
        (≡{n}≡)
      ) (vertex۰inv t γ).
    Proof.
      intros P1 P2 HP R1 R2 HR.
      apply vertex۰inv𑁒contractive.
      all: apply dist_dist_later; done.
    Qed.
    #[global] Instance vertex۰inv𑁒proper t γ :
      Proper (
        (≡) ==>
        (≡) ==>
        (≡)
      ) (vertex۰inv t γ).
    Proof.
      intros P1 P2 HP R1 R2 HR.
      rewrite !equiv_dist in HP HR |- * => n.
      apply vertex۰inv𑁒ne; done.
    Qed.

    Definition vertex۰output γ Q :=
      output۰frag γ Q.
    #[local] Instance : CustomIpat "output" :=
      " Houtput{which;}_frag{_{}}
      ".

    #[global] Instance vertex۰output𑁒contractive γ :
      Contractive (vertex۰output γ).
    Proof.
      solve_contractive.
    Qed.
    #[global] Instance vertex۰output𑁒proper γ :
      Proper ((≡) ==> (≡)) (vertex۰output γ).
    Proof.
      solve_proper.
    Qed.

    Definition vertex۰predecessor γ iter :=
      dependencies۰elem iter γ.
    #[local] Instance : CustomIpat "predecessor" :=
      " #Hdependencies{which;}_elem{_{}}
      ".

    #[global] Instance vertex۰model𑁒timeless t γ task iter :
      Timeless (vertex۰model t γ task iter).
    Proof.
      apply _.
    Qed.
    #[global] Instance vertex۰ready𑁒timeless iter :
      Timeless (vertex۰ready iter).
    Proof.
      apply _.
    Qed.
    #[global] Instance vertex۰finished𑁒timeless γ :
      Timeless (vertex۰finished γ).
    Proof.
      apply _.
    Qed.
    #[global] Instance vertex۰predecessor𑁒timeless γ iter :
      Timeless (vertex۰predecessor γ iter).
    Proof.
      apply _.
    Qed.

    #[global] Instance vertex۰inv𑁒persistent t γ P R :
      Persistent (vertex۰inv t γ P R).
    Proof.
      rewrite vertex۰inv𑁒unfold.
      apply _.
    Qed.
    #[global] Instance vertex۰ready𑁒persistent iter :
      Persistent (vertex۰ready iter).
    Proof.
      apply _.
    Qed.
    #[global] Instance vertex۰finished𑁒persistent γ :
      Persistent (vertex۰finished γ).
    Proof.
      apply _.
    Qed.
    #[global] Instance vertex۰predecessor𑁒persistent γ iter :
      Persistent (vertex۰predecessor γ iter).
    Proof.
      apply _.
    Qed.

    #[local] Lemma state𑁒alloc :
      ⊢ |==>
        ∃ γ_state,
        state₁' γ_state Own Init ∗
        state₂' γ_state Init.
    Proof.
      apply twins𑁒alloc'.
    Qed.
    #[local] Lemma state𑁒agree γ own1 state1 state2 :
      state₁ γ own1 state1 -∗
      state₂ γ state2 -∗
      ⌜state1 = state2⌝.
    Proof.
      apply: twins𑁒agree𑁒L.
    Qed.
    #[local] Lemma state₁𑁒exclusive γ state1 own2 state2 :
      state₁ γ Own state1 -∗
      state₁ γ own2 state2 -∗
      False.
    Proof.
      apply twins۰twin₁𑁒exclusive.
    Qed.
    #[local] Lemma state𑁒update {γ state1 state2} state :
      state₁ γ Own state1 -∗
      state₂ γ state2 ==∗
        state₁ γ Own state ∗
        state₂ γ state.
    Proof.
      apply twins𑁒update.
    Qed.
    #[local] Lemma state₁𑁒discard γ state :
      state₁ γ Own state ⊢ |==>
      state₁ γ Discard state.
    Proof.
      apply twins۰twin₁𑁒persist.
    Qed.

    #[local] Lemma iteration𑁒alloc iter :
      ⊢ |==>
        ∃ γ_iteration,
        iteration₁' γ_iteration iter ∗
        iteration₂' γ_iteration iter.
    Proof.
      apply twins𑁒alloc'.
    Qed.
    #[local] Lemma iteration𑁒agree γ iteration1 iteration2 :
      iteration₁ γ iteration1 -∗
      iteration₂ γ iteration2 -∗
      ⌜iteration1 = iteration2⌝.
    Proof.
      apply: twins𑁒agree𑁒L.
    Qed.
    #[local] Lemma iteration₁𑁒exclusive γ iteration1 iteration2 :
      iteration₁ γ iteration1 -∗
      iteration₁ γ iteration2 -∗
      False.
    Proof.
      apply twins۰twin₁𑁒exclusive.
    Qed.
    #[local] Lemma iteration𑁒update {γ iteration1 iteration2} iteration :
      iteration₁ γ iteration1 -∗
      iteration₂ γ iteration2 ==∗
        iteration₁ γ iteration ∗
        iteration₂ γ iteration.
    Proof.
      apply twins𑁒update.
    Qed.

    #[local] Lemma dependencies𑁒alloc :
      ⊢ |==>
        ∃ iter,
        dependencies۰auth iter Own ∅.
    Proof.
      apply mono_gmultiset𑁒alloc.
    Qed.
    #[local] Lemma dependencies𑁒add {iter Δ} δ :
      dependencies۰auth iter Own Δ ⊢ |==>
        dependencies۰auth iter Own ({[+δ+]} ⊎ Δ) ∗
        dependencies۰elem iter δ.
    Proof.
      apply mono_gmultiset𑁒insert'.
    Qed.
    #[local] Lemma dependencies𑁒elem_of iter own Δ δ :
      dependencies۰auth iter own Δ -∗
      dependencies۰elem iter δ -∗
      ⌜δ ∈ Δ⌝.
    Proof.
      apply mono_gmultiset۰elem𑁒valid.
    Qed.
    #[local] Lemma dependencies𑁒discard iter Δ :
      dependencies۰auth iter Own Δ ⊢ |==>
      dependencies۰auth iter Discard Δ.
    Proof.
      apply mono_gmultiset۰auth𑁒persist.
    Qed.

    #[local] Lemma predecessors𑁒alloc :
      ⊢ |==>
        ∃ γ_predecessors,
        predecessors۰auth' γ_predecessors ∅.
    Proof.
      apply auth_gmultiset𑁒alloc.
    Qed.
    #[local] Lemma predecessors𑁒elem_of γ Π π :
      predecessors۰auth γ Π -∗
      predecessors۰elem γ π -∗
      ⌜π ∈ Π⌝.
    Proof.
      apply auth_gmultiset𑁒elem_of.
    Qed.
    #[local] Lemma predecessors𑁒add {γ Π} π :
      predecessors۰auth γ Π ⊢ |==>
        predecessors۰auth γ ({[+π+]} ⊎ Π) ∗
        predecessors۰elem γ π.
    Proof.
      apply auth_gmultiset𑁒update𑁒alloc𑁒singleton.
    Qed.
    #[local] Lemma predecessors𑁒remove γ Π π :
      predecessors۰auth γ Π -∗
      predecessors۰elem γ π ==∗
      predecessors۰auth γ (Π ∖ {[+π+]}).
    Proof.
      apply auth_gmultiset𑁒update𑁒dealloc.
    Qed.

    #[local] Lemma output𑁒alloc P :
      ⊢ |==>
        ∃ γ_output,
        output۰auth' γ_output P false ∗
        output۰frag' γ_output P.
    Proof.
      apply subprops𑁒alloc.
    Qed.
    #[local] Lemma output𑁒wand {γ P finished Q1} Q2 E :
      ▷ output۰auth γ P finished -∗
      output۰frag γ Q1 -∗
      (Q1 -∗ Q2) ={E}=∗
        ▷ output۰auth γ P finished ∗
        output۰frag γ Q2.
    Proof.
      apply subprops𑁒wand.
    Qed.
    #[local] Lemma output𑁒divide {γ P finished} Qs E :
      ▷ output۰auth γ P finished -∗
      output۰frag γ ([∗ list] Q ∈ Qs, Q) ={E}=∗
        ▷ output۰auth γ P finished ∗
        [∗ list] Q ∈ Qs, output۰frag γ Q.
    Proof.
      apply subprops𑁒divide.
    Qed.
    #[local] Lemma output𑁒produce γ P :
      ▷ output۰auth γ P false -∗
      P -∗
      ▷ output۰auth γ P true.
    Proof.
      iIntros "Hauth HP".
      iApply (subprops𑁒produce with "Hauth [$HP]").
    Qed.
    #[local] Lemma output𑁒consume γ P Q E :
      ▷ output۰auth γ P true -∗
      output۰frag γ Q ={E}=∗
        ▷ output۰auth γ P true ∗
        ▷^2 Q.
    Proof.
      apply subprops𑁒consume.
    Qed.

    Lemma vertex۰model𑁒exclusive t γ task1 iter1 task2 iter2 :
      vertex۰model t γ task1 iter1 -∗
      vertex۰model t γ task2 iter2 -∗
      False.
    Proof.
      iIntros "(:model =1) (:model =2)".
      iApply (iteration₁𑁒exclusive with "Hiteration₁_1 Hiteration₁_2").
    Qed.
    Lemma vertex۰model𑁒finished t γ task iter :
      vertex۰model t γ task iter -∗
      vertex۰finished γ -∗
      False.
    Proof.
      iIntros "(:model =1) (:finished =2)".
      iApply (state₁𑁒exclusive with "Hstate₁_1 Hstate₁_2").
    Qed.

    Lemma vertex۰output𑁒wand {t γ P R Q1} Q2 :
      vertex۰inv t γ P R -∗
      vertex۰output γ Q1 -∗
      (Q1 -∗ Q2) ={⊤}=∗
      vertex۰output γ Q2.
    Proof.
      rewrite vertex۰inv𑁒unfold.
      iIntros "(:inv۰pre) (:output) H".
      iInv "Hinv" as "(:inv۰inner)".
      iMod (output𑁒wand with "Houtput_auth Houtput_frag H") as "($ & $)".
      iFrameSteps.
    Qed.
    Lemma vertex۰output𑁒divide {t γ P R} Qs :
      vertex۰inv t γ P R -∗
      vertex۰output γ ([∗ list] Q ∈ Qs, Q) ={⊤}=∗
      [∗ list] Q ∈ Qs, vertex۰output γ Q.
    Proof.
      rewrite vertex۰inv𑁒unfold.
      iIntros "(:inv۰pre) (:output)".
      iInv "Hinv" as "(:inv۰inner)".
      iMod (output𑁒divide with "Houtput_auth Houtput_frag") as "($ & $)".
      iFrameSteps.
    Qed.

    Lemma vertex𑁒predecessor𑁒finished γ iter :
      vertex۰predecessor γ iter -∗
      vertex۰ready iter -∗
      vertex۰finished γ.
    Proof.
      iIntros "(:predecessor) (:ready)".
      iDestruct (dependencies𑁒elem_of with "Hdependencies_auth Hdependencies_elem") as %Hγ.
      iDestruct (big_sepMS_elem_of with "HΔ") as "#Hstate₁"; first done.
      iSteps.
    Qed.

    Lemma vertex𑁒inv𑁒finished t γ P R :
      vertex۰inv t γ P R -∗
      vertex۰finished γ ={⊤}=∗
      ▷ □ R.
    Proof.
      setoid_rewrite vertex۰inv𑁒unfold.
      iIntros "(:inv۰pre) (:finished)".
      iInv "Hinv" as "(:inv۰inner)".
      iDestruct (state𑁒agree with "Hstate₁ Hstate₂") as %<-.
      iDestruct "Hinv_state" as "{Hstate₁} (:inv۰state۰finished >)".
      iSplitL. { iFrameSteps. }
      iSteps.
    Qed.
    Lemma vertex𑁒inv𑁒finished𑁒output t γ P R Q :
      vertex۰inv t γ P R -∗
      vertex۰finished γ -∗
      vertex۰output γ Q ={⊤}=∗
      ▷^2 Q.
    Proof.
      setoid_rewrite vertex۰inv𑁒unfold.
      iIntros "(:inv۰pre) (:finished) (:output)".
      iInv "Hinv" as "(:inv۰inner)".
      iDestruct (state𑁒agree with "Hstate₁ Hstate₂") as %<-.
      iMod (output𑁒consume with "Houtput_auth Houtput_frag") as "(Houtput_auth & HP)".
      iSplitR "HP". { iFrameSteps. }
      iSteps.
    Qed.

    Lemma vertex٠create𑁒spec P R (task : option val) :
      {{{
        True
      }}}
        vertex٠create task
      {{{
        t γ iter
      , RET #t;
        meta_token t ⊤ ∗
        vertex۰inv t γ P R ∗
        vertex۰model t γ (default (fun: <> => true)%V task) iter ∗
        vertex۰output γ P
      }}}.
    Proof.
      iIntros "%Φ _ HΦ".

      wp۰rec.

      wp۰bind (Match _ _ _ _).
      wp۰apply (wp𑁒wand (λ res,
        ⌜res = default (fun: <> => true)%V task⌝
      )%I) as (res) "->".
      { destruct task; iSteps. }

      wp۰apply+ (mpmc_stack_2٠create𑁒spec with "[//]") as (succs) "(#Hsuccessors_inv & Hsuccessors_model)".
      wp۰block t as "Hmeta" "(Ht_task & Ht_preds & Ht_succs & _)".
      iMod (pointsto𑁒persist with "Ht_succs") as "#Ht_succs".

      iMod state𑁒alloc as "(%γ_state & Hstate₁ & Hstate₂)".
      iMod dependencies𑁒alloc as "(%iter & Hdependencies_auth)".
      iMod (iteration𑁒alloc iter) as "(%γ_iteration & Hiteration₁ & Hiteration₂)".
      iMod predecessors𑁒alloc as "(%γ_predecessors & Hpredecessors_auth)".
      iMod (output𑁒alloc P) as "(%γ_output & Houtput_auth & Houtput_frag)".

      pose γ :=
        {|vertex۰name۰successors := succs
        ; vertex۰name۰state := γ_state
        ; vertex۰name۰iteration := γ_iteration
        ; vertex۰name۰predecessors := γ_predecessors
        ; vertex۰name۰output := γ_output
        |}.

      iApply ("HΦ" $! t γ).
      iFrame.
      rewrite vertex۰inv𑁒unfold. iStep 2.
      iApply inv_alloc.
      iExists 1, Init, iter, ∅. iFrame. iSplitR "Hsuccessors_model".
      - rewrite /inv۰state /inv۰state۰init.
        iExists ∅. rewrite big_sepMS_empty left_id. iSteps.
      - iExists []. iSteps.
    Qed.

    Lemma vertex٠create'𑁒spec P R task :
      {{{
        True
      }}}
        vertex٠create' task
      {{{
        t γ iter
      , RET #t;
        meta_token t ⊤ ∗
        vertex۰inv t γ P R ∗
        vertex۰model t γ (fun: "ctx" => task "ctx" ;; true) iter ∗
        vertex۰output γ P
      }}}.
    Proof.
      iIntros "%Φ _ HΦ".

      wp۰rec.
      wp۰apply+ (vertex٠create𑁒spec P R (Some _) with "[//]").
      iSteps.
    Qed.

    Lemma vertex٠task𑁒spec t γ task iter :
      {{{
        vertex۰model t γ task iter
      }}}
        vertex٠task #t
      {{{
        RET task;
        vertex۰model t γ task iter
      }}}.
    Proof.
      iSteps.
    Qed.

    Lemma vertex٠set_task𑁒spec t γ task1 iter task2 :
      {{{
        vertex۰model t γ task1 iter
      }}}
        vertex٠set_task #t task2
      {{{
        RET ();
        vertex۰model t γ task2 iter
      }}}.
    Proof.
      iSteps.
    Qed.

    Lemma vertex٠precede𑁒spec t1 γ1 P1 R1 t2 γ2 P2 R2 task iter :
      {{{
        vertex۰inv t1 γ1 P1 R1 ∗
        vertex۰inv t2 γ2 P2 R2 ∗
        vertex۰model t2 γ2 task iter
      }}}
        vertex٠precede #t1 #t2
      {{{
        RET ();
        vertex۰model t2 γ2 task iter ∗
        vertex۰predecessor γ1 iter
      }}}.
    Proof.
      setoid_rewrite vertex۰inv𑁒unfold.
      iIntros "%Φ ((:inv۰pre =1) & (:inv۰pre =2) & (:model which=2)) HΦ".

      wp۰rec.
      iApply (wp𑁒frame𑁒wand with "[Ht2_task HΦ]"); first iAccu.
      wp۰load.

      awp۰apply+ (mpmc_stack_2٠is_closed𑁒spec with "Hsuccessors1_inv") without "Hstate2₁ Hiteration2₁".
      iInv "Hinv_1" as "(:inv۰inner which=1 =1)".
      case_decide as [-> | Hstate1].

      - iDestruct "Hinv_state1" as "(:inv۰state۰finished which=1 =1 >) /=".
        iDestruct "Hinv_successors1" as "(:inv۰successors۰finished which=1 =1)".
        iAaccIntro with "Hsuccessors1_model"; iIntros "Hsuccs1_model !>".
        { iFrameSteps. }
        iSplitL. { iFrameSteps. }
        iIntros "{%} _ (Hstate2₁ & Hiteration2₁)".

        iApply fupd𑁒wp.
        iInv "Hinv_2" as "(:inv۰inner which=2 =1)".
        iDestruct (state𑁒agree with "Hstate2₁ Hstate2₂") as %<-.
        iDestruct (iteration𑁒agree with "Hiteration2₁ Hiteration2₂") as %<-.
        iDestruct "Hinv_state2" as "(:inv۰state۰init which=2 =1 >)".
        iMod (dependencies𑁒add γ1 with "Hdependencies2_auth") as "(Hdependencies2_auth & #Hdependencies2_elem)".
        iDestruct (big_sepMS𑁒insert₂ γ1 with "HΔ Hstate1₁") as "HΔ".
        iSplitR "Hstate2₁ Hiteration2₁".
        { assert ({[+γ1+]} ⊎ (Δ ⊎ Π) = ({[+γ1+]} ⊎ Δ) ⊎ Π) as ->.
          { rewrite assoc //. }
          iFrame. rewrite /inv۰state. iFrameSteps.
        }
        iSteps.

      - iDestruct "Hinv_successors1" as "(:inv۰successors which=1 =1)".
        iAaccIntro with "Hsuccessors1_model"; iIntros "Hsuccs_model !>".
        { iFrameSteps. rewrite bool_decide_eq_false_2 //. iSteps. }
        iSplitL.
        { iFrameSteps. rewrite bool_decide_eq_false_2 //. iSteps. }
        iIntros "{%} _ (Hstate2₁ & Hiteration2₁)".

        wp۰pures.

        wp۰bind (FAA _ _).
        iInv "Hinv_2" as "(:inv۰inner which=2 =1)".
        wp۰faa.
        iDestruct (state𑁒agree with "Hstate2₁ Hstate2₂") as %<-.
        iDestruct (iteration𑁒agree with "Hiteration2₁ Hiteration2₂") as %<-.
        iDestruct "Hinv_state2" as "(:inv۰state۰init which=2 =1)".
        iMod (dependencies𑁒add γ1 with "Hdependencies2_auth") as "(Hdependencies2_auth & #Hdependencies2_elem)".
        iMod (predecessors𑁒add γ1 with "Hpredecessors2_auth") as "(Hpredecessors2_auth & Hpredecessors2_elem )".
        iSplitR "Hstate2₁ Hiteration2₁ Hpredecessors2_elem".
        { assert ({[+γ1+]} ⊎ (Δ ⊎ Π) = Δ ⊎ ({[+γ1+]} ⊎ Π)) as ->.
          { rewrite assoc (comm _ _ Δ) -assoc //. }
          iFrameSteps. iPureIntro.
          rewrite gmultiset_size_disj_union gmultiset_size_singleton. lia.
        }
        iIntros "!> {%}".

        wp۰pures. clear.

        awp۰apply (mpmc_stack_2٠push𑁒spec with "Hsuccessors1_inv") without "Hstate2₁ Hiteration2₁".
        iInv "Hinv_1" as "(:inv۰inner which=1 =2)".
        case_decide as [-> | Hstate2].

        + iDestruct "Hinv_state1" as "(:inv۰state۰finished which=1 =2 >) /=".
          iDestruct "Hinv_successors1" as "(:inv۰successors۰finished which=1 =2)".
          iAaccIntro with "Hsuccessors1_model"; iIntros "Hsuccs1_model !>".
          { iFrameSteps. }
          iSplitR "Hpredecessors2_elem". { iFrameSteps. }
          iIntros "{%} _ (Hstate2₁ & Hiteration2₁)".

          wp۰pures.

          wp۰bind (FAA _ _).
          iInv "Hinv_2" as "(:inv۰inner which=2 =2)".
          wp۰faa.
          iDestruct (state𑁒agree with "Hstate2₁ Hstate2₂") as %<-.
          iDestruct (iteration𑁒agree with "Hiteration2₁ Hiteration2₂") as %<-.
          iDestruct "Hinv_state2" as "(:inv۰state۰init which=2 =2)".
          iDestruct (predecessors𑁒elem_of with "Hpredecessors2_auth Hpredecessors2_elem") as %Hγ1.
          iMod (predecessors𑁒remove with "Hpredecessors2_auth Hpredecessors2_elem") as "Hpredecessors2_auth".
          iDestruct (big_sepMS𑁒insert₂ γ1 with "HΔ Hstate1₁") as "HΔ".
          iSplitR "Hstate2₁ Hiteration2₁".
          { replace (Δ ⊎ Π) with ({[+γ1+]} ⊎ Δ ⊎ Π ∖ {[+γ1+]}) by multiset_solver.
            iFrameSteps. iPureIntro.
            rewrite gmultiset_size_difference; first multiset_solver.
            rewrite gmultiset_size_singleton.
            apply gmultiset𑁒elem_of𑁒size𑁒non_empty in Hγ1.
            lia.
          }
          iSteps.

        + iDestruct "Hinv_successors1" as "(:inv۰successors which=1 =2)".
          iAaccIntro with "Hsuccessors1_model"; iIntros "Hsuccs_model !>".
          { iFrameSteps. rewrite bool_decide_eq_false_2 //. iSteps. }
          iSplitL.
          { iFrameSteps. rewrite bool_decide_eq_false_2 //. iSteps.
            iExists (t2 :: succs). iSteps.
            iExists γ2, P2, R2. rewrite vertex۰inv𑁒unfold. iSteps.
          }
          iSteps.
    Qed.

    #[local] Lemma vertex٠release_run𑁒spec :
      ⊢ (
        ∀ pool ctx scope t γ P R task iter,
        {{{
          pool۰context pool ctx scope ∗
          vertex۰inv t γ P R ∗
          vertex۰model t γ task iter ∗
          vertex۰wp t γ P R task iter
        }}}
          vertex٠release ctx #t
        {{{
          RET ();
          pool۰context pool ctx scope
        }}}
      ) ∧ (
        ∀ pool ctx scope t γ P R π,
        {{{
          pool۰context pool ctx scope ∗
          vertex۰inv t γ P R ∗
          predecessors۰elem γ π ∗
          vertex۰finished π
        }}}
          vertex٠release ctx #t
        {{{
          RET ();
          pool۰context pool ctx scope
        }}}
      ) ∧ (
        ∀ pool ctx scope t γ iter P R task,
        {{{
          pool۰context pool ctx scope ∗
          vertex۰inv t γ P R ∗
          vertex۰ready iter ∗
          model' t γ task Ready iter ∗
          vertex۰wp t γ P R task iter
        }}}
          vertex٠run ctx #t
        {{{
          RET ();
          pool۰context pool ctx scope
        }}}
      ).
    Proof.
      iLöb as "HLöb".
      iDestruct "HLöb" as "(IHrelease & IHrelease_successor & IHrun)".
      repeat iSplit.

      { iClear "IHrelease IHrelease_successor".
        setoid_rewrite vertex۰inv𑁒unfold.
        iIntros "%pool %ctx %scope %t %γ %P %R %task %iter !> %Φ (Hctx & (:inv۰pre) & (:model) & Htask) HΦ".

        wp۰rec.
        iApply (wp𑁒frame𑁒wand with "HΦ").
        wp۰pures.

        wp۰bind (FAA _ _).
        iInv "Hinv" as "(:inv۰inner =1)".
        wp۰faa.
        iDestruct (state𑁒agree with "Hstate₁ Hstate₂") as %<-.
        iDestruct (iteration𑁒agree with "Hiteration₁ Hiteration₂") as %<-.
        iDestruct "Hinv_state" as "(:inv۰state۰init =1)".

        destruct_decide (size Π = 0) as ->%gmultiset_size_empty_inv | HΠ.

        - rewrite gmultiset_size_empty right_id.
          iMod (state𑁒update Ready with "Hstate₁ Hstate₂") as "(Hstate₁ & Hstate₂)".
          iMod (dependencies𑁒discard with "Hdependencies_auth") as "#Hdependencies_auth".
          iDestruct "HΔ" as "#HΔ".
          iSplitR "Hctx Ht_task Hstate₁ Hiteration₁ Htask". { iFrameSteps. }
          iIntros "{%} !>".

          wp۰apply+ ("IHrun" with "[$]").
          iSteps.

        - iMod (state𑁒update Released with "Hstate₁ Hstate₂") as "(Hstate₁ & Hstate₂)".
          iMod (dependencies𑁒discard with "Hdependencies_auth") as "#Hdependencies_auth".
          iSplitR "Hctx". { iFrameSteps. }
          iSteps.
      }

      { iClear "IHrelease IHrelease_successor".
        setoid_rewrite vertex۰inv𑁒unfold.
        iIntros "%pool %ctx %scope %t %γ %P %R %π !> %Φ (Hctx & (:inv۰pre) & Hpredecessors_elem & #Hπ) HΦ".

        wp۰rec.
        iApply (wp𑁒frame𑁒wand with "HΦ").
        wp۰pures.

        wp۰bind (FAA _ _).
        iInv "Hinv" as "(:inv۰inner)".
        wp۰faa.
        iDestruct (predecessors𑁒elem_of with "Hpredecessors_auth Hpredecessors_elem") as %Hπ.
        iMod (predecessors𑁒remove with "Hpredecessors_auth Hpredecessors_elem") as "Hpredecessors_auth".

        destruct state.

        - iDestruct "Hinv_state" as "(:inv۰state۰init)".
          iDestruct (big_sepMS𑁒insert₂ with "HΔ Hπ") as "HΔ".
          apply gmultiset𑁒elem_of𑁒size𑁒non_empty in Hπ as ?.
          iSplitR "Hctx".
          { replace (Δ ⊎ Π) with (({[+π+]} ⊎ Δ) ⊎ (Π ∖ {[+π+]})) by multiset_solver.
            iFrameSteps. iPureIntro.
            rewrite gmultiset_size_difference; first multiset_solver.
            rewrite gmultiset_size_singleton.
            lia.
          }
          iSteps.

        - iDestruct "Hinv_state" as "(:inv۰state۰released)".
          iDestruct (big_sepMS𑁒insert₂ with "HΔ Hπ") as "-##HΔ".
          iEval (rewrite (comm (⊎))) in "HΔ".
          destruct_decide (size Π = 1) as HΠ.

          + rewrite HΠ.
            assert (Π = {[+π+]}) as ->.
            { apply gmultiset𑁒size𑁒1𑁒elem_of in HΠ as (π_ & ->).
              set_solver.
            }
            rewrite gmultiset_difference_diag.

            iMod (state𑁒update Ready with "Hstate₁ Hstate₂") as "(Hstate₁ & Hstate₂)".
            iSplitR "Hctx Hdependencies_auth Ht_task Hstate₁ Hiteration₁ Htask". { iFrameSteps. }
            iIntros "{%} !>".

            wp۰apply+ ("IHrun" with "[$]").
            iSteps.

          + apply gmultiset𑁒elem_of𑁒size𑁒non_empty in Hπ as ?.
            iSplitR "Hctx".
            { replace (Δ ⊎ Π) with ((Δ ⊎ {[+π+]}) ⊎ (Π ∖ {[+π+]})) by multiset_solver.
              iFrameSteps. iPureIntro.
              rewrite gmultiset_size_difference; first multiset_solver.
              rewrite gmultiset_size_singleton.
              lia.
            }
            iSteps.

        - iDestruct "Hinv_state" as "(:inv۰state۰ready)".
          exfalso. set_solver.

        - iDestruct "Hinv_state" as "(:inv۰state۰finished)".
          assert (Π ≠ ∅) as ?%gmultiset_size_non_empty_iff by multiset_solver.
          iSplitR "Hctx".
          { iFrameSteps. iPureIntro.
            rewrite gmultiset_size_difference; first multiset_solver.
            rewrite gmultiset_size_singleton.
            lia.
          }
          iSteps.
      }

      { iClear "IHrun".
        setoid_rewrite vertex۰inv𑁒unfold.
        iIntros "%pool %ctx %scope %t %γ %iter %P %R %task !> %Φ (Hctx & (:inv۰pre) & #Hready & (:model') & Htask) HΦ".

        wp۰rec.
        wp۰apply+ (pool٠async𑁒spec True True with "[-HΦ $Hctx]"); last iSteps. iIntros "{% ctx scope} %ctx %scope Hctx".
        wp۰pures.

        wp۰bind (_ <-{preds} _)%E.
        iInv "Hinv" as "(:inv۰inner =1)".
        wp۰store.
        iDestruct (state𑁒agree with "Hstate₁ Hstate₂") as %<-.
        iMod (state𑁒update Init with "Hstate₁ Hstate₂") as "(Hstate₁ & Hstate₂)".
        iDestruct "Hinv_state" as "(:inv۰state۰ready =1)".
        iMod dependencies𑁒alloc as "(%iter' & Hdependencies_auth)".
        iMod (iteration𑁒update iter' with "Hiteration₁ Hiteration₂") as "(Hiteration₁ & Hiteration₂)".
        iSplitR "Hctx Ht_task Hstate₁ Hiteration₁ Htask".
        { iFrameSteps.
          iExists ∅. rewrite left_id big_sepMS_empty. iSteps.
        }
        iIntros "{%} !>".

        wp۰load.

        rewrite vertex۰wp𑁒unfold.
        wp۰apply (wp𑁒wand with "(Htask Hctx [$] [$])") as (res) "{%} (%b & %task & -> & Hctx & (:model) & Hb)".
        destruct b.

        - iDestruct "Hb" as "(HP & #HR)".

          wp۰load.

          awp۰apply (mpmc_stack_2٠close𑁒spec with "Hsuccessors_inv") without "Hctx".
          iInv "Hinv" as "(:inv۰inner =2)".
          iDestruct (state𑁒agree with "Hstate₁ Hstate₂") as %<-.
          iDestruct "Hinv_state" as "(:inv۰state۰init =2 >)".
          iDestruct "Hinv_successors" as "(:inv۰successors =2)".
          iAaccIntro with "Hsuccessors_model"; iIntros "Hsuccessors_model"; first iFrameSteps.
          iMod (state𑁒update Finished with "Hstate₁ Hstate₂") as "(Hstate₁ & Hstate₂)".
          iMod (state₁𑁒discard with "Hstate₁") as "#Hstate₁".
          iDestruct (output𑁒produce with "Houtput_auth HP") as "Houtput_auth".
          iSplitR "Hsuccs". { iFrameSteps. }
          iIntros "!> H£ Hctx {%}".

          iMod (lc_fupd_elim_later with "H£ Hsuccs") as "Hsuccs".
          wp۰apply+ (clist٠iter𑁒spec (λ _, pool۰context pool ctx scope) with "[$Hctx Hsuccs]"); [done | | iSteps].
          rewrite big_sepL_fmap.
          iApply (big_sepL_impl with "Hsuccs"). iIntros "!> %i %succ _ (:inv۰successor) Hctx".
          wp۰apply+ ("IHrelease_successor" with "[$Hctx $Hpredecessors_elem $Hstate₁]"); last iSteps.
          iApply (vertex۰inv𑁒unfold with "Hinv_succ").

        - wp۰apply+ ("IHrelease" with "[$]").
          iSteps.
      }
    Qed.
    Lemma vertex٠release𑁒spec pool ctx scope t γ P R task iter :
      {{{
        pool۰context pool ctx scope ∗
        vertex۰inv t γ P R ∗
        vertex۰model t γ task iter ∗
        vertex۰wp t γ P R task iter
      }}}
        vertex٠release ctx #t
      {{{
        RET ();
        pool۰context pool ctx scope
      }}}.
    Proof.
      iDestruct vertex٠release_run𑁒spec as "(H & _)".
      iApply "H".
    Qed.

    Lemma vertex٠yield𑁒spec t γ task' iter task :
      {{{
        vertex۰model t γ task' iter
      }}}
        vertex٠yield #t task
      {{{
        RET false;
        vertex۰model t γ task iter
      }}}.
    Proof.
      iIntros "%Φ Hmodel HΦ".

      wp۰rec.
      wp۰apply+ (vertex٠set_task𑁒spec with "[$]") as "Hmodel".
      iSteps.
    Qed.
  End vertex۰G.

  #[global] Opaque vertex۰inv.
  #[global] Opaque vertex۰model.
  #[global] Opaque vertex۰output.
  #[global] Opaque vertex۰ready.
  #[global] Opaque vertex۰finished.
  #[global] Opaque vertex۰predecessor.
End base.

Require zoo_parabs.vertex__opaque.

Section vertex۰G.
  Context `{vertex۰G : VertexG Σ}.

  Implicit Types 𝑡 : location.

  Definition vertex۰inv t P R : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.vertex۰inv 𝑡 γ P R.
  #[local] Instance : CustomIpat "inv" :=
    " ( %𝑡{}{_{!}}
      & %γ{}{_{!}}
      & {%Heq{};->}
      & #Hmeta{_{}}{_{!}}
      & #Hinv{_{}}
      )
    ".

  #[global] Instance vertex۰inv𑁒ne t n :
    Proper (
      (≡{n}≡) ==>
      (≡{n}≡) ==>
      (≡{n}≡)
    ) (vertex۰inv t).
  Proof.
    solve_proper.
  Qed.
  #[global] Instance vertex۰inv𑁒proper t :
    Proper (
      (≡) ==>
      (≡) ==>
      (≡)
    ) (vertex۰inv t).
  Proof.
    solve_proper.
  Qed.

  Definition vertex۰model t task iter : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.vertex۰model 𝑡 γ task iter.
  #[local] Instance : CustomIpat "model" :=
    " ( %𝑡{}{_{!}}
      & %γ{}{_{!}}
      & {%Heq{};->}
      & #Hmeta{_{}}{_{!}}
      & Hmodel{_{}}
      )
    ".

  Definition vertex۰output t Q : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.vertex۰output γ Q.
  #[local] Instance : CustomIpat "output" :=
    " ( %𝑡{}{_{!}}
      & %γ{}{_{!}}
      & {%Heq{};->}
      & #Hmeta{_{}}{_{!}}
      & Houtput{_{}}
      )
    ".

  Definition vertex۰ready :=
    base.vertex۰ready.

  Definition vertex۰finished t : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.vertex۰finished γ.
  #[local] Instance : CustomIpat "finished" :=
    " ( %𝑡{}{_{!}}
      & %γ{}{_{!}}
      & {%Heq{};->}
      & #Hmeta{_{}}{_{!}}
      & Hfinished{_{}}
      )
    ".

  Definition vertex۰predecessor t iter : iProp Σ :=
    ∃ 𝑡 γ,
    ⌜t = #𝑡⌝ ∗
    𝑡 ↪ γ ∗
    base.vertex۰predecessor γ iter.
  #[local] Instance : CustomIpat "predecessor" :=
    " ( %𝑡{}{_{!}}
      & %γ{}{_{!}}
      & {%Heq{};->}
      & #Hmeta{_{}}{_{!}}
      & Hpredecessor{_{}}
      )
    ".

  Definition vertex۰wp۰body t P R wp task iter : iProp Σ :=
    ∀ pool ctx scope iter',
    pool۰context pool ctx scope -∗
    vertex۰ready iter -∗
    vertex۰model t task iter' -∗
    WP task ctx {{ res,
      ∃ b task,
      ⌜res = #b⌝ ∗
      pool۰context pool ctx scope ∗
      vertex۰model t task iter' ∗
      if b then
        ▷ P ∗
        ▷ □ R
      else
        ▷ wp task iter'
    }}.
  #[local] Definition vertex۰wp۰pre
  : val → iProp Σ → iProp Σ →
    (val -d> vertex۰iteration -d> iProp Σ) →
    val -d> vertex۰iteration -d> iProp Σ
  :=
    vertex۰wp۰body.
  #[local] Instance vertex۰wp۰pre𑁒contractive t P R :
    Contractive (vertex۰wp۰pre t P R).
  Proof.
    rewrite /vertex۰wp۰pre /vertex۰wp۰body.
    solve_contractive.
  Qed.
  #[local] Instance vertex۰wp۰pre𑁒ne t P R :
    NonExpansive (vertex۰wp۰pre t P R).
  Proof.
    apply _.
  Qed.
  Definition vertex۰wp t P R : val → vertex۰iteration → iProp Σ :=
    fixpoint (vertex۰wp۰pre t P R).

  Lemma vertex۰wp𑁒unfold t P R task iter :
    vertex۰wp t P R task iter ⊣⊢
    vertex۰wp۰body t P R (vertex۰wp t P R) task iter.
  Proof.
    apply (fixpoint_unfold (vertex۰wp۰pre t P R)).
  Qed.
  #[global] Instance vertex۰wp𑁒ne n :
    Proper (
      (=) ==>
      (≡{n}≡) ==>
      (≡{n}≡) ==>
      (≡{n}≡) ==>
      (≡{n}≡) ==>
      (≡{n}≡)
    ) vertex۰wp.
  Proof.
    intros t t_ <-.
    induction (lt_wf n) as [n _ IH] => P1 P2 HP R1 R2 HR task task_ <- iter iter_ <-.
    rewrite !vertex۰wp𑁒unfold /vertex۰wp۰body.
    do 21 f_equiv. 1: solve_proper.
    f_contractive.
    apply (dist_le _ m) in HP; last by apply SIdx.lt_le_incl.
    apply (dist_le _ m) in HR; last by apply SIdx.lt_le_incl.
    apply IH; done.
  Qed.
  #[local] Lemma vertex۰wp𑁒to𑁒base 𝑡 γ P R task iter :
    𝑡 ↪ γ -∗
    vertex۰wp #𝑡 P R task iter -∗
    base.vertex۰wp 𝑡 γ P R task iter.
  Proof.
    iLöb as "HLöb" forall (task iter).

    iEval (rewrite vertex۰wp𑁒unfold base.vertex۰wp𑁒unfold).
    iIntros "#Hmeta Hwp %pool %ctx %scope %iter' Hctx Hready Hmodel".

    wp۰apply (wp𑁒wand with "(Hwp Hctx Hready [$Hmodel])") as (res) "{%} (%b & %task & -> & ($ & Hmodel & Hwp))"; first iSteps.
    iExists b, task. iStep.
    iDestruct "Hmodel" as "(:model =1)". simplify.
    iDestruct (meta𑁒agree with "Hmeta Hmeta_1") as %<-. iClear "Hmeta_1".
    destruct b; iFrameSteps.
  Qed.

  #[global] Instance vertex۰output𑁒contractive t :
    Contractive (vertex۰output t).
  Proof.
    solve_contractive.
  Qed.
  #[global] Instance vertex۰output𑁒proper t :
    Proper ((≡) ==> (≡)) (vertex۰output t).
  Proof.
    solve_proper.
  Qed.

  #[global] Instance vertex۰model𑁒timeless t task iter :
    Timeless (vertex۰model t task iter).
  Proof.
    apply _.
  Qed.
  #[global] Instance vertex۰ready𑁒timeless iter :
    Timeless (vertex۰ready iter).
  Proof.
    apply _.
  Qed.
  #[global] Instance vertex۰finished𑁒timeless t :
    Timeless (vertex۰finished t).
  Proof.
    apply _.
  Qed.
  #[global] Instance vertex۰predecessor𑁒timeless t iter :
    Timeless (vertex۰predecessor t iter).
  Proof.
    apply _.
  Qed.

  #[global] Instance vertex۰inv𑁒persistent t P R :
    Persistent (vertex۰inv t P R).
  Proof.
    apply _.
  Qed.
  #[global] Instance vertex۰ready𑁒persistent iter :
    Persistent (vertex۰ready iter).
  Proof.
    apply _.
  Qed.
  #[global] Instance vertex۰finished𑁒persistent t :
    Persistent (vertex۰finished t).
  Proof.
    apply _.
  Qed.
  #[global] Instance vertex۰predecessor𑁒persistent t iter :
    Persistent (vertex۰predecessor t iter).
  Proof.
    apply _.
  Qed.

  Lemma vertex۰model𑁒exclusive t task1 iter1 task2 iter2 :
    vertex۰model t task1 iter1 -∗
    vertex۰model t task2 iter2 -∗
    False.
  Proof.
    iIntros "(:model =1) (:model =2)". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %<-.
    iApply (base.vertex۰model𑁒exclusive with "Hmodel_1 Hmodel_2").
  Qed.
  Lemma vertex۰model𑁒finished t task iter :
    vertex۰model t task iter -∗
    vertex۰finished t -∗
    False.
  Proof.
    iIntros "(:model =1) (:finished =2)". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %<-.
    iApply (base.vertex۰model𑁒finished with "Hmodel_1 Hfinished_2").
  Qed.

  Lemma vertex۰output𑁒wand {t P R Q1} Q2 :
    vertex۰inv t P R -∗
    vertex۰output t Q1 -∗
    (Q1 -∗ Q2) ={⊤}=∗
    vertex۰output t Q2.
  Proof.
    iIntros "(:inv =1) (:output =2) H". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %<-.
    iMod (base.vertex۰output𑁒wand with "Hinv_1 Houtput_2 H") as "H".
    iFrameSteps.
  Qed.
  Lemma vertex۰output𑁒divide {t P R} Qs :
    vertex۰inv t P R -∗
    vertex۰output t ([∗ list] Q ∈ Qs, Q) ={⊤}=∗
    [∗ list] Q ∈ Qs, vertex۰output t Q.
  Proof.
    iIntros "(:inv =1) (:output =2)". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %<-.
    iMod (base.vertex۰output𑁒divide with "Hinv_1 Houtput_2") as "H".
    iApply (big_sepL_impl with "H").
    iSteps.
  Qed.
  Lemma vertex۰output𑁒split {t P R} Q1 Q2 :
    vertex۰inv t P R -∗
    vertex۰output t (Q1 ∗ Q2) ={⊤}=∗
      vertex۰output t Q1 ∗
      vertex۰output t Q2.
  Proof.
    iIntros "Hinv Houtput".
    iMod (vertex۰output𑁒divide [Q1;Q2] with "Hinv [Houtput]") as "($ & $ & _)" => //.
    { rewrite /= bi.sep_emp //. }
  Qed.

  Lemma vertex𑁒predecessor𑁒finished t iter :
    vertex۰predecessor t iter -∗
    vertex۰ready iter -∗
    vertex۰finished t.
  Proof.
    iIntros "(:predecessor) Hready". simplify.
    iDestruct (base.vertex𑁒predecessor𑁒finished with "Hpredecessor Hready") as "Hfinished".
    iSteps.
  Qed.

  Lemma vertex𑁒inv𑁒finished t P R :
    vertex۰inv t P R -∗
    vertex۰finished t ={⊤}=∗
    ▷ □ R.
  Proof.
    iIntros "(:inv =1) (:finished =2)". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %<-.
    iApply (base.vertex𑁒inv𑁒finished with "Hinv_1 Hfinished_2").
  Qed.
  Lemma vertex𑁒inv𑁒finished' t P R :
    £ 1 -∗
    vertex۰inv t P R -∗
    vertex۰finished t ={⊤}=∗
    □ R.
  Proof.
    iIntros "H£ Hinv Hfinished".
    iMod (vertex𑁒inv𑁒finished with "Hinv Hfinished") as "HR".
    iApply (lc_fupd_elim_later with "H£ HR").
  Qed.
  Lemma vertex𑁒inv𑁒finished𑁒output t P R Q :
    vertex۰inv t P R -∗
    vertex۰finished t -∗
    vertex۰output t Q ={⊤}=∗
    ▷^2 Q.
  Proof.
    iIntros "(:inv =1) (:finished =2) (:output =3)". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %<-.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_3") as %<-.
    iApply (base.vertex𑁒inv𑁒finished𑁒output with "Hinv_1 Hfinished_2 Houtput_3").
  Qed.
  Lemma vertex𑁒inv𑁒finished𑁒output' t P R Q :
    £ 2 -∗
    vertex۰inv t P R -∗
    vertex۰finished t -∗
    vertex۰output t Q ={⊤}=∗
    Q.
  Proof.
    iIntros "(H£1 & H£2) Hinv Hfinished Houtput".
    iMod (vertex𑁒inv𑁒finished𑁒output with "Hinv Hfinished Houtput") as "HP".
    iMod (lc_fupd_elim_later with "H£1 HP") as "HP".
    iApply (lc_fupd_elim_later with "H£2 HP").
  Qed.

  Lemma vertex٠create𑁒spec P R (task : option val) :
    {{{
      True
    }}}
      vertex٠create task
    {{{
      t iter
    , RET t;
      vertex۰inv t P R ∗
      vertex۰model t (default (fun: <> => true)%V task) iter ∗
      vertex۰output t P
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    iApply wp𑁒fupd.
    wp۰apply (base.vertex٠create𑁒spec with "[//]") as (𝑡 γ iter) "(Hmeta & #Hinv & Hmodel & Houtput)".
    iMod (meta𑁒set γ with "Hmeta") as "#Hmeta"; first done.
    iSteps.
  Qed.

  Lemma vertex٠create'𑁒spec P R task :
    {{{
      True
    }}}
      vertex٠create' task
    {{{
      t iter
    , RET t;
      vertex۰inv t P R ∗
      vertex۰model t (fun: "ctx" => task "ctx" ;; true) iter ∗
      vertex۰output t P
    }}}.
  Proof.
    iIntros "%Φ _ HΦ".

    iApply wp𑁒fupd.
    wp۰apply (base.vertex٠create'𑁒spec with "[//]") as (𝑡 γ iter) "(Hmeta & #Hinv & Hmodel & Houtput)".
    iMod (meta𑁒set γ with "Hmeta") as "#Hmeta"; first done.
    iSteps.
  Qed.

  Lemma vertex٠task𑁒spec t task iter :
    {{{
      vertex۰model t task iter
    }}}
      vertex٠task t
    {{{
      RET task;
      vertex۰model t task iter
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".

    wp۰apply (base.vertex٠task𑁒spec with "[$]").
    iSteps.
  Qed.

  Lemma vertex٠set_task𑁒spec t task1 iter task2 :
    {{{
      vertex۰model t task1 iter
    }}}
      vertex٠set_task t task2
    {{{
      RET ();
      vertex۰model t task2 iter
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".

    wp۰apply (base.vertex٠set_task𑁒spec with "[$]").
    iSteps.
  Qed.

  Lemma vertex٠precede𑁒spec t1 P1 R1 t2 P2 R2 task iter :
    {{{
      vertex۰inv t1 P1 R1 ∗
      vertex۰inv t2 P2 R2 ∗
      vertex۰model t2 task iter
    }}}
      vertex٠precede t1 t2
    {{{
      RET ();
      vertex۰model t2 task iter ∗
      vertex۰predecessor t1 iter
    }}}.
  Proof.
    iIntros "%Φ ((:inv =1) & (:inv =2) & Hmodel_2) HΦ". simplify.
    iDestruct "Hmodel_2" as "(:model =2 !=)". simplify.
    iDestruct (meta𑁒agree with "Hmeta_2 Hmeta_2_") as %<-. iClear "Hmeta_2_".

    wp۰apply (base.vertex٠precede𑁒spec with "[$Hmodel_2]").
    { iFrame "#". }
    iSteps.
  Qed.

  Lemma vertex٠release𑁒spec pool ctx scope t P R task iter :
    {{{
      pool۰context pool ctx scope ∗
      vertex۰inv t P R ∗
      vertex۰model t task iter ∗
      vertex۰wp t P R task iter
    }}}
      vertex٠release ctx t
    {{{
      RET ();
      pool۰context pool ctx scope
    }}}.
  Proof.
    iIntros "%Φ (Hctx & (:inv =1) & (:model =2) & Htask) HΦ". simplify.
    iDestruct (meta𑁒agree with "Hmeta_1 Hmeta_2") as %<-. iClear "Hmeta_2".
    iDestruct (vertex۰wp𑁒to𑁒base with "Hmeta_1 Htask") as "Htask".

    wp۰apply (base.vertex٠release𑁒spec with "[$] HΦ").
  Qed.
  Lemma vertex٠release𑁒spec' pool ctx scope t P R task iter :
    {{{
      pool۰context pool ctx scope ∗
      vertex۰inv t P R ∗
      vertex۰model t task iter ∗
      ( ∀ pool ctx scope,
        pool۰context pool ctx scope -∗
        vertex۰ready iter -∗
        WP task ctx {{ res,
          ⌜res = true%V⌝ ∗
          pool۰context pool ctx scope ∗
          ▷ P ∗
          ▷ □ R
        }}
      )
    }}}
      vertex٠release ctx t
    {{{
      RET ();
      pool۰context pool ctx scope
    }}}.
  Proof.
    iIntros "%Φ (Hctx & #Hinv & Hmodel & Htask) HΦ".

    wp۰apply (vertex٠release𑁒spec with "[- HΦ] HΦ").
    rewrite vertex۰wp𑁒unfold. iFrame "#∗". iSteps.
  Qed.

  Lemma vertex٠yield𑁒spec t task' iter task :
    {{{
      vertex۰model t task' iter
    }}}
      vertex٠yield t task
    {{{
      RET false;
      vertex۰model t task iter
    }}}.
  Proof.
    iIntros "%Φ (:model) HΦ".

    wp۰apply (base.vertex٠yield𑁒spec with "[$]").
    iSteps.
  Qed.
End vertex۰G.

#[global] Opaque vertex۰inv.
#[global] Opaque vertex۰model.
#[global] Opaque vertex۰output.
#[global] Opaque vertex۰ready.
#[global] Opaque vertex۰finished.
#[global] Opaque vertex۰predecessor.
