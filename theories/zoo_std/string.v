Require Import zoo.prelude.
Require Import zoo.base.
Require Export zoo_std.string__code.
Require Import zoo_std.string__types.
Require Import zoo.options.

Implicit Type str : string.

Definition string٠unsafe_get : val :=
  𝗳𝘂𝗻 "t" "i" ->
    Binop BinopStringGet "t" "i".

Definition string٠equal : val :=
  𝗳𝘂𝗻 "t1" "t2" ->
    "t1" =ₛ "t2".

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Implicit Type Φ : val → iProp Σ.

  Lemma string٠unsafe_getｰspec str i chr Φ :
    (0 ≤ i)%Z →
    String.get ₊i str = Some chr →
    Φ #chr ⊢
    WP string٠unsafe_get #str #i {{ Φ }}.
  Proof.
    iSteps.
  Qed.

  Lemma string٠equalｰspec str1 str2 Φ :
    Φ #(bool_decide (str1 = str2)) ⊢
    WP string٠equal #str1 #str2 {{ Φ }}.
  Proof.
    iSteps.
  Qed.
End zoo۰G.

Require zoo_std.string__opaque.
#[global] Opaque string٠unsafe_get.
#[global] Opaque string٠equal.
