Require Import zoo.prelude.
Require Import zoo.language.notations.
Require Import zoo.diaframe.
Require Export zoo_std.base.
Require Import zoo.options.

Definition diverge : val :=
  rec: "diverge" <> =>
    "diverge" ().

Section zoo_G.
  Context `{zoo_G : !ZooG Σ}.

  Implicit Types Φ : val → iProp Σ.

  Lemma diverge𑁒spec E Φ :
    ⊢ WP diverge () @ E {{ Φ }}.
  Proof.
    iLöb as "IH". wp_rec. iSteps.
  Qed.

  #[global] Instance diverge𑁒diaspec E :
    DIASPEC
    {{
      True
    }}
      diverge ()%V @ E
    {{
      RET ();
      False
    }}.
  Proof.
    iSteps.
    wp_apply diverge𑁒spec.
  Qed.
End zoo_G.

#[global] Opaque diverge.
