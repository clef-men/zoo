Require Import zoo.prelude.
Require Import zoo.base.
Require Import zoo.options.

Definition diverge : val :=
  rec: "diverge" <> =>
    "diverge" ().

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Implicit Types Φ : val → iProp Σ.

  Lemma diverge𑁒spec E Φ :
    ⊢ WP diverge () @ E {{ Φ }}.
  Proof.
    iLöb as "IH". wp۰rec. iSteps.
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
    wp۰apply diverge𑁒spec.
  Qed.
End zoo۰G.

#[global] Opaque diverge.
