Require Import zoo.prelude.
Require Import zoo.base.
Require Import zoo.options.

Definition diverge : val :=
  𝗿𝗲𝗰 "diverge" ⎽ ->
    "diverge" ().

Notation "'𝗱𝗶𝘃𝗲𝗿𝗴𝗲'" :=
  diverge
: expr_scope.

Section zoo۰G.
  Context `{zoo۰G : !ZooG Σ}.

  Implicit Type Φ : val → iProp Σ.

  Lemma diverge𑁒spec E Φ :
    ⊢ WP 𝗱𝗶𝘃𝗲𝗿𝗴𝗲 () @ E {{ Φ }}.
  Proof.
    iLöb as "IH". wp۰rec. iSteps.
  Qed.

  #[global] Instance diverge𑁒diaspec E :
    DIASPEC
    {{
      True
    }}
      𝗱𝗶𝘃𝗲𝗿𝗴𝗲 ()%V @ E
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
