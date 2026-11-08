# Guidelines

## Rocq proof style

Spacing matters for readability. Keep it consistent with existing proofs. Good reference files are `theories/zoo_saturn/bag_1.v`, `theories/zoo_saturn/stack_mpmc_1.v` and `theories/zoo_saturn/inf_ws_deque_1.v`.

1. **Spec proofs** (Hoare triples `{{{ }}}` and atomic triples `<<< >>>`): put a blank line after the first `iIntros`, the one that introduces the precondition and `HΦ`. This applies even when the next line is `iInv`.

   ```coq
   Proof.
     iIntros "%Φ (:inv) HΦ".

     wp۰rec. wp۰pures.
   ```

2. **Atomic sections**: an invariant opened with `iInv` (often just after `wp۰bind (…)%E.`) starts a block.
   - Put a blank line before the block, that is, before the `wp۰bind` if there is one.
   - The block runs until the invariant is closed: `iSplitR "…". { iFrameSteps. }` followed by `iModIntro.` or `iIntros "!> …"`.
   - Put a blank line after the block, before the next program step. For example, write `iModIntro.`, then a blank line, then `wp۰pures.`, not `iModIntro. wp۰pures.` on one line.
   - If the block ends the proof, nothing follows.

   ```coq
     wp۰pures.

     wp۰bind (𝗰𝗮𝘀 _ _ _)%E.
     iInv "Hinv" as "(:inv۰inner =1)".
     wp۰cas as _ | Hcas.

     - iSplitR "HΦ". { iFrameSteps. }
       iSteps.

     - iMod "HΦ" as "(%vs & (:model) & _ & HΦ)".
       …
   ```

3. **Case splits**: when a tactic in the main flow of a proof splits into branches (`wp۰cas as … | …`, or a `destruct` followed by bullets), put a blank line after it. Separate the `-`/`+` branches with blank lines.

4. **`iLöb`**: give it its own line, with a blank line before and after.

5. **Logical phases**: separate the phases of a proof with blank lines. Examples of phases:
   - `wp۰rec` and setup;
   - ghost allocations (`iMod …alloc`);
   - a `pose γ := {| … |}.` record;
   - registration through a fupd lemma;
   - the final `iApply "HΦ"`.

   Do not put blank lines inside a phase.

6. **No `all:` / `1:` / `2:` chains** to factor nearly identical branches. Prefer a uniform lemma, such as `wpｰcasｰnobranch'` instead of `wp۰cas`, or write explicit bullets.

Helper lemmas that are not specs use a compact layout, with no blank line after `iIntros`. If a helper lemma opens an invariant, rule 2 still applies to that section.
