import Palamedes.Synthesizer
import Palamedes.Examples.Simple.Eq2
import Palamedes.Examples.Simple.Eq2'
import Palamedes.Examples.Simple.ThreePlusOne

/-!
# `@[synth_norm]` / `synth_canon` contract tests

These are the Phase-1 safety net for the canonicalizer (see `synthesis-robustness-plan.html`).
The plan flags non-confluence of the `@[synth_norm]` set, and a regression of `synth_canon` back to
a goal-side `simp` (which leaks `Eq.mpr` into the generator), as the two top risks. Nothing else in
the build pins the *normal-form contract* itself — `lake build` + `ExtractionAudit` only check the
end-to-end corpus, coarsely and slowly. This file pins the contract directly and locally:

1. **Normal-form snapshots.** Each representative predicate head is run through `simp only
   [synth_norm]` and its result captured with `#guard_msgs`. If the seed set in
   `CGeneratorSearch.lean` changes the canonical form, these snapshots break loudly.
2. **Extraction cleanliness of the fast path.** A `run_cmd` confirms that a leaf synthesized through
   the `synth_canon` fast path (`genEq2`) extracts to raw `Gen` with *no* `convert`/`Subtype.val`/
   `Eq.mpr` residue — the headline `Eq.mpr` regression from §3 of the plan, guarded at unit level.

The `@[synth_norm]` set is **not** re-declared here; it is the live one seeded in
`CGeneratorSearch.lean` (active transitively via `Palamedes.Synthesizer`). So these tests track the
real set, not a copy.
-/

open Gen CorrectGen

set_option linter.unusedTactic false

namespace Palamedes.SynthNormTests

/-! ## 1. Normal-form snapshots

The contract is deliberately conservative: the seed set only *exposes the head* of a `decide`/`Bool`
predicate as a `Prop`, never restructuring it. The snapshots below are the executable statement of
that contract — the `unsolved goals` body is the canonical predicate the leaf `apply` then routes on.
-/

/- `decide`-headed equality canonicalizes to a bare `Prop` equality (`s_pure`'s shape). -/
/--
error: unsolved goals
n : ℕ
⊢ n = 2
-/
#guard_msgs in
example (n : Nat) : decide (n = 2) = true := by simp only [synth_norm]

/- `==`-headed equality (`beq`) canonicalizes the same way. -/
/--
error: unsolved goals
n : ℕ
⊢ n = 2
-/
#guard_msgs in
example (n : Nat) : (n == 2) = true := by simp only [synth_norm]

/- **Orientation is preserved.** A reversed equality stays reversed: `synth_norm` must never carry
`eq_comm`, because the fold/unfold path depends on the `fold-expr = value` orientation and a global
flip corrupts it (see `synth-canon-orientation-conflict` and the note in `CGeneratorSearch.lean`).
Any Phase-2 work that wants `x = e` for `s_pure` must do the flip *rule-locally*, not here — this
snapshot is the regression guard for that rule. -/
/--
error: unsolved goals
n : ℕ
⊢ 2 = n
-/
#guard_msgs in
example (n : Nat) : decide (2 = n) = true := by simp only [synth_norm]

/- **Bool `&&` is deliberately not split.** The seed set does not turn `_ && _` into `_ ∧ _`; the
Range corpus reaches the conjunction head via Prop-native `∧`, and adding a `&&`-splitter risks
destabilizing the fold path. `simp` making no progress here is the contract, not a gap. -/
/-- error: `simp` made no progress -/
#guard_msgs in
example (n : Nat) : (decide (5 ≤ n) && decide (n ≤ 10)) = true := by simp only [synth_norm]

/- An already-canonical `∨` head is a fixpoint of the set (confluence check). -/
/-- error: `simp` made no progress -/
#guard_msgs in
example (n : Nat) : n = 2 ∨ n = 5 := by simp only [synth_norm]

/- An already-canonical `∃ … ∧ …` head (`s_bind`'s shape) is a fixpoint too. -/
/-- error: `simp` made no progress -/
#guard_msgs in
example (b : Nat) : ∃ a, a = 3 ∧ b = a + 1 := by simp only [synth_norm]

/-! ## 2. Extraction cleanliness of the `synth_canon` fast path

`genEq2` (`generator_search (· = 2)`) routes through `synth_canon`'s `apply s_pure` fast path. The
plan's headline empirical result is that this extracts to clean `pure 2`, whereas a goal-side
`simp only [synth_norm]` would leave `↑(_proof.mpr (s_pure 2))` with `[Subtype.val, Eq.mpr, …]`
residue. We assert the clean outcome directly here so the regression surfaces at unit level, not
only in the corpus-wide `ExtractionAudit`. -/

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let env ← getEnv
  let some ci := env.find? ``genEq2
    | throwError "SynthNormTests: genEq2 not found"
  let some val := ci.value?
    | throwError "SynthNormTests: genEq2 has no value"
  -- same residue predicate as ExtractionAudit (no matcher auxiliaries are expected for this leaf)
  let isResidue (c : Name) : Bool :=
    c == ``Subtype.val || c == ``Eq.mpr || c == ``Eq.rec || c == ``CorrectGen ||
    (`Gen.CorrectGen).isPrefixOf c
  let bad := val.getUsedConstants.filter isResidue
  unless bad.isEmpty do
    throwError "synth_canon fast path leaked synthesis residue into genEq2: {bad.toList}"

end Palamedes.SynthNormTests
