import Lean

/-- The canonical-form simp set used by `synth_canon` (see `Synthesizer/CGeneratorSearch.lean`).

Lemmas tagged `@[synth_norm]` rewrite a user predicate toward a canonical Prop whose *outermost
head* is explicit (`a = e`, `_ ∨ _`, `∃ a, _ ∧ _`, or a `match` on the datatype), so that synthesis
rules can be routed by `apply`'s own unification instead of by a per-combinator `convert` + equality
proof. This is the one place the normal-form contract is defined; it replaces the inline curated
`simp only [...]` exclusion lists previously duplicated across the `norm_for_*` macros. -/
register_simp_attr synth_norm
