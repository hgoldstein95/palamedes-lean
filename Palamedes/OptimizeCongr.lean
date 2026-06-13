import Lean
import Palamedes.Gen

/-!
# The `@[gen_congr]` attribute

Registers `support`-congruence lemmas that tell the generator optimizer how to descend through a
`Gen` constructor or recursion-scheme combinator. The optimizer reads this registry at run time, so
**teaching it about a new datatype is just tagging that datatype's congruence lemma** — no edit to
the optimizer is required (mirroring how `@[extract]` and the Aesop `synthesis` rule set work).

Each lemma's shape is parsed *once*, when it is tagged, into a `CongrRule`; a lemma whose statement
is not of the expected form is rejected at that point rather than being silently dropped later.
-/

open Lean Meta

/-- A congruence rule the optimizer can descend through: the head constant of the term it applies
to, the `@[gen_congr]` lemma's name, and the argument positions to recurse into (ascending). -/
abbrev CongrRule := Name × Name × Array Nat

/-- Read a `@[gen_congr]` lemma's statement `support (H …) = support (H …)` to recover its head
constant `H` and the argument positions that differ between the two sides — i.e. the children to
recurse into. Whatever arguments coincide (seeds, scrutinees, instances) are left untouched.
Returns `none` if the statement is not of that shape (so the attribute can reject it). -/
def analyzeCongr (lemmaName : Name) : MetaM (Option CongrRule) := do
  forallTelescope (← getConstInfo lemmaName).type fun _ body => do
    let_expr Eq _ lhs rhs := body | return none
    let_expr Gen.support _ genL := lhs | return none
    let_expr Gen.support _ genR := rhs | return none
    let some head := genL.getAppFn.constName? | return none
    -- Both sides must be applications of the *same* head constant.
    unless genR.getAppFn.constName? == some head do return none
    let argsL := genL.getAppArgs
    let argsR := genR.getAppArgs
    if argsL.size != argsR.size then return none
    let mut diff := #[]
    for i in [0:argsL.size] do
      unless argsL[i]! == argsR[i]! do diff := diff.push i
    -- A congruence lemma with no differing arguments tells the optimizer nothing.
    if diff.isEmpty then return none
    return some (head, lemmaName, diff)

/-- Parsed `CongrRule`s for all `@[gen_congr]`-tagged lemmas, accumulated across imported modules. -/
initialize genCongrExt : SimplePersistentEnvExtension CongrRule (Array CongrRule) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := mkStateFromImportedEntries Array.push #[]
  }

/--
Mark a `support`-congruence lemma for the generator optimizer's structural descent. The lemma must
have the shape

    support (H a₁ … aₙ) = support (H a₁' … aₙ')

for a constant head `H`, with one hypothesis per argument that differs between the two sides. The
optimizer infers the head `H` and which arguments to recurse into directly from the statement, so
tagging a new datatype's `*_support_unfold_congr` lemma is all that is needed to support it. A lemma
not of this shape is rejected here rather than being silently ignored by the optimizer.
-/
initialize registerBuiltinAttribute {
  name := `gen_congr
  descr := "support-congruence lemma for the generator optimizer's structural descent"
  add := fun decl stx _ => do
    Attribute.Builtin.ensureNoArgs stx
    let some rule ← (analyzeCongr decl).run'
      | throwError "`@[gen_congr]`: `{decl}` is not a support-congruence lemma of the form \
          `support (H …) = support (H …)` with at least one differing argument"
    modifyEnv (genCongrExt.addEntry · rule)
}

/-- All registered `@[gen_congr]` congruence rules. -/
def getGenCongrRules (env : Environment) : Array CongrRule := genCongrExt.getState env
