import Palamedes.Basic

/-!
# Extraction audit

Every example in `Palamedes/Examples/` synthesizes a generator at elaboration time, but a
silent extraction failure does not break the build: if the `extract` simp set fails to
strip the `CorrectGen` combinator wrappers, the generator is left unchanged, so the optimizer's
support-preservation proof still holds trivially, and a `totality` failure is only a warning. The
result is a definition that elaborates fine but contains `(… : CorrectGen P).val` wrappers instead
of raw `Gen` code.

This module walks every `Gen`-typed definition in the example corpus and *fails to compile* if any
synthesis residue survives in a compiled term.
-/

open Lean Meta Elab Command

namespace Palamedes.ExtractionAudit

/-- Constants that should never survive extraction into a synthesized generator: the
`CorrectGen` combinators themselves, the `Subtype.val` projection that extraction is supposed
to eliminate, and `Eq` casts (which would mean a rewrite leaked out of a `convert` proof
argument into the generator). Matcher auxiliaries (e.g. `Gen.CorrectGen.List.s_unfold.match_1`)
are exempt: they are ordinary case splits that legitimately appear in `s_unfold` generators. -/
def isResidue (c : Name) : Bool :=
  if (c.toString.splitOn ".match_").length > 1 then false
  else
    c == ``Subtype.val || c == ``Eq.mpr || c == ``Eq.rec || c == ``CorrectGen ||
    (`Gen.CorrectGen).isPrefixOf c

run_cmd liftTermElabM do
  let env ← getEnv
  let mut total := 0
  for i in [0:env.header.moduleData.size] do
    let modName := env.header.moduleNames[i]!
    unless (`Palamedes.Examples).isPrefixOf modName do continue
    for n in env.header.moduleData[i]!.constNames do
      let some ci := env.find? n | continue
      let some val := ci.value? | continue
      let isGen ← forallTelescope ci.type fun _ body =>
        return body.getAppFn.constName? == some ``Gen
      unless isGen do continue
      total := total + 1
      let bad := val.getUsedConstants.filter isResidue
      unless bad.isEmpty do
        logError m!"extraction left synthesis residue in {n}: {bad.toList}"
  if total == 0 then
    logError "extraction audit found no generators to check; is the example corpus imported?"

end Palamedes.ExtractionAudit
