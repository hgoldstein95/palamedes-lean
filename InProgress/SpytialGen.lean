/-
Copyright (c) 2025 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

import SpytialLean
import Palamedes.Gen

/-!
# A custom Spytial relationalizer for `Gen`

`Gen`'s constructors carry functions (`bind`'s continuation `α → Gen β`, `indexed`'s
`Nat → Gen (Option α)`, `assume`'s `b → Gen α`), which the default Spytial walker renders as opaque
leaves. This module decomposes a `Gen` constructor-by-constructor so `#spytial` shows the actual
generator structure.

The walker looks the relationalizer up by the WHNF-reduced head of the value's *type*. Since
`def Gen (α : Type) := Raw.Gen α` unfolds to `Raw.Gen α`, we register against `Raw.Gen`.

See `InProgress/SPYTIAL_RELATIONALIZER_GUIDE.md` for the design rationale.
-/

open SpytialLean
open Lean Meta

namespace Palamedes.SpytialGen

/-- How many indices to probe for `indexed` (an unbounded `Nat → Gen (Option α)` family). -/
def genProbeDepth : Nat := 4

/-- Guard against the recursive blow-up of `indexed`. `indexed`'s function is *meant* to be
unbounded recursion (its body typically re-references the generator), so naively walking probed
bodies never terminates. We unfold a single recursion level: while expanding one `indexed`, this
ref is `true`, and any `indexed` encountered *inside* that expansion is rendered as a leaf marker
instead of being unfolded again. Sibling (non-nested) `indexed`s each still unfold once. -/
initialize genInsideIndexed : IO.Ref Bool ← IO.mkRef false

/-- Custom Spytial relationalizer for `Gen` / `Raw.Gen`. One node per constructor, recursing on
`Gen`-typed children and probing `indexed`'s function at `0 … genProbeDepth-1`. -/
partial def relationalizeGen : CustomRelationalizer := fun e recurse => do
  -- Reduce at `.all` transparency so we see through `@[irreducible]` recursion-scheme wrappers
  -- (e.g. `List.unfold`, `Tree.unfold`), which are defined as `indexed (…)` but which a default
  -- `whnf` will not peel — leaving us stuck on an opaque combinator head.
  let e ← withTransparency .all (Meta.whnf e)

  -- Make a fresh node, returning its atom id. The `type` doubles as the constructor name so
  -- Spytial auto-colors by constructor and per-call `with [...]` specs can select on it.
  let mkNode (type label : String) : StateT WalkState MetaM String := do
    let s ← get
    let (id, s) := s.freshId
    set s
    modify fun s => s.addAtom { id := id, type := type, label := label }
    pure id

  -- Add a labeled edge parent → child.
  let edge (parent child field : String) : StateT WalkState MetaM Unit :=
    modify fun s => s.addTuple field #["Gen", "Gen"]
      { atoms := #[parent, child], types := #["Gen", "Gen"] }

  let args := e.getAppArgs
  match e.getAppFn with
  | .const ``Raw.Gen.ret _ =>
    -- ret : {α} → α → Gen α                      args = #[α, value]
    let id ← mkNode "ret" "ret"
    let childId ← recurse args[1]!
    edge id childId "value"
    pure id

  | .const ``Raw.Gen.bind _ =>
    -- bind : {α β} → Gen α → (α → Gen β) → Gen β  args = #[α, β, x, k]
    let id ← mkNode "bind" "bind"
    let xId ← recurse args[2]!
    edge id xId "from"
    -- The continuation has no canonical input to feed it; render it as an opaque leaf.
    let kLabel ← ppLabel args[3]!
    let kId ← mkNode "kont" s!"λ {kLabel}"
    edge id kId "kont"
    pure id

  | .const ``Raw.Gen.pick _ =>
    -- pick : {α} → Gen α → Gen α → Gen α          args = #[α, x, y]
    let id ← mkNode "pick" "pick"
    let xId ← recurse args[1]!
    let yId ← recurse args[2]!
    edge id xId "left"
    edge id yId "right"
    pure id

  | .const ``Raw.Gen.indexed _ =>
    -- indexed : {α} → (Nat → Gen (Option α)) → Gen α   args = #[α, f]
    -- `indexed` is unbounded recursion; only unfold the outermost one (see `genInsideIndexed`).
    if ← genInsideIndexed.get then
      -- Already unfolding an `indexed`; this is a recursive position — stop here.
      mkNode "indexed" "indexed (…)"
    else
      genInsideIndexed.set true
      try
        let id ← mkNode "indexed" "indexed"
        let f := args[1]!
        for i in [:genProbeDepth] do
          let applied ← Meta.whnf (Expr.app f (mkNatLit i))   -- f i : Gen (Option α)
          let childId ← recurse applied
          edge id childId s!"@{i}"
        pure id
      finally
        genInsideIndexed.set false

  | .const ``Raw.Gen.assume _ =>
    -- assume : {α} → (b : Bool) → (b → Gen α) → Gen α   args = #[α, b, f]
    let id ← mkNode "assume" "assume"
    let bId ← recurse args[1]!
    edge id bId "cond"
    -- f's domain is a proof of `b = true`; there is nothing useful to feed it. Render opaque.
    let fId ← mkNode "body" "body"
    edge id fId "body"
    pure id

  | _ =>
    -- Not a recognized `Gen` constructor: degrade gracefully via the default walker.
    recurse e

end Palamedes.SpytialGen

/-- Register the relationalizer.

We use an `initialize` block rather than the `spytial_relationalizer` command because that command
registers into a runtime `IO.Ref` (`SpytialLean.spytialRelationalizerRegistry`) as a side effect of
*elaborating* the command — which is not replayed when this module is merely `import`ed, so the
registration would be lost in any downstream file. `initialize` blocks, by contrast, are re-run on
import, so registering here makes `#spytial` decompose `Gen` in every file that imports this one. -/
initialize SpytialLean.registerSpytialRelationalizer ``Raw.Gen Palamedes.SpytialGen.relationalizeGen

/- No default `spytial_spec` is attached on purpose.

A stored spec is applied to *every* `Gen` value, but a `Gen`'s relations/types vary by which
constructors appear (a `.ret` has only a `value` edge; a `.pick` has `left`/`right`; etc.). CnD
errors if a selector names a relation/type absent from the instance being rendered — e.g. an
`orientation` on `from` makes `#spytial (.ret 2 : Raw.Gen Nat)` fail with
"Expected selector from to evaluate to values of arity 2". So orientation on per-constructor edges
is unsafe as a global default.

Each constructor node instead gets its own atom `type` (`bind`, `pick`, `ret`, `indexed`, `assume`),
which Spytial auto-colors and which is always safe to render. Add layout/colors per call, naming
only the constructors you know are present:

  #spytial g with [
    .orientation (selector := "left")  (directions := [.left, .below]),
    .orientation (selector := "right") (directions := [.right, .below]),
    .atomColor   (selector := "pick")  (value := "#cc6699")
  ]
-/
