# Writing a custom Spytial relationalizer for `Gen`

Goal: make `#spytial` render a `Palamedes/Gen.lean` generator usefully, even though `Gen`'s
constructors carry **functions** (`bind`'s continuation `α → Gen β`, `indexed`'s `Nat → Gen (Option α)`,
`assume`'s `b → Gen α`). The default relationalizer renders any non-finite-domain function as an
opaque labeled leaf. A custom relationalizer lets us decompose `Gen` constructor-by-constructor and
decide what to do with each function.

This guide is self-contained: it gives the exact API, a working skeleton, and the gotchas. Palamedes
already depends on `spytialLean` (see `lakefile.toml`), so `import SpytialLean` works.

---

## 1. The mechanism

A custom relationalizer is a function registered against a **type name**. When the walker is about to
render a value whose type's head constant matches, it calls your function instead of the default
dispatch.

```lean
-- from SpytialLean/Relationalizer.lean
def CustomRelationalizer :=
  Expr → (Expr → StateT WalkState MetaM String) → StateT WalkState MetaM String
```

Your function receives:
- `e : Expr` — the value to render (NOT yet WHNF-reduced; call `Meta.whnf` yourself).
- `recurse : Expr → StateT WalkState MetaM String` — the default walker, already partially applied
  with the config. Call it on sub-expressions to render them normally (it re-enters custom
  relationalizers, so recursion into nested `Gen`s stays custom). It returns the **atom id** (a
  `String`) it assigned to that sub-expression.

You must return the atom id (`String`) of the node representing `e`.

Register with the command:

```lean
spytial_relationalizer <TypeName> <defName>
```

### Which type name to register against

The lookup uses the **WHNF-reduced head of the value's type**. In `Gen.lean`:

```lean
def Gen (α : Type) := Raw.Gen α
```

`Gen α` is a plain `def`, so `Meta.whnf` unfolds it to `Raw.Gen α`. The walker therefore looks up the
type name **`Raw.Gen`**, not `Gen`. Register against `Raw.Gen`:

```lean
spytial_relationalizer Raw.Gen relationalizeGen
```

> ⚠️ Verify this empirically before trusting it. Run `#spytial.datum someGen` and look at the `type`
> field of the atoms, or temporarily register against both and see which fires. If `Raw.Gen` doesn't
> trigger, try `Gen`. (The constructors after WHNF are `Raw.Gen.ret`, `Raw.Gen.bind`, etc., regardless.)

---

## 2. The `WalkState` API you build with

You manipulate state through `get` / `set` / `modify` (this runs in `StateT WalkState MetaM`).

```lean
-- allocate a fresh atom id
let s ← get
let (id, s) := s.freshId        -- id : String, e.g. "atom_7"
set s

-- add a node
modify fun s => s.addAtom { id := id, type := "Gen", label := "bind" }
--   JsonAtom fields: id (String), type (String, used as the node's "type" in selectors),
--                    label (String, shown on the node)

-- add an edge (relation tuple) from parent → child
modify fun s => s.addTuple "kont" #["Gen", "Gen"]
  { atoms := #[parentId, childId], types := #["Gen", "Gen"] }
--   addTuple relName types tuple
--   relName : String     — the edge/field name (this is what `.hideField`, `.orientation`, etc. select on)
--   types   : Array String — declared endpoint types, length 2 for a binary edge
--   JsonTuple.atoms : Array String — the atom ids the tuple connects, in order
--   JsonTuple.types : Array String — per-position types, same length as atoms
```

Helpers available (all from `SpytialLean`, opened via `open SpytialLean`):
- `recurse childExpr` → renders a sub-expression with the default machinery; returns its atom id.
- `ppLabel e : MetaM String` — pretty-prints `e` to a short label string (good for leaves).
- `shortName n : String` — last component of a `Name` (e.g. `` `Raw.Gen.bind `` → `"bind"`).
- `Meta.whnf`, `Meta.mkProjection e fieldName`, `e.getAppFn`, `e.getAppArgs`, `mkNatLit i`,
  `Expr.app f x` — standard for decomposing/building expressions.

---

## 3. Recommended `Gen` relationalizer

Strategy:
- One node per constructor, labeled with the constructor name.
- Recurse on `Gen`-typed sub-values (the `ret` payload, `bind`'s first arg, `pick`'s two args).
- For `indexed`'s `Nat → Gen (Option α)`: **probe** the function at `0, 1, … k` and render the
  results as numbered children (this is the "render the function body" trick — apply, then walk).
- For `bind`'s continuation `α → Gen β` and `assume`'s `b → Gen α`: there's no canonical input to feed
  them, so render them opaque (a single child node), OR drop them.

```lean
import SpytialLean
open SpytialLean
open Lean Meta

/-- How many indices to probe for `indexed`. -/
def genProbeDepth : Nat := 4

partial def relationalizeGen : CustomRelationalizer := fun e recurse => do
  let e ← Meta.whnf e

  -- helper: make this node and return its id
  let mkNode (label : String) : StateT WalkState MetaM String := do
    let s ← get
    let (id, s) := s.freshId
    set s
    modify fun s => s.addAtom { id := id, type := "Gen", label := label }
    pure id

  -- helper: add a labeled edge from parent → child
  let edge (parent child field : String) : StateT WalkState MetaM Unit :=
    modify fun s => s.addTuple field #["Gen", "Gen"]
      { atoms := #[parent, child], types := #["Gen", "Gen"] }

  let args := e.getAppArgs
  match e.getAppFn with
  | .const ``Raw.Gen.ret _ =>
    -- ret : {α} → α → Gen α   ⇒ args = #[α, value]
    let id ← mkNode "ret"
    let childId ← recurse (← Meta.whnf args[1]!)
    edge id childId "value"
    pure id

  | .const ``Raw.Gen.bind _ =>
    -- bind : {α β} → Gen α → (α → Gen β) → Gen β  ⇒ args = #[α, β, x, k]
    let id ← mkNode "bind"
    let xId ← recurse (← Meta.whnf args[2]!)
    edge id xId "from"
    -- continuation: render opaque (a labeled leaf). Comment out the next 3 lines to drop it instead.
    let kLabel ← ppLabel args[3]!
    let kId ← mkNode s!"λ {kLabel}"
    edge id kId "kont"
    pure id

  | .const ``Raw.Gen.pick _ =>
    -- pick : {α} → Gen α → Gen α → Gen α  ⇒ args = #[α, x, y]
    let id ← mkNode "pick"
    let xId ← recurse (← Meta.whnf args[1]!)
    let yId ← recurse (← Meta.whnf args[2]!)
    edge id xId "left"
    edge id yId "right"
    pure id

  | .const ``Raw.Gen.indexed _ =>
    -- indexed : {α} → (Nat → Gen (Option α)) → Gen α  ⇒ args = #[α, f]
    let id ← mkNode "indexed"
    let f := args[1]!
    for i in [:genProbeDepth] do
      let applied ← Meta.whnf (Expr.app f (mkNatLit i))   -- f i : Gen (Option α)
      let childId ← recurse applied
      edge id childId s!"@{i}"
    pure id

  | .const ``Raw.Gen.assume _ =>
    -- assume : {α} → (b : Bool) → (b → Gen α) → Gen α  ⇒ args = #[α, b, f]
    let id ← mkNode "assume"
    let bLabel ← ppLabel args[1]!
    let bId ← mkNode s!"cond {bLabel}"
    edge id bId "cond"
    -- f's domain is a proof of `b = true`; render opaque.
    let fId ← mkNode "body"
    edge id fId "body"
    pure id

  | _ =>
    -- Fallback: shouldn't happen for a well-formed Gen, but degrade gracefully.
    recurse e

spytial_relationalizer Raw.Gen relationalizeGen
```

### Important details

- **Argument indices.** The indices into `e.getAppArgs` above assume the implicit type arguments come
  first (`α`, then `β` for `bind`). `Gen` is declared `inductive Gen : Type → Type 1`, so `α` is an
  **index**, present in `getAppArgs`. If an index is wrong you'll get an off-by-one or a panic — debug
  by adding `dbg_trace s!"bind args = {args.size}"` and printing each `← ppLabel args[i]!`. Do NOT
  guess; print and confirm.
- **Always `Meta.whnf` before recursing** on a sub-value, so the child's constructor is exposed.
- **`partial def`** is needed because `relationalizeGen` is recursive through `recurse` only
  indirectly, but marking it `partial` avoids termination-checker friction; keep it.
- **Probing depth.** `indexed` represents an unbounded family; `genProbeDepth` is a display choice.
  If you want to show that it's truncated, add a final child node labeled `"…"`.

---

## 4. Testing and debugging

```lean
def g : Gen Nat := do let x ← pick (pure 1) (pure 2); pure (x + 10)

#spytial g            -- the diagram
#spytial.datum g      -- raw atoms + relations as JSON; check `type` and edge names
#spytial.spec g       -- the generated YAML spec (for debugging selectors)
```

Workflow:
1. Start with `#spytial.datum g` on a tiny generator to confirm the registered type name fires and the
   atom/edge shape is what you expect.
2. Use `dbg_trace` inside `relationalizeGen` to print `args.size` and `ppLabel` of each arg when an
   index is uncertain.
3. Once the structure is right, style it with a spec (next section).

---

## 5. Styling the result with a spec (optional)

After the relationalizer produces nodes/edges, you can lay them out and color them without touching
the relationalizer. Edge names you chose (`from`, `kont`, `left`, `right`, `@0`, …) and the node
`type` (`"Gen"`) / `label` (the constructor names) are the selectors.

```lean
spytial_spec Raw.Gen [
  .orientation (selector := "from")  (directions := [.below]),
  .orientation (selector := "left")  (directions := [.left, .below]),
  .orientation (selector := "right") (directions := [.right, .below]),
  .hideField (field := "kont"),                 -- drop the opaque continuations entirely
  .atomColor (selector := "{x : Gen | x.label = pick}") (value := "#cc6699")
]
```

(Selector syntax is CnD; see spytial-lean's `README.md` / `demos/Showcase.lean` for the full
operation list: `.orientation`, `.align`, `.cyclic`, `.group`, `.hideAtom`, `.hideField`,
`.attribute`, `.atomColor`, `.edgeColor`, `.size`, `.icon`, `.flag`, …)

---

## 6. Reference: `Gen` constructors (from `Palamedes/Gen.lean`)

```lean
namespace Raw
inductive Gen : Type → Type 1 where
  | ret     : α → Gen α
  | bind    : Gen α → (α → Gen β) → Gen β
  | pick    : Gen α → Gen α → Gen α
  | indexed : (Nat → Gen (Option α)) → Gen α
  | assume  : (b : Bool) → (b → Gen α) → Gen α
end Raw

def Gen (α : Type) := Raw.Gen α      -- ⇒ register the relationalizer on `Raw.Gen`
```

The user-facing smart constructors (`Gen.pick`, `Gen.assume`, `Gen.indexed`, `pure`, `>>=`) all
reduce to these `Raw.Gen.*` constructors under WHNF, so dispatching on `Raw.Gen.*` covers everything.

---

# Appendix: implementing "opaque call → node with its arguments as children" in spytial-lean

This is a **change to the spytial-lean library itself** (the dependency under `.lake/packages/` or
wherever it's checked out — the source repo is https://github.com/hgoldstein95/spytial-lean). It is
independent of the `Gen` relationalizer above; do it there if you want *every* opaque function
application `f a b c` to render as a node `f` with children `a`, `b`, `c`, instead of the current
single collapsed leaf.

## Background: the two "opaque function" paths

There are two distinct cases in `SpytialLean/Relationalizer.lean`, don't confuse them:

1. **Opaque lambda** `λ x => …` (`Relationalizer.lean:179-200`). A lambda has no arguments, so
   "arguments as children" does not apply — this path is unchanged. (For finite domains it already
   enumerates input→output edges; otherwise it's a leaf.)
2. **Opaque application** `f a b c` where `f` is a const that is neither a constructor nor a structure
   projection (`Relationalizer.lean:268-272`). This is the one to change.

The current code (the `else` branch around line 268):

```lean
else do
  -- Generic function application or unknown — leaf atom
  let label ← ppLabel e
  modify fun s => s.addAtom { id := atomId, type := typeName, label := label }
  pure atomId
```

## Recommended approach: opt-in via a `WalkConfig` flag

Make it off-by-default so existing diagrams don't change, and expose a dedicated command to turn it on
(mirroring exactly how `#spytial.proof` toggles `filterProofs`).

### Step 1 — add the config flag

In `SpytialLean/Relationalizer.lean`, the `WalkConfig` structure (around line 50):

```lean
structure WalkConfig where
  /-- When true, skip Prop-typed fields (data mode). When false, show them (proof mode). -/
  filterProofs : Bool := true
  /-- When true, render an opaque function application `f a b c` as a node for `f`
      with one child edge per (non-type/proof) argument, instead of a single leaf. -/
  expandOpaqueApps : Bool := false
```

### Step 2 — use it in the opaque-application branch

Replace the `else do … leaf atom` branch (`Relationalizer.lean:268-272`) with:

```lean
else if cfg.expandOpaqueApps then do
  -- Opaque application: node for the head, one child per non-type/proof argument
  modify fun s => s.addAtom { id := atomId, type := typeName, label := shortName fnName }
  let args := e.getAppArgs
  for i in [:args.size] do
    let arg := args[i]!
    let skip ← if cfg.filterProofs then isProofArg arg else pure false
    unless skip do                       -- isProofArg drops type params (Sort) and proofs (Prop)
      let childId ← walkExpr cfg arg      -- thread cfg so nested opaque calls expand too
      modify fun s => s.addTuple s!"arg{i}" #[typeName, typeName]
        { atoms := #[atomId, childId], types := #[typeName, typeName] }
  pure atomId
else do
  -- Generic function application or unknown — leaf atom (original behavior)
  let label ← ppLabel e
  modify fun s => s.addAtom { id := atomId, type := typeName, label := label }
  pure atomId
```

This mirrors the existing constructor branch (`Relationalizer.lean:228-244`), reusing `isProofArg` so
implicit type and proof arguments are filtered out. `fnName` is already bound in scope (the branch is
under `match e.getAppFn with | .const fnName _ => …`). Pass `cfg` to the recursive `walkExpr` so the
flag propagates into nested applications.

> Caveat — typeclass-instance arguments. `isProofArg` filters types (`Sort`) and proofs (`Prop`) but
> NOT instance arguments, so those would show up as children. If that's noisy, add a filter using
> `Lean.isClass? (← inferType arg)` and skip when it returns `some _`.

### Step 3 — expose a command toggle

In `SpytialLean/Command.lean`, the `#spytial.proof` command (`Command.lean:192-220`) is the template:
it's a copy of `#spytial` that calls `relationalize e { filterProofs := false }`. Add an analogous
command that sets the new flag. Minimal version:

```lean
/-- `#spytial.apps <term>` renders opaque function applications as nodes with their
    arguments as children (instead of a single collapsed leaf). -/
syntax (name := spytialAppsCmd) "#spytial.apps " term (" with " term)? : command

@[command_elab spytialAppsCmd]
def elabSpytialAppsCmd : CommandElab := fun
  | stx@`(#spytial.apps $t:term $[with $spec?]?) => do
    -- body identical to elabSpytialCmd, but:
    --   let di ← relationalize e { expandOpaqueApps := true }
    ...
  | stx => throwError "Unexpected syntax {stx}."
```

Copy the body of `elabSpytialCmd` (`Command.lean:69-95`) verbatim and change only the
`relationalize e` call to `relationalize e { expandOpaqueApps := true }`. (If you'd rather combine it
with proof mode, set both fields: `{ filterProofs := false, expandOpaqueApps := true }`.)

There's no per-`with` boolean-flag syntax today, so a dedicated command is the path of least
resistance and matches the existing `#spytial.proof` / `#spytial.datum` convention. If you prefer a
single command with options instead of a family of `#spytial.*` variants, that's a larger syntax
change — not recommended for a first pass.

### Step 4 — rebuild and test

The relationalizer is Lean-only (no widget/JS change needed — this only affects the atoms/relations
emitted). Rebuild spytial-lean (`lake build`) and, from Palamedes, bump the dependency if it's pinned
(`lake update spytialLean`). Then:

```lean
#spytial.apps  someValueContainingAnOpaqueCall
#spytial.datum someValueContainingAnOpaqueCall   -- still shows the OLD leaf form (default flag), good for A/B
```

## Alternative: do it locally in a custom relationalizer (no library change)

If you only want this behavior for one type and don't want to fork spytial-lean, replicate the Step-2
loop inside a `CustomRelationalizer` for that type (you have `e.getAppArgs` and the passed `recurse`
there too). That keeps the change in Palamedes. The library change is only worth it if you want the
expansion to apply globally across all types.
