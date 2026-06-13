import Palamedes.Gen
import Palamedes.Support
import Palamedes.OptimizeCongr

open Lean Elab Command Term Meta Gen

/-!
# Correct-by-Construction Optimizer

`optimizeGen` optimizes a generator, ideally with the goal of bubbling any `assume` statements up to
the nearest choice point and removing unnecessary backtracking. The optimizer is
correct-by-construction and builds a proof of corectness as it goes.
-/

/-- A rewrite result: the rewritten expression `expr` and the twin `support_*` lemma that justifies
it. The lemma's orientation (whether it is stated `support <original> = support expr` or the other
way round) is recovered when the proof is built, in `mkLeafProof`. -/
abbrev GenRewriteResult := Expr × Name

mutual

/-- Can some `assume` inside `e` bubble up to the *head* of `e`?

We descend the spine, accumulating in `crossed` the value-binders introduced on the way (those a
`bind` continuation binds). On reaching `assume b _`, the guard `b` reaches the head iff it mentions
none of them. Each case mirrors the lift lemma that would fire:

* `bind x f` — descend the scrutinee `x` (`support_assume_bind` lifts unconditionally) and the
  continuation under its binder `a` (`support_bind_assume` lifts iff the guard avoids `a`). When `x`
  is `pure a₀` we descend `f a₀` instead: `support_pure_bind` fires first, so a guard that mentioned
  the bound value becomes concrete and may now lift.
* `pick x y` — descend both arms. An assume in a single arm clears the pick
  by degrading to a `dite` (`support_assume_pick`); when both arms share the guard it lifts cleanly
  (`support_pick_assume_same`). Either outcome is wanted, so single-arm hits count.
* `dite`/`ite` — descend the branches (their proof binders never enter `crossed`).
* `indexed` — opaque barrier: a guard inside the fueled fixpoint is re-asserted per unfolding and
  cannot be hoisted.
* `ret`, or any non-`Gen` head — nothing to lift. -/
partial def assumeReachesHead (e : Expr) (crossed : Array FVarId) : MetaM Bool := do
  match_expr ← withReducible (reduce e) with
  | assume _ b g =>
    if crossed.all (fun fv => !b.containsFVar fv) then return true
    else assumeUnderBinder g crossed        -- a deeper assume commutes up past this stuck one
  | bind _ _ _ _ x f =>
    match_expr x with
    | pure _ _ _ a => assumeReachesHead (f.beta #[a]) crossed
    | _ => return (← assumeReachesHead x crossed) || (← assumeUnderBinder f crossed)
  | pick _ x y => return (← assumeReachesHead x crossed) || (← assumeReachesHead y crossed)
  | dite _ _ _ t f => return (← assumeUnderBinder t crossed) || (← assumeUnderBinder f crossed)
  | ite _ _ _ t f => return (← assumeReachesHead t crossed) || (← assumeReachesHead f crossed)
  | indexed _ _ => return false
  | _ => return false

/-- Descend under one leading binder. A value binder enters `crossed` (a guard may depend on it); a
proof binder (from `assume`/`dite`) does not — guards are `Bool`, so by proof irrelevance they
cannot mention it. -/
partial def assumeUnderBinder (f : Expr) (crossed : Array FVarId) : MetaM Bool := do
  forallBoundedTelescope (← inferType f) (some 1) fun xs _ => do
    let #[x] := xs | return false
    let crossed := if ← Meta.isProof x then crossed else crossed.push x.fvarId!
    assumeReachesHead (f.beta #[x]) crossed

end

/-- Single head rewrite of a `bind` node `x >>= f`. Mirrors the monad-law / commuting rules, and
additionally reports the twin `support_*` lemma proving the rewrite is support-preserving. -/
def optimizeBind? (x f : Expr) : MetaM (Option GenRewriteResult) :=
  match_expr x with
  -- pure_bind : pure a >>= f ~~> f a
  | pure _ _ _ a => return some (Expr.app f a, ``support_pure_bind)
  -- bind_bind : (x >>= f) >>= g ~~> x >>= (fun x -> f x >>= g)
  | bind _ _ _ _ x' g => do
    let .forallE _ argTy _ _ ← inferType g | return none
    let f' ← withLocalDecl `a .default argTy fun a => do
      mkLambdaFVars #[a] (← mkAppM ``bind #[.app g a, f])
    return some (← mkAppM ``bind #[x', f'], ``support_bind_bind)
  -- assume_bind : assume b g >>= f ~~> assume b (fun h => g h >>= f)
  | assume _ b g => do
    let f' ← withLocalDecl `h .default (← mkEq b (.const ``true [])) fun h => do
      mkLambdaFVars #[h] (← mkAppM ``bind #[.app g h, f])
    return some (← mkAppM ``assume #[b, f'], ``support_assume_bind)

  -- These three rules push a bind down through a branch (`pick`/`dite`/`ite`), duplicating the
  -- continuation `f`. That only pays off when it lets an `assume` bubble up past the branch, so each
  -- is gated on `assumeReachesHead`: distribute iff a resulting arm exposes a liftable assume.
  -- Branches with nothing to harvest are left alone — which is what bounds the term-size blowup that
  -- distributing nested `pick`s would otherwise cause.
  | pick _ x y => do
    let xb ← mkAppM ``bind #[x, f]
    let yb ← mkAppM ``bind #[y, f]
    unless (← assumeReachesHead xb #[]) || (← assumeReachesHead yb #[]) do return none
    return some (← mkAppM ``pick #[xb, yb], ``support_pick_bind)
  | dite _ P _ trueCase falseCase => do
    let trueCase' ← withLocalDecl `h .default P fun h => do
      mkLambdaFVars #[h] (← mkAppM ``bind #[.app trueCase h, f])
    let falseCase' ← withLocalDecl `h .default (.app (.const ``Not []) P) fun h => do
      mkLambdaFVars #[h] (← mkAppM ``bind #[.app falseCase h, f])
    unless (← assumeUnderBinder trueCase' #[]) || (← assumeUnderBinder falseCase' #[]) do return none
    return some (← mkAppM ``dite #[P, trueCase', falseCase'], ``support_if_bind)
  | ite _ P _ trueCase falseCase => do
    let trueCase' ← mkAppM ``bind #[trueCase, f]
    let falseCase' ← mkAppM ``bind #[falseCase, f]
    unless (← assumeReachesHead trueCase' #[]) || (← assumeReachesHead falseCase' #[]) do return none
    return some (← mkAppM ``ite #[P, trueCase', falseCase'], ``support_ite_bind)

  | _ => do
    lambdaBoundedTelescope f 1 fun args body => do
      -- bind_assume : x >>= fun a => assume b g ~~> assume b (fun h => (x >>= fun a => g h))
      --               (where a is not free in b)
      let #[a] := args | return none
      let_expr assume _ b g := body | return none

      -- We may only float `assume b …` above the binder for `a` if `b` doesn't mention `a` (a
      -- scoping requirement). This is conservative: a `b` that's a metavariable possibly depending
      -- on `a` slips past `containsFVar`, so we skip the rewrite rather than risk a malformed term.
      if b.containsFVar a.fvarId! then return none

      let f' ← withLocalDecl `h .default (← mkEq b (.const ``true [])) fun h => do
        mkLambdaFVars #[h] (← mkAppM ``bind #[x, ← mkLambdaFVars #[a] (.app g h)])
      return some (← mkAppM ``assume #[b, f'], ``support_bind_assume)

/-- Single head rewrite of a `pick` node `pick x y`. Reports the twin `support_*` lemma alongside
the rewritten expression. -/
def optimizePick? (x y : Expr) : MetaM (Option GenRewriteResult) :=
  match_expr x with
  | assume _ b f =>
    match_expr y with
    | assume _ b' g =>
      -- if both x and y are `assume`s, then we have one of two cases:
      -- if they assume the same boolean:
        -- assume_pick : pick (assume b f) (assume b g) ~~> assume b (pick f g)
      if b == b' then do
        let c ← mkEq b (.const ``true [])
        let f' ← withLocalDecl `h .default c fun h => do
          mkLambdaFVars #[h] (← mkAppM ``pick #[.app f h, .app g h])
        return some (← mkAppM ``assume #[b, f'], ``support_pick_assume_same)
      -- otherwise they assume different booleans:
        -- assume_pick : pick (assume b f) y ~~> if h : b then pick (f h) y else y
      else do
        let c ← mkEq b (.const ``true [])
        let fPos ← withLocalDecl `h .default c fun h => do
          mkLambdaFVars #[h] (← mkAppM ``pick #[.app f h, y])
        let fNeg ← withLocalDecl `h .default (.app (.const ``Not []) c) fun h =>
          mkLambdaFVars #[h] y
        return some (← mkAppM ``dite #[c, fPos, fNeg], ``support_assume_pick)
    -- if only x is an `assume`:
      -- assume_pick : pick (assume b f) y ~~> if h : b then pick (f h) y else y
    | _ => do
      let c ← mkEq b (.const ``true [])
      let fPos ← withLocalDecl `h .default c fun h => do
        mkLambdaFVars #[h] (← mkAppM ``pick #[.app f h, y])
      let fNeg ← withLocalDecl `h .default (.app (.const ``Not []) c) fun h =>
        mkLambdaFVars #[h] y
      return some (← mkAppM ``dite #[c, fPos, fNeg], ``support_assume_pick)
  | _ =>
    match_expr y with
    -- if only y is an `assume`:
      -- pick_assume : pick x (assume b f) ~~> if h : b then pick x (f h) else x
    | assume _ b f => do
      let c ← mkEq b (.const ``true [])
      let fPos ← withLocalDecl `h .default c fun h => do
        mkLambdaFVars #[h] (← mkAppM ``pick #[x, .app f h])
      let fNeg ← withLocalDecl `h .default (.app (.const ``Not []) c) fun h =>
        mkLambdaFVars #[h] x
      return some (← mkAppM ``dite #[c, fPos, fNeg], ``support_pick_assume)
    | _ => return none

/-! ## Proof-carrying traversal -/

/-- `support e`. -/
private def mkSupport (e : Expr) : MetaM Expr := mkAppM ``Gen.support #[e]

/-- `rfl : support e = support e`. -/
private def mkSupportRefl (e : Expr) : MetaM Expr := do mkEqRefl (← mkSupport e)

/-- `fun xs => rfl : ∀ xs, support (f xs) = support (f xs)`, for an unchanged (possibly
multi-argument) binder `f` whose codomain is a `Gen`. -/
private def mkBinderRefl (f : Expr) : MetaM Expr := do
  forallTelescope (← inferType f) fun xs _ => do
    mkLambdaFVars xs (← mkSupportRefl (f.beta xs))

/-- Prove `support lhs = support rhs` using the twin lemma `lemmaName`, in whichever orientation it
is stated. -/
private def mkLeafProof (lemmaName : Name) (lhs rhs : Expr) : MetaM Expr := do
  let lhsS ← mkSupport lhs
  let rhsS ← mkSupport rhs
  -- Fresh lemma instance per attempt, so a failed `isDefEq` can't pollute the next one (the goal
  -- itself is metavariable-free).
  let tryOrient (a b : Expr) : MetaM (Option Expr) := do
    let lem ← mkConstWithFreshMVarLevels lemmaName
    let (mvars, _, concl) ← forallMetaTelescope (← inferType lem)
    if ← isDefEq concl (← mkEq a b) then return some (← instantiateMVars (mkAppN lem mvars))
    else return none
  if let some pf ← tryOrient lhsS rhsS then return pf
  if let some pf ← tryOrient rhsS lhsS then return (← mkEqSymm pf)
  throwError "optimizer: twin lemma `{lemmaName}` matches neither orientation of goal\
    {indentExpr (← mkEq lhsS rhsS)}"

/-- Lift the child proofs `hyps` through a constructor with congruence lemma `lemmaName`, proving
`support node = support node'`. The lemma's structural arguments are solved by unifying its
conclusion with the (concrete) goal; whatever binders that leaves unassigned are exactly the
congruence hypotheses, which we discharge with `hyps`. Each hypothesis is matched to a child proof
*by type* rather than by position, so the lemma's hypothesis order need not track its argument
order. This tolerates implicit and interleaved hypotheses (e.g. `support_caseTy_congr`). -/
private def mkCongrProof (lemmaName : Name) (node node' : Expr) (hyps : Array Expr) : MetaM Expr := do
  let goal ← mkEq (← mkSupport node) (← mkSupport node')
  let lem ← mkConstWithFreshMVarLevels lemmaName
  let (mvars, _, concl) ← forallMetaTelescope (← inferType lem)
  unless ← isDefEq concl goal do
    throwError "optimizer: congruence lemma `{lemmaName}` does not match goal{indentExpr goal}"
  let mut hypMvars := #[]
  for m in mvars do
    unless ← m.mvarId!.isAssigned do
      hypMvars := hypMvars.push m
  unless hypMvars.size == hyps.size do
    throwError "optimizer: `{lemmaName}` expects {hypMvars.size} hypotheses, given {hyps.size}"
  let mut pool := hyps.toList
  for m in hypMvars do
    let mut rest : List Expr := []
    let mut matched := false
    for h in pool do
      if !matched && (← isDefEq m h) then
        matched := true
      else
        rest := rest ++ [h]
    unless matched do
      throwError "optimizer: no child proof discharges a hypothesis of `{lemmaName}`"
    pool := rest
  instantiateMVars (mkAppN lem mvars)

/-- The result of optimizing a subterm: the rewritten `expr` and, when something changed, a proof
that `support <input> = support expr` (`none` means the term is unchanged, i.e. `rfl`). -/
private structure OptResult where
  expr : Expr
  proof? : Option Expr

/-- Compose a chain of optional `support`-equality proofs with `Eq.trans`, dropping the `rfl`
(`none`) links. The shared midpoints are defeq, so `Eq.trans` type-checks across `none` gaps. -/
private def chainProofs (ps : Array (Option Expr)) : MetaM (Option Expr) :=
  ps.foldlM (init := none) fun acc p =>
    match acc, p with
    | none, x => pure x
    | some a, none => pure (some a)
    | some a, some b => some <$> mkEqTrans a b

/-- Is `e` a `Gen` or a (curried) function returning a `Gen`? Used to decide, at a node the
optimizer cannot descend through, whether there was actually anything to descend into. -/
private def isGenValued (e : Expr) : MetaM Bool := do
  forallTelescopeReducing (← inferType e) fun _ body => do
    let head := body.getAppFn
    return head.isConstOf ``Gen || head.isConstOf ``Raw.Gen

mutual

/-- Reduce `e0` (so `match_expr` sees through reducible defs) and optimize it to a fixed point,
returning the rewritten term and a proof that its `support` is unchanged. -/
private partial def optimize (table : Array CongrRule) (e0 : Expr) : MetaM OptResult := do
  optimizeReduced table (← withReducible (reduce e0))

/-- Optimize `e`, which is assumed *already reduced*. Optimize children (their subterms are already
reduced too), attempt one head rewrite, and — since a rewrite can introduce new redexes (e.g. the
`pure a >>= f ~> f a` beta) — re-`optimize` (re-reduce) the result. Reducing only here and at the
top avoids re-reducing each subtree once per level of depth. -/
private partial def optimizeReduced (table : Array CongrRule) (e : Expr) : MetaM OptResult := do
  let cong ← optimizeChildren table e
  match ← tryHeadRewrite cong.expr with
  | none => return cong
  | some (e', headPf) =>
    let rest ← optimize table e'
    let proof? ← chainProofs #[cong.proof?, some headPf, rest.proof?]
    return { expr := rest.expr, proof? }

/-- Optimize the children of `e` and reassemble, proving the result has the same `support` via the
`@[gen_congr]` lemma registered for `e`'s head constant. No head rewrite is attempted here. This
single generic case subsumes every `Gen` constructor and recursion-scheme combinator.

If `e`'s head has no registered congruence lemma, skipping is correct *only* when there is nothing
to descend into; if `e` carries a `Gen`-valued argument we would silently drop an optimization (and
potentially mask synthesis residue), so we fail loudly instead — the fix is to tag that head's
support-congruence lemma `@[gen_congr]`. -/
private partial def optimizeChildren (table : Array CongrRule) (e : Expr) : MetaM OptResult := do
  let some head := e.getAppFn.constName? | return { expr := e, proof? := none }
  let some (_, congrName, diff) := table.find? (·.1 == head)
    | do
        -- Compiler-generated eliminators (matchers, recursors) carry Gen-valued arms but are
        -- descended into structurally by neither the old nor the new optimizer; don't flag them.
        -- For an *ordinary* combinator a Gen-valued argument with no congruence lemma signals a
        -- missing `@[gen_congr]` tag, so fail loudly rather than silently skipping it.
        let isRec := match (← getEnv).find? head with
          | some (.recInfo _) => true
          | _ => false
        let auxiliary := (← Meta.getMatcherInfo? head).isSome || isRec
        if !auxiliary && (← e.getAppArgs.anyM isGenValued) then
          throwError "optimizer: `{head}` has a Gen-valued argument but no `@[gen_congr]` \
            congruence lemma to descend through it; tag its support-congruence lemma `@[gen_congr]`"
        return { expr := e, proof? := none }
  let args := e.getAppArgs
  let mut newArgs := args
  let mut hyps := #[]
  let mut changed := false
  for i in diff do
    let (arg', h?) ← optimizeBinder table args[i]!
    newArgs := newArgs.set! i arg'
    match h? with
    | some h => hyps := hyps.push h; changed := true
    | none   => hyps := hyps.push (← mkBinderRefl args[i]!)
  unless changed do return { expr := e, proof? := none }
  let node' := mkAppN e.getAppFn newArgs
  return { expr := node', proof? := some (← mkCongrProof congrName e node' hyps) }

/-- Optimize a child argument: under any leading binders (`f : dom₁ → … → Gen _`) when it is a
function, or directly when it is a plain `Gen`. Returns the rebuilt argument and, when something
changed, a proof `∀ xs, support (arg xs) = support (arg' xs)`. -/
private partial def optimizeBinder (table : Array CongrRule) (f : Expr) : MetaM (Expr × Option Expr) := do
  forallTelescope (← inferType f) fun xs _ => do
    -- `f` is a subterm of an already-reduced node, so `f.beta xs` is reduced (the substituted `xs`
    -- are atomic fvars); descend with `optimizeReduced` to avoid re-reducing it.
    let r ← optimizeReduced table (f.beta xs)
    let f' ← mkLambdaFVars xs r.expr
    match r.proof? with
    | none => return (f', none)
    | some p => return (f', some (← mkLambdaFVars xs p))

/-- Attempt a single head rewrite on `e`, returning the rewritten term and a proof
`support e = support e'`. -/
private partial def tryHeadRewrite (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let res? ←
    match_expr e with
    | bind _ _ _ _ x f => optimizeBind? x f
    | pick _ x y => optimizePick? x y
    | _ => pure none
  match res? with
  | none => return none
  | some (e', lemmaName) => return some (e', ← mkLeafProof lemmaName e e')

end

/-- Optimize a raw `Gen` term, returning the optimized term together with a proof that its
`support` equals that of the input. -/
def optimizeGen (e : Expr) : MetaM (Expr × Expr) := do
  let r ← optimize (getGenCongrRules (← getEnv)) e
  let proof ←
    match r.proof? with
    | some p => mkExpectedTypeHint p (← mkEq (← mkSupport e) (← mkSupport r.expr))
    | none => mkSupportRefl e
  return (r.expr, proof)
