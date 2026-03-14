import Lean
import Aesop

open Lean Tactic Elab Meta Tactic

-- From Kyle Miller

def ensureLHSIsMVar (g : MVarId) : MetaM (Expr × Expr × MVarId) :=
  g.withContext do
    let gty ← g.getType'
    let some (_, lhs, rhs) := gty.eq? | throwError "goal must be eq"
    let lhs ← whnfCore lhs
    if lhs.getAppFn.isMVar then
      return (lhs, rhs, g)
    let rhs ← whnfCore rhs
    if rhs.getAppFn.isMVar then
      let [g] ← g.applyConst ``Eq.symm | throwError "failure to apply Eq.symm"
      return (rhs, lhs, g)
    throwError "neither the LHS nor the RHS is a metavariable application"

/--
Replace each expr in `exprs` with the corresponding fvar in `fvars` by using `kabstract`,
and then creates a lambda that closes the fvars.
Throws an error if the result is not type correct.
Returns a lambda, like `mkLambdaFVars fvars e`.
-/
def mkLambdaGeneralizeFVars (exprs : Array Expr) (fvars : Array Expr) (e : Expr) : MetaM Expr := do
  let e ← (exprs.zip fvars).foldrM (init := e) fun (expr, fvar) e => do
    let e' ← kabstract e expr
    pure <| e'.instantiate1 fvar
  unless ← isTypeCorrect e do
    throwError "failed to generalize expression"
  return (← getLCtx).mkBinding (isLambda := true) fvars e

elab "rflm" : tactic => do
let g ← popMainGoal
  let (lhs, rhs, g) ← ensureLHSIsMVar g
  g.withContext do
    let m := lhs.getAppFn.mvarId!
    if ← m.isDelayedAssigned then
      -- We could probably try to handle these, but an error for now.
      throwError "metavariable is delayed assigned"
    let args ← lhs.getAppArgs.mapM instantiateMVars
    -- Enter a telescope for the mvar type.
    -- We will replace each `arg` with the corresponding `fvar` while using `kabstract`.
    -- This makes sure that when we do `mkLambdaFVars` that we get a function with
    -- the right type.
    forallBoundedTelescope (← m.getType) args.size fun fvars _ => do
      let rhs ← instantiateMVars rhs
      let rhs' ← mkLambdaGeneralizeFVars args fvars rhs
      unless ← m.checkedAssign rhs' do
        throwError "failed to assign metavariable (due to occurs check or local context mismatches)\n\n\
          Metavariable:{m}\n\
          Value:{indentExpr rhs'}"
    -- Given that that succeeded, now both sides are unified, so Eq.refl must work.
    g.assign (← mkEqRefl rhs)

elab "nth_assumption " n:num : tactic => do
  withMainContext do
    let n := n.getNat
    let goalType ← getMainTarget
    let ctx ← getLCtx
    let ms ← ctx.decls.toList.filterMapM fun decl: Option LocalDecl => do
      let .some decl := decl | return none
      let declExpr := decl.toExpr
      let declType ← inferType declExpr
      if ← isDefEq declType goalType then
        return some declExpr
      return none
    if n >= ms.length then
      throwError "no matching assumption with that index"
    closeMainGoal `assumption_1 ms.reverse[n]!

elab "clear_unused_assumptions" : tactic => do
  withMainContext do
    let g ← getMainGoal
    let goalType ← getMainTarget
    let ctx ← getLCtx
    let g' ← ctx.foldrM (init := g) fun decl (g : MVarId) => do
      if goalType.hasAnyFVar (· == decl.fvarId) then
        pure g
      else
        g.clear decl.fvarId
    replaceMainGoal [g']

elab "unfold_matches" : tactic =>
  withMainContext do
    let goalType ← getMainTarget
    let consts := goalType.getUsedConstants
    let ms := consts.filter (fun n => n.components.any (·.getString!.startsWith "match_"))
    for m in ms do
      unfoldTarget m

open LibrarySearch
elab "library_search" : tactic =>
  withMainContext do
    let g ← getMainGoal
    let tactic := fun exfalso =>
      solveByElim [] (exfalso := exfalso) (maxDepth := 6)
    match ← librarySearch g tactic (fun _ => pure false) with
    | none => pure ()
    | some _ => throwError "library_search failed"

/-- Extracts the conjuncts of an ∧-expression.

    NOTE: This needs to be in `MetaM`, although I'm not 100% sure why. I think it may have
    something to do with how `match_expr` works under the hood? -/
partial def getConjuncts (e : Expr) : MetaM (List Expr) := do
  match_expr e with
  | And p q => return (← getConjuncts p) ++ (← getConjuncts q)
  | _ => return [e]

/-- Proves a goal of the form `?a ∧ ?b = e` by partitioning the conjuncts in `e` based on whether or
  not they contain `v`.

  E.g., the goal `?a ∧ ?b = v < 3 ∧ x = 5 ∧ 1 < v` is solved with
  ```
  ?a = (x = 5)
  ?b = (v < 3 ∧ 1 < v)
  ```
  -/
elab "partition_conjuncts " v:ident : tactic =>
  withMainContext do
    let g ← getMainGoal
    let goalDecl ← g.getDecl
    let goalTy := goalDecl.type
    let var ← elabAsFVar v
    match_expr goalTy with
    | Eq _α _lhs rhs =>
      -- Get and partition the conjuncts
      let conjuncts ← getConjuncts rhs
      let (varIn, varNotIn) := conjuncts.partition (·.containsFVar var)

      -- Create a new `rhs` with the appropriate grouping of conjuncts
      let rhs' := mkAppN (.const ``And []) #[
          varNotIn.foldr (fun a b => mkAppN (.const ``And []) #[a, b]) (.const ``True []),
          varIn.foldr (fun a b => mkAppN (.const ``And []) #[a, b]) (.const ``True []),
        ]

      -- Assert that our goal's type is actually `rhs' = rhs` and prove the equality with aesop
      let goalTy' ← mkAppM ``Eq #[rhs', rhs]
      if ← isDefEq goalTy goalTy' then
        let ([], _) ← runTactic g (← `(tactic| aesop))
          | throwError "aesop could not prove {← instantiateMVars goalTy'}"

    | _ => pure ()


theorem exists_swap_2nd' {α β : Type}(P : α → β → Prop) : (∃ x: α, ∃ y: β, P x y) = (∃ y: β, ∃ x: α, P x y) := by
 simp_all only [eq_iff_iff]
 apply Iff.intro
 · intro a
   obtain ⟨w, h⟩ := a
   obtain ⟨w_1, h⟩ := h
   apply Exists.intro
   · apply Exists.intro
     · exact h
 · intro a
   obtain ⟨w, h⟩ := a
   obtain ⟨w_1, h⟩ := h
   apply Exists.intro
   · apply Exists.intro
     · exact h

syntax "exists_swap_2nd" : tactic
macro_rules
| `(tactic| exists_swap_2nd) => `(tactic| conv => congr; intro v; rw[exists_swap_2nd'])

theorem exists_swap_3rd' {α β γ : Type}(P : α → β → γ → Prop) : (∃ x: α, ∃ y : β, ∃ z : γ,  P x y z) = (∃ z : γ, ∃ x: α, ∃ y: β,  P x y z) := by
  simp_all only [eq_iff_iff]
  apply Iff.intro
  · intro a
    obtain ⟨w, h⟩ := a
    obtain ⟨w_1, h⟩ := h
    obtain ⟨w_2, h⟩ := h
    apply Exists.intro
    · apply Exists.intro
      · apply Exists.intro
        · exact h
  · intro a
    obtain ⟨w, h⟩ := a
    obtain ⟨w_1, h⟩ := h
    obtain ⟨w_2, h⟩ := h
    apply Exists.intro
    · apply Exists.intro
      · apply Exists.intro
        · exact h

syntax "exists_swap_3rd" : tactic
macro_rules
| `(tactic| exists_swap_3rd) => `(tactic| conv => congr; intro v; rw[exists_swap_3rd'])
