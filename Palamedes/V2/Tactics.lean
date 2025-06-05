import Aesop
import Palamedes.V2.Gen
import Palamedes.V2.CorrectGen
import Palamedes.V2.Optimizer
import Palamedes.V2.Total
import Palamedes.V2.Data.List

open Lean Tactic Elab Meta Tactic

macro "cgenerator_search" : tactic =>
  `(tactic|
    aesop
      (rule_sets := [-default, -builtin, synthesis])
      (config := {enableSimp := false}))

macro "totality" : tactic =>
  `(tactic|
    aesop
      (rule_sets := [totality]))

-- TODO: This is probably not good enough. If the optimizer fails to prove goals we care about, we
-- probably want to revisit this.
macro "optimality" : tactic =>
  `(tactic|
    aesop
      (add safe (by omega))
      (add unsafe congrFun)
      (add unsafe congrArg))

elab "optimize_gen " t:term : tactic =>
  withMainContext do
    let g ← getMainGoal
    let m ← mkFreshExprMVar none
    let gen ← elabTerm t (some (.app (.const ``Gen []) m))
    let gen' ← withReducible (reduce gen)
    let gen'' ← optimizeGen gen'
    let gen''' ← withReducible (reduce gen'')
    g.assign gen'''

-- Borrowed from Aesop
def printAsMillis (n : Nat) : String :=
  let str := toString (n.toFloat / 1000000)
  match str.split λ c => c == '.' with
  | [beforePoint] => beforePoint ++ "ms"
  | [beforePoint, afterPoint] => beforePoint ++ "." ++ afterPoint.take 1 ++ "ms"
  | _ => unreachable!

open Lean Tactic Elab Meta Tactic in
def solveGoalWithTactic (goalType : Expr) (tactic : TSyntax `tactic) : TacticM Expr := do
  let m ← mkFreshExprMVar goalType
  let unsolved ← evalTacticAt tactic m.mvarId!
  if unsolved.length > 0 then do
    throwError "goals left unsolved: {unsolved}"
  instantiateMVars m

register_option palamedes.debug : Bool := {
  defValue := false
  group := "palamedes"
  descr := "enable debug messages from palamedes"
}

register_option palamedes.timing : Bool := {
  defValue := false
  group := "palamedes"
  descr := "enable timing messages from palamedes"
}

def generatorSearchElab
    (stx : Syntax)
    (t : Term)
    (checkTotal : Bool)
    (tryThis : Bool) :
    TacticM Unit := do
  let opts ← getOptions
  let verbose := palamedes.debug.get opts
  let printTiming := palamedes.timing.get opts

  let startTime ← IO.monoNanosNow

  let g ← getMainGoal
  let .app (.const ``Gen []) α ← g.getType
    | throwError "goal type must be Gen α for some α"
  let ty := .forallE `α α (.sort 0) .default
  let mpred ← elabTerm t (some ty)

  if verbose then do
    TryThis.addSuggestion stx
      s!"-- generator_search ({← ppExpr mpred})
  let cg : CorrectGen ({← ppExpr mpred}) := by
    cgenerator_search
  let g : Gen ({← ppExpr α}) := by
    optimize_gen cg.val
  let _ : support cg.val = support g := by
    optimality
  let _ : Gen.total g := by
    totality
  exact g"

  -- Synthesize a correct generator by solving `CorrectGen P` and projecting the `.val`.
  let gen ← do
    try
      let cgen ← solveGoalWithTactic
        (mkAppN (.const ``CorrectGen []) #[α, mpred])
        (← `(tactic| cgenerator_search))
      withReducible (reduce (← mkAppM ``Subtype.val #[cgen]))
    catch e =>
      throwError m!"Failed during generator synthesis.\n{e.toMessageData}"
  if verbose then do
    logInfo m!"Synthesized generator:\n{(← ppExpr gen)}"

  -- Optimize the generator and prove that the optimized version is correct.
  let gen' ←
    try
      let gen' ← optimizeGen gen
      let gen' ← withReducible (reduce gen')
      let _ ← solveGoalWithTactic
        (← mkEq (← mkAppM ``Gen.support #[gen]) (← mkAppM ``Gen.support #[gen']))
        (← `(tactic| optimality))
      pure gen'
    catch e =>
      throwError m!"Failed during optimization.\n{e.toMessageData}"
  if verbose then do
    logInfo m!"Optimized generator:\n{(← ppExpr gen')}"

  -- Optionally: Check that the generator is "total," i.e., that it does not backtrack internally.
  if checkTotal then do
    try
      let _ ← solveGoalWithTactic
        (← mkAppM ``Gen.total #[gen'])
        (← `(tactic| totality))
    catch e =>
      logWarning m!"Failed during totality checking.
      {e.toMessageData}
      {gen'}
      could not be proved total.

      You can use `generator_search {t} allow_partial to turn off this check."

  if printTiming then do
    let endTime ← IO.monoNanosNow
    let elapsed := endTime - startTime
    logInfo m!"Synthesis for {← ppExpr mpred} took {printAsMillis elapsed}"

  if tryThis then
    withOptions ((pp.proofs.set · true) ∘ (pp.fieldNotation.generalized.set · false)) do
      TryThis.addExactSuggestion stx gen'

  closeMainGoal `generator_search gen'

syntax (name := generatorSearch) "generator_search " term " allow_partial"? : tactic

@[tactic generatorSearch]
def expandGeneratorSearch : Tactic := fun stx =>
  match stx with
  | `(tactic| generator_search $t allow_partial) =>
    generatorSearchElab stx t false false
  | `(tactic| generator_search $t) =>
    generatorSearchElab stx t true false
  | _ => throwError "invalid syntax"

syntax (name := generatorSearch?) "generator_search? " term " allow_partial"? : tactic

@[tactic generatorSearch?]
def expandGeneratorSearch? : Tactic := fun stx =>
  match stx with
  | `(tactic| generator_search? $t allow_partial) =>
    generatorSearchElab stx t false true
  | `(tactic| generator_search? $t) =>
    generatorSearchElab stx t true true
  | _ => throwError "invalid syntax"
