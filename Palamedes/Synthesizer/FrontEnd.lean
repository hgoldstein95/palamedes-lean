import Palamedes.Gen
import Palamedes.CorrectGen
import Palamedes.Optimizer
import Palamedes.Synthesizer.CGeneratorSearch
import Palamedes.Synthesizer.Optimality
import Palamedes.Synthesizer.Totality

open Lean Tactic Elab Meta Tactic

initialize
  registerTraceClass `palamedes.synthesis

register_option palamedes.debug : Bool := {
  defValue := false
  group := "palamedes"
  descr := "enable debug messages from palamedes"
}

/-- This is just a utility tactic for debugging. We don't call it in the real synthesizer. -/
elab "optimize_gen " t:term : tactic =>
  withMainContext do
    let m ← mkFreshExprMVar (some (.sort 0))
    let gen ← elabTerm t (some (.app (.const ``Gen []) m))
    let gen' ← withReducible (reduce gen)
    let gen'' ← optimizeGen gen'
    let gen''' ← withReducible (reduce gen'')
    closeMainGoal `optimize_gen gen'''

def solveGoalWithTactic (goalType : Expr) (tactic : TSyntax `tactic) : TacticM Expr := do
  let m ← mkFreshExprMVar goalType
  let unsolved ← evalTacticAt tactic m.mvarId!
  if unsolved.length > 0 then do
    throwError "goals left unsolved: {unsolved}"
  instantiateMVars m

def generatorSearchElab
    (stx : Syntax)
    (t : Lean.Term)
    (checkTotal : Bool)
    (tryThis : Bool) :
    TacticM Unit := do
  let opts ← getOptions
  let verbose := palamedes.debug.get opts

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

  let prettyPred ←
    try
      lambdaBoundedTelescope mpred 1 fun fvs body =>
        let a := fvs[0]!
        let subst := FVarSubst.empty
        let tgt := Expr.fvar (FVarId.mk `TARGET)
        return (subst.insert a.fvarId! tgt).apply body
    catch _ =>
      pure mpred

  withTraceNode `palamedes.trace (fun _ => pure m!"⟪{α}⟫⟪{prettyPred}⟫") do

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

section step

syntax (name := step) "step" "["tactic,*"]": tactic

open PrettyPrinter Lean.Parser.Tactic in
def fmtTactic (t : TSyntax `tactic) := do
    let prettyT ← ppCategory ``tacticSeq t
    return prettyT.pretty

def fmtTacticWithContinuation
  (t : TSyntax `tactic)
  (continuation : String) := do
    let prettyT ← fmtTactic t
    return prettyT ++ continuation

def suggestTacticOptions
  (stx : Syntax)
  (rs : List (TSyntax `tactic × List MVarId))
  (continuation: String)
  : MetaM Unit := do
  match rs with
  | [] => throwError "Empty tactic list; nothing to suggest."
  | [(t, [])] =>
    TryThis.addSuggestion stx
      s!"{← fmtTactic t}"
  | [(t, _)] =>
    TryThis.addSuggestion stx
      s!"{← fmtTacticWithContinuation t continuation}"
  | _ =>
    match rs.find? (fun (_, unsolved) => List.length unsolved == 0) with
    | some (t, _) =>
      TryThis.addSuggestion stx s!"{← fmtTactic t}"
    | none =>
      logInfoAt stx "Try one of: "
      let prettyRs ← rs.mapM
        (fun (t, _) => fmtTacticWithContinuation t continuation)
      TryThis.addSuggestions stx prettyRs.toArray (header := "")

def peekTactic (tactic : TSyntax `tactic) (g : MVarId) : TacticM (Option (List MVarId)) := do
  let s ← saveState
  try
    let unsolved ← evalTacticAt tactic g
    match unsolved with
    | [g'] => do
      let τ ← g.getType
      let τ' ← g'.getType
      let unchanged ← withoutModifyingState $ Lean.Meta.isDefEq τ τ'
      if unchanged then
        pure none
      else
        pure $ some unsolved
    | _ => pure $ some unsolved
  catch _ =>
    pure none
  finally
    restoreState s

@[tactic step]
def elabStep : Tactic := fun stx => do
  match stx with
  | `(tactic|step [$tactics:tactic,*]) =>
    let ts := tactics.getElems.toList
    let g ← getMainGoal
    let rs ← List.filterMapM (fun t => do
      let unsolved ← peekTactic t g
      match unsolved with
      | some gs =>
        let res := some (t, gs)
        pure res
      | none => pure none) ts
    if (rs.length == 0)
      then
        if ts.length == 0 then
          throwTacticEx `step g m!"No tactic options provided."
        else throwTacticEx `step g m!"All tactics failed."
      else
        let prettyTs ← ts.mapM (fun t => fmtTactic t)
        suggestTacticOptions stx rs s!"; step {prettyTs}"
  | _ => throwUnsupportedSyntax

set_option linter.unusedTactic false
example : forall x, x + 0 = x := by
  step [intro, rfl]
  sorry

example : exists x, x > 0 := by
  step [intro, rfl, aesop, exists 1]
  sorry

-- when replacing "step" with the tactic, auto-fill bullets with "step" after
-- or actually have a different tactic that will do that
-- look at how to turn aesop output tree into something pretty
-- [harry] quickchick as oracle

end step
