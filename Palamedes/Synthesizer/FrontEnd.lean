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

set_option pp.sanitizeNames true in
open PrettyPrinter Lean.Parser.Tactic in
def fmtTactic
  (t : TSyntax `tactic)
  (subgoals : List MVarId)
  (continuation : String) : String :=
    let prettyT :=
      match t.raw.reprint with
      | some x => x
      | none => t.raw.prettyPrint.pretty -- TODO
    match subgoals with
    | [] => prettyT
    | [_] => prettyT ++ "\n  " ++ continuation
    | _ =>
      let continuations := subgoals.map (fun _ => "\n  ." ++ continuation)
      let continuationsCat := continuations.foldr (· ++ ·) ""
      prettyT ++ continuationsCat

def suggestTacticOptions
  (stx : Syntax)
  (rs : List (TSyntax `tactic × List MVarId))
  (continuation: String)
  : MetaM Unit := do
  match rs with
  | [] => throwError "Empty tactic list; nothing to suggest."
  | [(t, [])] =>
    TryThis.addSuggestion stx
      s!"{fmtTactic t [] continuation}"
  | [(t, gs)] =>
    TryThis.addSuggestion stx
      s!"{fmtTactic t gs continuation}"
  | _ =>
    match rs.find? (fun (_, unsolved) => List.length unsolved == 0) with
    | some (t, gs) =>
      TryThis.addSuggestion stx s!"{fmtTactic t gs continuation}"
    | none => do
      let prettyRs ← rs.mapM
        (fun (t, gs) => return fmtTactic t gs continuation)
      TryThis.addSuggestions stx prettyRs.toArray (header := "Try one of:")

def peekTactic (tactic : TSyntax `tactic) (g : MVarId) : TacticM (Option (List MVarId)) := do
  let prettyT := fmtTactic tactic [] ""-- TODO
  let s ← saveState
  try
    let unsolved ← evalTacticAt tactic g
    match unsolved with
    | [g'] => do
      let τ ← g.getType
      let τ' ← g'.getType
      let unchanged ← withoutModifyingState $ Lean.Meta.isDefEq τ τ'
      if unchanged then
        IO.println s!"1: did NOT catch exception for {prettyT}"
        pure none
      else
        IO.println s!"2: did NOT catch exception for {prettyT}"
        pure $ some unsolved
    | _ =>
      IO.println s!"3: did NOT catch exception for {prettyT}; num subgoals: {unsolved.length}"
      pure $ some unsolved
  catch _ =>
    IO.println s!"4: caught exception for {prettyT}"
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
        let prettyTs ← ts.mapM (fun t => return fmtTactic t [] "")
        suggestTacticOptions stx rs s!"step {prettyTs}"
  | _ => throwUnsupportedSyntax

set_option linter.unusedTactic false
example : forall x, x + 0 = x := by
  step [intro, intro, rfl]
  sorry

example : exists x, x > 0 := by
  step [intro, rfl, aesop, exists 1]
  sorry

example : 5 = 5 ∧ 1 = 1 := by
  step [apply And.intro, rfl]
  sorry

example : ∃ x, x + 1 = 3 := by
  refine Exists.intro ?x ?p <;> try (exact rfl)

end step

section gstep

macro "gstep" : tactic =>

  `(tactic| step [
    ((repeat apply duncurry); intro), --4
    (apply convert (by norm_for_pure) (s_pure _)), --3
    (assumption), --4
    (apply convert (by norm_for_pick) (s_pick _ _)), --3
    (apply convert (by norm_for_bind) (s_bind _ _)), --3
    (apply convert (by norm_for_bind') (s_bind _ _)), --3 -- TODO Fix this
    (goal_is_eq_or_and; apply convert (by norm_for_List_unfold) (List.s_unfold _)), --4
    (goal_is_eq_or_and; apply convert (by norm_for_Tree_unfold) (Tree.s_unfold _)), --4
    (goal_is_eq_or_and; apply convert (by norm_for_Stack_unfold) (Stack.s_unfold _)), --4
    (goal_is_eq_or_and; apply convert (by norm_for_Term_unfold) (Term.s_unfold _)), --4
    (apply s_arbUnit), --3
    (apply s_arbBool), --3
    (apply s_arbNat), --3
    (apply s_arbTy), --3
    (apply s_arbLabel), --3
    (apply s_arbAtom _), --3
    (apply s_gt), --3
    (apply s_lt_partial), --3
    (apply s_between_partial), --3
    (apply (s_between (by first | aesop | omega))), --3
    (apply convert (by norm_for_elements) (s_elements_partial _)),--3
    (goal_is_or; clear_unused_assumptions; apply s_caseBool (by nth_assumption 0) (by intros; rflm)),--3
    (goal_is_or; clear_unused_assumptions; apply s_caseBool (by nth_assumption 1) (by intros; rflm)),--3
    (goal_is_or; clear_unused_assumptions; apply s_caseTy (by nth_assumption 0) (by intros; rflm)),--3
    (goal_is_or; clear_unused_assumptions; apply s_caseTy (by nth_assumption 1) (by intros; rflm)),--3
    (goal_is_or; clear_unused_assumptions; apply s_caseNat (by nth_assumption 0) (by intros; rflm)),--3
    (goal_is_or; clear_unused_assumptions; apply s_caseNat (by nth_assumption 1) (by intros; rflm))])--3

end gstep
