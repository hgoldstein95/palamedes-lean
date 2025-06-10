import Palamedes.V2.Synthesizer

import Mathlib.Lean.Expr
import Lean.Elab.Tactic.NormCast

open Gen CorrectGen

open Lean Meta Elab Tactic Term in
elab "partitionResult" : tactic => do
  let rec get_conjuncts (e: Expr) : TacticM $ (List Expr) := do
    --if let (Expr.app (Expr.app (Expr.const `And _) p) q) := e then
    if e.isAppOf `And then
      --properly deconstructing the ∧ for termination to kick in
      let (Expr.app (Expr.app (Expr.const `And _) p) q) := e | throwUnsupportedSyntax
      let lhs_conjuncts ← get_conjuncts p -- e.getAppArgs[0]!
      let rhs_conjuncts ← get_conjuncts q -- e.getAppArgs[1]!
      return lhs_conjuncts ++ rhs_conjuncts
    else if e.containsConst (λ c => c == `Exists) then
      dbg_trace "contains exists"
      throwUnsupportedSyntax -- TODO: better error
    else
      -- logInfo e.ctorName
      return [e]

  let rec partition (exprs : List Expr) : (List Expr) × (List Expr) :=
      match exprs with
      | .nil => ([],[])
      | .cons e es =>
        let (rest_t,rest_f) := partition es
        if e.hasLooseBVar 1 then
        --if Expr.containsFVar e id then
          (e :: rest_t,rest_f)
        else (rest_t, e :: rest_f)

  let mvarId ← getMainGoal
  mvarId.withContext do
    let mainDecl ← getMainDecl
    let e := mainDecl.type
    logInfo e.ctorName
    if e.isAppOf `Eq then
      --dbg_trace f!"maindecl: {t.isAppOf `CGen}"
      let origOuterLam := e.getAppArgs[2]!
      let (Expr.lam outer_name outer_type t outer_binfo) := origOuterLam | throwUnsupportedSyntax
      -- outer_name is definitely #1!!! otherwise there will be an error due to structure
      if t.isAppOf `Exists then
        let (Expr.lam name type body binfo) := t.getAppArgs[1]! | throwUnsupportedSyntax
        let conjuncts ← get_conjuncts body
        logInfo conjuncts
        -- let (Expr.bvar yidx) := conjuncts[0]!.getAppArgs[3]! | throwUnsupportedSyntax
        -- logInfo f!"yidx: {yidx} {conjuncts[0]!.hasLooseBVar (yidx + 1)}"

        --let id ← outer_name.fvarId!
        let (varIn,varNotIn) := partition conjuncts
        logInfo f!"{varIn}/{varNotIn}"
        if varIn.length < 1 then throwUnsupportedSyntax
        let nameIn := mkAndN $ varIn
        --logInfo nameIn
        let rest := mkAndN $ varNotIn
        --logInfo rest
        let allAnd := mkAnd rest nameIn
        --Reconstruct the exists:
        let newLam := (Expr.lam name type allAnd binfo)
        let newE := mkAppN t.getAppFn #[t.getAppArgs[0]!, newLam]
        logInfo newE
        --Reconstruct the CGen:
        let newOuterLam := Expr.lam outer_name outer_type newE outer_binfo
        --let newCGen := mkAppN e.getAppFn #[e.getAppArgs[0]!, newOuterLam]
        logInfo newOuterLam
        --Change the goal
        let newEMvarId ← mkFreshExprMVar newOuterLam
        --proofterming
        let copyOfNewE ← mkFreshExprMVar newOuterLam
        let simpTheorems ←  #[``and_comm,``and_assoc].foldlM (·.addConst ·) ({} : Meta.SimpTheorems)
        --let ctx ← Simp.mkContext {} #[simpTheorems]
        let (.some resultProof) ← NormCast.proveEqUsing simpTheorems origOuterLam newOuterLam | throwUnsupportedSyntax
        -- let (simpResMV,simpStats) ← simpTarget copyOfNewE.mvarId! ctx
        -- logInfo simpStats.usedTheorems.toArray[2]!.key
        logInfo resultProof.proof?.get!
        logInfo (← inferType resultProof.proof?.get!) --.proof?.get!
        -- let newImpliesOld ← mkArrow newCGen e
        -- let mvarIdImplies ← mkFreshExprMVar newImpliesOld (userName := `helper)
        -- let proofTerm := mkApp mvarIdImplies newEMvarId

        --assign the proof to get things to unify and be done with it?
        mvarId.assign resultProof.proof?.get!
        let e' ← instantiateMVars newOuterLam
        -- let e'_mvar ← mkFreshExprMVar e'
        -- replaceMainGoal [e'_mvar.mvarId!]

        -- let mNew ← mvarId.replaceTargetEq newCGen resultProof.proof?.get!
        -- replaceMainGoal [mNew]

        --run tauto to eliminate implication
        -- let taut_stx ← `(tactic| tauto)
        -- evalTactic taut_stx
      else throwUnsupportedSyntax
    else throwUnsupportedSyntax

def genTwoBetweens2 : CorrectGen (λ (v : Nat × Nat) => ∃ x, (2 ≤ x ∧ x ≤ 6) ∧ ∃ y, 2 ≤ y ∧ y ≤ 100 ∧ v = (x,y)) := by
  -- apply convert (by rfl) (cbind _ _)
  -- --sorry
  -- · gapply (cbetween (by first | aesop | omega))
  -- · intro a
  --   apply convert (by partitionResult) (cbind _ _)
  --   -- on_goal 3 =>
  --   --   gapply (cbetween (by first | aesop | omega))
  --   -- · intro a
  --   --   obtain ⟨val_1, property⟩ := a
  --   --   obtain ⟨left_1, right_1⟩ := property
  --   --   simp_all only
  --   --   apply synth_pure
  --   all_goals sorry
  sorry
