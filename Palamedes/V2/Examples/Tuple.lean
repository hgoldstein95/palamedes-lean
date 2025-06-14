import Palamedes.V2.Synthesizer
import Mathlib.Lean.Expr
import Lean.Elab.Tactic.NormCast

open Gen CorrectGen

-- theorem tup2exists {v : α × β} (P : α → β → Prop) :
--   P v.1 v.2 ↔ ∃ x : α, ∃ y : β, P x y ∧ v = (x,y) :=
--   by aesop

-- theorem tup2exists_fst {v : α × β} (P : α → β → Prop) (Q : α → Prop) :
--   P v.1 v.2 ∧ Q v.1 ↔ ∃ x : α, ∃ y : β, P x y ∧ Q x ∧ v = (x,y) :=
--   by aesop

-- open Lean Meta Elab Tactic Term Conv in
-- elab "tuple2exists" : conv => do
--   let mvarId ← getMainGoal
--   mvarId.withContext do
--     let mainDecl ← getMainDecl
--     let e := mainDecl.type
--     dbg_trace f!"{e.getAppArgs[1]!}"
--     --temporarily peel back correctgen
--     let e' := e.getAppArgs[1]!
--     let (Expr.lam name type body binfo) := e' | throwUnsupportedSyntax
--     -- do something for > 2
--     let flattenProd (prodApp : Expr) : MetaM (List Expr) := do
--       if prodApp.isAppOf `Prod then
--         let a := prodApp.getAppArgs[0]!
--         let b := prodApp.getAppArgs[1]!
--         return [a,b]
--         -- dbg_trace b
--         -- let a' ← if a.isAppOf `Prod then
--         --   flattenProd a
--         -- else
--         --   pure [a]
--         -- let b' ← if b.isAppOf `Prod then
--         --   flattenProd b
--         -- else
--         --   pure [b]
--         -- return a' ++  b'
--       else
--         throwUnsupportedSyntax

--     let [x,y] ← flattenProd type | throwUnsupportedSyntax
--     let lam_idx := body.looseBVarRange - 1
--     let xidx := lam_idx + 1
--     let yidx := lam_idx
--     let newVidx := lam_idx + 2
--     --dbg_trace body
--     let replaced := (body.liftLooseBVars lam_idx 2).replace (fun inner =>
--       if inner.isAppOf `Prod.fst then
--         --dbg_trace inner
--         let appArg := inner.appArg!
--         if appArg.isBVar && appArg.bvarIdx! == newVidx then
--           some (Expr.bvar xidx)
--         --dbg_trace inner.getAppFn[inner.getAppApps.size - 1]!
--         else none
--       else if inner.isAppOf `Prod.snd then
--       let appArg := inner.appArg!
--         if appArg.isBVar && appArg.bvarIdx! == newVidx then
--           some (Expr.bvar yidx)
--         --dbg_trace inner.getAppFn[inner.getAppApps.size - 1]!
--         else none
--       else none
--     )
--     dbg_trace replaced
--     if replaced == (body.liftLooseBVars lam_idx 2) then
--       throwUnsupportedSyntax
--     else
--       dbg_trace (← getLevel type.getAppArgs[1]!)
--       let f ← (mkConst' `Prod.mk)
--       let tup := mkApp4 f x y  (.bvar xidx) (.bvar yidx)
--       let v := (Expr.bvar newVidx)
--       let u ← getLevel type
--       let eq := mkApp3 (mkConst ``Eq [u]) type v tup
--       let newBody := mkAnd replaced eq
--       dbg_trace newBody
--       --create exists x,y
--       let exists_y := mkApp2 (mkConst `Exists [u]) y (mkLambda `y BinderInfo.default y newBody)
--       let exists_x := mkApp2 (mkConst `Exists [u]) x (mkLambda `x BinderInfo.default x exists_y)
--       let newlambda := mkLambda name binfo type exists_x
--       dbg_trace newlambda
--       --let newMvar ← mkFreshExprMVar newlambda
--       --temporarily put back cgen
--       let newcgen := mkApp2 e.getAppFn e.getAppArgs[0]! newlambda
--       dbg_trace newcgen
--       let newMvar ← mkFreshExprMVar newcgen
--       let simpTheorems ←  #[``Prod.mk.injEq, ``and_true, ``exists_eq_right_right', ``tup2exists].foldlM (·.addConst ·) ({} : Meta.SimpTheorems)
--       let (.some resultProof) ← NormCast.proveEqUsing simpTheorems e newcgen | throwUnsupportedSyntax
--       -- mvarId.assign resultProof.proof?.get!
--       modify fun _ => { goals := [newMvar.mvarId!] }


open Lean Meta Elab Tactic Term Conv in
elab "tuple2exists" : conv => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let mainDecl ← getMainDecl
    let e := mainDecl.type
    logInfo e.mdataExpr!
    let e' := e.mdataExpr!.getAppArgs[1]!
    logInfo e'
    let (Expr.lam name type body binfo) := e' | throwUnsupportedSyntax
    -- do something for > 2
    let flattenProd (prodApp : Expr) : MetaM (List Expr) := do
      if prodApp.isAppOf `Prod then
        let a := prodApp.getAppArgs[0]!
        let b := prodApp.getAppArgs[1]!
        return [a,b]
        -- dbg_trace b
        -- let a' ← if a.isAppOf `Prod then
        --   flattenProd a
        -- else
        --   pure [a]
        -- let b' ← if b.isAppOf `Prod then
        --   flattenProd b
        -- else
        --   pure [b]
        -- return a' ++  b'
      else
        throwUnsupportedSyntax
    let [x,y] ← flattenProd type | throwUnsupportedSyntax
    let lam_idx := body.looseBVarRange - 1
    let xidx := lam_idx + 1
    let yidx := lam_idx
    let newVidx := lam_idx + 2
    let replaced := (body.liftLooseBVars lam_idx 2).replace (fun inner =>
      if inner.isAppOf `Prod.fst then
        --dbg_trace inner
        let appArg := inner.appArg!
        if appArg.isBVar && appArg.bvarIdx! == newVidx then
          some (Expr.bvar xidx)
        --dbg_trace inner.getAppFn[inner.getAppApps.size - 1]!
        else none
      else if inner.isAppOf `Prod.snd then
      let appArg := inner.appArg!
        if appArg.isBVar && appArg.bvarIdx! == newVidx then
          some (Expr.bvar yidx)
        --dbg_trace inner.getAppFn[inner.getAppApps.size - 1]!
        else none
      else none
    )
    dbg_trace replaced


def genTupleOneElem : CorrectGen (λ (v: Int × Nat) => v.1 > 2) := by
  conv => (congr; tuple2exists)
  simp_all
  sorry

example: CorrectGen  (λ (v: Int × Nat) => v.1 > 2) = CorrectGen  (λ (v: Int × Nat) => ∃ x y, x > 2 ∧ v = (x, y)) := by
